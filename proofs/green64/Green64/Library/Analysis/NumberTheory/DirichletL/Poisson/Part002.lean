module

public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part008
public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Poisson / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes -/

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

namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

def nonzeroLatticeEnvelopeConstant : ℝ :=
  4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass

theorem nonzeroLatticeEnvelopeConstant_nonneg :
    0 ≤ nonzeroLatticeEnvelopeConstant := by
  have := eisensteinCauchyMass_nonneg
  unfold nonzeroLatticeEnvelopeConstant
  positivity

theorem scaled_cauchy_nonzero_mass (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤
        nonzeroLatticeEnvelopeConstant := by
  let F : ℝ → ℂ := fun x => (((1 + x) ^ 2)⁻¹ : ℝ)
  have hF (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 * ‖F x‖ ≤ 1 := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_inv_cancel₀ (by positivity : (1 + x) ^ 2 ≠ 0)]
  have hh := lattice_profile_nonzero_scaled_bound F 1 (by norm_num) hF t ht
  change t * (∑' h : {h : O // h ≠ 0}, ‖F (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
    nonzeroLatticeEnvelopeConstant * 1 at hh
  simpa only [F, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((1 + t * ‖eisEmbedding _‖ ^ 2) ^ 2)⁻¹ by positivity),
    mul_one] using hh

theorem nonzero_lattice_envelope_sum
    (t C : ℝ) (ht : 0 < t) (hC : 0 ≤ C)
    (f : {h : O // h ≠ 0} → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hbound : ∀ h, (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * f h ≤ C) :
    Summable f ∧ t * (∑' h, f h) ≤ nonzeroLatticeEnvelopeConstant * C := by
  have hp (h : {h : O // h ≠ 0}) :
      f h ≤ C * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hbound h
  have hs := (scaled_eisenstein_cauchy_summable t ht).subtype (fun h : O => h ≠ 0)
  have hfs : Summable f := Summable.of_nonneg_of_le hf hp (hs.mul_left C)
  refine ⟨hfs, ?_⟩
  have hh := hfs.tsum_le_tsum hp (hs.mul_left C)
  rw [tsum_mul_left] at hh
  calc
    _ ≤ t * (C * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
    _ = C * (t * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
    _ ≤ C * nonzeroLatticeEnvelopeConstant :=
      mul_le_mul_of_nonneg_left (scaled_cauchy_nonzero_mass t ht) hC
    _ = _ := mul_comm _ _

end EisensteinSchwartzPoisson

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def originalMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose

def dualMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose

theorem originalMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ originalMiddleDecayConstant W :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem dualMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ dualMiddleDecayConstant W :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem divisorBlockCost_mono_coefficients
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (D₁ D₂ B N : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (a a₀ : n → ℂ) (b b₀ : p → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ ‖a₀ j‖) (hb : ∀ k, ‖b k‖ ≤ ‖b₀ k‖) :
    divisorBlockCost ε hε D₁ D₂ B N a b ≤ divisorBlockCost ε hε D₁ D₂ B N a₀ b₀ := by
  have hA := sieveNorm_nonneg B (N / D₁)
  have hB := sieveNorm_nonneg B (N / D₂)
  unfold divisorBlockCost
  gcongr
  · exact ha _
  · exact hb _

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

def dualMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) :
    0 ≤ originalMiddleAt W S T rows left right a b M h := by
  unfold originalMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) :
    0 ≤ dualMiddleAt W S T rows left right a b M F h := by
  unfold dualMiddleAt
  positivity

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows ha hb

theorem actual_original_middle_all_frequencies
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
        2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := Real.sqrt (M / B) / (D₁ * D₂)
  have ht : 0 < t := by dsimp only [t]; positivity
  let C := originalMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (originalMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ 2 * t * C := by
    have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M
      hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ originalMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (originalMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h.val‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : Real.sqrt (M / B) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt (M / B) / (D₁ * D₂) = 2 * t := by dsimp only [t]; ring
    rw [hpre] at hp
    change originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * (2 * t * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = 2 * t * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ 2 * t * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t (2 * t * C) ht (by positivity)
    _ (fun h => originalMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * (2 * t * C) := hv
    _ = _ := by dsimp only [C]; ring

end

theorem dual_middle_scale_identity (M F B N : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N) :
    Real.sqrt ((M / F) / B) = (M / (F * N)) * (N * Real.sqrt (F / (M * B))) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ (M / F) / B by positivity),
    Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem actual_dual_middle_all_frequencies
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
        (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N)) *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := (N * Real.sqrt (F / (M * B))) / (D₁ * D₂)
  let r := M / (F * N)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr0 : 0 < r := by dsimp only [r]; positivity
  let C := dualMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (dualMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ (2 * t * r) * C := by
    have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M F
      hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ dualMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (dualMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h.val‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF) (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) = 2 * t * r := by
      rw [dual_middle_scale_identity M F B N hM hF (by linarith) (by linarith)]
      dsimp only [t, r]
      ring
    rw [hpre] at hp
    change dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * ((2 * t * r) * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = (2 * t * r) * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ (2 * t * r) * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t ((2 * t * r) * C) ht (by positivity)
    _ (fun h => dualMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M F h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * ((2 * t * r) * C) := hv
    _ = _ := by dsimp only [C, r]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def divisorExponentConstant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) : ℝ :=
  (h.divisor_pair deltaLoss hδ).choose

theorem divisorExponentConstant_pos {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    0 < divisorExponentConstant h deltaLoss hδ := (h.divisor_pair deltaLoss hδ).choose_spec.1

theorem divisor_cost_with_constant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (B N D₁ D₂ : ℝ)
    (hB : 1 ≤ B) (hN : 1 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) ≤
      divisorEnergyFactor ε hε N a b *
        (divisorExponentConstant h deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂))) := by
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ B N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left
    ((h.divisor_pair deltaLoss hδ).choose_spec.2 B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

theorem sqrt_div_mul_rpow (M B α : ℝ) (hM : 0 ≤ M) (hB : 0 < B) :
    Real.sqrt (M / B) * B ^ α = Real.sqrt M * B ^ (α - 1 / 2) := by
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow, Real.sqrt_div hM]
  ring

theorem original_middle_scale_shape (M B N D T α : ℝ)
    (hM : 0 ≤ M) (hB : 0 < B) (hD : D ≤ T * Real.sqrt (M / B)) :
    N + B ^ α * D ≤ N + T * Real.sqrt M * B ^ (α - 1 / 2) := by
  calc
    _ ≤ N + B ^ α * (T * Real.sqrt (M / B)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hB.le α))
    _ = _ := by rw [mul_left_comm (B ^ α) T, mul_comm (B ^ α), sqrt_div_mul_rpow M B α hM hB]; ring

theorem dual_middle_scale_shape (M F B N D T α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N)
    (hD : D ≤ T * (N * Real.sqrt (F / (M * B)))) :
    (M / (F * N)) * (N + B ^ α * D) ≤
      M / F + T * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hratio : 0 ≤ M / (F * N) := by positivity
  calc
    _ ≤ (M / (F * N)) * (N + B ^ α * (T * (N * Real.sqrt (F / (M * B))))) := by gcongr
    _ = M / F + T * (Real.sqrt ((M / F) / B) * B ^ α) := by
      rw [dual_middle_scale_identity M F B N hM hF hB hN]
      field_simp

    _ = _ := by rw [sqrt_div_mul_rpow (M / F) B α (by positivity) hB]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.original_middle_block
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * Real.sqrt (M / B)) :
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + U * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (originalMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc hk)
    _ = ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          (N + B ^ α * (D₁ * D₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (original_middle_scale_shape M B N (D₁ * D₂) U α hM.le (by linarith) hcut) (by positivity)

theorem HasSieveExponent.dual_middle_block
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * (N * Real.sqrt (F / (M * B)))) :
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + U * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (dualMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N))) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          ((M / (F * N)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁ * D₂) U α hM hF (by linarith) (by linarith) hcut) (by positivity)

end CanonicalQuadraticSieve

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology Matrix MatrixGroups

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def integralComplexMatrix : SL(2,O) →* SL(2,ℂ) := Matrix.SpecialLinearGroup.map eisEmbedding

@[simp] lemma integralComplexMatrix_apply (M : SL(2,O)) (i j : Fin 2) :
    integralComplexMatrix M i j = eisEmbedding (M i j) := rfl

lemma integralComplexMatrix_levelThree (M : levelThree) :
    integralComplexMatrix (M : SL(2,O)) = complexMatrix M := rfl

lemma row_wedge_gram (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) +
      Complex.normSq (u 0*star (v 0)+u 1*star (v 1)) = rowEnergy u * rowEnergy v := by
  simp only [rowEnergy,← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma row_wedge_le_energy (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) ≤ rowEnergy u * rowEnergy v := by
  rw [← row_wedge_gram u v]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

lemma bottom_row_wedge_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) 0 * complexBottomRow h 1 -
      complexBottomRow (g*h) 1 * complexBottomRow h 0 = g 1 0 := by
  have hd : h 0 0*h 1 1-h 0 1*h 1 0=1 := by
    simpa only [Matrix.det_fin_two] using h.property
  simp only [complexBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination g 1 0 * hd

theorem hyperbolicHeight_mul_bound (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicHeight (g • w) * hyperbolicHeight w * Complex.normSq (g 1 0) ≤ 1 := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) ≤ 1
    have hw := row_wedge_le_energy (complexBottomRow (g*h)) (complexBottomRow h)
    rw [bottom_row_wedge_mul] at hw
    have hp : 0 < rowEnergy (complexBottomRow (g*h)) * rowEnergy (complexBottomRow h) :=
      mul_pos (rowEnergy_pos _ (complexBottomRow_ne_zero _))
        (rowEnergy_pos _ (complexBottomRow_ne_zero _))
    have he : liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) =
        Complex.normSq (g 1 0) /
          (rowEnergy (complexBottomRow (g*h))*rowEnergy (complexBottomRow h)) := by
      simp only [liftedHeight,div_eq_mul_inv,mul_inv]
      ring
    rw [he]
    exact (div_le_one hp).mpr hw

lemma one_le_normSq_embedding (c : O) (hc : c≠0) : 1 ≤ Complex.normSq (eisEmbedding c) := by
  rw [Complex.normSq_eq_norm_sq,eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))

theorem integral_hyperbolicHeight_mul_le_one (M : SL(2,O)) (hc : M 1 0≠0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w) * hyperbolicHeight w ≤ 1 := by
  have hb := hyperbolicHeight_mul_bound (integralComplexMatrix M) w
  have hc1 := one_le_normSq_embedding (M 1 0) hc
  have hp := mul_pos (hyperbolicHeight_pos (integralComplexMatrix M • w)) (hyperbolicHeight_pos w)
  change _ * _ * Complex.normSq (eisEmbedding (M 1 0)) ≤ 1 at hb
  nlinarith

def cuspHoroball (σ : SL(2,O)) (Y : ℝ) : Set HyperbolicSpace :=
  {w | Y < hyperbolicHeight (integralComplexMatrix σ⁻¹ • w)}

theorem cuspHoroball_disjoint (σ τ : SL(2,O)) (Y Z : ℝ)
    (hY : 1≤Y) (hZ : 1≤Z) (hc : (σ⁻¹*τ) 1 0≠0) :
    Disjoint (cuspHoroball σ Y) (cuspHoroball τ Z) := by
  apply Set.disjoint_left.mpr
  intro w hwσ hwτ
  have hprod := integral_hyperbolicHeight_mul_le_one (σ⁻¹*τ) hc
    (integralComplexMatrix τ⁻¹ • w)
  simp only [map_mul,map_inv,mul_smul,smul_inv_smul] at hprod
  have hσ : 1 < hyperbolicHeight (integralComplexMatrix σ⁻¹ • w) := lt_of_le_of_lt hY hwσ
  have hτ : 1 < hyperbolicHeight (integralComplexMatrix τ⁻¹ • w) := lt_of_le_of_lt hZ hwτ
  simp only [map_inv] at hσ hτ
  nlinarith [mul_pos (sub_pos.mpr hσ) (sub_pos.mpr hτ)]

def InequivalentCusps (σ τ : SL(2,O)) : Prop :=
  ∀ M : levelThree, (σ⁻¹*(M : SL(2,O))*τ) 1 0≠0

def cuspNeighborhood (σ : SL(2,O)) (Y : ℝ) : Set HyperbolicSpace :=
  {w | ∃ M : levelThree, w ∈ cuspHoroball ((M : SL(2,O))*σ) Y}

lemma cuspNeighborhood_invariant (σ : SL(2,O)) (Y : ℝ) (M : levelThree) (w : HyperbolicSpace) :
    complexMatrix M • w ∈ cuspNeighborhood σ Y ↔ w ∈ cuspNeighborhood σ Y := by
  constructor
  · rintro ⟨N,hN⟩
    refine ⟨M⁻¹*N,?_⟩
    change Y < hyperbolicHeight (integralComplexMatrix (((M⁻¹*N : levelThree) : SL(2,O))*σ)⁻¹ • w)
    change Y < hyperbolicHeight (integralComplexMatrix ((N : SL(2,O))*σ)⁻¹ • (complexMatrix M • w)) at hN
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,inv_inv,map_mul,map_inv,mul_smul,
      integralComplexMatrix_levelThree] using hN
  · rintro ⟨N,hN⟩
    refine ⟨M*N,?_⟩
    change Y < hyperbolicHeight (integralComplexMatrix (((M*N : levelThree) : SL(2,O))*σ)⁻¹ • (complexMatrix M • w))
    change Y < hyperbolicHeight (integralComplexMatrix ((N : SL(2,O))*σ)⁻¹ • w) at hN
    simpa only [Subgroup.coe_mul,mul_inv_rev,map_mul,map_inv,mul_smul,
      integralComplexMatrix_levelThree,inv_smul_smul] using hN

theorem cuspNeighborhood_disjoint (σ τ : SL(2,O)) (hστ : InequivalentCusps σ τ)
    (Y Z : ℝ) (hY : 1≤Y) (hZ : 1≤Z) :
    Disjoint (cuspNeighborhood σ Y) (cuspNeighborhood τ Z) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨M,hM⟩ ⟨N,hN⟩
  apply Set.disjoint_left.mp (cuspHoroball_disjoint ((M : SL(2,O))*σ) ((N : SL(2,O))*τ) Y Z hY hZ ?_) hM hN
  have hc := hστ (M⁻¹*N)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,mul_assoc] using hc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma cosetHeight_pos (x : CuspCosets) (w : HyperbolicSpace) : 0<cosetHeight x w := by
  induction x using Quotient.inductionOn with
  | _ M => exact (cosetHeight_cosetOf M w).symm ▸ hyperbolicHeight_pos _

lemma cosetHeight_rightEquiv (M : levelThree) (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight (rightEquiv M x) w = cosetHeight x (complexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf (N*M)) w = cosetHeight (cosetOf N) (complexMatrix M • w)
    rw [cosetHeight_cosetOf,cosetHeight_cosetOf,map_mul,mul_smul]

lemma high_coset_unique (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace)
    (x y : CuspCosets) (hx : Y<cosetHeight x w) (hy : Y<cosetHeight y w) : x=y := by
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      by_contra hne
      have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0≠0 := by
        intro hc
        have hT : M*N⁻¹ ∈ cuspStabilizer := (mem_cuspStabilizer_iff _).mpr hc
        exact hne ((cosetOf_eq_iff M N).mpr ⟨M*N⁻¹,hT,by group⟩)
      have hp := integral_hyperbolicHeight_mul_le_one
        ((M*N⁻¹ : levelThree) : SL(2,O)) hc (complexMatrix N • w)
      rw [integralComplexMatrix_levelThree,map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change Y<cosetHeight (cosetOf M) w at hx
      change Y<cosetHeight (cosetOf N) w at hy
      rw [cosetHeight_cosetOf] at hx hy
      have hm := lt_of_le_of_lt hY hx
      have hn := lt_of_le_of_lt hY hy
      nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hn)]

lemma high_cosets_finite (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace) :
    Set.Finite {x : CuspCosets | Y<cosetHeight x w} := by
  have h : Set.Subsingleton {x : CuspCosets | Y<cosetHeight x w} :=
    fun x hx y hy => high_coset_unique Y hY w x y hx hy
  exact h.finite

def cuspCutoffTerm (Y : ℝ) (F : ℝ → ℂ) (x : CuspCosets) (w : HyperbolicSpace) : ℂ :=
  if Y<cosetHeight x w then (cosetCharacter x)⁻¹ * F (cosetHeight x w) else 0

lemma cuspCutoffTerm_finiteSupport (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x => cuspCutoffTerm Y F x w) := by
  apply (high_cosets_finite Y hY w).subset
  intro x hx
  by_contra hn
  simp only [Function.mem_support] at hx
  change ¬Y<cosetHeight x w at hn
  exact hx (by simp [cuspCutoffTerm,hn])

lemma cuspCutoffTerm_summable (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Summable (fun x => cuspCutoffTerm Y F x w) :=
  summable_of_hasFiniteSupport (cuspCutoffTerm_finiteSupport Y hY F w)

def cuspCutoffCorrection (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑'x,cuspCutoffTerm Y F x w

lemma cuspCutoffTerm_automorphy (Y : ℝ) (F : ℝ → ℂ) (M : levelThree)
    (x : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm Y F x (complexMatrix M • w) =
      complexCharacter M * cuspCutoffTerm Y F (rightEquiv M x) w := by
  have hM : complexCharacter M≠0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  simp only [cuspCutoffTerm,cosetHeight_rightEquiv,cosetCharacter_rightEquiv]
  split_ifs <;> simp [mul_inv_rev,hM,mul_assoc,mul_left_comm,mul_comm]

theorem cuspCutoffCorrection_automorphy (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (M : levelThree) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (complexMatrix M • w) = complexCharacter M*cuspCutoffCorrection Y F w := by
  have hsum := cuspCutoffTerm_summable Y hY F w
  have hreindex := (rightEquiv M).hasSum_iff.mpr hsum.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact (cuspCutoffTerm_summable Y hY F (complexMatrix M • w)).hasSum.unique
    (hscale.congr_fun (fun x => cuspCutoffTerm_automorphy Y F M x w))

lemma cuspCutoffCorrection_eq (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (w : HyperbolicSpace) (x : CuspCosets) (hx : Y<cosetHeight x w) :
    cuspCutoffCorrection Y F w = (cosetCharacter x)⁻¹*F (cosetHeight x w) := by
  unfold cuspCutoffCorrection
  rw [tsum_eq_single x]
  · simp [cuspCutoffTerm,hx]
  · intro y hy
    have hn : ¬Y<cosetHeight y w := fun hh => hy (high_coset_unique Y hY w y x hh hx)
    simp [cuspCutoffTerm,hn]

lemma hyperbolicHeight_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (upperPoint z v hv)=v := by
  have h := hyperbolicHeight_action_upperPoint 1 z v hv
  simpa [Matrix.one_apply] using h

def infinityConstantMode (s : ℂ) (v : ℝ) : ℂ :=
  if hv : 0<v then eisensteinFourierCoefficient v hv s 0 else 0

def truncatedAtInfinity (Y : ℝ) (s : ℂ) (w : HyperbolicSpace) : ℂ :=
  hyperbolicEisenstein s w-cuspCutoffCorrection Y (infinityConstantMode s) w

theorem truncatedAtInfinity_automorphy (Y : ℝ) (hY : 1≤Y) (s : ℂ) (hs : 2<s.re)
    (M : levelThree) (w : HyperbolicSpace) :
    truncatedAtInfinity Y s (complexMatrix M • w) = complexCharacter M*truncatedAtInfinity Y s w := by
  rw [truncatedAtInfinity,hyperbolicEisenstein_automorphy M s hs,
    cuspCutoffCorrection_automorphy Y hY]
  unfold truncatedAtInfinity
  ring

theorem truncatedAtInfinity_upperPoint (Y : ℝ) (hY : 1≤Y) (s : ℂ)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hYv : Y<v) :
    truncatedAtInfinity Y s (upperPoint z v hv) =
      upperEisenstein z v hv s-eisensteinFourierCoefficient v hv s 0 := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [truncatedAtInfinity,cuspCutoffCorrection_eq Y hY _ _ (cosetOf 1) (hh.symm ▸ hYv),
    hh,cosetCharacter_cosetOf,map_one,inv_one,one_mul,hyperbolicEisenstein_upperPoint]
  rw [infinityConstantMode,dite_eq_left hv]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.SupportNorms -/

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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem sourceSupportMobius_norm (E : Finset ι) :
    ‖supportMobius (fun i => Ideal.span {p i}) E‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj E)
  simp only [norm_mul, norm_one] at h
  nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) E)]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem norm_primeProduct_ge_one (S : Finset ι) :
    1 ≤ ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
  have h := primeProductNorm_ge_one p hp S
  dsimp only [primeProductNorm] at h
  nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ S, p i))]

include hp hinj in
theorem secondSourceCommonCoefficient_norm_le_one
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (G E : Finset ι) :
    ‖secondSourceCommonCoefficient p hg Ψ m c d G E‖ ≤ 1 := by
  have hA := (secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)
  have hA2 : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hN := primeProductNorm_ge_one p hp E
  have hμ := sourceSupportMobius_norm p hinj E
  change ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ)‖ = 1 at hμ
  simp only [secondSourceCommonCoefficient, norm_mul, norm_div,
    Complex.norm_of_nonneg (sq_nonneg _), primeSubsetGenerator_norm_eq_productNorm,
    Complex.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp E).le, hμ]
  exact (mul_le_of_le_one_left (div_nonneg zero_le_one (zero_le_one.trans hN))
    hA2).trans ((div_le_one (by linarith)).mpr hN)

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d H S‖ ≤ ‖H S‖ := by
  have he : secondInputCoefficient p hg Ψ m c d H S =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) S * H S := by
    simp only [secondInputCoefficient, mul_one]
  rw [he, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((secondInputCoefficient_norm_le p hg Ψ m c d S).trans (hΨ _))

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_schwartz_bound (g : 𝓢(ℝ, ℂ)) (X : ℝ) (S : Finset ι) :
    ‖normalizedColumn p (fun U => g (columnLog p X U)) S‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
  simp only [normalizedColumn, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact (div_le_self (norm_nonneg _) (norm_primeProduct_ge_one p hp S)).trans (g.norm_le_seminorm ℝ _)

include hp hinj in
theorem residualPairWeight_schwartz_bound
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O) (g : 𝓢(ℝ, ℂ)) (X : ℝ)
    (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 g) ^ 2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S).trans
    (normalizedColumn_schwartz_bound p hp g X (G∪S))
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) T).trans
    (normalizedColumn_schwartz_bound p hp g X (G∪T))
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) (apply_nonneg _ _)

include hp in
theorem residualPairWeight_support_bounds
    (Ψ : O →* ℂ) (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (G E S T : Finset ι) (hEG : E ⊆ G)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T ≠ 0) :
    primeProductNorm p G ≤ X*Real.exp M ∧ primeProductNorm p E ≤ X*Real.exp M ∧
      primeProductNorm p S ≤ X*Real.exp M ∧ primeProductNorm p T ≤ X*Real.exp M := by
  obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hG := normalizedColumn_subset_norm_bound p hp g M X hX hgM G S G Finset.subset_union_left hS
  exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G S S Finset.subset_union_right hS,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G T T Finset.subset_union_right hT⟩

end
section

theorem tail_radial_scalar_le (Y E n lengthScale H P : ℝ) (A : ℕ)
    (hY : 0 < Y) (hE : 0 < E) (hn : 1 ≤ n) (hL : 1 ≤ lengthScale)
    (hden : E*n^2 ≤ lengthScale^3) (hH : 0 ≤ H) (hP : 0 ≤ P) :
    (Y/n) * (P / ((min 1 (Y/(E*n^2)))^2 * (1+H)^A)) ≤
      Y*P*(1+lengthScale^3/Y)^2 / (1+H)^A := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : 0 < E*n^2 := mul_pos hE (sq_pos_of_pos hn0)
  have hs : 0 < Y/(E*n^2) := div_pos hY he
  have hr : 0 ≤ lengthScale^3/Y := div_nonneg (pow_nonneg (zero_le_one.trans hL) _) hY.le
  have hi : (min 1 (Y/(E*n^2)))⁻¹ ≤ 1+lengthScale^3/Y := by
    by_cases h : 1 ≤ Y/(E*n^2)
    · rw [min_eq_left h, inv_one]
      linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), inv_div]
      exact (div_le_div_of_nonneg_right hden hY.le).trans (by linarith)
  have hi0 : 0 ≤ (min 1 (Y/(E*n^2)))⁻¹ := inv_nonneg.mpr (le_min zero_le_one hs.le)
  have hi2 := pow_le_pow_left₀ hi0 hi 2
  have hyn : Y/n ≤ Y := div_le_self hY.le hn
  calc
    _ = (Y/n)*P*((min 1 (Y/(E*n^2)))⁻¹)^2 / (1+H)^A := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hyn hP) hi2 (sq_nonneg _) (mul_nonneg hY.le hP)

theorem sum_pair_indicator {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (U : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, if P a ∧ P b then U else 0) =
      ((s.filter P).card : ℝ)^2 * U := by
  calc
    _ = ∑ a ∈ s.filter P, ∑ b ∈ s.filter P, U := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : P a
      · simp only [h, true_and, ite_true]
      · simp only [h, false_and, ite_false, Finset.sum_const_zero]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, pow_two]; ring

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hp hinj

theorem residualTailCost_polynomial
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X Y H lengthScale P : ℝ) (A : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hXL : X * Real.exp M ≤ lengthScale) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * ((SchwartzMap.seminorm ℝ 0 0 g)^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := (SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
    (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hG,hE,hS,hT⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M X hX hgM G E S T hEG hw
    exact ⟨hG.trans hXL,hE.trans hXL,hS.trans hXL,hT.trans hXL⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [ite_eq_left hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [ite_eq_left hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [ite_eq_left ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_schwartz_bound p hp hg hinj Ψ hΨ m c d g X G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [ite_eq_right hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [ite_eq_right hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [ite_eq_left hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [ite_eq_right hd]
    exact hz.le

theorem secondSourceTailCost_polynomial
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X Y H lengthScale P : ℝ) (A : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hXL : X * Real.exp M ≤ lengthScale) (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (fun S => normalizedColumn p (fun U => g (columnLog p X U)) (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := (SchwartzMap.seminorm ℝ 0 0 g)^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [ite_eq_left hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_polynomial p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d g M X Y H lengthScale P A hX hY hH hP hL hXL hgM
            rw [ite_eq_left hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [ite_eq_right hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_polynomial p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d g M X Y H lengthScale P A hX hY hH hP hL hXL hgM
        rw [ite_eq_right hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg hB _) hC)
    _ = _ := by ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

theorem firstCoreSecondCutoff_tail_polynomial
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
          (Y*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := firstCoreSecondCutoff_tail_bound p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  dsimp only
  have hX' : 0 < X / primeProductNorm p D :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hgbase : ∀ u, firstCoreBaseProfile g V negative u ≠ 0 → |u| ≤ M := by
    intro u hu
    apply hgM u
    intro hz
    apply hu
    simp only [firstCoreBaseProfile_apply, hz, zero_mul]
  have hP : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := mul_nonneg hC.le (apply_nonneg _ _)
  exact (hb F D Ψ m c d g V W negative t X Y M H hX hY hH hgM).trans
    (secondSourceTailCost_polynomial p hp hg hinj (F\D) Ψ hΨ m c d
      (firstCoreBaseProfile g V negative) M (X / primeProductNorm p D) Y H
      (1 + X / primeProductNorm p D * Real.exp M) (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) A
      hX' hY hH hP (by linarith [mul_pos hX' (Real.exp_pos M)]) (by linarith) hgbase)

theorem firstCoreSecondCutoff_tail_fixed_source
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A : ℕ) (g V W : 𝓢(ℝ, ℂ)) (negative : Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        C*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^A := by
  obtain ⟨s,C,hC,hb⟩ := firstCoreSecondCutoff_tail_polynomial p hp hg hinj hc A
  let C₀ := 128^4 * (SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀, by linarith, ?_⟩
  intro F D Ψ m c d t X Y M H hΨ hX hY hH hgM
  dsimp only
  have h := hb F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  apply h.trans
  calc
    _ = C₀*(1+X/primeProductNorm p D*Real.exp M)^4*Y*
        (1+(1+X/primeProductNorm p D*Real.exp M)^3/Y)^2/(1+H)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_complete_finite_transfer
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (D₀ E₀ V₀ X₀ K₀ : Finset ι → κ → ℝ) (Y : ℝ),
        (∀ R j, 0 < D₀ R j) → (∀ R j, 0 < E₀ R j) → (∀ R j, 0 < V₀ R j) →
        (∀ R j, 0 < X₀ R j) → (∀ R j, 0 < K₀ R j) → 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z t : ℝ) (Srows : Finset O)
        (label : Finset ι → SecondExpansionData ι → κ)
        (T : Finset ι → κ → Finset (Ideal O × O)) (lengthScale : Finset ι → κ → ℝ),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        (∀ R ∈ (F\A₀).powerset, ∀ j, 0 ≤ lengthScale R j) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorZ p
            (secondExpansionScale p (X / primeProductNorm p A₀)
              (primeSubsetGenerator (fun i => Ideal.span {p i}) R) (expansionSupportData C D x))
            (X₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorUd p (D₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorUe p (E₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorUv p (V₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          |secondSectorKap p (K₀ R j) (expansionSupportData C D x)| ≤ H) →
        (∀ R ∈ (F\A₀).powerset, ∀ j,
          ∀ x ∈ secondDyadicSector (F\A₀) (firstCoreSecondCutoff p A₀ X Y M Z) R label j,
          (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
            secondSupportRow p (expansionSupportData C D x)) ∈ T R j) →
        (∀ R ∈ (F\A₀).powerset, ∀ j, ∀ q ∈ T R j, q.1 ≠ ⊥) →
        (∀ R ∈ (F\A₀).powerset, ∀ j, ∀ q ∈ T R j, (Ideal.absNorm q.1 : ℝ) ≤ lengthScale R j) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Ltail := 1 + X' * Real.exp M
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        let _Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
        (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖ ^ 2) +
          ‖firstCoreTest (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X)
            negative t A₀ ∅‖ ^ 2 ≤
        (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖ ^ 2) +
            (∑ z : SecondRayIndex, ∑ R ∈ (F\A₀).powerset, ∑ j : κ,
              (Y * ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) R)‖ ^ 2 /
                  X' ^ 2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (lengthScale R j * Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
                (1+Y*K₀ R j/(D₀ R j*(E₀ R j)^2*(V₀ R j)^2*(X₀ R j)^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R) (T R j)
                (windows 5) (windows 6) (X₀ R j) (X₀ R j) J) +
            Ctail*Ltail^4*Y*(1+Ltail^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    firstCoreInputRow_finite_second_transfer (κ := κ) p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M H hM hH hgM ε hε decayOrder J
  obtain ⟨Ctail,hCtail,htail⟩ :=
    firstCoreSecondCutoff_tail_fixed_source p hp hg hinj hc tailOrder g V rowMajorant negative
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
    A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows label T lengthScale hv hCB hD hΨ hX hZ hSrows hSrows0
    hL hz hud hue huv hkap hmap hT hnorm
  dsimp only
  have hf := htrans D₀ E₀ V₀ X₀ K₀ Y hD₀ hE₀ hV₀ hX₀ hK₀ hY
    A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows label T lengthScale hv hCB hD hΨ hX hZ hSrows hSrows0
    hL hz hud hue huv hkap hmap hT hnorm
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have ht := htail F A₀ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) t X Y M Z hΨ' hX hY hZ hgM
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact le_rfl
    · exact ht
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem sqrt_scale_shell_upper (M B b : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hb : B / 2 ≤ b) : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
  simpa only [one_mul, div_one] using principal_middle_prefactor_bound
    M B b 1 1 1 1 hM hB hb (by norm_num) le_rfl (by norm_num) le_rfl

theorem original_middle_rectangle_upper (M B b D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * Real.sqrt (M / b)) :
    D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B) := by
  calc
    _ ≤ d * e := mul_le_mul hd he hD₂ (hD₁.trans hd)
    _ ≤ U * Real.sqrt (M / b) := hcut
    _ ≤ U * (2 * Real.sqrt (M / B)) :=
      mul_le_mul_of_nonneg_left (sqrt_scale_shell_upper M B b hM hB hb) hU
    _ = _ := by ring

theorem dual_middle_rectangle_upper (M F B b N D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : B / 2 ≤ b) (hN : 0 ≤ N) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * (N * Real.sqrt (F / (M * b)))) :
    D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B))) := by
  have harg (z : ℝ) : F / (M * z) = (F / M) / z := by ring
  simp only [harg] at hcut ⊢
  have hh := original_middle_rectangle_upper (F / M) B b D₁ D₂ d e (U * N)
    (div_pos hF hM) hB hb (mul_nonneg hU hN) hD₁ hD₂ hd he
    (by simpa only [mul_assoc] using hcut)
  simpa only [mul_assoc] using hh

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

def dualMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalMiddleWindowAt W S T rows left right a b M P h ∧
    originalMiddleWindowAt W S T rows left right a b M P h ≤
      originalMiddleAt W S T rows left right a b M h := by
  classical
  constructor
  · unfold originalMiddleWindowAt
    positivity
  · unfold originalMiddleWindowAt originalMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualMiddleWindowAt W S T rows left right a b M F P h ∧
    dualMiddleWindowAt W S T rows left right a b M F P h ≤
      dualMiddleAt W S T rows left right a b M F h := by
  classical
  constructor
  · unfold dualMiddleWindowAt
    positivity
  · unfold dualMiddleWindowAt dualMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    originalMiddleWindowAt W S T rows left right a b M P h = 0 := by
  classical
  simp only [originalMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    dualMiddleWindowAt W S T rows left right a b M F P h = 0 := by
  classical
  simp only [dualMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows -/

section

namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.original_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    originalMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B)
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.original_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply original_middle_rectangle_upper M B (Ideal.absNorm (rows i)) D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM (by linarith) (hrows i).2.1 hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) = fun _ => 0 :=
      funext (fun h => originalMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.dual_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U *
        (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    dualMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M F P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B)))
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.dual_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W F hF hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM hF (by linarith) (hrows i).2.1 (by linarith) hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) = fun _ => 0 :=
      funext (fun h => dualMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M F P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FourierBridge

theorem large_principal_scale_shape (X N Q D V : ℝ) (hD : 0 < D)
    (hcut : X * N ≤ V * D) :
    (X / D) * (N + Q * D) ≤ V + X * Q := by
  have hh : X * N / D ≤ V := (div_le_iff₀ hD).mpr hcut
  calc
    _ = X * N / D + X * Q := by field_simp
    _ ≤ _ := add_le_add hh le_rfl

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalCorrectionAt (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
  (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
  (a : n → ℂ) (b : p → ℂ)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hleft hright

theorem principalCorrectionAt_bound :
    principalCorrectionAt S T rows left right a b M ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hh := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b
    (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add, logPhase_zero, mul_one] at hh
  have heq : (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖) =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ := by
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E.val i j k‖)]
    apply Finset.sum_congr rfl
    intro D hD
    exact Finset.sum_coe_sort T (fun E => ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)
  have hp := principal_middle_prefactor_sum S T rows
    (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖)
    (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
    (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
  change principalCorrectionAt S T rows left right a b M ≤ _ at hp
  rw [heq] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem HasSieveExponent.large_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (V : ℝ)
    (hcut : Real.sqrt (M / B) * N ≤ V * (D₁ * D₂)) :
    principalCorrectionAt S T rows left right a b M ≤
      2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (V + Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hb := principalCorrectionAt_bound ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have hf := divisorEnergyFactor_nonneg ε hε N a b
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        (divisorEnergyFactor ε hε N a b *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        ((Real.sqrt (M / B) / (D₁ * D₂)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        (V + Real.sqrt (M / B) * B ^ α) := mul_le_mul_of_nonneg_left
      (large_principal_scale_shape _ _ _ _ _ (by positivity) hcut) (by positivity)
    _ = _ := by rw [sqrt_div_mul_rpow M B α hM.le (by linarith)]

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem sum_two_subtype_pools {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (f : Ideal O → Ideal O → A) :
    (∑ D : S, ∑ E : T, f D.val E.val) = ∑ D ∈ S, ∑ E ∈ T, f D E := by
  rw [Finset.sum_coe_sort S (fun D => ∑ E : T, f D E.val)]
  apply Finset.sum_congr rfl
  intro D hD
  exact Finset.sum_coe_sort T (f D)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold originalMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M P h := by
  classical
  simp_rw [originalMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.original_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.original_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply originalMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply originalMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact originalMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold dualMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M F P h := by
  classical
  simp_rw [dualMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.dual_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M F P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.dual_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W F hF P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply dualMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply dualMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact dualMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M F P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor {n p : Type*} [Fintype n] [Fintype p]
    (u : n → p → ℂ) (z : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z)‖ = c * ‖∑ j, ∑ k, u j k * z‖ := by
  simp only [← Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (M : ℝ) (h : O)
    (d : Ideal O) (i : m) : ℂ :=
  ((Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) *
      ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def originalProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalProductDivisorMiddleAt W K rows left right a b M P h := by
  classical
  unfold originalProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    originalProductDivisorMiddleAt W K rows left right a b M P h ≤
      originalMiddleWindowAt W S T rows left right a b M (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i _ _ => originalPrincipalKernel W rows M h d i)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [originalMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold originalPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.original_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.original_middle_pool deltaLoss hδ ε hε S T B N M U hB hN hM hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := originalProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => originalProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

end

end OAI

end

