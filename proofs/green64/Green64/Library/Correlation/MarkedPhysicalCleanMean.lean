module

public import Green64.Library.Correlation.MarkedPhysicalCleanHilbert
public import Green64.Library.Correlation.Part046

@[expose] public section

/-!
# Correlation / MarkedPhysicalCleanMean

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedPhysicalCleanMean -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 400000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 BG m)
variable (cap sizes : BG → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
local notation "Small" => GroupState SP sm (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bm sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP sm BP bm sizes prime
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "BPerm" => BigGroupPerm (BG := BG) (J+ell)
local notation "pat" => sourceOriginalProbeMemoryPattern434 J m hmJ nu
local notation "Frame" => SourceBigAux BP J m pat × (BPerm × BPerm) × (SPerm × SPerm)

/-- The original auxiliary harmonic law and all FOUR independently
averaged endpoint permutations. This weight does not involve the future. -/
def sourceOriginalMarkedPhysicalFrameMass434 (Vb : BG → ℝ) (r : Frame) : ℝ :=
  sourceAuxMass BP bm J m Vb pat r.1 *
    bigEndpointPairMass (BG := BG) (J+ell) *
    groupPermutationPairMass (G := SG) (J+ell)

private theorem frame_mass_nonneg
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g) (r : Frame) :
    0 ≤ sourceOriginalMarkedPhysicalFrameMass434 BP bm J ell m hmJ nu Vb r :=
  mul_nonneg
    (mul_nonneg (source_original_memory_aux_mass_nonneg434 BP bm J m Vb hVb pat r.1)
      (source_original_B26_big_permutation_mass_nonneg434 (J+ell)))
    (groupPermutationPairMass_positive (G := SG) (J+ell)).le

/-- Exact total mass, with the untilted auxiliary law kept distinct from
the tilted active density. No factorial or auxiliary-count loss occurs. -/
theorem source_original_MARKED_PHYSICAL_frame_mass_one434
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g) :
    (∑ r : Frame,sourceOriginalMarkedPhysicalFrameMass434 BP bm J ell m hmJ nu Vb r)=1 := by
  have hn (aux : SourceBigAux BP J m pat) :
      ‖(sourceAuxMass BP bm J m Vb pat aux:ℂ) *
        (bigEndpointPairMass (BG := BG) (J+ell):ℂ) *
        (groupPermutationPairMass (G := SG) (J+ell):ℂ)‖ =
      sourceAuxMass BP bm J m Vb pat aux *
        bigEndpointPairMass (BG := BG) (J+ell) *
        groupPermutationPairMass (G := SG) (J+ell) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (source_original_memory_aux_mass_nonneg434 BP bm J m Vb hVb pat aux),
      abs_of_nonneg (source_original_B26_big_permutation_mass_nonneg434 (G := BG) (J+ell)),
      abs_of_nonneg (groupPermutationPairMass_positive (G := SG) (J+ell)).le]
  have h := source_original_memory_ALL_OUTER_total_mass434 (SG := SG) BP bm
    J ell m Vb hVb hHarmonic pat
  simp_rw [hn] at h
  simpa only [sourceOriginalMarkedPhysicalFrameMass434,Fintype.sum_prod_type] using h

/-- Coherent original averaging: every channel acts on the SAME full
SMALL/active/OLD/seen future before the auxiliary/permutation sum. -/
def sourceOriginalMarkedPhysicalCleanMean434
    (o k : ℤ) (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (K : Frame → Shared → Torus → A → Finset ℕ → A → ℂ)
    (f : Small → A → Finset ℕ → Old → ℂ)
    (xs : Small) (a : A) (S : Finset ℕ) (t : Old) : ℂ :=
  ∑ r : Frame,(sourceOriginalMarkedPhysicalFrameMass434 BP bm J ell m hmJ nu Vb r:ℂ) *
    sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP bm J ell m hmJ nu
      cap sizes hsizes prime r.1 o k q Vs Vb mu
      r.2.2.1 r.2.2.2 r.2.1.1 r.2.1.2 (K r) f xs a S t

/-- Original auxiliary and all endpoint means preserve the verified
physical-sector Hilbert estimate, including arbitrary joint K and future.
The coefficient cap is paid once, not once per endpoint or group. -/
theorem source_original_MARKED_PHYSICAL_mean_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (o k : ℤ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (C : ℝ) (hC : 0 ≤ C)
    (K : Frame → Shared → Torus → A → Finset ℕ → A → ℂ)
    (hK : ∀ r d y a S b,‖K r d y a S b‖ ≤ C)
    (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell cap sizes hsizes prime
      Vs Vb mu
      (sourceOriginalMarkedPhysicalCleanMean434 SP sm BP bm J ell m hmJ nu
        cap sizes hsizes prime o k q Vs Vb mu K f) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell cap sizes hsizes prime
        Vs Vb mu f := by
  let w := sourceOriginalMarkedPhysicalFrameMass434 (SG := SG) BP bm J ell m hmJ nu Vb
  let R (r : Frame) := sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP bm
    J ell m hmJ nu cap sizes hsizes prime r.1 o k q Vs Vb mu
      r.2.2.1 r.2.2.2 r.2.1.1 r.2.1.2 (K r) f
  let E := sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell
    cap sizes hsizes prime Vs Vb mu
  let delta := (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
    (C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g))
  have hw : ∀ r : Frame,0 ≤ w r := frame_mass_nonneg BP bm J ell m hmJ nu Vb hVb
  have h1 : (∑ r : Frame,w r)=1 :=
    source_original_MARKED_PHYSICAL_frame_mass_one434 BP bm J ell m hmJ nu Vb hVb hHarmonic
  let mass (z : Small × Old) (a : A) :=
    sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu
      (z.1,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a z.2)
  have hp (z : Small × Old) (a : A) : 0 ≤ mass z a :=
    source_original_memory_FULL_density_mass_nonneg434 SP sm BP bm J ell cap
      Vs Vb mu hVs hVb hmu _
  have hpoint (z : Small × Old) (a : A) (S : Finset ℕ) :
      ‖∑ r : Frame,(w r:ℂ)*R r z.1 a S z.2‖^2 ≤
      ∑ r : Frame,w r*‖R r z.1 a S z.2‖^2 := by
    have h := source_original_finite_weighted_complex_kernel_CS434
      w hw (fun _ => (1:ℂ)) (fun r => R r z.1 a S z.2)
    simpa only [one_mul,norm_one,one_pow,mul_one,h1] using h
  have hmean : E (sourceOriginalMarkedPhysicalCleanMean434 SP sm BP bm J ell m hmJ nu
      cap sizes hsizes prime o k q Vs Vb mu K f) ≤ ∑ r : Frame,w r*E (R r) := by
    change (∑ z : Small × Old,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
      ∑ a : A,mass z a*‖∑ r : Frame,(w r:ℂ)*R r z.1 a S z.2‖^2) ≤ _
    calc
      _ ≤ ∑ z : Small × Old,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
          ∑ a : A,mass z a*(∑ r : Frame,w r*‖R r z.1 a S z.2‖^2) := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hpoint z a S) (hp z a)
      _ = ∑ z : Small × Old,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
          ∑ r : Frame,w r*(∑ a : A,mass z a*‖R r z.1 a S z.2‖^2) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro S hS
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = ∑ z : Small × Old,∑ r : Frame,w r*
          (∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
            ∑ a : A,mass z a*‖R r z.1 a S z.2‖^2) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [E,sourceOriginalMarkedPhysicalSectorEnergy434,mass,Finset.mul_sum]
  calc
    _ ≤ ∑ r : Frame,w r*E (R r) := hmean
    _ ≤ ∑ r : Frame,w r*(delta*E f) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (hw r)
      exact source_original_MARKED_PHYSICAL_CLEAN_Hilbert434 SP sm BP bm J ell m hmJ nu
        cap sizes hsizes prime hi r.1 o k q hq hq1 Vs hVs Vb hVb mu hmu
        r.2.2.1 r.2.2.2 r.2.1.1 r.2.1.2 C hC (K r) (hK r) f
    _ = _ := by rw [← Finset.sum_mul,h1,one_mul]

variable (P : BG → Finset ℕ)
variable [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]

/-- Canonical original complex K, with its true joint auxiliary ban and
oriented Mellin/Fourier phase. keep can impose the two physical OLD masks. -/
def sourceOriginalMarkedPhysicalCanonicalK434
    (Vb : BG → ℝ) (Q : ℕ) (hA hB xi zeta theta : ℝ) (o k : ℤ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat)
    {R : Type}
    (keep : Shared → R →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Finset ℕ →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Prop)
    (d : Shared) (r : R) :=
  sourceOriginalB26CanonicalNumericCleanK434 J ell m hmJ nu P Vb Q
    hA hB xi zeta theta o k (sourceOriginalB26SmallTupleD434 SP sm J ell d) aux (keep d r)

theorem source_original_MARKED_PHYSICAL_canonical_K_cap434
    (Vb : BG → ℝ) (Q : ℕ) (hA hB xi zeta theta : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (o k : ℤ) (ho : o=1 ∨ o= -1)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat)
    {R : Type}
    (keep : Shared → R →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Finset ℕ →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → Prop)
    (d : Shared) (r : R)
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (S : Finset ℕ)
    (b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) :
    ‖sourceOriginalMarkedPhysicalCanonicalK434 SP sm J ell m hmJ nu P Vb Q
      hA hB xi zeta theta o k aux keep d r a S b‖ ≤ (Q:ℝ)^4*(xi⁻¹)^2 := by
  unfold sourceOriginalMarkedPhysicalCanonicalK434 sourceOriginalB26CanonicalNumericCleanK434
  split_ifs
  · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
    exact source_original_memory_CANONICAL_K_norm434 P Vb J ell m hmJ nu
      Q hA hB xi hhA hhB hxi aux a b
  · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
    exact source_original_memory_CANONICAL_K_norm434 P Vb J ell m hmJ nu
      Q hA hB xi hhA hhB hxi aux b a
  · simp only [norm_zero]
    positivity


variable (pprime : (g : BG) → Fin (sizes g) → {p : ℕ // p ∈ P g})
local notation "PA" => SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell
local notation "POld" => SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
  (fun _ p => (p : ℕ)) sizes pprime
local notation "PTorus" => memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g})
  (fun _ p => (p : ℕ)) sizes pprime
local notation "PFrame" => SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m pat ×
  (BPerm × BPerm) × (SPerm × SPerm)

/-- The complete original auxiliary/endpoint mean for one canonical
comparison pattern, with NO assumed analytic cap on K. The explicit
Q^8 xi^-4 price remains, alongside the marked refresh gain. -/
theorem source_original_MARKED_PHYSICAL_CANONICAL_mean_Hilbert434
    (hi : Function.Injective (fun p : Sigma (fun g => {p : ℕ // p ∈ P g}) => p.2.val))
    (o k : ℤ) (ho : o=1 ∨ o= -1)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : {p : ℕ // p ∈ P g},1/(p.val:ℝ))=Vb g)
    (mu : (g : BG) → {p : ℕ // p ∈ P g} → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Q : ℕ) (hA hB xi zeta theta : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (keep : PFrame → Shared → PTorus → PA → Finset ℕ → PA → Prop)
    (f : Small → PA → Finset ℕ → POld → ℂ) :
    let K := fun r : PFrame => sourceOriginalMarkedPhysicalCanonicalK434
      SP sm J ell m hmJ nu P Vb Q hA hB xi zeta theta o k r.1 (keep r)
    sourceOriginalMarkedPhysicalSectorEnergy434 SP sm
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell cap sizes hsizes pprime Vs Vb mu
      (sourceOriginalMarkedPhysicalCleanMean434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
        J ell m hmJ nu cap sizes hsizes pprime o k q Vs Vb mu K f) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (((Q:ℝ)^4*(xi⁻¹)^2)^2 *
        (∏ g : BG,((∑ p : {p : ℕ // p ∈ P g},mu g p)^2/4)^
          sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalMarkedPhysicalSectorEnergy434 SP sm
        (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
        J ell cap sizes hsizes pprime Vs Vb mu f := by
  dsimp only
  apply source_original_MARKED_PHYSICAL_mean_Hilbert434 SP sm
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) J ell m hmJ nu
    cap sizes hsizes pprime hi o k q hq hq1 Vs hVs Vb hVb hHarmonic mu hmu
    ((Q:ℝ)^4*(xi⁻¹)^2) (by positivity)
  intro r d y a S b
  exact source_original_MARKED_PHYSICAL_canonical_K_cap434 SP sm J ell m hmJ nu
    P Vb Q hA hB xi zeta theta hhA hhB hxi o k ho r.1 (keep r) d y a S b

end Green64Analytic.CorrelationSquare

end

end

