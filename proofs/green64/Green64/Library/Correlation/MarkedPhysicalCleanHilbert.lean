module

public import Green64.Library.Weights.MarkedSmallBigHilbert
public import Green64.Library.Weights.Part057
public import Green64.Library.Correlation.Part045

@[expose] public section

/-!
# Correlation / MarkedPhysicalCleanHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedPhysicalCleanHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

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

/-- The fixed-sector part of the true ordered physical density:
SMALL Haar, every pending mu, one original factorial per group, and
the proved Vb^sizes sector reweighting. -/
def sourceOriginalMarkedPhysicalSectorWeight434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  sourceOriginalB26SectorConstant434 SP sm BP J ell sizes prime Vs mu *
    ∏ g : BG,(Vb g)^(sizes g)

theorem source_original_MARKED_PHYSICAL_density_factor434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (xs : Small) (a : A) (t : Old) :
    sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t) =
    sourceOriginalMarkedPhysicalSectorWeight434 SP sm BP J ell sizes prime Vs Vb mu *
      sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu a := by
  rw [sourceOriginalMemoryFullDensityMass434,
    source_original_B26_SECTOR_PHYSICAL_MASS434,
    source_original_B26_sector_mass_factor434,
    source_original_memory_sector_density_projection434]
  dsimp only [sourceOriginalB26FrozenBigState434]
  unfold sourceOriginalMarkedPhysicalSectorWeight434 sourceOriginalBigRefreshMass434
  ring

/-- Joint physical energy in an actual frozen ordered Fock sector.
The same numerical seen carrier is used at both ends of the operator. -/
def sourceOriginalMarkedPhysicalSectorEnergy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : Small → A → Finset ℕ → Old → ℂ) : ℝ :=
  ∑ z : Small × Old,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
    ∑ a : A,sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu
      (z.1,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a z.2) *
        ‖f z.1 a S z.2‖^2

theorem source_original_MARKED_PHYSICAL_energy_factor434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell cap sizes hsizes
      prime Vs Vb mu f =
    sourceOriginalMarkedPhysicalSectorWeight434 SP sm BP J ell sizes prime Vs Vb mu *
      sourceOriginalMarkedSmallBigEnergy434 SP sm BP bm J ell sizes prime mu f := by
  unfold sourceOriginalMarkedPhysicalSectorEnergy434
  simp_rw [source_original_MARKED_PHYSICAL_density_factor434]
  simp only [sourceOriginalMarkedSmallBigEnergy434,sourceOriginalB26NumericActiveEnergy434,
    Finset.mul_sum,mul_assoc]

/-- The source divisor in the marked channel is exactly the original
physical D. Shared SMALL labels are not external or freshly resampled. -/
theorem source_original_MARKED_PHYSICAL_divisor434
    (aux : SourceBigAux BP J m pat) (xs : Small) (a : A) (t : Old)
    (sigma : BPerm) (ss : SPerm) :
    sourceOrientedPhysicalD SP sm BP bm J ell m cap pat aux
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t)
      sigma ss =
    sourceOriginalB26FrozenD434 BP bm J ell m
      (sourceOriginalB26SmallTupleD434 SP sm J ell
        (memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs))
      pat aux a sigma := by
  have hd :
      (∏ g : SG,∏ i ∈ sourceSmallShared J ell g,
        sm g (marks (sm g) (J+ell) (xs g) (ss g i))) =
      sourceOriginalB26SmallTupleD434 SP sm J ell
        (memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs) := by
    unfold sourceOriginalB26SmallTupleD434
    apply Finset.prod_congr rfl
    intro g hg
    simpa only [Finset.univ_eq_attach,memoryOriginalSmallGroupSharedLabels,
      memoryOriginalSmallSharedLabels] using
      (Finset.prod_attach (sourceSmallShared J ell g)
        (fun i => sm g (marks (sm g) (J+ell) (xs g) (ss g i)))).symm
  simpa only [hd] using source_original_B26_FROZEN_D_from_original434
    SP sm BP bm J ell m cap sizes hsizes prime xs a
    (memoryOriginalSmallGroupResidue SP sm (J+ell) xs,t) pat aux sigma ss

/-- One literal CLEAN channel with both actual physical endpoint kernels.
BIG legality and the original no-store/no-promotion branch coefficient at
rho=1 are read from the frozen ordered state. K retains the whole joint
coefficient and may include both OLD masks. Its cap is paid explicitly. -/
def sourceOriginalMarkedPhysicalCleanChannel434
    (aux : SourceBigAux BP J m pat) (o k : ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (ss tt : SPerm) (sigma tau : BPerm)
    (K : Shared → Torus → A → Finset ℕ → A → ℂ)
    (f : Small → A → Finset ℕ → Old → ℂ)
    (xs : Small) (a : A) (S : Finset ℕ) (t : Old) : ℂ :=
  let d := memoryOriginalSmallGroupSharedLabels SP sm (J+ell) (sourceSmallShared J ell) ss xs
  let r : Torus := (memoryOriginalSmallGroupResidue SP sm (J+ell) xs,t)
  let D := sourceOrientedPhysicalD SP sm BP bm J ell m cap pat aux
    (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap sizes hsizes prime a t) sigma ss
  let step := o*k*(D:ℤ)
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  if (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) a).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S then
    ∑ b : A,sourceOriginalB26FrozenPhysicalCoefficient434 SP sm BP bm
      J ell m cap sizes hsizes prime mu Vb pat a b sigma tau D step r *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu (eT b)).image
          (fun p : Sigma BP => bm p.1 p.2)) then
        K d r (eS a) S (eT b) *
          ∑ ys : Small,groupPermutedKernel SP sm (J+ell) q Vs
            (sourceSmallShared J ell) step (fun _ _ => 1) ss tt xs ys *
            f ys b (S ∪ (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu (eT b)).image
              (fun p : Sigma BP => bm p.1 p.2))
              (fun g i => t g i+(step : ZMod (bm g (prime g i))))
       else 0)
  else 0

/-- Exact factorization of the literal marked physical channel, preserving
the original source D, signed shift and SAME future at its updated seen. -/
theorem source_original_MARKED_PHYSICAL_channel_factor434
    (aux : SourceBigAux BP J m pat) (o k : ℤ)
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (ss tt : SPerm) (sigma tau : BPerm)
    (K : Shared → Torus → A → Finset ℕ → A → ℂ)
    (f : Small → A → Finset ℕ → Old → ℂ)
    (xs : Small) (a : A) (S : Finset ℕ) (t : Old) :
    sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP bm J ell m hmJ nu
      cap sizes hsizes prime aux o k q Vs Vb mu ss tt sigma tau K f xs a S t =
    sourceOriginalMarkedSmallBigComposite434 SP sm BP bm J ell m hmJ nu sizes prime
      aux o k q Vs mu ss tt sigma tau K f xs a S t := by
  unfold sourceOriginalMarkedPhysicalCleanChannel434
  dsimp only
  rw [source_original_MARKED_PHYSICAL_divisor434]
  simp_rw [source_original_B26_FROZEN_PHYSICAL_coefficient434]
  unfold sourceOriginalMarkedSmallBigComposite434 sourceOriginalMarkedSmallSynthesis434
    sourceOriginalSmallEndpointSynthesis434 sourceOriginalB26NumericResidueClean434
  dsimp only
  split_ifs with hs
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs with hn
    · rw [source_original_SMALL_row_endpoint_factor434 SP sm J ell q hq Vs hVs]
      simp only [sourceOriginalMarkedSmallHalf434,memory_frozen_residue_actual_translate]
      ring
    · simp only [mul_zero]
  · simp only [mul_zero]

/-- A quantitative bound for the actual marked SMALL/BIG CLEAN channel
in its unchanged physical Fock-sector density. Every original pending
factor and factorial cancels only because the operator preserves the
sector; no new density is installed between its two endpoints. -/
theorem source_original_MARKED_PHYSICAL_CLEAN_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (aux : SourceBigAux BP J m pat) (o k : ℤ)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (ss tt : SPerm) (sigma tau : BPerm) (C : ℝ) (hC : 0 ≤ C)
    (K : Shared → Torus → A → Finset ℕ → A → ℂ)
    (hK : ∀ d r a S b,‖K d r a S b‖ ≤ C)
    (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell cap sizes hsizes
      prime Vs Vb mu
      (sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP bm J ell m hmJ nu
        cap sizes hsizes prime aux o k q Vs Vb mu ss tt sigma tau K f) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (C^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)) *
      sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP bm J ell cap sizes hsizes
        prime Vs Vb mu f := by
  have hw : 0 ≤ sourceOriginalMarkedPhysicalSectorWeight434
      SP sm BP J ell sizes prime Vs Vb mu :=
    mul_nonneg (source_original_B26_sector_constant_nonneg434 SP sm BP J ell
      sizes prime Vs hVs mu hmu)
      (Finset.prod_nonneg (fun g _ => pow_nonneg (hVb g).le _))
  have he :
      sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP bm J ell m hmJ nu
        cap sizes hsizes prime aux o k q Vs Vb mu ss tt sigma tau K f =
      sourceOriginalMarkedSmallBigComposite434 SP sm BP bm J ell m hmJ nu sizes prime
        aux o k q Vs mu ss tt sigma tau K f := by
    funext xs a S t
    exact source_original_MARKED_PHYSICAL_channel_factor434 SP sm BP bm J ell m hmJ nu
      cap sizes hsizes prime aux o k q hq.le Vs hVs Vb mu ss tt sigma tau K f xs a S t
  rw [he,source_original_MARKED_PHYSICAL_energy_factor434,
    source_original_MARKED_PHYSICAL_energy_factor434]
  have h := mul_le_mul_of_nonneg_left
    (source_original_MARKED_SMALL_BIG_Hilbert434 SP sm BP bm J ell m hmJ nu sizes prime
      hi aux o k q hq hq1 Vs hVs mu (fun g p => (hmu g p).le)
      ss tt sigma tau C hC K hK f) hw
  convert h using 1 <;> ring

end Green64Analytic.CorrelationSquare

end

end

