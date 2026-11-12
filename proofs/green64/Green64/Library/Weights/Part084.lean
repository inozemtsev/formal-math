module

public import Green64.Library.Weights.MarkedSmallSharpEnergy
public import Green64.Library.Weights.Part083

@[expose] public section

/-!
# Weights / Part084

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26SharpRawHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
variable (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Small" => GroupState SP sm (J+ell)
local notation "Old" => SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "BPerm" => BigGroupPerm (BG := G) (J+ell)

/-- Quantitative bound for the independent RAW channel after both true
SMALL maps and all OLD translations. The original mixed RAW divisor,
Nodup and numerical seen are retained. There is no Q/xi coefficient cost. -/
theorem source_original_B26_SHARP_RAW_SMALL_BIG_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (ss tt : SPerm) (sigma tau : BPerm) (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ => Subtype.val) J ell sizes prime mu
      (sourceOriginalB26NodupRawChannel434 SP sm P J ell m hmJ nu sizes prime mu
        q Vs zeta theta o k ss tt sigma tau f) ≤
    (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs)^2 *
      (∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ => Subtype.val) J ell sizes prime mu f := by
  let cost := sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs
  let delta := ∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g
  have hc : 0 ≤ cost := source_original_SMALL_sharp_cost_nonneg434 ell q hq1 Vs hVs
  have hd : 0 ≤ delta :=
    Finset.prod_nonneg (fun g _ => pow_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) _)
  let F := sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ => Subtype.val) J ell sizes prime q Vs tt f
  let H := fun d : Shared => sourceOriginalB26NodupRawResidue434 SP sm P J ell m hmJ nu sizes prime mu
    (sourceOriginalB26SmallTupleD434 SP sm J ell d) zeta theta o k sigma tau (F d)
  have he :
      sourceOriginalB26NodupRawChannel434 SP sm P J ell m hmJ nu sizes prime mu
        q Vs zeta theta o k ss tt sigma tau f =
      sourceOriginalMarkedSmallSynthesis434 SP sm BP (fun _ => Subtype.val) J ell sizes prime q Vs ss H := by
    funext xs a S t
    exact source_original_B26_NODUP_RAW_CHANNEL_FACTOR434 SP sm P J ell m hmJ nu
      sizes prime mu q hq.le Vs hVs zeta theta o k ss tt sigma tau f xs a S t
  have hbig (d : Shared) :
      sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu (H d) ≤
      delta*sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu (F d) :=
    source_original_B26_NODUP_RAW_RESIDUE_Hilbert434 P J ell m hmJ nu SP sm sizes prime
      hi mu hmu (sourceOriginalB26SmallTupleD434 SP sm J ell d) zeta theta o k ho sigma tau (F d)
  have hs := source_original_MARKED_SMALL_sharp_synthesis_energy434 SP sm BP (fun _ => Subtype.val)
    J ell sizes prime q hq hq1 Vs hVs mu hmu ss H
  have ht := source_original_MARKED_SMALL_sharp_half_energy434 SP sm BP (fun _ => Subtype.val)
    J ell sizes prime q hq hq1 Vs hVs mu hmu tt f
  rw [he]
  calc
    _ ≤ cost*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu (H d)) := hs
    _ ≤ cost*(∑ d : Shared,delta*sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu (F d)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d _ => hbig d)) hc
    _ = (cost*delta)*(∑ d : Shared,sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu (F d)) := by
      rw [←Finset.mul_sum]
      ring
    _ ≤ (cost*delta)*(cost*sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ => Subtype.val)
        J ell sizes prime mu f) := mul_le_mul_of_nonneg_left ht (mul_nonneg hc hd)
    _ = _ := by dsimp only [cost,delta]; ring

/-- The same RAW gain in the unchanged true physical Fock-sector
density, including every pending prime weight and its original factorial. -/
theorem source_original_B26_SHARP_RAW_PHYSICAL_SECTOR_Hilbert434
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Vb : G → ℝ) (hVb : ∀ g,0 < Vb g)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (ss tt : SPerm) (sigma tau : BPerm) (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap sizes hsizes prime
      Vs Vb mu (sourceOriginalB26NodupRawChannel434 SP sm P J ell m hmJ nu sizes prime mu
        q Vs zeta theta o k ss tt sigma tau f) ≤
    (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs)^2 *
      (∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
        J ell cap sizes hsizes prime Vs Vb mu f := by
  have hw : 0 ≤ sourceOriginalMarkedPhysicalSectorWeight434 SP sm BP J ell sizes prime Vs Vb mu :=
    mul_nonneg (source_original_B26_sector_constant_nonneg434 SP sm BP J ell
      sizes prime Vs hVs mu hmu) (Finset.prod_nonneg (fun g _ => pow_nonneg (hVb g).le _))
  rw [source_original_MARKED_PHYSICAL_energy_factor434,source_original_MARKED_PHYSICAL_energy_factor434]
  have h := mul_le_mul_of_nonneg_left
    (source_original_B26_SHARP_RAW_SMALL_BIG_Hilbert434 SP sm P J ell m hmJ nu sizes prime
      hi mu (fun g p => (hmu g p).le) q hq hq1 Vs hVs zeta theta o k ho ss tt sigma tau f) hw
  convert h using 1 <;> ring


end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26SharpRawFull -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Explicit coherent RAW energy budget. The original tilted masses
and SMALL costs remain; there is no conductor Q or cell width xi. -/
def sourceOriginalB26SharpRawFamilyHilbertBudget434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (blockA blockB : Finset G) (q : ℝ) (Vs : SG → ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ) : ℝ :=
  ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ) *
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q Vs)^2 *
        ∏ g : G,((∑ p : {p : ℕ // p ∈ P g},mu g p)^2/4)^
          sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g

variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
variable (data : SourceComparisonData434 SG G cfg x L Y Hp)
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
variable (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
variable (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
variable (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
local notation "BP" => (fun g => {p : ℕ // p ∈ data.Tb g})
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Small" => GroupState SP sm (J+ell)
local notation "Old" => SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)
local notation "BPerm" => BigGroupPerm (BG := G) (J+ell)
local notation "mu" => physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
local notation "Budget" => sourceOriginalB26SharpRawFamilyHilbertBudget434 data.Tb J ell m hmJ
  blockA blockB q data.Vsmall mu
local notation "E" => sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
  J ell cap sizes hsizes prime data.Vsmall data.Vbig mu

/-- The literal coherent two-block RAW family, with all four independent
endpoint signs and its arbitrary joint SMALL/OLD/seen future, obeys the
explicit conductor-free budget in the same true physical sector density. -/
theorem source_original_B26_SHARP_RAW_PHYSICAL_FAMILY_Hilbert434
    (hq : 0 < q) (hq1 : q < 1) (ho : o=1 ∨ o= -1)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (hmu : ∀ g (p : BP g),0 < mu g p)
    (sigma tau : SourceOriginalProbePattern434 G m → BPerm)
    (epsSrc epsTgt : Bool) (ss tt : SPerm) (f : Small → A → Finset ℕ → Old → ℂ) :
    E (sourceOriginalB26NodupPhysicalRawFamily434 data SP sm sizes prime cap hsizes
      q N blockA blockB J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f) ≤
    Budget * E f := by
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let sign := fun nu : SourceOriginalProbePattern434 G m =>
    sourceOriginalB26NumericSharedSign434 (Fintype.card SG) J ell m hmJ nu epsSrc epsTgt
  let R := fun nu : family => sourceOriginalB26NodupRawChannel434 SP sm data.Tb
    J ell m hmJ nu.val sizes prime mu q data.Vsmall zeta theta o k ss tt (sigma nu.val) (tau nu.val) f
  let gain := fun nu : family => (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q data.Vsmall)^2 *
    ∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu.val g
  have hVs (g : SG) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hsign (nu : family) : ‖sign nu.val‖=1 := by
    unfold sign sourceOriginalB26NumericSharedSign434
    split_ifs <;> simp
  have hR (nu : family) : E (fun xs a S t => sign nu.val*R nu xs a S t) ≤ gain nu * E f := by
    have he : E (fun xs a S t => sign nu.val*R nu xs a S t) = E (R nu) := by
      unfold sourceOriginalMarkedPhysicalSectorEnergy434
      simp only [norm_mul,hsign,one_mul]
    rw [he]
    exact source_original_B26_SHARP_RAW_PHYSICAL_SECTOR_Hilbert434 SP sm data.Tb
      J ell m hmJ nu.val sizes prime cap hsizes hi mu hmu q hq hq1 data.Vsmall hVs data.Vbig hVb
      zeta theta o k ho ss tt (sigma nu.val) (tau nu.val) f
  let w := fun (z : Small × Old) (a : A) =>
    sourceOriginalMemoryFullDensityMass434 SP sm BP (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu
      (z.1,sourceOriginalB26FrozenBigState434 BP (fun _ => Subtype.val) J ell cap sizes hsizes prime a z.2)
  have hw (z : Small × Old) (a : A) : 0 ≤ w z a :=
    source_original_memory_FULL_density_mass_nonneg434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu hVs hVb hmu _
  have he :
      sourceOriginalB26NodupPhysicalRawFamily434 data SP sm sizes prime cap hsizes
        q N blockA blockB J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f =
      (fun xs a S t => ∑ nu : family,(1:ℂ)*(sign nu.val*R nu xs a S t)) := by
    funext xs a S t
    simpa only [one_mul,sourceOriginalB26NodupPhysicalRawFamily434,R,sign] using
      (Finset.sum_coe_sort family (fun nu => sign nu *
        sourceOriginalB26NodupRawChannel434 SP sm data.Tb J ell m hmJ nu sizes prime mu
          q data.Vsmall zeta theta o k ss tt (sigma nu) (tau nu) f xs a S t)).symm
  have hb := source_original_RAW_weighted_history_energy434
    (sourceOriginalMemoryBirthPool434 BP (fun _ => Subtype.val)) w hw
    (fun _ : family => (1:ℝ)) (fun _ => zero_le_one)
    (fun nu z a S => sign nu.val*R nu z.1 a S z.2) (fun nu => gain nu*E f) hR
  rw [he]
  calc
    _ ≤ (∑ _nu : family,(1:ℝ))*∑ nu : family,(1:ℝ)*(gain nu*E f) := hb
    _ = Budget * E f := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,one_mul]
      rw [←Finset.sum_mul,←mul_assoc]
      congr 1
      simp only [Fintype.card_coe,sourceOriginalB26SharpRawFamilyHilbertBudget434,gain]
      congr 1
      exact Finset.sum_coe_sort family (fun nu =>
        (sourceOriginalSharpSmallConditioningConstant434 (SG := SG) ell q data.Vsmall)^2 *
          ∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)

/-- All four original endpoint permutation means preserve the explicit
RAW bound, without a factorial or permutation-cardinality loss. -/
theorem source_original_B26_SHARP_RAW_PHYSICAL_MEAN_Hilbert434
    (hq : 0 < q) (hq1 : q < 1) (ho : o=1 ∨ o= -1)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (hmu : ∀ g (p : BP g),0 < mu g p)
    (epsSrc epsTgt : Bool) (f : Small → A → Finset ℕ → Old → ℂ) :
    E (sourceOriginalB26NodupPhysicalRawMean434 data SP sm sizes prime cap hsizes
      q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤ Budget * E f := by
  let Index := (SPerm × SPerm) × (BPerm × BPerm)
  let cs := groupPermutationPairMass (G := SG) (J+ell)
  let cb := bigEndpointPairMass (BG := G) (J+ell)
  let alpha := cs*cb
  let R := fun st : Index => sourceOriginalB26NodupPhysicalRawFamily434 data SP sm sizes prime cap hsizes
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
    epsSrc epsTgt st.1.1 st.1.2 f
  have hVs (g : SG) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  let w := fun (z : Small × Old) (a : A) =>
    sourceOriginalMemoryFullDensityMass434 SP sm BP (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu
      (z.1,sourceOriginalB26FrozenBigState434 BP (fun _ => Subtype.val) J ell cap sizes hsizes prime a z.2)
  have hw (z : Small × Old) (a : A) : 0 ≤ w z a :=
    source_original_memory_FULL_density_mass_nonneg434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu hVs hVb hmu _
  have ha : 0 ≤ alpha :=
    mul_nonneg (source_original_B26_big_permutation_mass_nonneg434 (G := SG) (J+ell))
      (source_original_B26_big_permutation_mass_nonneg434 (G := G) (J+ell))
  have hS : (∑ st : SPerm × SPerm,cs)=1 :=
    source_original_B26_big_permutation_mass_total434 (G := SG) (J+ell)
  have hB : (∑ st : BPerm × BPerm,cb)=1 :=
    source_original_B26_big_permutation_mass_total434 (G := G) (J+ell)
  have htotal : (∑ st : Index,alpha)=1 := by
    change (∑ st : (SPerm × SPerm) × (BPerm × BPerm),cs*cb)=1
    rw [Fintype.sum_prod_type]
    simp only [←Finset.mul_sum,hB,mul_one,hS]
  have hR (st : Index) : E (R st) ≤ Budget * E f :=
    source_original_B26_SHARP_RAW_PHYSICAL_FAMILY_Hilbert434 data SP sm sizes prime cap hsizes
      q N blockA blockB J ell m hmJ Q h xi zeta theta o k
      hq hq1 ho hi hmu (fun _ => st.2.1) (fun _ => st.2.2) epsSrc epsTgt st.1.1 st.1.2 f
  have hb := source_original_RAW_weighted_history_energy434
    (sourceOriginalMemoryBirthPool434 BP (fun _ => Subtype.val)) w hw
    (fun _ : Index => alpha) (fun _ => ha) (fun st z a S => R st z.1 a S z.2)
    (fun _ => Budget*E f) hR
  change E (sourceOriginalB26NodupPhysicalRawMean434 data SP sm sizes prime cap hsizes
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
      (∑ st : Index,alpha)*∑ _st : Index,alpha*(Budget*E f) at hb
  simpa only [htotal,←Finset.sum_mul,one_mul] using hb

end Green64Analytic.CorrelationSquare

namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
variable (data : SourceComparisonData434 SG G cfg x L Y Hp)
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
variable (cap : G → ℕ) (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
variable (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
variable (epsSrc epsTgt : Bool)
local notation "BP" => (fun g => {p : ℕ // p ∈ data.Tb g})
local notation "State" => FullPhysicalState SP sm BP (fun _ => Subtype.val) (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP (fun _ => Subtype.val) (J+ell)
local notation "mu" => physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
local notation "Budget" => sourceOriginalB26SharpRawFamilyHilbertBudget434 data.Tb J ell m hmJ
  blockA blockB q data.Vsmall mu
local notation "E" => sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
  J ell cap data.Vsmall data.Vbig mu

/-- Conductor-free quantitative RAW estimate on the FULL ordered
physical Fock times numerical-seen carrier. Sector weights, factorials
and the joint future are unchanged; no sector count is charged. -/
theorem source_original_B26_SHARP_RAW_FULL_ORDERED_Hilbert434
    (hq : 0 < q) (hq1 : q < 1) (ho : o=1 ∨ o= -1)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (hmu : ∀ g (p : BP g),0 < mu g p) (f : State → Finset ℕ → ℂ) :
    E (sourceOriginalB26NodupFullOrderedRaw434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤ Budget * E f := by
  rw [source_original_MARKED_ordered_energy_sectors434,
    source_original_MARKED_ordered_energy_sectors434,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  let sizes : G → ℕ := fun g => (d.1 g).val
  let prime : (g : G) → Fin (sizes g) → BP g := d.2
  have hsz (g : G) : sizes g ≤ cap g := Nat.le_of_lt_succ (d.1 g).isLt
  let F := fun (xs : GroupState SP sm (J+ell)) (a : SourceOriginalB26Active434 BP J ell)
      (S : Finset ℕ) (t : SourceOriginalMarkedSectorOld434 BP (fun _ => Subtype.val) cap d) =>
    f (sourceOriginalMarkedSectorEmbed434 SP sm BP (fun _ => Subtype.val) J ell cap d xs a t) S
  change sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
    J ell cap sizes hsz prime data.Vsmall data.Vbig mu
    (sourceOriginalB26NodupPhysicalRawMean434 data SP sm sizes prime cap hsz q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt F) ≤
    Budget * sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap sizes hsz prime data.Vsmall data.Vbig mu F
  exact source_original_B26_SHARP_RAW_PHYSICAL_MEAN_Hilbert434 data SP sm sizes prime cap hsz
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k hq hq1 ho hi hmu epsSrc epsTgt F

/-- The same explicit RAW estimate after original Fock orbit averaging. -/
theorem source_original_B26_SHARP_RAW_FULL_ORBIT_Hilbert434
    (hq : 0 < q) (hq1 : q < 1) (ho : o=1 ∨ o= -1)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (hmu : ∀ g (p : BP g),0 < mu g p) (F : Out → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu
      (sourceOriginalB26NodupFullOrbitRaw434 data SP sm cap q N blockA blockB
        J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt F) ≤
    Budget * sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu F := by
  have hVs (g : SG) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  apply le_trans (source_original_MARKED_orbit_compression_energy434 SP sm BP (fun _ => Subtype.val)
    J ell cap data.Vsmall data.Vbig mu hVs hVb hmu _)
  have h := source_original_B26_SHARP_RAW_FULL_ORDERED_Hilbert434 data SP sm cap q N blockA blockB
    J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt hq hq1 ho hi hmu
    (fun b T => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap b) T)
  rw [source_original_MARKED_ordered_orbit_energy434] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

