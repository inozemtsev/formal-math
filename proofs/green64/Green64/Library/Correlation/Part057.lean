module

public import Green64.Library.Weights.B26NodupMarkedSmallCleanRawSaving
public import Green64.Library.Weights.MarkedCleanMeanLiteral

@[expose] public section

/-!
# Correlation / Part057

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26NodupPhysicalChannelLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
variable (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
variable (Vb : G → ℝ) (mu : (g : G) → ((fun g => {p : ℕ // p ∈ P g})) g → ℝ)

/-- Literal allowed auxiliary row, including the original auxiliary/ACTIVE
ban, the numerical birth-list Nodup, and each auxiliary's own full shift. -/
def sourceOriginalB26NodupAllowedResidue434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (Vb : G → ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall Q : ℕ) (hA hB xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : (BigGroupPerm (BG := G) (J+ell))) (F : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) → Finset ℕ → (memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime) → ℂ)
    (a : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)) (S : Finset ℕ) (r : (memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime)) : ℂ :=
  if (sourceOriginalBigRefreshPacket434 ((fun g => {p : ℕ // p ∈ P g})) (fun _ => J+ell) a).image
      (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val) ⊆ S then
    ∑ b : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell),sourceOriginalB26FrozenFreshLaw434 ((fun g => {p : ℕ // p ∈ P g})) J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) a b sigma tau *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
        (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
          (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val)) ∧
        sourceOriginalB26NumericBirthNodup434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu tau b then
        ∑ aux : SourceBigAux ((fun g => {p : ℕ // p ∈ P g})) J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu),(sourceAuxMass ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J m Vb (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux:ℂ) *
          (if sourceOriginalB26FrozenAuxBan434 ((fun g => {p : ℕ // p ∈ P g})) J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux a b then
            originalEdgeScalar
              (sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q hA hB xi aux
                (fun g i => a g (sigma g i)) (fun g i => b g (tau g i)))
              zeta theta (sourceOriginalB26FrozenD434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m dsmall (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux a sigma) o k *
            F b (S ∪ (sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
                (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val))
              (r+memoryFrozenResidueShift SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) sizes prime
                (o*k*(sourceOriginalB26FrozenD434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m dsmall (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux a sigma:ℤ)))
           else 0)
       else 0)
  else 0

/-- Independent literal RAW comparator, with its true RAW divisor and shift.
It is defined directly, rather than by subtracting an already bounded error. -/
def sourceOriginalB26NodupRawResidue434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (sigma tau : (BigGroupPerm (BG := G) (J+ell))) (F : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) → Finset ℕ → (memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime) → ℂ)
    (a : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)) (S : Finset ℕ) (r : (memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime)) : ℂ :=
  if (sourceOriginalBigRefreshPacket434 ((fun g => {p : ℕ // p ∈ P g})) (fun _ => J+ell) a).image
      (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val) ⊆ S then
    ∑ b : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell),sourceOriginalB26FrozenFreshLaw434 ((fun g => {p : ℕ // p ∈ P g})) J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) a b sigma tau *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
        (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
          (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val)) ∧
        sourceOriginalB26NumericBirthNodup434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu tau b then
        originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta
          (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu dsmall a b sigma tau) o k *
        F b (S ∪ (sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
          (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
            (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val))
          (r+memoryFrozenResidueShift SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) sizes prime
            (o*k*(sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
              dsmall a b sigma tau:ℤ)))
       else 0)
  else 0

/-- Original CLEAN joint K and its literal residue row agree exactly.
The inverse permutations in K are discharged before the actual ban is tested. -/
theorem source_original_B26_NODUP_AUX_RESIDUE_LITERAL434
    (d : (SourceOriginalB26SharedTuple434 SP J ell)) (Q : ℕ) (hA hB xi zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0) (sigma tau : (BigGroupPerm (BG := G) (J+ell)))
    (F : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) → Finset ℕ → (memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime) → ℂ) (a : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)) (S : Finset ℕ) (r : (memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime)) :
    (∑ aux : SourceBigAux ((fun g => {p : ℕ // p ∈ P g})) J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu),(sourceAuxMass ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J m Vb (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux:ℂ) *
      sourceOriginalB26NumericResidueClean434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu
        (sourceOriginalB26SmallTupleD434 SP sm J ell d) aux o k
        (memoryFrozenResidueShift SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) sizes prime) mu sigma tau
        (sourceOriginalMarkedCleanJointK434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu aux sigma tau
          (sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q hA hB xi)
          zeta theta o k d) F a S r) =
    sourceOriginalB26NodupAllowedResidue434 SP sm P J ell m hmJ nu sizes prime Vb mu
      (sourceOriginalB26SmallTupleD434 SP sm J ell d) Q hA hB xi zeta theta o k
      sigma tau F a S r := by
  unfold sourceOriginalB26NumericResidueClean434 sourceOriginalMarkedCleanJointK434
    sourceOriginalB26NodupAllowedResidue434 sourceOriginalB26NumericBirthNodup434
  dsimp only
  simp only [Equiv.symm_apply_apply]
  by_cases hs : (sourceOriginalBigRefreshPacket434 ((fun g => {p : ℕ // p ∈ P g})) (fun _ => J+ell) a).image
      (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val) ⊆ S
  · simp only [if_pos hs,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hf : Disjoint S ((sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
      (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
        (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val))
    <;> by_cases hn : (sourceOriginalMarkedCleanBirthNumbers434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ nu)
      (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).Nodup
    <;> simp only [hf,hn,ho,true_and,and_true,false_and,and_false,
      ite_true,ite_false,mul_zero,zero_mul,Finset.sum_const_zero,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro aux haux
    by_cases ha : sourceOriginalB26FrozenAuxBan434 (fun g => {p : ℕ // p ∈ P g})
      J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux a b
    <;> simp [ha,hk,sourceOriginalB26EndpointPermutationEquiv434]
    <;> ring
  · simp [hs]

variable (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)

/-- The allowed residue row, between both actual SMALL endpoint maps,
is the original physical CLEAN auxiliary sum with the exact joint K. -/
theorem source_original_B26_NODUP_PHYSICAL_AUX_CHANNEL_LITERAL434
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Q : ℕ) (hA hB xi zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0) (ss tt : (GroupPermFamily (G := SG) (J+ell))) (sigma tau : (BigGroupPerm (BG := G) (J+ell)))
    (f : (GroupState SP sm (J+ell)) → (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) → Finset ℕ → (SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime) → ℂ)
    (xs : (GroupState SP sm (J+ell))) (a : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)) (S : Finset ℕ) (t : (SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime)) :
    (∑ aux : SourceBigAux ((fun g => {p : ℕ // p ∈ P g})) J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu),(sourceAuxMass ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J m Vb (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux:ℂ) *
      sourceOriginalMarkedPhysicalCleanChannel434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu
        cap sizes hsizes prime aux o k q Vs Vb mu ss tt sigma tau
        (sourceOriginalMarkedCleanJointK434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu aux sigma tau
          (sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q hA hB xi)
          zeta theta o k) f xs a S t) =
    sourceOriginalMarkedSmallSynthesis434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell sizes prime q Vs ss
      (fun d => sourceOriginalB26NodupAllowedResidue434 SP sm P J ell m hmJ nu
        sizes prime Vb mu (sourceOriginalB26SmallTupleD434 SP sm J ell d)
        Q hA hB xi zeta theta o k sigma tau
        (sourceOriginalMarkedSmallHalf434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell sizes prime q Vs tt f d))
      xs a S t := by
  calc
    _ = ∑ aux : SourceBigAux ((fun g => {p : ℕ // p ∈ P g})) J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu),(sourceAuxMass ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J m Vb (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux:ℂ) *
        sourceOriginalMarkedSmallBigComposite434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu sizes prime
          aux o k q Vs mu ss tt sigma tau
          (sourceOriginalMarkedCleanJointK434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu aux sigma tau
            (sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q hA hB xi)
            zeta theta o k) f xs a S t := by
      apply Finset.sum_congr rfl
      intro aux haux
      rw [source_original_MARKED_PHYSICAL_channel_factor434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu
        cap sizes hsizes prime aux o k q hq Vs hVs]
    _ = _ := by
      unfold sourceOriginalMarkedSmallBigComposite434 sourceOriginalMarkedSmallSynthesis434
        sourceOriginalSmallEndpointSynthesis434
      dsimp only
      rw [← source_original_B26_NODUP_AUX_RESIDUE_LITERAL434 SP sm P J ell m hmJ nu
        sizes prime Vb mu _ Q hA hB xi zeta theta o k ho hk sigma tau]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro aux haux
      ring

/-- The direct RAW channel has the real SMALL kernel and OLD translation,
with D_raw read at the actual two independently permuted endpoints. -/
def sourceOriginalB26NodupRawChannel434
    {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (ss tt : (GroupPermFamily (G := SG) (J+ell))) (sigma tau : (BigGroupPerm (BG := G) (J+ell)))
    (f : (GroupState SP sm (J+ell)) → (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) → Finset ℕ → (SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime) → ℂ)
    (xs : (GroupState SP sm (J+ell))) (a : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)) (S : Finset ℕ) (t : (SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime)) : ℂ :=
  if (sourceOriginalBigRefreshPacket434 ((fun g => {p : ℕ // p ∈ P g})) (fun _ => J+ell) a).image
      (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val) ⊆ S then
    ∑ b : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell),sourceOriginalB26FrozenFreshLaw434 ((fun g => {p : ℕ // p ∈ P g})) J ell m mu (sourceOriginalProbeMemoryPattern434 J m hmJ nu) a b sigma tau *
      (if Disjoint S ((sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
        (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
          (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val)) ∧
        sourceOriginalB26NumericBirthNodup434 ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell m hmJ nu tau b then
        let D := sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
          (sourceOriginalB26SmallSourceD434 SP sm J ell xs ss) a b sigma tau
        let step := o*k*(D:ℤ)
        originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta D o k *
          ∑ ys : (GroupState SP sm (J+ell)),groupPermutedKernel SP sm (J+ell) q Vs
            (sourceSmallShared J ell) step (fun _ _ => 1) ss tt xs ys *
            f ys b (S ∪ (sourceOriginalB26FreeBirthSet434 ((fun g => {p : ℕ // p ∈ P g})) J ell m hmJ nu
              (sourceOriginalB26EndpointPermutationEquiv434 ((fun g => {p : ℕ // p ∈ P g})) (J+ell) tau b)).image
                (fun p : Sigma ((fun g => {p : ℕ // p ∈ P g})) => p.2.val))
              (fun g i => t g i+(step : ZMod (prime g i).val))
       else 0)
  else 0

/-- Exact factorization of RAW, using its own shift at both SMALL and OLD.
No identification of D_aux with D_raw is assumed. -/
theorem source_original_B26_NODUP_RAW_CHANNEL_FACTOR434
    (q : ℝ) (hq : 0 ≤ q) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (ss tt : (GroupPermFamily (G := SG) (J+ell))) (sigma tau : (BigGroupPerm (BG := G) (J+ell)))
    (f : (GroupState SP sm (J+ell)) → (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell) → Finset ℕ → (SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime) → ℂ)
    (xs : (GroupState SP sm (J+ell))) (a : (SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)) (S : Finset ℕ) (t : (SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g}) (fun _ => Subtype.val) sizes prime)) :
    sourceOriginalB26NodupRawChannel434 SP sm P J ell m hmJ nu sizes prime mu
      q Vs zeta theta o k ss tt sigma tau f xs a S t =
    sourceOriginalMarkedSmallSynthesis434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell sizes prime q Vs ss
      (fun d => sourceOriginalB26NodupRawResidue434 SP sm P J ell m hmJ nu sizes prime mu
        (sourceOriginalB26SmallTupleD434 SP sm J ell d) zeta theta o k sigma tau
        (sourceOriginalMarkedSmallHalf434 SP sm ((fun g => {p : ℕ // p ∈ P g})) ((fun _ => Subtype.val)) J ell sizes prime q Vs tt f d))
      xs a S t := by
  unfold sourceOriginalB26NodupRawChannel434
  dsimp only
  rw [source_original_MARKED_SMALL_shared_divisor434]
  unfold sourceOriginalMarkedSmallSynthesis434 sourceOriginalSmallEndpointSynthesis434
    sourceOriginalB26NodupRawResidue434
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

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NodupPhysicalFamilyLiteral -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The coherent residue error equals the difference of two directly
defined literal operators. Their full auxiliary and RAW shifts stay distinct. -/
theorem source_original_B26_NODUP_NUMERIC_RESIDUE_LITERAL434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi zeta : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (f : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → memoryFrozenResidueGroup SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    sourceOriginalB26NodupNumericResidueCleanRawFamily434 data SP sm sizes prime q N
      blockA blockB J ell m hmJ Q hA hB xi zeta c theta orientation k
      sigma tau epsSrc epsTgt f =
    fun a S r =>
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
        sourceOriginalB26NodupAllowedResidue434 SP sm data.Tb J ell m hmJ nu sizes prime
          data.Vbig (physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
            (fun _ => Subtype.val) q N data.Vbig)
          (c nu) Q (hA nu) (hB nu) xi zeta (theta nu) (orientation nu) k
          (sigma nu) (tau nu) f a S r) -
      (∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
        sourceOriginalB26NodupRawResidue434 SP sm data.Tb J ell m hmJ nu sizes prime
          (physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
            (fun _ => Subtype.val) q N data.Vbig)
          (c nu) zeta (theta nu) (orientation nu) k (sigma nu) (tau nu) f a S r) := by
  funext a S r
  unfold sourceOriginalB26NodupNumericResidueCleanRawFamily434
    sourceOriginalB26NodupAllowedResidue434 sourceOriginalB26NodupRawResidue434
  dsimp only
  by_cases hs : (sourceOriginalBigRefreshPacket434 (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ => J+ell) a).image (fun p => p.2.val) ⊆ S
  · simp only [if_pos hs]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro nu hnu
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← mul_sub]
    congr 1
    split_ifs
    · rfl
    · simp
  · simp [hs]

/-- Coherent actual physical CLEAN channels with the original joint K,
the true auxiliary ban and the true birth-list Nodup in every pattern. -/
def sourceOriginalB26NodupPhysicalCleanFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  fun xs a S r =>
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      ∑ aux : SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ nu),
        (sourceAuxMass BP (fun _ => Subtype.val) J m data.Vbig
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux:ℂ) *
        sourceOriginalMarkedPhysicalCleanChannel434 SP sm BP (fun _ => Subtype.val)
          J ell m hmJ nu cap sizes hsizes prime aux o k q data.Vsmall data.Vbig mu
          ss tt (sigma nu) (tau nu)
          (sourceOriginalMarkedCleanJointK434 SP sm BP (fun _ => Subtype.val)
            J ell m hmJ nu aux (sigma nu) (tau nu)
            (sourceOriginalProbeMemoryCanonicalK434 data.Tb data.Vbig J ell m hmJ nu Q h h xi)
            zeta theta o k) f xs a S r

/-- Coherent direct physical RAW channels. The mixed endpoint sign factor,
RAW pattern sign, true RAW divisor and numerical history are all retained. -/
def sourceOriginalB26NodupPhysicalRawFamily434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  fun xs a S r =>
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt *
      sourceOriginalB26NodupRawChannel434 SP sm data.Tb J ell m hmJ nu sizes prime mu
        q data.Vsmall zeta theta o k ss tt (sigma nu) (tau nu) f xs a S r

/-- Exact physical CLEAN-minus-RAW identity for all four endpoint signs
and one common arbitrary future, before the original endpoint means. -/
theorem source_original_B26_NODUP_PHYSICAL_FAMILY_LITERAL434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (epsSrc epsTgt : Bool)
    (ss tt : Green64SmallHaar.GroupPermFamily (G := ι) (J+ell))
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (hq : 0 ≤ q) (ho : o=1 ∨ o= -1) (hk : k≠0) :
    sourceOriginalB26NodupMarkedSmallCleanRaw434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f =
    fun xs a S r =>
      sourceOriginalB26NodupPhysicalCleanFamily434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r -
      sourceOriginalB26NodupPhysicalRawFamily434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r := by
  funext xs a S r
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  have hVs (g : ι) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hClean (nu : SourceOriginalProbePattern434 G m) :=
    source_original_B26_NODUP_PHYSICAL_AUX_CHANNEL_LITERAL434
      SP sm data.Tb J ell m hmJ nu sizes prime data.Vbig mu cap hsizes
      q hq data.Vsmall hVs Q h h xi zeta theta o k ho hk ss tt (sigma nu) (tau nu) f xs a S r
  have hRaw (nu : SourceOriginalProbePattern434 G m) :=
    source_original_B26_NODUP_RAW_CHANNEL_FACTOR434
      SP sm data.Tb J ell m hmJ nu sizes prime mu
      q hq data.Vsmall hVs zeta theta o k ss tt (sigma nu) (tau nu) f xs a S r
  let Cnu := fun nu : SourceOriginalProbePattern434 G m =>
    sourceOriginalMarkedSmallSynthesis434 SP sm BP (fun _ => Subtype.val) J ell sizes prime
      q data.Vsmall ss
      (fun d => sourceOriginalB26NodupAllowedResidue434 SP sm data.Tb J ell m hmJ nu
        sizes prime data.Vbig mu (sourceOriginalB26SmallTupleD434 SP sm J ell d)
        Q h h xi zeta theta o k (sigma nu) (tau nu)
        (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ => Subtype.val)
          J ell sizes prime q data.Vsmall tt f d)) xs a S r
  let Rnu := fun nu : SourceOriginalProbePattern434 G m =>
    sourceOriginalMarkedSmallSynthesis434 SP sm BP (fun _ => Subtype.val) J ell sizes prime
      q data.Vsmall ss
      (fun d => sourceOriginalB26NodupRawResidue434 SP sm data.Tb J ell m hmJ nu
        sizes prime mu (sourceOriginalB26SmallTupleD434 SP sm J ell d)
        zeta theta o k (sigma nu) (tau nu)
        (sourceOriginalMarkedSmallHalf434 SP sm BP (fun _ => Subtype.val)
          J ell sizes prime q data.Vsmall tt f d)) xs a S r
  have hCF :
      sourceOriginalB26NodupPhysicalCleanFamily434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r =
      ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt*Cnu nu := by
    unfold sourceOriginalB26NodupPhysicalCleanFamily434
    apply Finset.sum_congr rfl
    intro nu hnu
    exact congrArg (fun z : ℂ =>
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt*z) (hClean nu)
  have hRF :
      sourceOriginalB26NodupPhysicalRawFamily434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k sigma tau epsSrc epsTgt ss tt f xs a S r =
      ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
        sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt*Rnu nu := by
    unfold sourceOriginalB26NodupPhysicalRawFamily434
    apply Finset.sum_congr rfl
    intro nu hnu
    exact congrArg (fun z : ℂ =>
      sourceOriginalB26NumericSharedSign434 (Fintype.card ι) J ell m hmJ nu epsSrc epsTgt*z) (hRaw nu)
  rw [hCF,hRF]
  unfold sourceOriginalB26NodupMarkedSmallCleanRaw434
  try dsimp only
  simp_rw [source_original_B26_NODUP_NUMERIC_RESIDUE_LITERAL434]
  simp only [Cnu,Rnu,sourceOriginalMarkedSmallSynthesis434,sourceOriginalSmallEndpointSynthesis434,
    mul_sub,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro nu hnu <;> ring

/-- Both original normalized endpoint-pair means of the actual CLEAN family. -/
def sourceOriginalB26NodupPhysicalCleanMean434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (epsSrc epsTgt : Bool)
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ :=
  let SPerm := Green64SmallHaar.GroupPermFamily (G := ι) (J+ell)
  let BPerm := BigGroupPerm (BG := G) (J+ell)
  let alpha := Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell) *
    bigEndpointPairMass (BG := G) (J+ell)
  fun xs a S r =>
    ∑ st : (SPerm × SPerm) × (BPerm × BPerm),(alpha:ℂ) *
      sourceOriginalB26NodupPhysicalCleanFamily434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
        epsSrc epsTgt st.1.1 st.1.2 f xs a S r

/-- The same four normalized means of the independently defined direct RAW family. -/
def sourceOriginalB26NodupPhysicalRawMean434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (epsSrc epsTgt : Bool)
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ) :
    Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ :=
  let SPerm := Green64SmallHaar.GroupPermFamily (G := ι) (J+ell)
  let BPerm := BigGroupPerm (BG := G) (J+ell)
  let alpha := Green64SmallHaar.groupPermutationPairMass (G := ι) (J+ell) *
    bigEndpointPairMass (BG := G) (J+ell)
  fun xs a S r =>
    ∑ st : (SPerm × SPerm) × (BPerm × BPerm),(alpha:ℂ) *
      sourceOriginalB26NodupPhysicalRawFamily434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k (fun _ => st.2.1) (fun _ => st.2.2)
        epsSrc epsTgt st.1.1 st.1.2 f xs a S r

/-- The already proved small error is exactly the difference of these
two literal physical means, with both actual shifts and no altered future. -/
theorem source_original_B26_NODUP_PHYSICAL_MEAN_LITERAL434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (cap : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta theta : ℝ) (o k : ℤ)
    (epsSrc epsTgt : Bool)
    (f : Green64SmallHaar.GroupState SP sm (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      Finset ℕ → SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) sizes prime → ℂ)
    (hq : 0 ≤ q) (ho : o=1 ∨ o= -1) (hk : k≠0) :
    sourceOriginalB26NodupMarkedSmallCleanRawMean434 data SP sm sizes prime q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f =
    fun xs a S r =>
      sourceOriginalB26NodupPhysicalCleanMean434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f xs a S r -
      sourceOriginalB26NodupPhysicalRawMean434 data SP sm sizes prime cap hsizes q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f xs a S r := by
  funext xs a S r
  unfold sourceOriginalB26NodupMarkedSmallCleanRawMean434
    sourceOriginalB26NodupPhysicalCleanMean434 sourceOriginalB26NodupPhysicalRawMean434
  try dsimp only
  simp_rw [source_original_B26_NODUP_PHYSICAL_FAMILY_LITERAL434
    data SP sm sizes prime cap hsizes q N blockA blockB J ell m hmJ Q h xi zeta theta o k
    _ _ epsSrc epsTgt _ _ f hq ho hk]
  simp only [mul_sub,Finset.sum_sub_distrib]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26NodupFullPhysicalCleanRaw -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The coherent literal physical CLEAN-minus-RAW packet in every actual
ordered Fock sector. The RAW channel is independently defined; both sides
keep the same full future, numerical history and their own full shift. -/
def sourceOriginalB26NodupFullOrderedCleanRaw434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (cap : G → ℕ) (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (h xi zeta theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (f : FullPhysicalState SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell) cap → Finset ℕ → ℂ)
    (x : FullPhysicalState SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell) cap) (S : Finset ℕ) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let z := sourceOriginalMarkedSectorEquiv434 SP sm BP (fun _ => Subtype.val) J ell cap x
  sourceOriginalB26NodupPhysicalCleanMean434 data SP sm
    (fun g => (z.1.1 g).val) z.1.2 cap (fun g => Nat.le_of_lt_succ (z.1.1 g).isLt)
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt
    (fun ys b T u => f
      (sourceOriginalMarkedSectorEmbed434 SP sm BP (fun _ => Subtype.val) J ell cap z.1 ys b u) T)
    z.2.1.1 z.2.2 S z.2.1.2 -
  sourceOriginalB26NodupPhysicalRawMean434 data SP sm
    (fun g => (z.1.1 g).val) z.1.2 cap (fun g => Nat.le_of_lt_succ (z.1.1 g).isLt)
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt
    (fun ys b T u => f
      (sourceOriginalMarkedSectorEmbed434 SP sm BP (fun _ => Subtype.val) J ell cap z.1 ys b u) T)
    z.2.1.1 z.2.2 S z.2.1.2

/-- Original weighted orbit compression of the literal full ordered packet. -/
def sourceOriginalB26NodupFullOrbitCleanRaw434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (cap : G → ℕ) (q : ℝ) (N : ℕ) (blockA blockB : Finset G)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (h xi zeta theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell) → Finset ℕ → ℂ)
    (X : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell)) (S : Finset ℕ) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  fullPhysicalOrbitAverage SP sm BP (fun _ => Subtype.val) (J+ell) cap data.Vsmall mu
    (fun x => sourceOriginalB26NodupFullOrderedCleanRaw434 data SP sm cap q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt
      (fun y T => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap y) T)
      x S) X

/-- Arbitrary-power saving of the literal coherent CLEAN-minus-RAW packet
on the FULL ordered Fock times numerical-seen carrier, in the original
physical density. Uniformity over all pending sectors costs no sector count.
The conductor exponents precede J, and J precedes the L limit. -/
theorem eventually_source_original_B26_NODUP_FULL_ORDERED_CLEAN_RAW_SAVING434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck)
    (ell : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ J : ℕ, ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (cap : G → ℕ)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g,data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g,loB g ≤ hiB g)
      (hBigUpper : ∀ g,(hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g,Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k≠0)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (epsSrc epsTgt : Bool)
      (f : FullPhysicalState SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell) cap → Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap
      data.Vsmall data.Vbig mu
      (sourceOriginalB26NodupFullOrderedCleanRaw434 data SP sm cap q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f) ≤
    L^(-Bgoal)*sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu f := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_FIXED_J_NODUP_MARKED_SMALL_CLEAN_RAW_MEAN_SAVING434
      cfg gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  intro J
  filter_upwards [hEvent J,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hMain hVisit
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig cap
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm hmJ zeta theta o k ho hk0 hZeta hk epsSrc epsTgt f
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  let Q := Nat.ceil (4*L^(D+Ck+1))
  let h := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
  let xi := L^(-(Cxi:ℝ))
  have hLocal (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → BP g)
      (F : GroupState SP sm (J+ell) → SourceOriginalB26Active434 BP J ell →
        Finset ℕ → SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime → ℂ) :=
    hMain x Y Hprime data SP sm sizes prime sep loB hiB
      hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hDisjoint
      m hm hmJ zeta theta o k ho hZeta hk epsSrc epsTgt F
  refine ⟨(hLocal (fun _ => 0) (fun _ i => Fin.elim0 i) (fun _ _ _ _ => 0)).1,?_⟩
  have hVs (g : ι) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ => Subtype.val) q N g p := by
    have hz := (source_original_B26_physical_baseline_half434 BP (fun _ => Subtype.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hz]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hVb g) (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
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
    (fun xs a S t =>
      sourceOriginalB26NodupPhysicalCleanMean434 data SP sm sizes prime cap hsz q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt F xs a S t -
      sourceOriginalB26NodupPhysicalRawMean434 data SP sm sizes prime cap hsz q N
        blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt F xs a S t) ≤
    L^(-Bgoal)*sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap sizes hsz prime data.Vsmall data.Vbig mu F
  rw [← source_original_B26_NODUP_PHYSICAL_MEAN_LITERAL434 data SP sm sizes prime cap hsz
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt F hq.le ho hk0]
  rw [source_original_MARKED_PHYSICAL_energy_factor434,
    source_original_MARKED_PHYSICAL_energy_factor434]
  have hw : 0 ≤ sourceOriginalMarkedPhysicalSectorWeight434
      SP sm BP J ell sizes prime data.Vsmall data.Vbig mu :=
    mul_nonneg (source_original_B26_sector_constant_nonneg434 SP sm BP J ell
      sizes prime data.Vsmall hVs mu hmu)
      (Finset.prod_nonneg (fun g _ => pow_nonneg (hVb g).le _))
  have hBound := mul_le_mul_of_nonneg_left (hLocal sizes prime F).2 hw
  convert hBound using 1 <;> ring

/-- The same arbitrary-power saving after the original weighted Fock orbit
compression. This is a one-visit CLEAN-minus-RAW estimate; it makes no
claim that the full signed RAW continuation or the N-step chain contracts. -/
theorem eventually_source_original_B26_NODUP_FULL_ORBIT_CLEAN_RAW_SAVING434
    (cfg : SourceComparisonFixed434)
    (gamma dscale Bgoal Cfreq Ck : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hGoal : 0 ≤ Bgoal) (hCk : 0 ≤ Ck)
    (ell : ℕ) (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    ∃ (D H : ℝ) (Cq Cxi : ℕ), 0 ≤ D ∧ 0 ≤ H ∧
    ∀ J : ℕ, ∀ᶠ L : ℝ in atTop,
    let Q : ℕ := Nat.ceil (4*L^(D+Ck+1))
    let h : ℝ := Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ)
    let xi : ℝ := L^(-(Cxi:ℝ))
    0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h≤1 ∧ 0<xi ∧ xi⁻¹≤L^Cxi ∧
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ)
      (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
      (sm : (g : ι) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (cap : G → ℕ)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      (loB hiB : G → ℕ)
      (hBigFull : ∀ g,data.Tb g = sourceOriginalActualPrimeBand434 (loB g) (hiB g))
      (hLoLeHi : ∀ g,loB g ≤ hiB g)
      (hBigUpper : ∀ g,(hiB g:ℝ) ≤ Real.exp (L^dscale))
      (hLoLarge : ∀ g,Real.exp (L^gamma) ≤ ((loB g+1:ℕ):ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (blockA blockB : Finset G) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax) (hmJ : m ≤ J)
      (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k≠0)
      (hZeta : |zeta| ≤ L^Cfreq) (hk : (k.natAbs:ℝ) ≤ L^Ck)
      (epsSrc epsTgt : Bool)
      (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ => Subtype.val) (J+ell) → Finset ℕ → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let N := 2*Nat.ceil (L^(0.52:ℝ))
    let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
    k.natAbs*Nat.ceil (L^(D+1)) ≤ Q ∧
    sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val) J ell cap
      data.Vsmall data.Vbig mu
      (sourceOriginalB26NodupFullOrbitCleanRaw434 data SP sm cap q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt F) ≤
    L^(-Bgoal)*sourceOriginalMemoryMarkedEnergy434 SP sm BP (fun _ => Subtype.val)
      J ell cap data.Vsmall data.Vbig mu F := by
  obtain ⟨D,H,Cq,Cxi,hD,hH,hEvent⟩ :=
    eventually_source_original_B26_NODUP_FULL_ORDERED_CLEAN_RAW_SAVING434
      cfg gamma dscale Bgoal Cfreq Ck hgamma hd hGoal hCk ell q hq hq1
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  refine ⟨D,H,Cq,Cxi,hD,hH,?_⟩
  intro J
  filter_upwards [hEvent J,eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc]
    with L hMain hVisit
  dsimp only at hMain ⊢
  obtain ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,hMain⟩ := hMain
  refine ⟨hQpos,hQupper,hh,hwidth,hxi,hXi,?_⟩
  intro ι G instI instDI instG instDG x Y Hprime data
    SP instSP instDSP sm instNZsmall instNZbig cap
    sep loB hiB hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig
    blockA blockB hDisjoint m hm hmJ zeta theta o k ho hk0 hZeta hk epsSrc epsTgt F
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let mu := physicalSourceMuTilde BP (fun _ => Subtype.val) q N data.Vbig
  have hVs (g : ι) : 0 < data.Vsmall g := cfg.hv.trans_le (data.hVsmall g)
  have hVb (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) :
      0 < physicalSourceBaseline BP (fun _ => Subtype.val) q N g p := by
    have hz := (source_original_B26_physical_baseline_half434 BP (fun _ => Subtype.val)
      q hq.le hq1.le N g p (hVisit p.val (hTbLower g p.val p.property))).1
    linarith only [hz]
  have hmu (g : G) (p : BP g) : 0 < mu g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hVb g) (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))
  have hBound := hMain x Y Hprime data SP sm cap sep loB hiB
    hBigFull hLoLeHi hBigUpper hLoLarge hTbLower hVbig blockA blockB hDisjoint
    m hm hmJ zeta theta o k ho hk0 hZeta hk epsSrc epsTgt
    (fun y T => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap y) T)
  refine ⟨hBound.1,?_⟩
  apply le_trans (source_original_MARKED_orbit_compression_energy434
    SP sm BP (fun _ => Subtype.val) J ell cap data.Vsmall data.Vbig mu hVs hVb hmu _)
  have h := hBound.2
  rw [source_original_MARKED_ordered_orbit_energy434] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

