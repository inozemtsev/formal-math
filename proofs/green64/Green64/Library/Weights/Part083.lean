module

public import Green64.Library.Weights.B26RawCoherentKernel
public import Green64.Library.Weights.MarkedCleanMeanLiteral
public import Green64.Library.Correlation.Part049
public import Green64.Library.Weights.Part070
public import Green64.Library.Correlation.Part027
public import Green64.Library.Correlation.Part045
public import Green64.Library.Weights.Part076

@[expose] public section

/-!
# Weights / Part083

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26RawResidueHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
variable (nu : SourceOriginalProbePattern434 G m)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Perm" => BigGroupPerm (BG := G) (J+ell)

/-- Direct RAW on the actual numeric-seen carrier, with both original
endpoint permutations, the full mixed divisor and the birth-list Nodup. -/
def sourceOriginalB26NodupRawActive434
    (mu : (g : G) → BP g → ℝ) (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (sigma tau : Perm) (f : A → Finset ℕ → ℂ) : A → Finset ℕ → ℂ :=
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  sourceOriginalB26NumericPermutedClean434 BP (fun _ => Subtype.val)
    J ell m hmJ nu mu sigma tau
    (fun a _S b => if sourceOriginalB26NumericBirthNodup434 BP (fun _ => Subtype.val)
        J ell m hmJ nu tau (eT.symm b) then
      originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta
        (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
          dsmall (eS.symm a) (eT.symm b) sigma tau) o k else 0) f

/-- Genuine RAW energy bound, not a bound on auxiliary-minus-RAW.
The original no-rebirth gain applies to its joint unit-modulus phase. -/
theorem source_original_B26_NODUP_RAW_ACTIVE_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (sigma tau : Perm) (f : A → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP (fun _ => Subtype.val) J ell mu
      (sourceOriginalB26NodupRawActive434 P J ell m hmJ nu mu
        dsmall zeta theta o k sigma tau f) ≤
    (∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalB26NumericActiveEnergy434 BP (fun _ => Subtype.val) J ell mu f := by
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  let K := fun a : A => fun _S : Finset ℕ => fun b : A =>
    if sourceOriginalB26NumericBirthNodup434 BP (fun _ => Subtype.val)
        J ell m hmJ nu tau (eT.symm b) then
      originalEdgeScalar (-((-1:ℂ)^(nu.1.card+nu.2.card))) zeta theta
        (sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
          dsmall (eS.symm a) (eT.symm b) sigma tau) o k else 0
  have hK (a : A) (S : Finset ℕ) (b : A) : ‖K a S b‖ ≤ 1 := by
    dsimp only [K]
    split_ifs
    · rw [source_original_edge_scalar_norm434 _ zeta theta _ o k ho]
      simp
    · simp
  simpa only [one_pow,one_mul,sourceOriginalB26NodupRawActive434] using
    source_original_B26_NUMERIC_permuted_Hilbert434 BP (fun _ => Subtype.val)
      J ell m hmJ nu hi mu hmu sigma tau 1 (by norm_num) K hK f

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
variable (sizes : G → ℕ) (oldPrime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
local notation "Torus" => memoryFrozenResidueGroup SP sm BP (fun _ => Subtype.val) sizes oldPrime


/-- The RAW mixed source/target displacement is diagonalized on ALL true
SMALL and OLD residue coordinates. It is not replaced by a target-only
shift. The frequency change keeps the same full mixed divisor. -/
theorem source_original_B26_NODUP_RAW_RESIDUE_FOURIER434
    (mu : (g : G) → BP g → ℝ) (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ)
    (sigma tau : Perm) (f : A → Finset ℕ → Torus → ℂ) :
    sourceOriginalB26NodupRawResidue434 SP sm P J ell m hmJ nu sizes oldPrime mu
      dsmall zeta theta o k sigma tau f =
    sourceOriginalNumericSeenFourierLift434
      (fun psi => sourceOriginalB26NodupRawActive434 P J ell m hmJ nu mu dsmall zeta
        (theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes oldPrime psi/(2*Real.pi))
        o k sigma tau) f := by
  let angle := fun psi : AddChar Torus ℂ =>
    theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes oldPrime psi/(2*Real.pi)
  let law := fun a b : A => sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
    (sourceOriginalProbeMemoryPattern434 J m hmJ nu) a b sigma tau
  let draw := fun a b : A => sourceOriginalB26CanonicalRawDivisor434 P J ell m hmJ nu
    dsmall a b sigma tau
  let birth := fun b : A => sourceOriginalB26RawBirth434 P J ell m hmJ nu tau b
  let valid := fun b : A => sourceOriginalB26NumericBirthNodup434 BP (fun _ => Subtype.val)
    J ell m hmJ nu tau b
  let rawK : ℂ := -((-1:ℂ)^(nu.1.card+nu.2.card))
  funext a S r
  have hshift (D : ℕ) (F : Torus → ℂ) :
      originalEdgeScalar rawK zeta theta D o k *
        F (r+memoryFrozenResidueShift SP sm BP (fun _ => Subtype.val) sizes oldPrime (o*k*(D:ℤ))) =
      ∑ psi : AddChar Torus ℂ,originalEdgeScalar rawK zeta (angle psi) D o k *
        (AddChar.complexBasis Torus).equivFun F psi * psi r := by
    have hs := memory_frozen_full_residue_fourier_shift_formula
      SP sm BP (fun _ => Subtype.val) sizes oldPrime (o*k*(D:ℤ)) F r
    dsimp only at hs
    rw [hs,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro psi hpsi
    dsimp only [angle]
    rw [←source_original_B26_FROZEN_scalar_frequency434]
    simp only [Module.Basis.equivFun_apply]
    ring
  unfold sourceOriginalNumericSeenFourierLift434
  simp only [Module.Basis.equivFun_symm_apply,AddChar.complexBasis_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  by_cases hS : sourceOriginalB26RawInventory434 P J ell a ⊆ S
  · have hcore (psi : AddChar Torus ℂ) :
        sourceOriginalB26NodupRawActive434 P J ell m hmJ nu mu dsmall zeta
          (angle psi) o k sigma tau
          (fun b T => (AddChar.complexBasis Torus).equivFun (f b T) psi) a S =
        ∑ b : A,law a b*(if Disjoint S (birth b) ∧ valid b then
          originalEdgeScalar rawK zeta (angle psi) (draw a b) o k *
            (AddChar.complexBasis Torus).equivFun (f b (S∪birth b)) psi else 0) := by
      unfold sourceOriginalB26NodupRawActive434 sourceOriginalB26NumericPermutedClean434
      dsimp only
      change (if sourceOriginalB26RawInventory434 P J ell a ⊆ S then _ else 0) = _
      rw [if_pos hS]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Equiv.symm_apply_apply]
      change law a b*(if Disjoint S (birth b) then
        (if valid b then originalEdgeScalar rawK zeta (angle psi) (draw a b) o k else 0)*
          (AddChar.complexBasis Torus).equivFun (f b (S∪birth b)) psi else 0) = _
      by_cases hf : Disjoint S (birth b) <;> by_cases hn : valid b <;> simp [hf,hn]
    change sourceOriginalB26NodupRawResidue434 SP sm P J ell m hmJ nu sizes oldPrime mu
      dsmall zeta theta o k sigma tau f a S r =
      ∑ psi : AddChar Torus ℂ,sourceOriginalB26NodupRawActive434 P J ell m hmJ nu mu
        dsmall zeta (angle psi) o k sigma tau
        (fun b T => (AddChar.complexBasis Torus).equivFun (f b T) psi) a S * psi r
    simp_rw [hcore]
    unfold sourceOriginalB26NodupRawResidue434
    change (if sourceOriginalB26RawInventory434 P J ell a ⊆ S then _ else 0) = _
    rw [if_pos hS]
    have hterm (b : A) :
        (if Disjoint S (birth b) ∧ valid b then
          originalEdgeScalar rawK zeta theta (draw a b) o k *
            f b (S∪birth b) (r+memoryFrozenResidueShift SP sm BP
              (fun _ => Subtype.val) sizes oldPrime (o*k*(draw a b:ℤ))) else 0) =
        ∑ psi : AddChar Torus ℂ,(if Disjoint S (birth b) ∧ valid b then
          originalEdgeScalar rawK zeta (angle psi) (draw a b) o k *
            (AddChar.complexBasis Torus).equivFun (f b (S∪birth b)) psi else 0)*psi r := by
      by_cases hf : Disjoint S (birth b) ∧ valid b
      · simp only [if_pos hf]
        exact hshift (draw a b) (f b (S∪birth b))
      · simp [hf]
    change (∑ b : A,law a b*(if Disjoint S (birth b) ∧ valid b then
      originalEdgeScalar rawK zeta theta (draw a b) o k *
        f b (S∪birth b) (r+memoryFrozenResidueShift SP sm BP
          (fun _ => Subtype.val) sizes oldPrime (o*k*(draw a b:ℤ))) else 0)) = _
    simp_rw [hterm,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro psi hpsi
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · unfold sourceOriginalB26NodupRawResidue434 sourceOriginalB26NodupRawActive434
      sourceOriginalB26NumericPermutedClean434
    dsimp only [sourceOriginalB26RawInventory434] at hS
    simp only [hS,ite_false,zero_mul,Finset.sum_const_zero]

/-- The independently defined RAW residue channel has the sharp original
no-rebirth energy gain. This is uniform in every Fourier/Mellin parameter
and signed shift and has NO Q or xi cost, no residue count and no history
count. It does not assert contraction of the whole signed evolution. -/
theorem source_original_B26_NODUP_RAW_RESIDUE_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (dsmall : ℕ) (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (sigma tau : Perm) (f : A → Finset ℕ → Torus → ℂ) :
    sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu
      (sourceOriginalB26NodupRawResidue434 SP sm P J ell m hmJ nu sizes oldPrime mu
        dsmall zeta theta o k sigma tau f) ≤
    (∏ g : G,((∑ p : BP g,mu g p)^2/4)^
      sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalB26NumericResidueEnergy434 BP (fun _ => Subtype.val) J ell mu f := by
  rw [source_original_B26_NODUP_RAW_RESIDUE_FOURIER434]
  exact source_original_NUMERIC_SEEN_FOURIER_spectral_lift434
    (sourceOriginalMemoryBirthPool434 BP (fun _ => Subtype.val))
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) _
    (fun psi => sourceOriginalB26NodupRawActive434 P J ell m hmJ nu mu dsmall zeta
      (theta+sourceOriginalB26ModeAngle434 SP sm BP (fun _ => Subtype.val) sizes oldPrime psi/(2*Real.pi))
      o k sigma tau)
    (fun psi F => source_original_B26_NODUP_RAW_ACTIVE_Hilbert434 P J ell m hmJ nu
      hi mu hmu dsmall zeta _ o k ho sigma tau F) f

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26RawPhysicalHilbert -/

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
theorem source_original_B26_NODUP_RAW_SMALL_BIG_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (ss tt : SPerm) (sigma tau : BPerm) (f : Small → A → Finset ℕ → Old → ℂ) :
    sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ => Subtype.val) J ell sizes prime mu
      (sourceOriginalB26NodupRawChannel434 SP sm P J ell m hmJ nu sizes prime mu
        q Vs zeta theta o k ss tt sigma tau f) ≤
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalMarkedSmallBigEnergy434 SP sm BP (fun _ => Subtype.val) J ell sizes prime mu f := by
  let cost := memorySmallGroupConditioningConstant (SG := SG) ell q Vs
  let delta := ∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g
  have hc : 0 ≤ cost := by
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    have hq' : 0 < 1-q := sub_pos.mpr hq1
    positivity
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
  have hs := source_original_MARKED_SMALL_synthesis_energy434 SP sm BP (fun _ => Subtype.val)
    J ell sizes prime q hq hq1 Vs hVs mu hmu ss H
  have ht := source_original_MARKED_SMALL_half_energy434 SP sm BP (fun _ => Subtype.val)
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
theorem source_original_B26_NODUP_RAW_PHYSICAL_SECTOR_Hilbert434
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
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      (∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) *
      sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
        J ell cap sizes hsizes prime Vs Vb mu f := by
  have hw : 0 ≤ sourceOriginalMarkedPhysicalSectorWeight434 SP sm BP J ell sizes prime Vs Vb mu :=
    mul_nonneg (source_original_B26_sector_constant_nonneg434 SP sm BP J ell
      sizes prime Vs hVs mu hmu) (Finset.prod_nonneg (fun g _ => pow_nonneg (hVb g).le _))
  rw [source_original_MARKED_PHYSICAL_energy_factor434,source_original_MARKED_PHYSICAL_energy_factor434]
  have h := mul_le_mul_of_nonneg_left
    (source_original_B26_NODUP_RAW_SMALL_BIG_Hilbert434 SP sm P J ell m hmJ nu sizes prime
      hi mu (fun g p => (hmu g p).le) q hq hq1 Vs hVs zeta theta o k ho ss tt sigma tau f) hw
  convert h using 1 <;> ring

/-- Weighted coherent energy for the full same-history future. This
accounts for a pattern sum or a probability mean without a history count. -/
theorem source_original_RAW_weighted_history_energy434
    {I X Z : Type} [Fintype I] [Fintype X] [Fintype Z]
    (pool : Finset ℕ) (w : Z → X → ℝ) (hw : ∀ z x,0 ≤ w z x)
    (alpha : I → ℝ) (ha : ∀ i,0 ≤ alpha i)
    (F : I → Z → X → Finset ℕ → ℂ) (C : I → ℝ)
    (hF : ∀ i,(∑ z,∑ S ∈ pool.powerset,∑ x,w z x*‖F i z x S‖^2) ≤ C i) :
    (∑ z,∑ S ∈ pool.powerset,∑ x,w z x*‖∑ i,(alpha i:ℂ)*F i z x S‖^2) ≤
      (∑ i,alpha i) * ∑ i,alpha i*C i := by
  let total := ∑ i,alpha i
  have ht : 0 ≤ total := Finset.sum_nonneg (fun i _ => ha i)
  have hp (z : Z) (S : Finset ℕ) (x : X) :
      ‖∑ i,(alpha i:ℂ)*F i z x S‖^2 ≤ total*∑ i,alpha i*‖F i z x S‖^2 := by
    have h := source_original_finite_weighted_complex_kernel_CS434 alpha ha
      (fun _ => (1:ℂ)) (fun i => F i z x S)
    simpa only [one_mul,norm_one,one_pow,mul_one] using h
  calc
    _ ≤ ∑ z,∑ S ∈ pool.powerset,∑ x,w z x*(total*∑ i,alpha i*‖F i z x S‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hp z S x) (hw z x)
    _ = total*∑ i,alpha i*(∑ z,∑ S ∈ pool.powerset,∑ x,w z x*‖F i z x S‖^2) := by
      simp only [Finset.mul_sum]
      trans ∑ z,∑ S ∈ pool.powerset,∑ i,∑ x,total*(alpha i*(w z x*‖F i z x S‖^2))
      · apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro x hx
        ring
      trans ∑ z,∑ i,∑ S ∈ pool.powerset,∑ x,total*(alpha i*(w z x*‖F i z x S‖^2))
      · apply Finset.sum_congr rfl
        intro z hz
        exact Finset.sum_comm
      · exact Finset.sum_comm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hF i) (ha i))) ht

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26RawPhysicalFamilyHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Explicit coherent RAW energy budget. The original tilted masses
and SMALL costs remain; there is no conductor Q or cell width xi. -/
def sourceOriginalB26RawFamilyHilbertBudget434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (blockA blockB : Finset G) (q : ℝ) (Vs : SG → ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ) : ℝ :=
  ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ) *
    ∑ nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
      (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
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
local notation "Budget" => sourceOriginalB26RawFamilyHilbertBudget434 data.Tb J ell m hmJ
  blockA blockB q data.Vsmall mu
local notation "E" => sourceOriginalMarkedPhysicalSectorEnergy434 SP sm BP (fun _ => Subtype.val)
  J ell cap sizes hsizes prime data.Vsmall data.Vbig mu

/-- The literal coherent two-block RAW family, with all four independent
endpoint signs and its arbitrary joint SMALL/OLD/seen future, obeys the
explicit conductor-free budget in the same true physical sector density. -/
theorem source_original_B26_NODUP_RAW_PHYSICAL_FAMILY_Hilbert434
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
  let gain := fun nu : family => (memorySmallGroupConditioningConstant (SG := SG) ell q data.Vsmall)^2 *
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
    exact source_original_B26_NODUP_RAW_PHYSICAL_SECTOR_Hilbert434 SP sm data.Tb
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
      simp only [Fintype.card_coe,sourceOriginalB26RawFamilyHilbertBudget434,gain]
      congr 1
      exact Finset.sum_coe_sort family (fun nu =>
        (memorySmallGroupConditioningConstant (SG := SG) ell q data.Vsmall)^2 *
          ∏ g : G,((∑ p : BP g,mu g p)^2/4)^sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)

/-- All four original endpoint permutation means preserve the explicit
RAW bound, without a factorial or permutation-cardinality loss. -/
theorem source_original_B26_NODUP_RAW_PHYSICAL_MEAN_Hilbert434
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
    source_original_B26_NODUP_RAW_PHYSICAL_FAMILY_Hilbert434 data SP sm sizes prime cap hsizes
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

end

end

/-! ## SourceOriginalMarkedCleanFullFamily -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (cap : BG → ℕ)
variable {I : Type} [Fintype I] (nu : I → SourceOriginalProbePattern434 BG m)
local notation "patterns" => (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i))
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Sum ALL actual pattern channels coherently on the FULL ordered space.
Each channel uses the same complex future and the same numerical history. -/
def sourceOriginalMarkedCleanOrderedFamily434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (f : State → Finset ℕ → ℂ) (x : State) (S : Finset ℕ) : ℂ :=
  ∑ i : I,sourceOriginalMarkedFullOrderedClean434 SP sm BP bm J ell m hmJ (nu i) cap
    o k q Vs Vb mu
    (sourceOriginalMarkedCleanFamilySectorK434 SP sm BP bm J ell m hmJ cap nu
      K zeta theta o k i) f x S

/-- The ORIGINAL orbit average of the coherent full-space family. -/
def sourceOriginalMarkedCleanOrbitFamily434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ) (X : Out) (S : Finset ℕ) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun x => sourceOriginalMarkedCleanOrderedFamily434 SP sm BP bm J ell m hmJ cap nu
      mu Vb K q Vs zeta theta o k
      (fun y T => F (physicalFockProjection SP sm BP bm (J+ell) cap y) T) x S) X

/-- Active-in-seen is derived from the true numerical inventory, not an
extra restriction of the finite reachable physical state space. -/
theorem source_original_MARKED_CLEAN_reachable_active434
    (x : State) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) S) :
    (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) (fun g => (x.2 g).1)).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S := by
  intro p hp
  obtain ⟨⟨g,v⟩,hv,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.mem_sigma.mp hv).2
  change (x.2 g).1 i = v at he
  change bm g v ∈ S
  rw [← he]
  apply hr.2
  unfold sourceOriginalPhysicalInventory434
  apply Multiset.mem_sum.mpr
  refine ⟨g,Finset.mem_univ _,?_⟩
  unfold sourceOriginalBigInventory434
  apply Multiset.mem_add.mpr
  left
  apply Multiset.mem_sum.mpr
  exact ⟨i,Finset.mem_univ _,Multiset.mem_singleton_self _⟩

/-- The full assembled family IS the literal original CLEAN row on its
actual reachable source support, in every OLD sector simultaneously. -/
theorem source_original_MARKED_CLEAN_full_ordered_literal434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (x : State) (S : Finset ℕ)
    (hseen : (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) (fun g => (x.2 g).1)).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs Vb mu K zeta theta o k x S F =
    sourceOriginalMarkedCleanOrderedFamily434 SP sm BP bm J ell m hmJ cap nu
      mu Vb K q Vs zeta theta o k
      (fun y T => F (physicalFockProjection SP sm BP bm (J+ell) cap y) T) x S := by
  rcases (sourceOriginalMarkedSectorEquiv434 SP sm BP bm J ell cap).symm.surjective x
    with ⟨⟨d,⟨xs,t⟩,a⟩,rfl⟩
  change sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q 1 Vs Vb mu K zeta theta o k
    (sourceOriginalMarkedSectorEmbed434 SP sm BP bm J ell cap d xs a t) S F = _
  unfold sourceOriginalMarkedCleanOrderedFamily434
  exact source_original_MARKED_CLEAN_family_mean_literal434 SP sm BP bm J ell m hmJ
    cap (fun g => (d.1 g).val) (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2
    nu mu Vb K q Vs zeta theta o k F xs a t S hseen

/-- Exact identification AFTER original weighted orbit compression.
No representative, uniform orbit law, or new reachability axiom is assumed. -/
theorem source_original_MARKED_CLEAN_full_orbit_literal434
    (mu : (g : BG) → BP g → ℝ) (Vb : BG → ℝ)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (zeta theta : ℝ) (o k : ℤ)
    (F : Out → Finset ℕ → ℂ)
    (X : Out) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) X S) :
    sourceOriginalMarkedCleanOrbitFamily434 SP sm BP bm J ell m hmJ cap nu
      mu Vb K q Vs zeta theta o k F X S =
    fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun x => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k x S F) X := by
  unfold sourceOriginalMarkedCleanOrbitFamily434 fullPhysicalOrbitAverage
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hp := (Finset.mem_filter.mp hx).2
  have hx' : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) S := by
    rw [hp]
    exact hr
  exact congrArg (fun z : ℂ => (fullPhysicalMass SP sm BP bm (J+ell) cap Vs mu x:ℂ)*z)
    (source_original_MARKED_CLEAN_full_ordered_literal434 SP sm BP bm J ell m hmJ cap nu
      mu Vb K q Vs zeta theta o k F x S
      (source_original_MARKED_CLEAN_reachable_active434 SP sm BP bm J ell cap x S hx')).symm

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMarkedCleanFamilyHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
variable {I : Type} [Fintype I]
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)

/-- Coherent pattern-sum inequality in the ORIGINAL physical energy.
The explicit finite PATTERN count is charged; no history count occurs. -/
theorem source_original_MARKED_ordered_family_energy434
    (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hVb : ∀ g,0 < Vb g) (hmu : ∀ g p,0 < mu g p)
    (f : I → State → Finset ℕ → ℂ) :
    sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (fun x S => ∑ i : I,f i x S) ≤
    (Fintype.card I:ℝ) * ∑ i : I,
      sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu (f i) := by
  let w := sourceOriginalMemoryFullDensityMass434 SP sm BP bm J ell cap Vs Vb mu
  have hw (x : State) : 0 ≤ w x :=
    source_original_memory_FULL_density_mass_nonneg434 SP sm BP bm J ell cap
      Vs Vb mu hVs hVb hmu x
  have hp (x : State) (S : Finset ℕ) :
      ‖∑ i : I,f i x S‖^2 ≤ (Fintype.card I:ℝ)*∑ i : I,‖f i x S‖^2 := by
    have h := source_original_finite_weighted_complex_kernel_CS434
      (fun _ : I => (1:ℝ)) (fun _ => zero_le_one) (fun _ => (1:ℂ)) (fun i => f i x S)
    simpa using h
  have ht (x : State) (S : Finset ℕ) :
      w x*‖∑ i : I,f i x S‖^2 ≤
      ∑ i : I,(Fintype.card I:ℝ)*(w x*‖f i x S‖^2) := by
    calc
      _ ≤ w x*((Fintype.card I:ℝ)*∑ i : I,‖f i x S‖^2) :=
        mul_le_mul_of_nonneg_left (hp x S) (hw x)
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  unfold sourceOriginalMarkedOrderedEnergy434
  change (∑ x : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
    w x*‖∑ i : I,f i x S‖^2) ≤ _
  calc
    _ ≤ ∑ x : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        ∑ i : I,(Fintype.card I:ℝ)*(w x*‖f i x S‖^2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.sum_le_sum (fun S hS => ht x S)
    _ = ∑ x : State,∑ i : I,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        (Fintype.card I:ℝ)*(w x*‖f i x S‖^2) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i : I,∑ x : State,∑ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
        (Fintype.card I:ℝ)*(w x*‖f i x S‖^2) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum,w]

variable (m : ℕ) (hmJ : m ≤ J) (nu : I → SourceOriginalProbePattern434 BG m)
local notation "patterns" => (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i))

/-- Exact explicit CLEAN family budget in squared physical norm.
This charges the true joint coefficient once per pattern and retains
the marked free-slot gain of each actual pattern. -/
def sourceOriginalMarkedCleanFamilyHilbertBudget434
    (q : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (C : I → ℝ) : ℝ :=
  (Fintype.card I:ℝ) * ∑ i : I,
    (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      ((C i)^2 * ∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g)

theorem source_original_MARKED_CLEAN_family_budget_nonneg434
    (q : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (C : I → ℝ) :
    0 ≤ sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C := by
  unfold sourceOriginalMarkedCleanFamilyHilbertBudget434
  apply mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg _)
  intro i hi
  apply mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) _)
  exact Finset.prod_nonneg (fun g hg => pow_nonneg
    (div_nonneg (sq_nonneg _) (by norm_num)) _)

/-- FULL original ordered CLEAN family Hilbert bound. The exact source
joint coefficient is retained through the coherent sum. -/
theorem source_original_MARKED_CLEAN_full_ordered_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ)
    (C : I → ℝ) (hC : ∀ i,0 ≤ C i) (hK : ∀ i aux a b,‖K i aux a b‖ ≤ C i)
    (f : State → Finset ℕ → ℂ) :
    sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalMarkedCleanOrderedFamily434 SP sm BP bm J ell m hmJ cap nu
        mu Vb K q Vs zeta theta o k f) ≤
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C *
      sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu f := by
  let E := sourceOriginalMarkedOrderedEnergy434 SP sm BP bm J ell cap Vs Vb mu
  let R (i : I) := sourceOriginalMarkedFullOrderedClean434 SP sm BP bm J ell m hmJ (nu i) cap
    o k q Vs Vb mu
    (sourceOriginalMarkedCleanFamilySectorK434 SP sm BP bm J ell m hmJ cap nu
      K zeta theta o k i) f
  have h (i : I) : E (R i) ≤
      (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
        ((C i)^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
          sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g)) * E f := by
    apply source_original_MARKED_FULL_ORDERED_CLEAN_Hilbert434 SP sm BP bm J ell m hmJ (nu i)
      cap hi o k q hq hq1 Vs hVs Vb hVb hHarmonic mu hmu (C i) (hC i)
    intro d r e y a S b
    exact source_original_MARKED_CLEAN_family_sector_K_cap434 SP sm BP bm J ell m hmJ cap nu
      K zeta theta o k C hC hK i d r e y a S b
  calc
    _ ≤ (Fintype.card I:ℝ)*∑ i : I,E (R i) :=
      source_original_MARKED_ordered_family_energy434 SP sm BP bm J ell cap
        Vs Vb mu hVs hVb hmu R
    _ ≤ (Fintype.card I:ℝ)*∑ i : I,
        ((memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
          ((C i)^2*(∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
            sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g))) * E f := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h i)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      exact (mul_assoc _ _ _).symm

/-- Full physical orbit/history bound for the actual coherent CLEAN
family identified by full_orbit_literal, without any history loss. -/
theorem source_original_MARKED_CLEAN_full_orbit_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ)
    (C : I → ℝ) (hC : ∀ i,0 ≤ C i) (hK : ∀ i aux a b,‖K i aux a b‖ ≤ C i)
    (F : Out → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu
      (sourceOriginalMarkedCleanOrbitFamily434 SP sm BP bm J ell m hmJ cap nu
        mu Vb K q Vs zeta theta o k F) ≤
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C *
      sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F := by
  apply le_trans (source_original_MARKED_orbit_compression_energy434 SP sm BP bm
    J ell cap Vs Vb mu hVs hVb hmu _)
  have h := source_original_MARKED_CLEAN_full_ordered_Hilbert434 SP sm BP bm J ell cap m hmJ nu
    hi mu hmu Vb hVb hHarmonic K q hq hq1 Vs hVs zeta theta o k C hC hK
    (fun y S => F (physicalFockProjection SP sm BP bm (J+ell) cap y) S)
  rw [source_original_MARKED_ordered_orbit_energy434] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCleanFiniteHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (cap : BG → ℕ)
variable {I : Type} [Fintype I] (nu : I → SourceOriginalProbePattern434 BG m)
local notation "patterns" => (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i))
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The TRUE finite reachable CLEAN action equals the full physical
Hilbert-family operator, with the actual history lift and orbit mass. -/
theorem source_original_ACTUAL_CLEAN_finite_orbit_exact434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (f : H → ℂ) (a : H) :
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs Vb mu K zeta theta o k f a =
    sourceOriginalMarkedCleanOrbitFamily434 SP sm BP bm J ell m hmJ cap nu
      mu Vb K q Vs zeta theta o k
      (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f)
      a.val.1 a.val.2 := by
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap a.val.1 a.val.2 ha.2.2
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) a.val.2 := by
    simpa only [x,hp] using ha.2.2
  have hframe := source_original_SOURCE_MARKED_FILTERED_E_frame_row434
    SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q 1 Vs Vb mu K zeta theta o k x a.val.2 hx F
  have hrep := source_original_SOURCE_MARKED_CLEAN_E_orbit_representative434
    SP sm BP bm J ell m cap patterns x a.val.2 hx q 1 Vs Vb mu hVs hmu
    K zeta theta o k F
  change fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu _ _ = _ at hrep
  rw [hp] at hrep
  calc
    _ = sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k x a.val.2 F := hframe.symm
    _ = _ := hrep.symm.trans
      (source_original_MARKED_CLEAN_full_orbit_literal434 SP sm BP bm J ell m hmJ cap nu
        mu Vb K q Vs zeta theta o k F a.val.1 a.val.2 ha.2.2).symm

/-- Quantitative Hilbert estimate for the ACTUAL finite signed CLEAN
E on the original reachable Fock x seen state space at rho=1.
This is an operator bound for every complex future, not a Schur bound. -/
theorem source_original_ACTUAL_CLEAN_finite_H_Hilbert434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ)
    (C : I → ℝ) (hC : ∀ i,0 ≤ C i) (hK : ∀ i aux a b,‖K i aux a b‖ ≤ C i)
    (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu)
      (sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs Vb mu K zeta theta o k f) ≤
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu) f := by
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f
  let R := sourceOriginalMarkedCleanOrbitFamily434 SP sm BP bm J ell m hmJ cap nu
    mu Vb K q Vs zeta theta o k F
  calc
    _ = sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu)
        (fun a : H => R a.val.1 a.val.2) := by
      congr 1
      funext a
      exact source_original_ACTUAL_CLEAN_finite_orbit_exact434 SP sm BP bm J ell m hmJ cap nu
        hcap mu hmu Vb K q Vs hVs zeta theta o k f a
    _ ≤ sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu R :=
      source_original_ACTUAL_signed_DIRTY_reachable_le_joint_energy434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu R
    _ ≤ sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C *
        sourceOriginalMemoryMarkedEnergy434 SP sm BP bm J ell cap Vs Vb mu F :=
      source_original_MARKED_CLEAN_full_orbit_Hilbert434 SP sm BP bm J ell cap m hmJ nu
        hi mu hmu Vb hVb hHarmonic K q hq hq1 Vs hVs zeta theta o k C hC hK F
    _ = _ := by
      rw [source_original_ACTUAL_signed_DIRTY_lift_joint_energy_exact434
        SP sm BP bm J ell cap Vs Vb mu hVs hVb hmu f]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualFiniteEOLDTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A bounded endpoint multiplier is contractive in the unchanged
physical squared norm, including zero-mass coordinates. -/
theorem source_original_ACTUAL_energy_multiplier434
    {H : Type} [Fintype H] (pi : H → ℝ) (u f : H → ℂ)
    (hu : ∀ a,‖u a‖ ≤ 1) :
    sourceOriginalSignedJointForwardEnergy434 pi (fun a => u a*f a) ≤
    sourceOriginalSignedJointForwardEnergy434 pi f := by
  unfold sourceOriginalSignedJointForwardEnergy434
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  have ht : ‖u a‖*‖f a‖ ≤ ‖f a‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hu a) (norm_nonneg (f a))
  exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)) 2

/-- Actual endpoint projectors are contractive without modifying pi. -/
theorem source_original_ACTUAL_energy_projector434
    {H : Type} [Fintype H] (pi : H → ℝ) (keep : H → Prop) (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434 pi (fun a => if keep a then f a else 0) ≤
    sourceOriginalSignedJointForwardEnergy434 pi f := by
  unfold sourceOriginalSignedJointForwardEnergy434
  apply Finset.sum_le_sum
  intro a ha
  by_cases h : keep a
  · simp only [if_pos h,le_refl]
  · simp only [if_neg h,norm_zero,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact sq_nonneg _

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {I : Type} [Fintype I] (patterns : I → SourcePattern BG J m)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP bm (J+ell)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exact OLD factorization survives the literal witness filter and the
global birth marker. No coefficient or future is replaced by its norm. -/
theorem source_original_MARKED_FILTERED_E_OLD_sandwich434
    (keep : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : State) (S : Finset ℕ) (F : Out → Finset ℕ → ℂ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs Vb mu K zeta theta o k x S F =
    sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho x *
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        keep q 1 Vs Vb mu K zeta theta o k x S
        (fun Y T => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho Y * F Y T) := by
  unfold sourceOriginalMemoryMarkedFilteredE434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : sourceOrientedPhysicalLegal SP sm BP bm J ell m cap patterns x o k z ∧
      keep x z ∧ orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns S z
  · simp only [if_pos h]
    rw [source_original_memory_OLD_source_coefficient_sandwich434
      SP sm BP bm J ell m cap patterns q rho Vs Vb mu K zeta theta o k x z]
    ring
  · simp only [if_neg h,mul_zero]

/-- The SAME factorization holds on the actual finite reachable carrier,
using its actual canonical source and the unchanged zero history lift. -/
theorem source_original_ACTUAL_finite_E_OLD_sandwich434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (keep : (x : State) → FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x → Prop)
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (f : H → ℂ) (a : H) :
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      keep q rho Vs Vb mu K zeta theta o k f a =
    sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho
      (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1) *
      sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
        keep q 1 Vs Vb mu K zeta theta o k
        (fun b => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho b.val.1*f b) a := by
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  let fR : H → ℂ := fun b => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho b.val.1*f b
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap f
  have hF : sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap fR =
      fun Y T => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho Y * F Y T := by
    funext Y T
    unfold sourceOriginalActualSignedHistoryLift434
    dsimp only [F]
    unfold sourceOriginalActualSignedHistoryLift434
    split_ifs <;> simp only [fR,mul_zero]
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap a.val.1 a.val.2 ha.2.2
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) a.val.2 := by
    simpa only [x,hp] using ha.2.2
  have hR := source_original_SOURCE_MARKED_FILTERED_E_frame_row434
    SP sm BP bm J ell m cap patterns keep q rho Vs Vb mu K zeta theta o k x a.val.2 hx F
  have h1 := source_original_SOURCE_MARKED_FILTERED_E_frame_row434
    SP sm BP bm J ell m cap patterns keep q 1 Vs Vb mu K zeta theta o k x a.val.2 hx
    (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap fR)
  calc
    _ = sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
        keep q rho Vs Vb mu K zeta theta o k x a.val.2 F := hR.symm
    _ = sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho x *
        sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
          keep q 1 Vs Vb mu K zeta theta o k x a.val.2
          (fun Y T => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho Y * F Y T) :=
      source_original_MARKED_FILTERED_E_OLD_sandwich434 SP sm BP bm J ell m cap patterns
        keep q rho Vs Vb mu K zeta theta o k x a.val.2 F
    _ = sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho x *
        sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
          keep q 1 Vs Vb mu K zeta theta o k x a.val.2
          (sourceOriginalActualSignedHistoryLift434 SP sm BP bm J ell cap fR) := by rw [hF]
    _ = _ := congrArg (fun z => sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho x*z) h1

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCleanOLDMaskedHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1100000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (cap : BG → ℕ)
variable {I : Type} [Fintype I] (nu : I → SourceOriginalProbePattern434 BG m)
local notation "patterns" => (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i))
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- The genuine finite CLEAN E at every admissible rho has the SAME
Hilbert budget as rho=1. OLD endpoint factors are retained explicitly.
No free damping claim is made for a subsequent G evolution. -/
theorem source_original_ACTUAL_CLEAN_finite_H_rho_Hilbert434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ)
    (C : I → ℝ) (hC : ∀ i,0 ≤ C i) (hK : ∀ i aux a b,‖K i aux a b‖ ≤ C i)
    (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu)
      (sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs Vb mu K zeta theta o k f) ≤
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu) f := by
  let pi := sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu
  let E := sourceOriginalSignedJointForwardEnergy434 pi
  let fR : H → ℂ := fun b => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho b.val.1*f b
  let R := sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q 1 Vs Vb mu K zeta theta o k fR
  let u : H → ℂ := fun a => sourceOriginalMemoryOldInput434 SP sm BP bm J ell cap rho
    (sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1)
  have hu (a : H) : ‖u a‖ ≤ 1 :=
    source_original_memory_OLD_input_norm_le_one434 SP sm BP bm J ell cap rho hrho hrho1 _
  have hf : E fR ≤ E f := source_original_ACTUAL_energy_multiplier434 pi
    (fun b => sourceOriginalMemoryOldOutput434 SP sm BP bm J ell rho b.val.1) f
    (fun b => source_original_memory_OLD_output_norm_le_one434 SP sm BP bm J ell rho hrho hrho1 _)
  calc
    _ = E (fun a => u a*R a) := by
      congr 1
      funext a
      exact source_original_ACTUAL_finite_E_OLD_sandwich434 SP sm BP bm J ell m cap patterns
        hcap (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs Vb mu K zeta theta o k f a
    _ ≤ E R := source_original_ACTUAL_energy_multiplier434 pi u R hu
    _ ≤ sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C * E fR :=
      source_original_ACTUAL_CLEAN_finite_H_Hilbert434 SP sm BP bm J ell m hmJ cap nu
        hcap hi mu hmu Vb hVb hHarmonic K q hq hq1 Vs hVs zeta theta o k C hC hK fR
    _ ≤ _ := mul_le_mul_of_nonneg_left hf
      (source_original_MARKED_CLEAN_family_budget_nonneg434 BP J ell m hmJ nu q Vs mu C)

/-- Actual signed CLEAN E MATRIX with BOTH original total-OLD≤T
projectors, full source joint K, physical density and numerical seen.
Its quantitative bound is proved for every complex future; no assumed
CLEAN Schur estimate or history-count factor is present. -/
theorem source_original_ACTUAL_CLEAN_OLD_MASKED_finite_H_Hilbert434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(bm g p:ℝ))=Vb g)
    (K : SourcePatternK BP J ell m patterns)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ)
    (C : I → ℝ) (hC : ∀ i,0 ≤ C i) (hK : ∀ i aux a b,‖K i aux a b‖ ≤ C i)
    (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu)
      (fun a : H => ∑ b : H,sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs Vb mu K zeta theta o k T a b*f b) ≤
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu) f := by
  let pi := sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs Vb mu
  let E := sourceOriginalSignedJointForwardEnergy434 pi
  let gate := sourceOriginalActualSignedOLDGate434 SP sm BP bm J ell cap T
  let fT : H → ℂ := fun b => if gate b then f b else 0
  let R := sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
    (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
    q rho Vs Vb mu K zeta theta o k fT
  calc
    _ = E (fun a => if gate a then R a else 0) := by
      congr 1
      funext a
      exact (source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434
        SP sm BP bm J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q rho Vs Vb mu K zeta theta o k T f a).symm
    _ ≤ E R := source_original_ACTUAL_energy_projector434 pi gate R
    _ ≤ sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C * E fT :=
      source_original_ACTUAL_CLEAN_finite_H_rho_Hilbert434 SP sm BP bm J ell m hmJ cap nu
        hcap hi mu hmu Vb hVb hHarmonic K q hq hq1 rho hrho hrho1
        Vs hVs zeta theta o k C hC hK fT
    _ ≤ _ := mul_le_mul_of_nonneg_left (source_original_ACTUAL_energy_projector434 pi gate f)
      (source_original_MARKED_CLEAN_family_budget_nonneg434 BP J ell m hmJ nu q Vs mu C)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualRawComparisonCleanHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- RAW is the empty probe; every comparison is its ORIGINAL probe pair. -/
def sourceOriginalMarkedRawComparisonProbe434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G) (m : ℕ) :
    SourceOriginalMemoryRawComparisonIndex434 blockA blockB m → SourceOriginalProbePattern434 G m
  | none => (∅,∅)
  | some nu => nu.val

theorem source_original_MARKED_RAW_COMPARISON_pattern_exact434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G) (J m : ℕ) (hmJ : m ≤ J) :
    sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ =
    fun i => sourceOriginalProbeMemoryPattern434 J m hmJ
      (sourceOriginalMarkedRawComparisonProbe434 blockA blockB m i) := by
  funext i
  cases i with
  | none =>
    dsimp only [sourceOriginalMemoryRawComparisonPattern434,
      sourceOriginalMarkedRawComparisonProbe434,sourceOriginalProbeMemoryPattern434]
    congr 1
    funext g
    simp [sourceOriginalProbeFreedSlots434]
  | some nu => rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (P : BG → Finset ℕ)
variable [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
variable (blockA blockB : Finset BG) (J ell m : ℕ) (hmJ : m ≤ J) (cap : BG → ℕ)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "Index" => SourceOriginalMemoryRawComparisonIndex434 blockA blockB m
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP
  (fun _ p => (p : ℕ)) J ell cap

/-- Quantitative ORIGINAL RAW + ALL comparison CLEAN matrix bound.
The actual orientation transpose, joint canonical K, numerical histories,
physical density and BOTH OLD projectors are retained. The cap of K is
PROVED from its arithmetic formula: no analytic K-smallness premise and
no bounded terminal mask is assumed. -/
theorem source_original_ACTUAL_RAW_COMPARISON_CLEAN_OLD_Hilbert434
    (hcap : ∀ g,Fintype.card {p : ℕ // p ∈ P g} ≤ cap g)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : BG) → {p : ℕ // p ∈ P g} → ℝ) (hmu : ∀ g p,0 < mu g p)
    (Vb : BG → ℝ) (hVb : ∀ g,0 < Vb g)
    (hHarmonic : ∀ g,(∑ p : {p : ℕ // p ∈ P g},1/(p.val:ℝ))=Vb g)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 BG m → ℝ) (xi : ℝ) (hxi : 0 < xi)
    (hhA : ∀ v ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hA v)
    (hhB : ∀ v ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,0 < hB v)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ) (f : H → ℂ) :
    let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
    let Kn := memoryOrientationK BP J ell m pats
      (sourceOriginalMemoryRawComparisonK434 P Vb blockA blockB J ell m hmJ Q hA hB xi) o
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ p => p.val)
        J ell cap Vs Vb mu)
      (fun a : H => ∑ b : H,sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP (fun _ p => p.val) J ell m cap pats
        (sourceOriginalCleanChoice434 SP sm BP (fun _ p => p.val) J ell m cap pats)
        q rho Vs Vb mu Kn zeta theta o k T a b*f b) ≤
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ
      (sourceOriginalMarkedRawComparisonProbe434 blockA blockB m) q Vs mu
      (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi) *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ p => p.val)
          J ell cap Vs Vb mu) f := by
  dsimp only
  let pats := sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
  let nu := sourceOriginalMarkedRawComparisonProbe434 blockA blockB m
  let C := sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi
  let pi := sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ p => p.val)
    J ell cap Vs Vb mu
  let gain := sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C
  let lhs (ps : Index → SourcePattern BG J m) (K : SourcePatternK BP J ell m ps) : ℝ :=
    sourceOriginalSignedJointForwardEnergy434 pi
      (fun a : H => ∑ b : H,sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP (fun _ p => p.val) J ell m cap ps
        (sourceOriginalCleanChoice434 SP sm BP (fun _ p => p.val) J ell m cap ps)
        q rho Vs Vb mu K zeta theta o k T a b*f b)
  have hC (i : Index) : 0 ≤ C i :=
    source_original_memory_RAW_COMPARISON_cap_nonneg434 blockA blockB m Q xi i
  have hall : ∀ K : SourcePatternK BP J ell m
      (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i)),
      (∀ i aux a b,‖K i aux a b‖ ≤ C i) →
      lhs (fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i)) K ≤
        gain * sourceOriginalSignedJointForwardEnergy434 pi f := by
    intro K hK
    exact source_original_ACTUAL_CLEAN_OLD_MASKED_finite_H_Hilbert434
      SP sm BP (fun _ p => p.val) J ell m hmJ cap nu
      hcap hi mu hmu Vb hVb hHarmonic K q hq hq1 rho hrho hrho1
      Vs hVs zeta theta o k T C hC hK f
  have hraw : ∀ K : SourcePatternK BP J ell m pats,
      (∀ i aux a b,‖K i aux a b‖ ≤ C i) →
      lhs pats K ≤ gain * sourceOriginalSignedJointForwardEnergy434 pi f := by
    have hp : pats = fun i => sourceOriginalProbeMemoryPattern434 J m hmJ (nu i) :=
      source_original_MARKED_RAW_COMPARISON_pattern_exact434 blockA blockB J m hmJ
    rw [hp]
    exact hall
  apply hraw
  intro i aux a b
  unfold memoryOrientationK
  split_ifs
  · exact source_original_memory_RAW_COMPARISON_K_cap434 P Vb blockA blockB J ell m hmJ Q
      hA hB xi hhA hhB hxi i aux a b
  · exact source_original_memory_RAW_COMPARISON_K_cap434 P Vb blockA blockB J ell m hmJ Q
      hA hB xi hhA hhB hxi i aux b a

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualCleanExplicitBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The genuine tilted mass bound yields a gain at every BIG group.
All actual extra comparison free slots only improve this bound. -/
theorem source_original_MARKED_CLEAN_family_budget_three_halves434
    {SG : Type} [Fintype SG] {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J)
    {I : Type} [Fintype I] (nu : I → SourceOriginalProbePattern434 BG m)
    (q : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hmu : ∀ g p,0 ≤ mu g p) (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ (3:ℝ)/2)
    (C : I → ℝ) :
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ nu q Vs mu C ≤
    ((Fintype.card I:ℝ)*(∑ i : I,(C i)^2)) *
      (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      ((9:ℝ)/16)^(ell*Fintype.card BG) := by
  have hDelta (i : I) :
      (∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
        sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g) ≤
      ((9:ℝ)/16)^(ell*Fintype.card BG) := by
    have h1 :
        (∏ g : BG,((∑ p : BP g,mu g p)^2/4)^
          sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g) ≤
        ((9:ℝ)/16)^(∑ g : BG,sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_le_prod₀
      · intro g hg
        positivity
      · intro g hg
        apply pow_le_pow_left₀ (by positivity)
        have h0 : 0 ≤ ∑ p : BP g,mu g p := Finset.sum_nonneg (fun p _ => hmu g p)
        have hs := pow_le_pow_left₀ h0 (hMass g) 2
        nlinarith only [hs]
    have hc : ell*Fintype.card BG ≤
        ∑ g : BG,sourceOriginalProbeFreeMarkCount434 J ell m hmJ (nu i) g := by
      calc
        _ = ∑ _g : BG,ell := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun g _ => Nat.le_add_right _ _)
    obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hc
    apply h1.trans
    rw [hn,pow_add]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 9/16) (by norm_num : (9:ℝ)/16 ≤ 1))
  unfold sourceOriginalMarkedCleanFamilyHilbertBudget434
  calc
    _ ≤ (Fintype.card I:ℝ)*∑ i : I,
        (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
          ((C i)^2*((9:ℝ)/16)^(ell*Fintype.card BG)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hDelta i) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Exact RAW-plus-comparison coefficient-square cost; the original
finite pattern set is counted once, without auxiliary/history inflation. -/
theorem source_original_RAW_COMPARISON_CLEAN_cap_square_sum434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (blockA blockB : Finset BG) (m Q : ℕ) (xi : ℝ) :
    (∑ i : SourceOriginalMemoryRawComparisonIndex434 blockA blockB m,
      (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi i)^2) =
    1 + ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ) *
      ((Q:ℝ)^4*(xi⁻¹)^2)^2 := by
  simp [SourceOriginalMemoryRawComparisonIndex434,Fintype.sum_option,
    sourceOriginalMemoryRawComparisonCap434,add_comm]

/-- A completely explicit usable budget for the actual RAW/comparison
CLEAN matrix: SMALL conditioning, true pattern count, canonical K price,
and the physical BIG marked gain are all visible. -/
theorem source_original_RAW_COMPARISON_CLEAN_budget_three_halves434
    {SG : Type} [Fintype SG] {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)]
    (blockA blockB : Finset BG) (J ell m : ℕ) (hmJ : m ≤ J)
    (q : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hmu : ∀ g p,0 ≤ mu g p) (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ (3:ℝ)/2)
    (Q : ℕ) (xi : ℝ) :
    sourceOriginalMarkedCleanFamilyHilbertBudget434 BP J ell m hmJ
      (sourceOriginalMarkedRawComparisonProbe434 blockA blockB m) q Vs mu
      (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi) ≤
    (((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card+1:ℕ):ℝ) *
      (1 + ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ) *
        ((Q:ℝ)^4*(xi⁻¹)^2)^2) *
      (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      ((9:ℝ)/16)^(ell*Fintype.card BG) := by
  have h := source_original_MARKED_CLEAN_family_budget_three_halves434 BP J ell m hmJ
    (sourceOriginalMarkedRawComparisonProbe434 blockA blockB m) q Vs mu hmu hMass
    (sourceOriginalMemoryRawComparisonCap434 blockA blockB m Q xi)
  rw [source_original_RAW_COMPARISON_CLEAN_cap_square_sum434] at h
  simpa only [SourceOriginalMemoryRawComparisonIndex434,Fintype.card_option,Fintype.card_coe] using h

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26RawFullPhysicalHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Explicit remaining RAW cost under the already proved physical
tilted-mass bound. Q and xi are absent; the true pattern and SMALL
costs have not been declared small. -/
theorem source_original_B26_RAW_budget_three_halves434
    {SG G : Type} [Fintype SG] [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (blockA blockB : Finset G) (q : ℝ) (Vs : SG → ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p,0 ≤ mu g p)
    (hMass : ∀ g,(∑ p : {p : ℕ // p ∈ P g},mu g p) ≤ (3:ℝ)/2) :
    sourceOriginalB26RawFamilyHilbertBudget434 P J ell m hmJ blockA blockB q Vs mu ≤
      ((sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card:ℝ)^2 *
      (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      ((9:ℝ)/16)^(ell*Fintype.card G) := by
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  have he : sourceOriginalB26RawFamilyHilbertBudget434 P J ell m hmJ blockA blockB q Vs mu =
      sourceOriginalMarkedCleanFamilyHilbertBudget434 (fun g => {p : ℕ // p ∈ P g})
        J ell m hmJ (fun nu : family => nu.val) q Vs mu (fun _ => 1) := by
    unfold sourceOriginalB26RawFamilyHilbertBudget434 sourceOriginalMarkedCleanFamilyHilbertBudget434
    simp only [one_pow,one_mul,Fintype.card_coe]
    congr 1
    exact (Finset.sum_coe_sort family (fun nu =>
      (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
        ∏ g : G,((∑ p : {p : ℕ // p ∈ P g},mu g p)^2/4)^
          sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g)).symm
  rw [he]
  have h := source_original_MARKED_CLEAN_family_budget_three_halves434
    (fun g => {p : ℕ // p ∈ P g}) J ell m hmJ (fun nu : family => nu.val) q Vs mu hmu hMass
    (fun _ => 1)
  simpa only [one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe,pow_two] using h

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
local notation "Budget" => sourceOriginalB26RawFamilyHilbertBudget434 data.Tb J ell m hmJ
  blockA blockB q data.Vsmall mu
local notation "E" => sourceOriginalMarkedOrderedEnergy434 SP sm BP (fun _ => Subtype.val)
  J ell cap data.Vsmall data.Vbig mu

/-- The independently defined RAW packet in every actual ordered
Fock sector, using the original four normalized endpoint means. -/
def sourceOriginalB26NodupFullOrderedRaw434 (f : State → Finset ℕ → ℂ) (a : State) (S : Finset ℕ) : ℂ :=
  let z := sourceOriginalMarkedSectorEquiv434 SP sm BP (fun _ => Subtype.val) J ell cap a
  sourceOriginalB26NodupPhysicalRawMean434 data SP sm
    (fun g => (z.1.1 g).val) z.1.2 cap (fun g => Nat.le_of_lt_succ (z.1.1 g).isLt)
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt
    (fun ys b T u => f (sourceOriginalMarkedSectorEmbed434 SP sm BP (fun _ => Subtype.val) J ell cap z.1 ys b u) T)
    z.2.1.1 z.2.2 S z.2.1.2

/-- The corresponding literal CLEAN packet is also defined directly
from its original physical channels and joint K, not from an error bound. -/
def sourceOriginalB26NodupFullOrderedClean434 (f : State → Finset ℕ → ℂ) (a : State) (S : Finset ℕ) : ℂ :=
  let z := sourceOriginalMarkedSectorEquiv434 SP sm BP (fun _ => Subtype.val) J ell cap a
  sourceOriginalB26NodupPhysicalCleanMean434 data SP sm
    (fun g => (z.1.1 g).val) z.1.2 cap (fun g => Nat.le_of_lt_succ (z.1.1 g).isLt)
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt
    (fun ys b T u => f (sourceOriginalMarkedSectorEmbed434 SP sm BP (fun _ => Subtype.val) J ell cap z.1 ys b u) T)
    z.2.1.1 z.2.2 S z.2.1.2

theorem source_original_B26_NODUP_FULL_CLEAN_RAW_difference434
    (f : State → Finset ℕ → ℂ) :
    sourceOriginalB26NodupFullOrderedCleanRaw434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f =
    fun a S => sourceOriginalB26NodupFullOrderedClean434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f a S -
    sourceOriginalB26NodupFullOrderedRaw434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt f a S := rfl

/-- Conductor-free quantitative RAW estimate on the FULL ordered
physical Fock times numerical-seen carrier. Sector weights, factorials
and the joint future are unchanged; no sector count is charged. -/
theorem source_original_B26_NODUP_RAW_FULL_ORDERED_Hilbert434
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
  exact source_original_B26_NODUP_RAW_PHYSICAL_MEAN_Hilbert434 data SP sm sizes prime cap hsz
    q N blockA blockB J ell m hmJ Q h xi zeta theta o k hq hq1 ho hi hmu epsSrc epsTgt F

/-- The actual weighted orbit compression of the direct RAW packet. -/
def sourceOriginalB26NodupFullOrbitRaw434 (F : Out → Finset ℕ → ℂ) (X : Out) (S : Finset ℕ) : ℂ :=
  fullPhysicalOrbitAverage SP sm BP (fun _ => Subtype.val) (J+ell) cap data.Vsmall mu
    (fun a => sourceOriginalB26NodupFullOrderedRaw434 data SP sm cap q N blockA blockB
      J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt
      (fun b T => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap b) T) a S) X

/-- The same explicit RAW estimate after original Fock orbit averaging. -/
theorem source_original_B26_NODUP_RAW_FULL_ORBIT_Hilbert434
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
  have h := source_original_B26_NODUP_RAW_FULL_ORDERED_Hilbert434 data SP sm cap q N blockA blockB
    J ell m hmJ Q h xi zeta theta o k epsSrc epsTgt hq hq1 ho hi hmu
    (fun b T => F (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap b) T)
  rw [source_original_MARKED_ordered_orbit_energy434] at h
  exact h

end Green64Analytic.CorrelationSquare

end

end

