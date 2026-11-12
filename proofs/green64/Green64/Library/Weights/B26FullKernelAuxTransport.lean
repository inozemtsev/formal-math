module

public import Green64.Library.Correlation.B26CanonicalPhysicalBridge

@[expose] public section

/-!
# Weights / B26FullKernelAuxTransport

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26FullKernelAuxTransport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

private theorem freed_swap
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (g : G) :
    sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g =
      sourceOriginalProbeFreedSlots434 J m hmJ ν g := by
  simp [sourceOriginalProbeFreedSlots434, or_comm]

theorem source_original_B26_full_K_swap_pattern434
    {G : Type} [DecidableEq G] (J m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) :
    sourceOriginalProbeMemoryPattern434 J m hmJ ν.swap =
      sourceOriginalProbeMemoryPattern434 J m hmJ ν := by
  unfold sourceOriginalProbeMemoryPattern434
  congr 1
  funext g
  exact freed_swap J m hmJ ν g

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}), NeZero p.val]
variable (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "pat" => sourceOriginalProbeMemoryPattern434 J m hmJ ν
local notation "swpat" => sourceOriginalProbeMemoryPattern434 J m hmJ ν.swap

/-- Actual auxiliary reindexing is an involutive bijection. -/
def sourceOriginalProbeSwapAuxEquiv434 :
    SourceBigAux BP J m pat ≃ SourceBigAux BP J m swpat where
  toFun := sourceOriginalProbeSwapAux434 P J m hmJ ν
  invFun := sourceOriginalProbeSwapAux434 P J m hmJ ν.swap
  left_inv := by intro aux; funext g j; rfl
  right_inv := by intro aux; funext g j; rfl

private theorem aux_prod_swap {M : Type} [CommMonoid M]
    (f : (g : G) → BP g → M) (aux : SourceBigAux BP J m pat) :
    (∏ g : G, ∏ j : sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g,
      f g (sourceOriginalProbeSwapAux434 P J m hmJ ν aux g j)) =
    ∏ g : G, ∏ j : sourceOriginalProbeFreedSlots434 J m hmJ ν g, f g (aux g j) := by
  apply Finset.prod_congr rfl
  intro g hg
  let e : sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g ≃
      sourceOriginalProbeFreedSlots434 J m hmJ ν g :=
    Equiv.subtypeEquivRight (fun j => by rw [freed_swap])
  exact Fintype.prod_equiv e _ _ (by intro j; rfl)

/-- The original untilted harmonic auxiliary law is unchanged. -/
theorem source_original_B26_full_K_swap_aux_mass434
    (V : G → ℝ) (aux : SourceBigAux BP J m pat) :
    sourceAuxMass BP (fun _ => Subtype.val) J m V swpat
      (sourceOriginalProbeSwapAux434 P J m hmJ ν aux) =
    sourceAuxMass BP (fun _ => Subtype.val) J m V pat aux := by
  rw [source_original_probe_memory_aux_mass434, source_original_probe_memory_aux_mass434]
  exact aux_prod_swap P J m hmJ ν (fun g p => sourcePrimeSharedAtom434 (V g) p.val) aux

/-- The full source divisor is preserved, including its SMALL factor,
every original shared BIG slot and every freed auxiliary coordinate. -/
theorem source_original_B26_full_K_swap_divisor434
    (dsmall : ℕ) (aux : SourceBigAux BP J m pat)
    (a : SourceOriginalB26Active434 BP J ell)
    (sigma : BigGroupPerm (BG := G) (J+ell)) :
    sourceOriginalB26FrozenD434 BP (fun _ => Subtype.val) J ell m dsmall swpat
      (sourceOriginalProbeSwapAux434 P J m hmJ ν aux) a sigma =
    sourceOriginalB26FrozenD434 BP (fun _ => Subtype.val) J ell m dsmall pat aux a sigma := by
  rw [source_original_probe_memory_frozen_divisor434,
    source_original_probe_memory_frozen_divisor434]
  have hs (g : G) : sourceOriginalProbeSharedSlots434 J ell m hmJ ν.swap g =
      sourceOriginalProbeSharedSlots434 J ell m hmJ ν g := by
    unfold sourceOriginalProbeSharedSlots434
    rw [freed_swap]
  simp only [hs]
  rw [aux_prod_swap]

/-- Both genuine auxiliary bans are retained by the same reindexing. -/
theorem source_original_B26_full_K_swap_aux_ban434
    (aux : SourceBigAux BP J m pat) (a b : SourceOriginalB26Active434 BP J ell) :
    sourceOriginalB26FrozenAuxBan434 BP J ell m swpat
      (sourceOriginalProbeSwapAux434 P J m hmJ ν aux) a b ↔
    sourceOriginalB26FrozenAuxBan434 BP J ell m pat aux a b := by
  constructor
  · intro hb g j i
    let j' : sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g :=
      ⟨j.val, by
        have hj := j.property
        change j.val ∈ sourceOriginalProbeFreedSlots434 J m hmJ ν g at hj
        simpa only [freed_swap] using hj⟩
    exact hb g j' i
  · intro hb g j i
    exact hb g ⟨j.val, by
      have hj := j.property
      change j.val ∈ sourceOriginalProbeFreedSlots434 J m hmJ ν.swap g at hj
      change j.val ∈ sourceOriginalProbeFreedSlots434 J m hmJ ν g
      simpa only [freed_swap] using hj⟩ i

/-- Full physical joint K, including the actual ban and numerical
birth-list Nodup, agrees after the endpoint transpose and block swap.
The statement includes orientation -1 with its complete conjugation. -/
theorem source_original_B26_full_joint_K_transpose434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (V : G → ℝ) (Q : ℕ) (hA hB xi zeta theta : ℝ) (o k : ℤ)
    (aux : SourceBigAux BP J m pat)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    {R : Type} (d : SourceOriginalB26SharedTuple434 SP J ell) (r : R)
    (a b : SourceOriginalB26Active434 BP J ell) (S : Finset ℕ) :
    sourceOriginalMarkedCleanJointK434 SP sm BP (fun _ => Subtype.val) J ell m hmJ ν.swap
      (sourceOriginalProbeSwapAux434 P J m hmJ ν aux) sigma tau
      (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν.swap Q hB hA xi)
      zeta theta o k d r a S b =
    sourceOriginalMarkedCleanJointK434 SP sm BP (fun _ => Subtype.val) J ell m hmJ ν
      aux sigma tau
      (fun v u w => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi v w u)
      zeta theta o k d r a S b := by
  have hb : sourceOriginalMarkedCleanBirthNumbers434 BP (fun _ => Subtype.val) J ell m swpat b =
      sourceOriginalMarkedCleanBirthNumbers434 BP (fun _ => Subtype.val) J ell m pat b := by
    rw [source_original_B26_full_K_swap_pattern434]
  unfold sourceOriginalMarkedCleanJointK434
  dsimp only
  rw [source_original_B26_full_K_swap_divisor434, source_original_B26_full_K_swap_aux_ban434,
    hb, source_original_B26_full_K_transpose434]

end Green64Analytic.CorrelationSquare

end

end

