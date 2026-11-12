module

public import Green64.Library.Weights.B26FullKernelAuxTransport
public import Green64.Library.Weights.B26OriginalRawNoneSplit

@[expose] public section

/-!
# Weights / B26FullRowTranspose

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26FullRowTranspose -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The original two-block family is reindexed by exchanging its blocks. -/
def sourceOriginalProbeSwapFamilyEquiv434
    {G : Type} [DecidableEq G] (blockA blockB : Finset G) (m : ℕ) :
    ↥(sourceOriginalTwoBlockProbePatterns434 blockA blockB m) ≃
      ↥(sourceOriginalTwoBlockProbePatterns434 blockB blockA m) where
  toFun := fun v => ⟨v.val.swap, by
    have hv := (source_original_two_block_probe_pattern_mem434 blockA blockB m v.val.1 v.val.2).mp v.property
    exact (source_original_two_block_probe_pattern_mem434 blockB blockA m v.val.2 v.val.1).mpr
      ⟨hv.2.2.1,hv.2.2.2,hv.1,hv.2.1⟩⟩
  invFun := fun v => ⟨v.val.swap, by
    have hv := (source_original_two_block_probe_pattern_mem434 blockB blockA m v.val.1 v.val.2).mp v.property
    exact (source_original_two_block_probe_pattern_mem434 blockA blockB m v.val.2 v.val.1).mpr
      ⟨hv.2.2.1,hv.2.2.2,hv.1,hv.2.1⟩⟩
  left_inv := by intro v; apply Subtype.ext; rfl
  right_inv := by intro v; apply Subtype.ext; rfl

variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
variable (J ell m : ℕ) (hmJ : m ≤ J) (cap : G → ℕ)
variable (blockA blockB : Finset G) (V : G → ℝ) (Q : ℕ) (h xi : ℝ)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "patsA" => sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
local notation "patsB" => sourceOriginalMemoryRawComparisonPattern434 blockB blockA J m hmJ
local notation "KA" => sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q
  (fun _ => h) (fun _ => h) xi
local notation "KB" => sourceOriginalMemoryRawComparisonK434 P V blockB blockA J ell m hmJ Q
  (fun _ => h) (fun _ => h) xi

/-- RAW-none is fixed. Every genuine comparison auxiliary tuple is
transported bijectively; all original endpoint permutations are fixed. -/
def sourceOriginalB26FullFrameSwapEquiv434 :
    SourceOriginalB26FrozenFrame434 BP J ell m patsA ≃
      SourceOriginalB26FrozenFrame434 BP J ell m patsB := by
  apply Equiv.sigmaCongr (Equiv.optionCongr (sourceOriginalProbeSwapFamilyEquiv434 blockA blockB m))
  intro v
  apply Equiv.prodCongr _ (Equiv.refl _)
  cases v with
  | none => exact Equiv.refl _
  | some v => exact sourceOriginalProbeSwapAuxEquiv434 P J m hmJ v.val

variable (sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
local notation "Small" => GroupState SP sm (J+ell)
local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "Out" => FullPhysicalOutput SP sm BP (fun _ => Subtype.val) (J+ell)
local notation "SPerm" => GroupPermFamily (G := SG) (J+ell)

private theorem indexed_transpose
    (prime : (g : G) → Fin (sizes g) → BP g)
    (mu : (g : G) → BP g → ℝ) (q : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (F : Out → Finset ℕ → ℂ)
    (xs ys : Small) (a b : A) (t : SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime) (S : Finset ℕ)
    (r : SourceOriginalB26FrozenFrame434 BP J ell m patsA) (ss tt : SPerm) :
    sourceOriginalMarkedCleanIndexedTerm434 SP sm BP (fun _ => Subtype.val) J ell m cap
      sizes hsizes prime patsB mu V KB q Vs zeta theta o k F xs ys a b t S
      (sourceOriginalB26FullFrameSwapEquiv434 P J ell m hmJ blockA blockB r) ss tt =
    sourceOriginalMarkedCleanIndexedTerm434 SP sm BP (fun _ => Subtype.val) J ell m cap
      sizes hsizes prime patsA mu V (fun v aux u w => KA v aux w u)
      q Vs zeta theta o k F xs ys a b t S r ss tt := by
  rcases r with ⟨v,aux,sigma,tau⟩
  cases v with
  | none => rfl
  | some v =>
    change SourceBigAux BP J m (sourceOriginalProbeMemoryPattern434 J m hmJ v.val) at aux
    have he : sourceOriginalB26FullFrameSwapEquiv434 P J ell m hmJ blockA blockB
        ⟨some v,aux,sigma,tau⟩ =
      ⟨some (sourceOriginalProbeSwapFamilyEquiv434 blockA blockB m v),
        sourceOriginalProbeSwapAux434 P J m hmJ v.val aux,sigma,tau⟩ := rfl
    rw [he]
    unfold sourceOriginalMarkedCleanIndexedTerm434 sourceOriginalB26FrozenPhysicalWeight434
    dsimp only [sourceOriginalMemoryRawComparisonPattern434,
      sourceOriginalMemoryRawComparisonK434, sourceOriginalProbeSwapFamilyEquiv434]
    simp only [Equiv.coe_fn_mk]
    simp only [source_original_B26_full_K_swap_divisor434,
      source_original_B26_full_K_swap_aux_mass434, source_original_B26_full_K_swap_aux_ban434,
      source_original_B26_full_K_transpose434, source_original_B26_full_K_swap_pattern434]

/-- Full physical RAW-plus-comparison CLEAN row transpose. This
includes the common complex future, actual D and OLD translations,
all birth/history tests, all endpoint means and the entire RAW-none term. -/
theorem source_original_B26_FULL_CLEAN_row_transpose434
    (prime : (g : G) → Fin (sizes g) → BP g)
    (mu : (g : G) → BP g → ℝ) (q : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (F : Out → Finset ℕ → ℂ)
    (xs : Small) (a : A) (t : SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime) (S : Finset ℕ) :
    let st := (xs,sourceOriginalB26FrozenBigState434 BP (fun _ => Subtype.val)
      J ell cap sizes hsizes prime a t)
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patsB
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsB)
      q 1 Vs V mu KB zeta theta o k st S F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patsA
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsA)
      q 1 Vs V mu (fun v aux u w => KA v aux w u) zeta theta o k st S F := by
  dsimp only
  simp_rw [source_original_MARKED_CLEAN_full_literal_row434]
  let e := sourceOriginalB26FullFrameSwapEquiv434 P J ell m hmJ blockA blockB
  have he := e.sum_comp (fun r => ∑ b : A,∑ ys : Small,∑ ss : SPerm,∑ tt : SPerm,
    sourceOriginalMarkedCleanIndexedTerm434 SP sm BP (fun _ => Subtype.val) J ell m cap
      sizes hsizes prime patsB mu V KB q Vs zeta theta o k F xs ys a b t S r ss tt)
  rw [←he]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro ys hys
  apply Finset.sum_congr rfl
  intro ss hss
  apply Finset.sum_congr rfl
  intro tt htt
  exact indexed_transpose SP sm P J ell m hmJ cap blockA blockB V Q h xi
    sizes hsizes prime mu q Vs zeta theta o k F xs ys a b t S r ss tt

end Green64Analytic.CorrelationSquare

end

end

