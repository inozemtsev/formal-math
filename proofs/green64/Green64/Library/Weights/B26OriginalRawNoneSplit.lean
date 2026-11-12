module

public import Green64.Library.Weights.B26ActualFiniteConductorFree
public import Green64.Library.Correlation.Part045

@[expose] public section

/-!
# Weights / B26OriginalRawNoneSplit

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26OriginalRawNoneSplit -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The literal RAW-none pattern, kept separate from the comparison family. -/
def sourceOriginalB26RawNonePattern434
    {G : Type} [DecidableEq G] (J m : ℕ) : PUnit → SourcePattern G J m :=
  fun _ => ⟨fun _ => ∅, by intro g; simp⟩

variable {SG G : Type} [Fintype SG] [DecidableEq SG] [Fintype G] [DecidableEq G]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
variable (J ell m : ℕ) (hmJ : m ≤ J) (cap : G → ℕ)
variable (blockA blockB : Finset G) (V : G → ℝ) (Q : ℕ) (h xi : ℝ)
local notation "BP" => (fun g => {p : ℕ // p ∈ P g})
local notation "State" => FullPhysicalState SP sm BP (fun _ => Subtype.val) (J+ell) cap
local notation "Out" => FullPhysicalOutput SP sm BP (fun _ => Subtype.val) (J+ell)
local notation "Hist" => sourceOriginalActualSignedHistoryState434 SP sm BP (fun _ => Subtype.val) J ell cap
local notation "family" => sourceOriginalTwoBlockProbePatterns434 blockA blockB m
local notation "pats" => sourceOriginalMemoryRawComparisonPattern434 blockA blockB J m hmJ
local notation "patsC" => (fun v : family => sourceOriginalProbeMemoryPattern434 J m hmJ (Subtype.val v))
local notation "pats0" => (sourceOriginalB26RawNonePattern434 (G := G) J m)
local notation "K" => sourceOriginalMemoryRawComparisonK434 P V blockA blockB J ell m hmJ Q
  (fun _ => h) (fun _ => h) xi
local notation "KC" => (fun v : family => sourceOriginalProbeMemoryCanonicalK434
  P V J ell m hmJ (Subtype.val v) Q h h xi)

/-- Exact signed RAW-none plus comparison decomposition of the
original physical CLEAN row in every real OLD sector. -/
theorem source_original_B26_original_CLEAN_raw_none_split434
    (sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → BP g)
    (mu : (g : G) → BP g → ℝ) (q : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (F : Out → Finset ℕ → ℂ)
    (xs : GroupState SP sm (J+ell)) (a : SourceOriginalB26Active434 BP J ell)
    (t : SourceOriginalB26OldResidues434 BP (fun _ => Subtype.val) sizes prime)
    (S : Finset ℕ) :
    let st := (xs,sourceOriginalB26FrozenBigState434 BP (fun _ => Subtype.val)
      J ell cap sizes hsizes prime a t)
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap pats
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats)
      q 1 Vs V mu K zeta theta o k st S F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap pats0
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0)
      q 1 Vs V mu (fun _ _ _ _ => 1) zeta theta o k st S F +
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patsC
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsC)
      q 1 Vs V mu KC zeta theta o k st S F := by
  dsimp only
  simp_rw [source_original_MARKED_CLEAN_full_literal_row434]
  simp only [SourceOriginalB26FrozenFrame434, Fintype.sum_sigma,
    Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_unique]
  rfl

private theorem original_split_any_state
    (mu : (g : G) → BP g → ℝ) (q : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (F : Out → Finset ℕ → ℂ)
    (st : State) (S : Finset ℕ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap pats
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats)
      q 1 Vs V mu K zeta theta o k st S F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap pats0
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0)
      q 1 Vs V mu (fun _ _ _ _ => 1) zeta theta o k st S F +
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patsC
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsC)
      q 1 Vs V mu KC zeta theta o k st S F := by
  rcases (sourceOriginalMarkedSectorEquiv434 SP sm BP (fun _ => Subtype.val) J ell cap).symm.surjective st
    with ⟨⟨d,⟨xs,t⟩,a⟩,rfl⟩
  exact source_original_B26_original_CLEAN_raw_none_split434 SP sm P J ell m hmJ cap
    blockA blockB V Q h xi (fun g => (d.1 g).val)
    (fun g => Nat.le_of_lt_succ (d.1 g).isLt) d.2 mu q Vs zeta theta o k F xs a t S

/-- The decomposition remains exact with both OLD endpoint multipliers,
for every rho. No assertion about the following ghost G is used. -/
theorem source_original_B26_original_CLEAN_raw_none_split_rho434
    (mu : (g : G) → BP g → ℝ) (q rho : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (F : Out → Finset ℕ → ℂ)
    (st : State) (S : Finset ℕ) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap pats
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats)
      q rho Vs V mu K zeta theta o k st S F =
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap pats0
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0)
      q rho Vs V mu (fun _ _ _ _ => 1) zeta theta o k st S F +
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val)
      J ell m cap patsC
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsC)
      q rho Vs V mu KC zeta theta o k st S F := by
  conv_lhs =>
    rw [source_original_MARKED_FILTERED_E_OLD_sandwich434, original_split_any_state, mul_add]
  congr 1 <;> symm <;> apply source_original_MARKED_FILTERED_E_OLD_sandwich434

end Green64Analytic.CorrelationSquare

end

end

