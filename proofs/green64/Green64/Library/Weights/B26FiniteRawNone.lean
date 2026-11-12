module

public import Green64.Library.Weights.B26OriginalRawNoneSplit

@[expose] public section

/-!
# Weights / B26FiniteRawNone

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26FiniteRawNone -/

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

/-- Exact RAW-none split on the actual finite reachable Fock×seen space.
Canonical representatives and the zero extension of the same future
are derived from their original definitions. -/
theorem source_original_B26_finite_CLEAN_raw_none_split434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (mu : (g : G) → BP g → ℝ) (q rho : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (f : Hist → ℂ) (a : Hist) :
    sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val) J ell m cap pats
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats)
      q rho Vs V mu K zeta theta o k f a =
    sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0)
      q rho Vs V mu (fun _ _ _ _ => 1) zeta theta o k f a +
    sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val) J ell m cap patsC
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsC)
      q rho Vs V mu KC zeta theta o k f a := by
  let st := sourceOriginalCanonicalPhysical434 SP sm BP (fun _ => Subtype.val) (J+ell) cap a.val.1
  let F := sourceOriginalActualSignedHistoryLift434 SP sm BP (fun _ => Subtype.val) J ell cap f
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP (fun _ => Subtype.val) J ell cap a.val.1 a.val.2).mp a.property
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP (fun _ => Subtype.val) (J+ell) cap hcap a.val.1 a.val.2 ha.2.2
  have hs : sourceOriginalPhysicalReachable434 SP sm BP (fun _ => Subtype.val) (J+ell)
      (physicalFockProjection SP sm BP (fun _ => Subtype.val) (J+ell) cap st) a.val.2 := by
    simpa only [st,hp] using ha.2.2
  have lit {I : Type} [Fintype I] (pp : I → SourcePattern G J m)
      (KK : SourcePatternK BP J ell m pp) :
      sourceOriginalActualSignedFiniteE434 SP sm BP (fun _ => Subtype.val) J ell m cap pp
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pp)
        q rho Vs V mu KK zeta theta o k f a =
      sourceOriginalMemoryMarkedFilteredE434 SP sm BP (fun _ => Subtype.val) J ell m cap pp
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pp)
        q rho Vs V mu KK zeta theta o k st a.val.2 F := by
    exact (source_original_SOURCE_MARKED_FILTERED_E_frame_row434
      SP sm BP (fun _ => Subtype.val) J ell m cap pp
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pp)
      q rho Vs V mu KK zeta theta o k st a.val.2 hs F).symm
  rw [lit pats K,lit pats0 (fun _ _ _ _ => 1),lit patsC KC]
  exact source_original_B26_original_CLEAN_raw_none_split_rho434 SP sm P J ell m hmJ cap
    blockA blockB V Q h xi mu q rho Vs zeta theta o k F st a.val.2

/-- Both original total-OLD projectors preserve the same signed split. -/
theorem source_original_B26_MASKED_CLEAN_raw_none_split434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (mu : (g : G) → BP g → ℝ) (q rho : ℝ) (Vs : SG → ℝ)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ) (f : Hist → ℂ) (a : Hist) :
    (∑ b : Hist, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP (fun _ => Subtype.val) J ell m cap pats
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats)
      q rho Vs V mu K zeta theta o k T a b * f b) =
    (∑ b : Hist, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP (fun _ => Subtype.val) J ell m cap pats0
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0)
      q rho Vs V mu (fun _ _ _ _ => 1) zeta theta o k T a b * f b) +
    (∑ b : Hist, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP (fun _ => Subtype.val) J ell m cap patsC
      (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap patsC)
      q rho Vs V mu KC zeta theta o k T a b * f b) := by
  rw [←source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434,
    ←source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434,
    ←source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434]
  unfold sourceOriginalActualSignedOLDMaskedFiniteE434
  split_ifs with ha
  · exact source_original_B26_finite_CLEAN_raw_none_split434 SP sm P J ell m hmJ cap
      blockA blockB V Q h xi hcap mu q rho Vs zeta theta o k _ a
  · simp

include hmJ in
/-- The separate original RAW-none matrix has no conductor price.
This includes its real OLD multipliers and both total-OLD projectors. -/
theorem source_original_B26_RAW_NONE_MASKED_Hilbert434
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (hi : Function.Injective (fun p : Sigma BP => p.2.val))
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hHarmonic : ∀ g,(∑ p : BP g,1/(p.val:ℝ))=V g)
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (zeta theta : ℝ) (o k : ℤ) (T : ℕ) (f : Hist → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ => Subtype.val)
        J ell cap Vs V mu)
      (fun a : Hist => ∑ b : Hist, sourceOriginalActualSignedOLDMaskedEMatrix434
        SP sm BP (fun _ => Subtype.val) J ell m cap pats0
        (sourceOriginalCleanChoice434 SP sm BP (fun _ => Subtype.val) J ell m cap pats0)
        q rho Vs V mu (fun _ _ _ _ => 1) zeta theta o k T a b * f b) ≤
    ((memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      ∏ g : G,((∑ p : BP g,mu g p)^2/4)^ell) *
      sourceOriginalSignedJointForwardEnergy434
        (sourceOriginalActualSignedTrueFockDensity434 SP sm BP (fun _ => Subtype.val)
          J ell cap Vs V mu) f := by
  have ht := source_original_ACTUAL_CLEAN_OLD_MASKED_finite_H_Hilbert434 SP sm BP
    (fun _ => Subtype.val) J ell m hmJ cap
    (fun _ : PUnit => ((∅,∅) : SourceOriginalProbePattern434 G m))
    hcap hi mu hmu V hV hHarmonic (fun _ _ _ _ => 1)
    q hq hq1 rho hrho hrho1 Vs hVs zeta theta o k T
    (fun _ => 1) (by intro i; norm_num) (by intro i aux a b; simp) f
  have hp0 : (fun _ : PUnit => sourceOriginalProbeMemoryPattern434 J m hmJ
      ((∅,∅) : SourceOriginalProbePattern434 G m)) = pats0 := by
    funext i
    unfold sourceOriginalProbeMemoryPattern434 sourceOriginalB26RawNonePattern434
    congr 1
    funext g
    simp [sourceOriginalProbeFreedSlots434]
  rw [hp0] at ht
  simpa [sourceOriginalProbeFreedSlots434, sourceOriginalProbeFreeMarkCount434,
    sourceOriginalMarkedCleanFamilyHilbertBudget434] using ht

end Green64Analytic.CorrelationSquare

end

end

