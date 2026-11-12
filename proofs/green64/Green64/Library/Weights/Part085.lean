module

public import Green64.Library.Weights.B26FiniteRawNone
public import Green64.Library.Weights.Part076
public import Green64.Library.Correlation.MemoryBirthParityGauge
public import Green64.Library.Correlation.B26FrozenCleanPhysicalFourier
public import Green64.Library.Weights.Part075
public import Green64.Library.Correlation.Part036
public import Green64.Library.Correlation.MemoryActualDomain
public import Green64.Library.Weights.OriginalGroupMasses
public import Green64.Library.Weights.Part073
public import Green64.Library.Correlation.Part032
public import Green64.Library.Weights.CleanCofactorGrowth
public import Mathlib
public import Green64.Library.Correlation.Part001
public import Green64.Library.Correlation.Part027
public import Green64.Library.Weights.Part024

@[expose] public section

/-!
# Weights / Part085

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredCleanObstructionSupport -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- The original shared slots and original first-J freed slots partition J. -/
theorem sourceOriginalRetiredCleanObstruction_shared_card434
    {G : Type} [DecidableEq G] (J ell m : ℕ)
    (pat : SourcePattern G J m) (g : G) :
    (sourceBigShared J ell m pat g).card + (pat.free g).card = J := by
  classical
  have he : sourceBigShared J ell m pat g =
      sourceOriginalSharedSlots434 J ell (pat.free g) := by
    ext i
    simp only [sourceBigShared, sourceOriginalSharedSlots434,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨hi, hn⟩
      let j : Fin J := ⟨i.val, hi⟩
      refine ⟨j, ?_, Fin.ext rfl⟩
      intro hj
      exact hn ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, he⟩
      have hv : j.val = i.val := congrArg Fin.val he
      refine ⟨by omega, ?_⟩
      rintro ⟨z, hz, hzi⟩
      exact hj ((Fin.ext (hzi.trans hv.symm) : z = j) ▸ hz)
  rw [he, source_original_shared_slot_card434]
  have hc : (pat.free g).card ≤ J := by
    simpa using (pat.free g).card_le_univ
  omega

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p, NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap

/-- Exact count of the real numerical birth LIST on a CLEAN branch.
No injectivity of labels is assumed at this stage. -/
theorem sourceOriginalRetiredCleanObstruction_birth_length434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (hc : sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z) :
    (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).length =
      ell * Fintype.card BG + ∑ g : BG, ((patterns z.1).free g).card := by
  have hc' := (source_original_MARKED_CLEAN_predicate434
    SP sm BP bm J ell m cap patterns x z).mp hc
  have hb := source_original_memory_CLEAN_birth_shared_complement434
    SP sm BP bm J ell m cap patterns x z hc'
  have hs :
      (∑ g : BG, (sourceBigShared J ell m (patterns z.1) g).card) +
      (∑ g : BG, ((patterns z.1).free g).card) = J * Fintype.card BG := by
    rw [← Finset.sum_add_distrib]
    simp_rw [sourceOriginalRetiredCleanObstruction_shared_card434]
    simp [Nat.mul_comm]
  rw [Nat.add_mul] at hb
  omega

/-- Exact count on the ORIGINAL numerical-seen carrier. Both birth-list
Nodup and no-rebirth are taken from the original eligibility predicate. -/
theorem sourceOriginalRetiredCleanObstruction_seen_increment434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap)
    (z : FullOrientedSourceChoice SP sm BP bm J ell m cap patterns x)
    (S : Finset ℕ)
    (hc : sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns x z)
    (hb : orientedEFreshBatchEligible SP sm BP bm J ell m cap patterns S z) :
    (S ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset).card =
      S.card + ell * Fintype.card BG + ∑ g : BG, ((patterns z.1).free g).card := by
  rw [Finset.card_union_of_disjoint hb.2, List.toFinset_card_of_nodup hb.1,
    sourceOriginalRetiredCleanObstruction_birth_length434 SP sm BP bm J ell m cap patterns x z hc]
  omega

/-- Every genuine comparison row is zero on a future below the RAW-none
seen layer. This is the original physical witness sum with arbitrary K,
all permutations, both orientations, full D, and arbitrary phases. -/
theorem sourceOriginalRetiredCleanObstruction_marked_zero434
    (hfree : ∀ nu, ∃ g : BG, 0 < ((patterns nu).free g).card)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (S : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (hF : ∀ y S', S.card + ell * Fintype.card BG < S'.card → F y S' = 0) :
    sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k x S F = 0 := by
  unfold sourceOriginalMemoryMarkedFilteredE434
  apply Finset.sum_eq_zero
  intro z hz
  split_ifs with h
  · have hi := sourceOriginalRetiredCleanObstruction_seen_increment434
      SP sm BP bm J ell m cap patterns x z S h.2.1 h.2.2
    obtain ⟨g, hg⟩ := hfree z.1
    have hp : 0 < ∑ g : BG, ((patterns z.1).free g).card :=
      hg.trans_le (Finset.single_le_sum (f := fun j : BG => ((patterns z.1).free j).card) (fun j _ => Nat.zero_le _) (Finset.mem_univ g))
    rw [hF _ _ (by omega), mul_zero]
  · rfl

/-- The support separation is transported to the actual reachable finite
Fock-times-seen action, without an enlarged history state. -/
theorem sourceOriginalRetiredCleanObstruction_finite_zero434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (hfree : ∀ nu, ∃ g : BG, 0 < ((patterns nu).free g).card)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (a : H) (f : H → ℂ)
    (hf : ∀ b : H, a.val.2.card + ell * Fintype.card BG < b.val.2.card → f b = 0) :
    sourceOriginalActualSignedFiniteE434 SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k f a = 0 := by
  let x := sourceOriginalCanonicalPhysical434 SP sm BP bm (J+ell) cap a.val.1
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  have hp := source_original_REACHABLE_canonical_projection434
    SP sm BP bm (J+ell) cap hcap a.val.1 a.val.2 ha.2.2
  have hx : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (physicalFockProjection SP sm BP bm (J+ell) cap x) a.val.2 := by
    simpa only [x, hp] using ha.2.2
  unfold sourceOriginalActualSignedFiniteE434
  rw [← source_original_SOURCE_MARKED_FILTERED_E_frame_row434
    SP sm BP bm J ell m cap patterns _ q rho Vs V mu K zeta theta o k x a.val.2 hx]
  apply sourceOriginalRetiredCleanObstruction_marked_zero434
    SP sm BP bm J ell m cap patterns hfree q rho Vs V mu K zeta theta o k x a.val.2
  intro y S hS
  unfold sourceOriginalActualSignedHistoryLift434
  split_ifs with h
  · exact hf ⟨(y,S),h⟩ hS
  · rfl

/-- Both actual OLD projectors preserve the exact zero comparison block. -/
theorem sourceOriginalRetiredCleanObstruction_masked_zero434
    (hcap : ∀ g, Fintype.card (BP g) ≤ cap g)
    (hfree : ∀ nu, ∃ g : BG, 0 < ((patterns nu).free g).card)
    (q rho : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (o k : ℤ)
    (T : ℕ) (a : H) (f : H → ℂ)
    (hf : ∀ b : H, a.val.2.card + ell * Fintype.card BG < b.val.2.card → f b = 0) :
    (∑ b : H, sourceOriginalActualSignedOLDMaskedEMatrix434
      SP sm BP bm J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q rho Vs V mu K zeta theta o k T a b * f b) = 0 := by
  rw [← source_original_ACTUAL_signed_OLD_masked_E_matrix_exact434]
  unfold sourceOriginalActualSignedOLDMaskedFiniteE434
  split_ifs with ha
  · apply sourceOriginalRetiredCleanObstruction_finite_zero434
      SP sm BP bm J ell m cap patterns hcap hfree q rho Vs V mu K zeta theta o k a
    intro b hb
    rw [hf b hb]
    split_ifs <;> rfl
  · rfl

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceNativeB26FrozenDivisorCap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- ORIGINAL physical B26 BIG frozen divisor under the source
sourceOriginalB26FrozenD434, with untouched dependent active marks,
signed endpoint permutation and independent auxiliary free draws:
the total shared BIG plus auxiliary prime product has exactly J
prime factors per BIG group, because sourceBigShared and pat.free
PARTITION the first J slots, with no deduplication of prime values.
This is stronger than the generic 2J+ell count and works for any
nonempty true original group.

The source SMALL shared divisor dsmall remains an external factor
here; its true SMALL P source window is handled separately. -/
theorem source_native_original_B26_frozen_BIG_divisor_bound434
    (r : ℕ) (L : ℝ) (hL : Real.exp 1 ≤ L)
    (J ell m dsmall : ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
    (a : SourceOriginalB26Active434 (SourceNativeMemoryBP434 r L) J ell)
    (sigma : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L)
      (J+ell)) :
    let U : ℝ := Real.exp (L^(2/5:ℝ))
    ((sourceOriginalB26FrozenD434
      (SourceNativeMemoryBP434 r L)
      (fun _ p => p.val) J ell m dsmall pat aux a sigma:ℕ):ℝ) ≤
      (dsmall:ℝ) * U^(J*Fintype.card
        (sourceNativeOriginalBigType434 r L)) := by
  classical
  let BG := sourceNativeOriginalBigType434 r L
  let BP := SourceNativeMemoryBP434 r L
  let U : ℝ := Real.exp (L^(2/5:ℝ))
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hU : 1 ≤ U := Real.one_le_exp
    (Real.rpow_nonneg hLp.le _)
  have hGroup : ∀ g : BG,
      (((∏ i ∈ sourceBigShared J ell m pat g,
         ((a g (sigma g i)).val:ℕ)) *
         (∏ j : ↥(pat.free g), ((aux g j).val:ℕ)):ℕ):ℝ) ≤
      U^J := by
    intro g
    have hShare := source_original_ACTUAL_finite_nat_product_uniform_upper434
      (sourceBigShared J ell m pat g)
      (fun i => (a g (sigma g i)).val) U
      (le_trans (by norm_num) hU)
      (by intro i hi
          exact (source_native_original_Tb_prime_range434 r L g
            (a g (sigma g i)).val (a g (sigma g i)).property).2.2)
    have hAux := source_original_ACTUAL_finite_nat_product_uniform_upper434
      (Finset.univ : Finset ↥(pat.free g))
      (fun j => (aux g j).val) U
      (le_trans (by norm_num) hU)
      (by intro j hj
          exact (source_native_original_Tb_prime_range434 r L g
            (aux g j).val (aux g j).property).2.2)
    have hAux' : (((∏ j : ↥(pat.free g), ((aux g j).val:ℕ)):ℕ):ℝ) ≤
        U^(pat.free g).card := by
      simpa only [Finset.card_univ,Fintype.card_coe] using hAux
    have hCard := sourceOriginalRetiredCleanObstruction_shared_card434
      J ell m pat g
    calc
      _ = (((∏ i ∈ sourceBigShared J ell m pat g,
        ((a g (sigma g i)).val:ℕ)):ℕ):ℝ) *
        (((∏ j : ↥(pat.free g), ((aux g j).val:ℕ)):ℕ):ℝ) := by
          push_cast
          rfl
      _ ≤ U^(sourceBigShared J ell m pat g).card *
        U^(pat.free g).card := by
          apply mul_le_mul hShare hAux' 
          · exact Nat.cast_nonneg _
          · exact pow_nonneg (by linarith : 0 ≤ U) _
      _ = U^J := by
          rw [←pow_add]
          congr 1
  unfold sourceOriginalB26FrozenD434
  rw [Nat.cast_mul, Nat.cast_prod]
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc
    _ ≤ ∏ _g : BG, U^J := by
      apply Finset.prod_le_prod₀
      · intro g hg; exact Nat.cast_nonneg _
      · intro g hg; exact hGroup g
    _ = U^(J*Fintype.card BG) := by
      simp [Finset.prod_const, pow_mul, mul_comm]

/-- The genuine original physical frozen BIG piece is bounded
UNIFORMLY by exp(J * C_group * L^.4 log L), while dsmall stays
external and unmodified. -/
theorem eventually_native_original_B26_frozen_BIG_divisor_cap434
    (r : ℕ) (hr : 1 ≤ r) (J ell m : ℕ) :
    let Cg : ℝ := 3+(Real.log 2)⁻¹
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (dsmall : ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
        (a : SourceOriginalB26Active434 (SourceNativeMemoryBP434 r L) J ell)
        (sigma : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L)
          (J+ell)),
        ((sourceOriginalB26FrozenD434
          (SourceNativeMemoryBP434 r L)
          (fun _ p => p.val) J ell m dsmall pat aux a sigma:ℕ):ℝ) ≤
          (dsmall:ℝ) *
            Real.exp (((J:ℝ)*Cg)*L^(2/5:ℝ)*Real.log L) := by
  classical
  let Cg : ℝ := 3+(Real.log 2)⁻¹
  filter_upwards [
    eventually_source_native_original_group_masses434 r hr,
    eventually_ge_atTop (Real.exp 1)]
    with L hMass hL
  refine ⟨hL, ?_⟩
  intro dsmall pat aux a sigma
  obtain ⟨_,hS,_⟩ := hMass
  have hCount : (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      Cg*Real.log L :=
    (source_native_original_group_upper_counts434 r L hS hr hL).2
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hPow : 0 ≤ L^(2/5:ℝ) :=
    Real.rpow_nonneg hLp.le _
  have hProduct := source_native_original_B26_frozen_BIG_divisor_bound434
    r L hL J ell m dsmall pat aux a sigma
  have hExp :
      (Real.exp (L^(2/5:ℝ)))^(J*Fintype.card
          (sourceNativeOriginalBigType434 r L)) ≤
      Real.exp (((J:ℝ)*Cg)*L^(2/5:ℝ)*Real.log L) := by
    have hCount' : ((J*Fintype.card
        (sourceNativeOriginalBigType434 r L):ℕ):ℝ) ≤
        (J:ℝ)*Cg*Real.log L := by
      have hh := mul_le_mul_of_nonneg_left hCount
        (Nat.cast_nonneg J)
      push_cast
      nlinarith [hh]
    calc
      _ = Real.exp (((J*Fintype.card
           (sourceNativeOriginalBigType434 r L):ℕ):ℝ) *
             L^(2/5:ℝ)) := by rw [Real.exp_nat_mul]
      _ ≤ Real.exp (((J:ℝ)*Cg*Real.log L)*L^(2/5:ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCount' hPow)
      _ = Real.exp (((J:ℝ)*Cg)*L^(2/5:ℝ)*Real.log L) := by
        congr 1
        ring
  exact hProduct.trans
    (mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg _))
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalFullPhysicalDIdentity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ACTUAL original oriented source physical D on the genuine
SMALL Option(S,Ts) + BIG Tb Fock state, including all marked copies
and independent BIG auxiliary slots, is LITERALLY the original B26
frozen SMALL×BIG divisor. No new sample space or label copy is used.
Both orientation/future flags are outside D as in SOURCE03. -/
theorem source_native_original_FROZEN_D_eq_PHYSICAL_D434
    (r : ℕ) (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell m : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell)) :
    sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m cap pat aux x bs ss =
    sourceOriginalB26FrozenD434
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m
      (sourceOriginalPhysicalSourceSMALLFactor434
        (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
        J ell cap x ss)
      pat aux (fun g i => (x.2 g).1 i) bs := by
  rfl

/-- At ANY original physical state and source phase, the TRUE full
SMALL/SHARED + BIG/FREE source divisor has a pointwise REAL bound
using exactly original source group prime intervals. The SMALL
group bound still uses J+ell (a safe loss), whereas the BIG
shared/free partition proves exactly J slots per group.
This is stronger than the former bare BIG-only divisor cap. -/
theorem source_native_original_FULL_PHYSICAL_D_pointwise_upper434
    (r : ℕ) (L : ℝ) (hL : Real.exp 1 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
    (J ell m : ℕ)
    (cap : sourceNativeOriginalBigType434 r L → ℕ)
    (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
    (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
    (x : FullPhysicalState
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      (J+ell) cap)
    (bs : BigGroupPerm (BG := sourceNativeOriginalBigType434 r L) (J+ell))
    (ss : GroupPermFamily
      (G := SourceNativeMemorySG434 r L hS) (J+ell)) :
    ((sourceOrientedPhysicalD
      (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
      J ell m cap pat aux x bs ss:ℕ):ℝ) ≤
      (Real.exp (L^(1/5:ℝ)))^((J+ell) *
        Fintype.card (SourceNativeMemorySG434 r L hS)) *
      (Real.exp (L^(2/5:ℝ)))^(J*
        Fintype.card (sourceNativeOriginalBigType434 r L)) := by
  classical
  let SG := SourceNativeMemorySG434 r L hS
  let SP := SourceNativeMemorySP434 r L hS
  let BG := sourceNativeOriginalBigType434 r L
  let BP := SourceNativeMemoryBP434 r L
  let U : ℝ := Real.exp (L^(1/5:ℝ))
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hU : 1 ≤ U := Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hsPrime : ∀ g : SG, ∀ p : SP g, (p.val:ℝ) ≤ U := by
    intro g p
    cases g with
    | none =>
      exact (source_native_original_S_prime_range434 r L hS
        p.val p.property).2.2
    | some g =>
      exact (source_native_original_Ts_prime_range434 r L hS
        g p.val p.property).2.2
  have hs := source_original_ACTUAL_PHYSICAL_SMALL_finite_upper434
    SP (fun _ p => p.val) BP (fun _ p => p.val)
    J ell cap x ss U hU hsPrime
  have hb := source_native_original_B26_frozen_BIG_divisor_bound434
    r L hL J ell m
    (sourceOriginalPhysicalSourceSMALLFactor434
      SP (fun _ p => p.val) BP (fun _ p => p.val)
      J ell cap x ss)
    pat aux (fun g i => (x.2 g).1 i) bs
  rw [source_native_original_FROZEN_D_eq_PHYSICAL_D434]
  exact (hb.trans (mul_le_mul_of_nonneg_right hs
    (pow_nonneg (Real.exp_pos _).le _))) 
    -- Product order is actual dsmall * BIG upper; the last inequality
    -- must multiply the SMALL bound by the BIG cap.
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalFullPhysicalDCap -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The TRUE physical full S/Ts/Tb source D, including all independent
BIG auxiliary draws, is SUBEXPONENTIAL under the unchanged original
P-band geometry. No relabeling into a surrogate BIG-only divisor.

Explicit source exponent:
  Ctotal=(J+ell)*(1+Cg)+J*Cg, Cg=3+(log 2)^-1.
All J,ell,m and r are fixed BEFORE L.
The actual physical state, both source permutations, all marks,
and all aux tuples are universally quantified AFTER L. -/
theorem eventually_native_original_FULL_PHYSICAL_D_cap434
    (r : ℕ) (hr : 1 ≤ r) (J ell m : ℕ) :
    let Cg : ℝ := 3+(Real.log 2)⁻¹
    let Ctotal : ℝ :=
      ((J+ell:ℕ):ℝ)*(Cg+1)+(J:ℝ)*Cg
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 r L).Nonempty)
        (cap : sourceNativeOriginalBigType434 r L → ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) J m)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) J m pat)
        (x : FullPhysicalState
          (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
          (J+ell) cap)
        (bs : BigGroupPerm (BG:=sourceNativeOriginalBigType434 r L)
          (J+ell))
        (ss : GroupPermFamily (G:=SourceNativeMemorySG434 r L hS)
          (J+ell)),
        ((sourceOrientedPhysicalD
          (SourceNativeMemorySP434 r L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 r L) (fun _ p => p.val)
          J ell m cap pat aux x bs ss:ℕ):ℝ) ≤
          Real.exp (Ctotal*L^(2/5:ℝ)*Real.log L) := by
  classical
  let Cg : ℝ := 3+(Real.log 2)⁻¹
  let Ctotal : ℝ :=
    ((J+ell:ℕ):ℝ)*(Cg+1)+(J:ℝ)*Cg
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    have hh : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  filter_upwards [
      eventually_source_native_original_group_masses434 r hr,
      eventually_ge_atTop (Real.exp 1)]
    with L hMass hL
  refine ⟨hL, ?_⟩
  intro hS cap pat aux x bs ss
  let SG := SourceNativeMemorySG434 r L hS
  let BG := sourceNativeOriginalBigType434 r L
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hL
  have hLog : 1 ≤ Real.log L := by
    apply Real.le_log_iff_exp_le hLp |>.mpr
    exact hL
  have hCount := source_native_original_group_upper_counts434
    r L hS hr hL
  have hSmall : (Fintype.card SG:ℝ) ≤ (Cg+1)*Real.log L := by
    have hOption : Fintype.card SG = 1+
        Fintype.card (sourceNativeOriginalTsType434 r L hS) := by
      simp [SG, Fintype.card_option, add_comm]
    rw [hOption]
    have hTs : ((Fintype.card
      (sourceNativeOriginalTsType434 r L hS)):ℝ) ≤
        Cg*Real.log L := hCount.1
    push_cast
    nlinarith [hTs,hLog]
  have hBig : (Fintype.card BG:ℝ) ≤ Cg*Real.log L := hCount.2
  have hSmCount :
      (((J+ell)*Fintype.card SG:ℕ):ℝ) ≤
        ((J+ell:ℕ):ℝ)*(Cg+1)*Real.log L := by
    have hh := mul_le_mul_of_nonneg_left hSmall
      (Nat.cast_nonneg (J+ell))
    push_cast
    nlinarith [hh]
  have hBgCount :
      ((J*Fintype.card BG:ℕ):ℝ) ≤
        (J:ℝ)*Cg*Real.log L := by
    have hh := mul_le_mul_of_nonneg_left hBig (Nat.cast_nonneg J)
    push_cast
    nlinarith [hh]
  have hPow :
      L^(1/5:ℝ) ≤ L^(2/5:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hP2 : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg hLp.le _
  have hExSm : (((J+ell)*Fintype.card SG:ℕ):ℝ)*L^(1/5:ℝ) ≤
      ((J+ell:ℕ):ℝ)*(Cg+1)*Real.log L*L^(2/5:ℝ) := by
    have hNon : 0 ≤ (((J+ell)*Fintype.card SG:ℕ):ℝ) :=
      Nat.cast_nonneg _
    calc
      _ ≤ (((J+ell)*Fintype.card SG:ℕ):ℝ)*L^(2/5:ℝ) :=
        mul_le_mul_of_nonneg_left hPow hNon
      _ ≤ (((J+ell:ℕ):ℝ)*(Cg+1)*Real.log L)*L^(2/5:ℝ) :=
        mul_le_mul_of_nonneg_right hSmCount hP2
  have hExBg : ((J*Fintype.card BG:ℕ):ℝ)*L^(2/5:ℝ) ≤
      ((J:ℝ)*Cg*Real.log L)*L^(2/5:ℝ) :=
    mul_le_mul_of_nonneg_right hBgCount hP2
  have hFull := source_native_original_FULL_PHYSICAL_D_pointwise_upper434
    r L hL hS J ell m cap pat aux x bs ss
  have hExp :
      (Real.exp (L^(1/5:ℝ)))^((J+ell)*Fintype.card SG) *
      (Real.exp (L^(2/5:ℝ)))^(J*Fintype.card BG) ≤
      Real.exp (Ctotal*L^(2/5:ℝ)*Real.log L) := by
    have hSmExp : (Real.exp (L^(1/5:ℝ)))^((J+ell)*Fintype.card SG) =
        Real.exp ((((J+ell)*Fintype.card SG:ℕ):ℝ)*L^(1/5:ℝ)) := by
      rw [Real.exp_nat_mul]
    have hBgExp : (Real.exp (L^(2/5:ℝ)))^(J*Fintype.card BG) =
        Real.exp (((J*Fintype.card BG:ℕ):ℝ)*L^(2/5:ℝ)) := by
      rw [Real.exp_nat_mul]
    rw [hSmExp,hBgExp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [Ctotal]
    nlinarith [hExSm,hExBg]
  exact hFull.trans hExp
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeActualBIGFreeAux -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64ComparisonPartial Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The ACTUAL ORIGINAL full S/Ts/Tb J=1 selected-prime product
is ≤exp(2L) UNIFORMLY over ALL possible prime assignments
to real source P-bands, not only a specially selected witness.
This uses the checked true original group-cardinal bound and
positive harmonic P band mass, and the physical subexponential
scale hierarchy. -/
theorem eventually_native_original_ALL_P_any_J1_endpoint_cap434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∀ (p : SourceNativeOriginalAllP434 r L → ℕ),
        (∀ g, p g ∈ SourceNativeOriginalAllPBand434 r L g) →
        ((∏ g : SourceNativeOriginalAllP434 r L, p g:ℕ):ℝ) ≤
          Real.exp (2*L) := by
  classical
  let C : ℝ := 3+(Real.log 2)⁻¹
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  filter_upwards [
    eventually_native_original_ALL_P_J_divisor_cap434 r hr 1,
    eventually_clean_cofactor_growth434 C (1/2) hC
      (by norm_num : (0:ℝ)<(1/2:ℝ)),
    eventually_ge_atTop (Real.exp 1)]
    with L hCap hGrow hL
  refine ⟨(Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL, ?_⟩
  intro p hp
  let G := SourceNativeOriginalAllP434 r L
  let s : G × Fin 1 → ℕ := fun gi => p gi.1
  have hs : s ∈ Fintype.piFinset
      (fun i : G × Fin 1 =>
        SourceNativeOriginalAllPBand434 r L i.1) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact hp i.1
  have hprod : sourceNativeOriginalAllPCommonDivisor434 r L 1 s =
      ∏ g : G, p g := by
    unfold sourceNativeOriginalAllPCommonDivisor434
    rw [Fintype.prod_prod_type]
    change (∏ g : G, ∏ k : Fin 1, p g) = ∏ g : G, p g
    simp
  have hRoot : ((∏ g : G, p g:ℕ):ℝ) ≤
      Real.exp (C*L^(2/5:ℝ)*Real.log L) := by
    have hh := hCap.2 s hs
    simpa [hprod,C] using hh
  have hL1 : (1:ℝ) ≤ L :=
    (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hL
  have hP : 0 ≤ L^(2/5:ℝ) :=
    Real.rpow_nonneg (by linarith : (0:ℝ)≤L) _
  have hLog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hE : 0 ≤ C*L^(2/5:ℝ)*Real.log L :=
    mul_nonneg (mul_nonneg hC hP) hLog
  have hGrow1 : Real.exp (C*L^(2/5:ℝ)*Real.log L) ≤
      Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hE]
  have hHuge : Real.exp (2*C*L^(2/5:ℝ)*Real.log L) ≤
      8*Real.exp L*L^(2*C)*
        Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := by
    have he : 1 ≤ Real.exp L := Real.one_le_exp (by linarith)
    have hp : 1 ≤ L^(2*C) := Real.one_le_rpow hL1 (by linarith)
    have hh : 1 ≤ 8*Real.exp L*L^(2*C) := by
      nlinarith [mul_le_mul_of_nonneg_left hp
        (by positivity : 0 ≤ 8*Real.exp L)]
    have hx : 0 ≤ Real.exp (2*C*L^(2/5:ℝ)*Real.log L) :=
      (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_right hh hx]
  calc
    ((∏ g : G, p g:ℕ):ℝ) ≤
      Real.exp (C*L^(2/5:ℝ)*Real.log L) := hRoot
    _ ≤ Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := hGrow1
    _ ≤ 8*Real.exp L*L^(2*C)*
        Real.exp (2*C*L^(2/5:ℝ)*Real.log L) := hHuge
    _ ≤ Real.exp (2*L) := by
      have hh : 8*Real.exp L*L^(2*C)*
        Real.exp (2*C*L^(2/5:ℝ)*Real.log L) <
          Real.exp (2*L) := by
        convert hGrow using 1 <;> ring
      exact hh.le

/-- TRUE original BIG source pattern with exactly ONE free slot
in EVERY independent BIG group, not a zero-free branch and not
an abstract auxiliary list. Source m=1, J=1 exactly. -/
noncomputable def source_native_actual_J1_m1_pattern434
    (r : ℕ) (L : ℝ) :
    SourcePattern (sourceNativeOriginalBigType434 r L) 1 1 where
  free := fun _ => {(0:Fin 1)}
  free_bound := by
    intro g
    simp

/-- Given one genuine auxiliary prime q_g in every BIG group,
construct its EXACT dependent original SourceBigAux value at each
nonempty source free slot. The q_g belongs to the unchanged
sourceNativeOriginalTb P-band by its subtype proof. -/
noncomputable def source_native_actual_J1_m1_aux434
    (r : ℕ) (L : ℝ)
    (q : SourceNativeOriginalAllP434 r L → ℕ)
    (hq : ∀ g : SourceNativeOriginalAllP434 r L,
      q g ∈ SourceNativeOriginalAllPBand434 r L g) :
    SourceBigAux (SourceNativeMemoryBP434 r L) 1 1
      (source_native_actual_J1_m1_pattern434 r L) := by
  intro g j
  exact ⟨q (sourceNativeOriginalBigToAll434 r L g),
    hq (sourceNativeOriginalBigToAll434 r L g)⟩

/-- With all real original P groups possessing TWO distinct prime
choices p_g,q_g, construct an ACTUAL nonempty BIG free source
sector of one independent auxiliary draw in EVERY BIG group,
whose chosen actual prime q_g avoids every ordinary endpoint
P-divisor in the coherent source product w=prod_g p_g.

The source sourceAuxAvoidsEndpoints has additional ACTIVE ordered
source and target Fock slots; no such Fock/OLD legality is claimed.
This theorem closes the literal SIZE and SPARE PRIME arithmetic
obstructions to a nonempty original BIG auxiliary sector, retaining
both true Fock group types. -/
theorem eventually_native_original_ALL_P_TRUE_BIG_FREE_nonvacuous434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧
      ∃ (w : ℕ)
        (A : SourceNativeOriginalAllP434 r L → Finset ℕ)
        (pat : SourcePattern (sourceNativeOriginalBigType434 r L) 1 1)
        (aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1 pat),
        0 < w ∧ (w:ℝ) ≤ Real.exp (2*L) ∧
        (∀ g, 0 < (A g).card) ∧
        (∀ g, A g ⊆ w.primeFactors) ∧
        (∀ g : sourceNativeOriginalBigType434 r L,
           (pat.free g).card = 1) ∧
        (∀ (g : sourceNativeOriginalBigType434 r L)
           (j : ↥(pat.free g)), (aux g j).val ∉ w.primeFactors) := by
  classical
  filter_upwards [
    eventually_native_original_ALL_P_spare_auxiliary434 r hr,
    eventually_native_original_ALL_P_any_J1_endpoint_cap434 r hr]
    with L hSpare hCap
  refine ⟨hSpare.1, ?_⟩
  obtain ⟨p,q,hp,hq,hNe,hAvoid⟩ := hSpare.2
  let G := SourceNativeOriginalAllP434 r L
  let w : ℕ := ∏ g : G, p g
  let A : G → Finset ℕ := fun g => {p g}
  let pat : SourcePattern (sourceNativeOriginalBigType434 r L) 1 1 :=
    source_native_actual_J1_m1_pattern434 r L
  let aux : SourceBigAux (SourceNativeMemoryBP434 r L) 1 1 pat :=
    source_native_actual_J1_m1_aux434 r L q hq
  have hL1 : (1:ℝ) ≤ L := hSpare.1
  have hPrime : ∀ g : G, (p g).Prime := by
    intro g
    exact (source_native_original_ALL_P_prime_range434
      r L hL1 g (p g) (hp g)).1
  have hwpos : 0 < w := by
    dsimp [w]
    apply Finset.prod_pos
    intro g hg
    exact (hPrime g).pos
  have hApos : ∀ g : G, 0 < (A g).card := by
    intro g
    simp [A]
  have hAdiv : ∀ g : G, A g ⊆ w.primeFactors := by
    intro g v hv
    have heq : v=p g := Finset.mem_singleton.mp hv
    subst v
    apply Nat.mem_primeFactors.mpr
    exact ⟨hPrime g, Finset.dvd_prod_of_mem p (Finset.mem_univ g),
      Nat.ne_of_gt hwpos⟩
  have hcap : (w:ℝ) ≤ Real.exp (2*L) := hCap.2 p hp
  have hFree : ∀ g : sourceNativeOriginalBigType434 r L,
      (pat.free g).card=1 := by
    intro g
    simp [pat,source_native_actual_J1_m1_pattern434]
  have hAux : ∀ (g : sourceNativeOriginalBigType434 r L)
      (j : ↥(pat.free g)), (aux g j).val ∉ w.primeFactors := by
    intro g j
    exact hAvoid (sourceNativeOriginalBigToAll434 r L g)
  exact ⟨w,A,pat,aux,hwpos,hcap,hApos,hAdiv,hFree,hAux⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativePhysicalBIGVacuumLegal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- For any REAL labelled BIG source prime p_g in each original
BIG group and ANY physical signed displacement, there exists a
genuine source/target BIG Fock E_i branch with:
M=1, B=0, source and target ACTIVE lists both p_g,
zero OLD atoms, no stores or promotions, and both actual
permutation families identity. When the original J=1,m=1
free pattern removes the single BIG shared slot, the fixed
BIG edge is ACTUALLY PhysicalEdgeLegal.

This is a nontrivial exact support witness in the full
ACTIVE+OLD/Fock finite source state space, not an abstract
external adjacency relation. The target OLD list is the true
Fock vacuum and the source zero-capacity constraint B=0 is
preserved. No nonzero transfer weight is asserted here. -/
theorem source_original_TRUE_BIG_vacuum_unshared_legal434
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (modulus : (g : BG) → BP g → ℕ)
    [∀ g, ∀ p, NeZero (modulus g p)]
    (p : (g : BG) → BP g) (D : ℕ) (step : ℤ) :
    ∃ (x : BigGroupState BP modulus 1 (fun _ => 0))
      (b : BigGroupBranch BP modulus 1 (fun _ => 0) x),
      BigGroupEdgeLegal BP modulus 1 (fun _ => 0)
        x (fun _ => ∅)
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
        D step b := by
  classical
  let x : BigGroupState BP modulus 1 (fun _ => 0) :=
    fun g =>
      ((fun (_ : Fin 1) => p g),
       Green64Fock.vacuumState (Green64Fock.Atom (BP g) (modulus g)) 0)
  let noChoice (g : BG) :
      BigEdgeChoice (modulus g) 1 0 (x g) :=
    (∅, ⟨∅, ⟨
      (fun i => by cases i with | mk val h => simp at h),
      (by intro a b hh
          cases a with | mk val ha => simp at ha)
    ⟩⟩)
  let branch : BigGroupBranch BP modulus 1 (fun _ => 0) x :=
    fun g => ((fun (_ : Fin 1) => p g), noChoice g)
  refine ⟨x,branch,?_⟩
  intro g
  change PhysicalEdgeLegal (modulus g) 1 0 (x g)
    (fun _ : Fin 1 => p g) ∅
    (Equiv.refl _) (Equiv.refl _) D step (noChoice g)
  constructor
  · intro i hi
    simp at hi
  · simp [noChoice]
  · simp [noChoice]
  · intro ⟨i,hi⟩
    change i ∈ (∅ : Finset (Fin 1)) at hi
    simp at hi
  · intro ⟨i,hi⟩
    change i ∈ (∅ : Finset (Fin 1)) at hi
    simp at hi
  · intro ⟨i,hi⟩
    change i ∈ (∅ : Finset (Fin 1)) at hi
    simp at hi
  · intro i hi
    simp [noChoice] at hi
  · simp [pending_output_length,x,noChoice]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeFullPhysicalVacuumLegal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Genuine original SOURCE03 FULL SMALL Haar + BIG ACTIVE/OLD
Fock E_i physical support is NONEMPTY for J=1, ell=0, m=1
when every original SMALL group has a true prime ps_g and every
original BIG group has distinct physical ACTIVE pb_g and
independently sampled FREE auxiliary qb_g.

The source construction uses:
- each SMALL torus y_g=0 and its ACTUAL ordered one-mark state ps_g,
  requiring distinctness only within each group (Fin1);
- each BIG source ACTIVE list pb_g with original Fock j_g=0 vacuum,
  cutoff B_g=0, genuine target ACTIVE pb_g, no OLD stores/promotions,
  and no fabricated Fock atom;
- all ORIGINAL independent endpoint permutations identity;
- ALL BIG shared marks absent, since J=1 and free C_g={0};
- the original source D from SMALL shared ps and BIG FREE qb,
  and the actual signed common step orientation*k*D;
- every BIG free auxiliary qb_g excluded from BOTH ordered
  source and target BIG ACTIVE lists by the genuine qb_g != pb_g;
- orientation=1, k arbitrary nonzero.

This proves a valid entry in the exact finite
SourcePhysicalLegal/FullPhysicalEdgeLegal source operator,
not just an abstract BIG legal branch or harmonic RAW scalar.
It does NOT imply its physical complex coefficient is nonzero,
and does not prove the signed D61 integral. -/
theorem source_original_FULL_PHYSICAL_J1_m1_vacuum_legal434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type)
    [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ)
    [∀ g, ∀ p, NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type)
    [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ)
    [∀ g, ∀ p, NeZero (bigMod g p)]
    (ps : (g : SG) → SP g)
    (pb qb : (g : BG) → BP g)
    (hNe : ∀ g, qb g ≠ pb g)
    (k : ℤ) (hk : k ≠ 0) :
    let pat : SourcePattern BG 1 1 := {
      free := fun _ => {0}
      free_bound := by intro g; simp
    };
    let patterns : Unit → SourcePattern BG 1 1 := fun _ => pat;
    let aux : SourceBigAux BP 1 1 pat := fun g _ => qb g;
    ∃ (x : FullPhysicalState SP smallMod BP bigMod 1 (fun _ => 0))
      (b : FullPhysicalEdgeBranch SP smallMod BP bigMod
        1 (fun _ => 0) x),
      SourcePhysicalLegal SP smallMod BP bigMod 1 0 1
        (fun _ => 0) patterns x 1 k ⟨(),(aux,b)⟩ ∧
      groupEdgeAllowedPerm SP smallMod 1 (sourceSmallShared 1 0)
        (sourcePhysicalStep SP smallMod BP bigMod
          1 0 1 (fun _ => 0) pat aux x 1 k)
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
        x.1 b.smallTarget := by
  classical
  let pat : SourcePattern BG 1 1 := {
    free := fun _ => {0}
    free_bound := by intro g; simp
  }
  let patterns : Unit → SourcePattern BG 1 1 := fun _ => pat
  let aux : SourceBigAux BP 1 1 pat := fun g _ => qb g
  let small : GroupState SP smallMod 1 := fun g =>
    ⟨((fun _ => 0), (fun (_ : Fin 1) => ps g)), by
      constructor
      · intro i j _
        exact Subsingleton.elim i j
      · intro i
        rfl⟩
  let big : BigGroupState BP bigMod 1 (fun _ => 0) := fun g =>
    ((fun (_ : Fin 1) => pb g),
      Green64Fock.vacuumState
        (Green64Fock.Atom (BP g) (bigMod g)) 0)
  let x : FullPhysicalState SP smallMod BP bigMod 1 (fun _ => 0) :=
    (small,big)
  let c (g : BG) : BigEdgeChoice (bigMod g) 1 0 (big g) :=
    (∅, ⟨∅, ⟨
      (fun i => by cases i with | mk val h => simp at h),
      (by intro a b hh; cases a with | mk val ha => simp at ha)
    ⟩⟩)
  obtain ⟨smallTarget,hSmallSupported⟩ :=
    source_original_FULL_PHYSICAL_J1_SMALL_Haar_target434
      SP smallMod BP bigMod 1 (fun _ => 0) pat aux x 1 k
  let b : FullPhysicalEdgeBranch SP smallMod BP bigMod 1
      (fun _ => 0) x := {
    sigmaBig := fun _ => Equiv.refl _
    tauBig := fun _ => Equiv.refl _
    bigChoice := fun g => ((fun (_ : Fin 1) => pb g), c g)
    smallTarget := smallTarget
  }
  refine ⟨x,b,?_,?_⟩
  have hShared : ∀ g : BG,
      sourceBigShared 1 0 1 pat g = ∅ := by
    intro g
    ext i
    fin_cases i
    simp [sourceBigShared,pat]
  have hBig : FullPhysicalEdgeLegal SP smallMod BP bigMod
      1 (fun _ => 0) x (sourceBigShared 1 0 1 pat)
      (sourcePhysicalD SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x)
      (sourcePhysicalStep SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x 1 k) b := by
    change BigGroupEdgeLegal BP bigMod 1 (fun _ => 0)
      big (sourceBigShared 1 0 1 pat)
      b.sigmaBig b.tauBig
      (sourcePhysicalD SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x)
      (sourcePhysicalStep SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x 1 k)
      b.bigChoice
    intro g
    have he := hShared g
    change PhysicalEdgeLegal (bigMod g) 1 0 (big g)
      (fun _ => pb g) (sourceBigShared 1 0 1 pat g)
      (Equiv.refl _) (Equiv.refl _)
      (sourcePhysicalD SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x)
      (sourcePhysicalStep SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x 1 k)
      (c g)
    rw [he]
    constructor
    · intro i hi; simp at hi
    · simp [c]
    · simp [c]
    · intro ⟨i,hi⟩
      change i ∈ (∅ : Finset (Fin 1)) at hi
      simp at hi
    · intro ⟨i,hi⟩
      change i ∈ (∅ : Finset (Fin 1)) at hi
      simp at hi
    · intro ⟨i,hi⟩
      change i ∈ (∅ : Finset (Fin 1)) at hi
      simp at hi
    · intro i hi; simp [c] at hi
    · simp [pending_output_length,big,c]
  have hAvoid : sourceAuxAvoidsEndpoints SP smallMod BP bigMod
      1 0 1 (fun _ => 0) pat aux x b := by
    intro g j i
    change qb g ≠ pb g ∧ qb g ≠ pb g
    exact ⟨hNe g,hNe g⟩
  change FullPhysicalEdgeLegal SP smallMod BP bigMod 1
      (fun _ => 0) x
      (sourceBigShared 1 0 1 pat)
      (sourcePhysicalD SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x)
      (sourcePhysicalStep SP smallMod BP bigMod
        1 0 1 (fun _ => 0) pat aux x 1 k) b
    ∧ sourceAuxAvoidsEndpoints SP smallMod BP bigMod
      1 0 1 (fun _ => 0) pat aux x b
    ∧ (1 = 1 ∨ (1:ℤ) = -1) ∧ k ≠ 0
  exact ⟨hBig,hAvoid,Or.inl rfl,hk⟩
  · exact hSmallSupported
end Green64Analytic.SourceBlockSieve

end

end

