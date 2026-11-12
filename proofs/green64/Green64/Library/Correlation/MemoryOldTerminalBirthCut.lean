module

public import Green64.Library.Weights.Part063
public import Green64.Library.Correlation.Part030

@[expose] public section

/-!
# Correlation / MemoryOldTerminalBirthCut

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryOldTerminalBirthCut -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)

/-- Actual reachable pending background atoms are distinct numerical
values already present in the true background seen set. -/
theorem source_original_REACHABLE_background_pending_le_seen434
    (background : (g : BG) → Finset (BP g))
    (y : FullPhysicalOutput SP sm BP bm M) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm M y seen) :
    (∑ g,((y.2 g).2.filter (fun z => z.1 ∈ background g)).card) ≤
      (seen ∩ sourceOriginalNumericBackground434 BP bm background).card := by
  let inv : Multiset ℕ := ∑ g,
    ((y.2 g).2.filter (fun z => z.1 ∈ background g)).map (fun z => bm g z.1)
  have hle : inv ≤ sourceOriginalPhysicalInventory434 SP sm BP bm M y := by
    apply Finset.sum_le_sum
    intro g hg
    apply le_trans (Multiset.map_le_map (Multiset.filter_le _ _))
    exact le_add_of_nonneg_left (zero_le)
  have hn : inv.Nodup := Multiset.nodup_of_le hle hy.1
  have hs : inv.toFinset ⊆ seen ∩ sourceOriginalNumericBackground434 BP bm background := by
    intro n h
    have hmem : n ∈ inv := Multiset.mem_toFinset.mp h
    refine Finset.mem_inter.mpr ⟨hy.2 n (Multiset.mem_of_le hle hmem),?_⟩
    obtain ⟨g,hg,hp⟩ := Multiset.mem_sum.mp hmem
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hp
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ g,
      Finset.mem_image_of_mem (bm g) (Multiset.mem_filter.mp hz).2⟩
  have hh := Finset.card_le_card hs
  rw [Multiset.toFinset_card_of_nodup hn] at hh
  simpa only [inv,Multiset.card_sum,Multiset.card_map] using hh

variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The existing OLD event inclusion now reaches the actual numerical
birth counter used by the proved full-chain generating identity. -/
theorem source_original_MEMORY_history_OLD_tail_implies_seen434
    (initial y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (hy : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell) y seen)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (H : ℕ)
    (ht : H + Fintype.card BG * ((n+1)*(J+ell)) < ∑ g,(y.2 g).2.card) :
    H < (seen ∩ sourceOriginalNumericBackground434 BP bm
      (fun g => Finset.univ \
        sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns initial n h g)).card := by
  have htail := source_original_MEMORY_history_OLD_tail_implies_background434
    SP sm BP bm J ell m patterns initial y seen hy n h H ht
  have hseen := source_original_REACHABLE_background_pending_le_seen434 SP sm BP bm (J+ell)
    (fun g => Finset.univ \
      sourceOriginalFullActiveHistoryPool434 SP sm BP bm J ell m patterns initial n h g) y seen hy
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hseen
  exact htail.trans_le hseen

private theorem split_seen_extends (seen B a b : Finset ℕ) :
    seen ⊆ ((seen ∩ B) ∪ a) ∪ ((seen \ B) ∪ b) := by
  intro n hn
  by_cases hb : n ∈ B
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hn,hb⟩))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hn,hb⟩))

variable (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background

/-- Exact locality of the original branching mixed chain on extensions
of its input numerical seen. This includes both actual G gates and E
birth updates and does not impose a bound or product form on the test. -/
theorem source_original_MEMORY_seen_extension_congr434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F G : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (hFG : ∀ out st,seen ⊆ st → F out st=G out st) :
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk F y seen =
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk G y seen := by
  induction n generalizing start sk y seen with
  | zero =>
      unfold sourceOriginalSeenSeparatedBackgroundChain434 sourceOriginalGhostBackgroundSeenRow434
      apply Finset.sum_congr rfl
      intro ab hab
      split_ifs
      · congr 1
        exact hFG _ _ (split_seen_extends seen B _ _)
      · rfl
  | succ n ih =>
      rcases h with ⟨r,h⟩
      rw [sourceOriginalSeenSeparatedBackgroundChain434,sourceOriginalSeenSeparatedBackgroundChain434]
      unfold sourceOriginalGhostBackgroundSeenRow434
      apply Finset.sum_congr rfl
      intro ab hab
      split_ifs
      · congr 1
        dsimp only
        unfold sourceOriginalSourceEFrameFibreRow434
        apply Finset.sum_congr rfl
        intro f hf
        dsimp only
        congr 1
        apply ih h (start+1) _ _ _
        intro out st hst
        apply hFG out st
        apply Finset.Subset.trans (split_seen_extends seen B
          (sourceOriginalNumericBackground434 BP bm (fun g => (ab.1 g).2.1))
          (sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)))
        apply Finset.Subset.trans ?_ hst
        intro v hv
        by_cases hb : v ∈ B
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv,hb⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨hv,hb⟩))
      · rfl

/-- A true numerical background tail at the input persists to the
terminal observation of the complete original branching chain. -/
theorem source_original_MEMORY_background_terminal_cut434
    (q : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ) (k : ℤ) (N : ℕ)
    (n : ℕ) (h : SourceOriginalSourceFrameHistory434 SP sm BP J ell m patterns n)
    (start : ℕ) (sk y : FullPhysicalOutput SP sm BP bm (J+ell)) (seen : Finset ℕ)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ)
    (H : ℕ) (ht : H < (seen ∩ B).card) :
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk F y seen =
    sourceOriginalSeenSeparatedBackgroundChain434 SP sm BP bm J ell m cap patterns background
      q Vs V mu K zeta theta k N n h start sk
      (fun out st => if H < (st ∩ B).card then F out st else 0) y seen := by
  apply source_original_MEMORY_seen_extension_congr434
  intro out st hs
  have hc : (seen ∩ B).card ≤ (st ∩ B).card :=
    Finset.card_le_card (fun p hp => Finset.mem_inter.mpr
      ⟨hs (Finset.mem_inter.mp hp).1,(Finset.mem_inter.mp hp).2⟩)
  exact (if_pos (ht.trans_le hc)).symm
end Green64Analytic.CorrelationSquare

end

end

