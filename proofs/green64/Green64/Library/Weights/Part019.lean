module

public import Green64.Library.Weights.SourcePOriginalGroupGeometry
public import Mathlib
public import Green64.Library.Weights.Part016

@[expose] public section

/-!
# Weights / Part019

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourcePOriginalAllGroupIndices -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Explicit finite index bound, automatically large enough for ALL source
P bands, without a cutoff j_x assumption. -/
noncomputable def sourceOriginalPAllIndexBound (L : ℝ) : ℕ :=
  ⌈2 + Real.log L / Real.log 2⌉₊

/-- Exactly every j≥0 whose source interval [3s_j/2,9s_j/5]
is contained in one of the two specified logarithmic ranges. -/
noncomputable def sourceOriginalPAllGroupIndices (r₀ : ℕ) (L : ℝ) : Finset ℕ :=
  (Finset.range (sourceOriginalPAllIndexBound L)).filter
    (sourceOriginalPGroupIndex r₀ L)

/-- Completeness: the finite presentation equals the unrestricted
mathematical predicate j∈ℕ selecting the ORIGINAL source P groups. -/
theorem source_original_P_all_groups_mem_iff
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : 1 < L) (j : ℕ) :
    j ∈ sourceOriginalPAllGroupIndices r₀ L ↔
      sourceOriginalPGroupIndex r₀ L j := by
  classical
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hj
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      change j < ⌈2 + Real.log L / Real.log 2⌉₊
      have hjle := source_original_P_group_index_le_log r₀ L hr₀ hL j hj
      exact (Nat.lt_ceil).mpr (by linarith)
    · exact hj

end Green64Analytic.SourceBlockSieve

end

/-! ## SourceNativeOriginalGroupCounts -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Every original SMALL index; no index is discarded or added. -/
def sourceNativeOriginalSmallIndices434 (r : ℕ) (L : ℝ) : Finset ℕ :=
  (sourceOriginalPAllGroupIndices r L).filter (fun j =>
    L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale r L j ∧
    (9/5:ℝ)*sourceOriginalPGroupScale r L j ≤ L^(1/5:ℝ))

/-- Every original BIG index, independently of the SMALL cardinality. -/
def sourceNativeOriginalBigIndices434 (r : ℕ) (L : ℝ) : Finset ℕ :=
  (sourceOriginalPAllGroupIndices r L).filter (fun j =>
    L^(3/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale r L j ∧
    (9/5:ℝ)*sourceOriginalPGroupScale r L j ≤ L^(2/5:ℝ))

/-- The split preserves the ENTIRE existing native source family. -/
theorem source_native_original_group_partition434 (r : ℕ) (L : ℝ) :
    sourceNativeOriginalSmallIndices434 r L ∪ sourceNativeOriginalBigIndices434 r L =
      sourceOriginalPAllGroupIndices r L := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with hs | hb
    · exact (Finset.mem_filter.mp hs).1
    · exact (Finset.mem_filter.mp hb).1
  · intro hj
    have hband : sourceOriginalPGroupIndex r L j :=
      (Finset.mem_filter.mp hj).2
    rcases hband with hs | hb
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hj,hs⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hj,hb⟩))

/-- The original SMALL and BIG branches cannot overlap when L>1. -/
theorem source_native_original_group_partition_disjoint434
    (r : ℕ) (L : ℝ) (hL : 1 < L) :
    Disjoint (sourceNativeOriginalSmallIndices434 r L)
      (sourceNativeOriginalBigIndices434 r L) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hs hb
  have hsmall := (Finset.mem_filter.mp hs).2
  have hbig := (Finset.mem_filter.mp hb).2
  have hLp : 0 < L := zero_lt_one.trans hL
  have hscale : 0 ≤ sourceOriginalPGroupScale r L j := by
    unfold sourceOriginalPGroupScale
    positivity
  have hgap : L^(1/5:ℝ) < L^(3/10:ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hL (by norm_num)
  nlinarith [hsmall.2,hbig.1]

/-- Logarithmic index inequalities, converted to the true dyadic power. -/
theorem source_native_original_dyadic_window434
    (L a b : ℝ) (j : ℕ) (hL : 1 ≤ L)
    (hlo : a*(Real.log L / Real.log 2) ≤ (j:ℝ))
    (hhi : (j:ℝ) ≤ b*(Real.log L / Real.log 2)) :
    L^a ≤ (2:ℝ)^j ∧ (2:ℝ)^j ≤ L^b := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfirst : a*Real.log L ≤ (j:ℝ)*Real.log 2 :=
    (div_le_iff₀ h2).mp (by simpa only [mul_div_assoc] using hlo)
  have hsecond : (j:ℝ)*Real.log 2 ≤ b*Real.log L :=
    (le_div_iff₀ h2).mp (by simpa only [mul_div_assoc] using hhi)
  have hj : (2:ℝ)^j = Real.exp (Real.log 2*(j:ℝ)) := by
    rw [←Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
  rw [hj,Real.rpow_def_of_pos hLp,Real.rpow_def_of_pos hLp]
  exact ⟨Real.exp_le_exp.mpr (by nlinarith),
    Real.exp_le_exp.mpr (by nlinarith)⟩

/-- A fixed interior window supplies original indices in either P-band.
This proves containment in the complete family; it does not replace that family
by the interior subwindow. -/
theorem source_native_original_interior_band434
    (r : ℕ) (L a : ℝ) (j : ℕ) (hr : 1 ≤ r) (hL : 1 ≤ L)
    (hLarge : (22/15:ℝ)*(r:ℝ) ≤ L^(1/20:ℝ))
    (hlo : L^(9/10-a) ≤ (2:ℝ)^j)
    (hhi : (2:ℝ)^j ≤ L^(19/20-a)) :
    L^a ≤ (3/2:ℝ)*sourceOriginalPGroupScale r L j ∧
    (9/5:ℝ)*sourceOriginalPGroupScale r L j ≤ L^(a+1/10) := by
  let d : ℝ := (r:ℝ)*(11/5:ℝ)
  let q : ℝ := (2:ℝ)^j
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hrp : (0:ℝ) < r := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr)
  have hd : 0 < d := by dsimp [d]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hden : 0 < d*q := mul_pos hd hq
  have ha : 0 < L^a := Real.rpow_pos_of_pos hLp _
  have he : 0 < L^(1/20:ℝ) := Real.rpow_pos_of_pos hLp _
  have hb : 0 < L^(19/20-a) := Real.rpow_pos_of_pos hLp _
  have hc : 0 < L^(a+1/10) := Real.rpow_pos_of_pos hLp _
  have hprod : L^a * L^(1/20:ℝ) * L^(19/20-a) = L := by
    rw [←Real.rpow_add hLp,←Real.rpow_add hLp]
    rw [show a+(1/20:ℝ)+(19/20-a) = 1 by ring,Real.rpow_one]
  have hprod' : L^(a+1/10)*L^(9/10-a) = L := by
    rw [←Real.rpow_add hLp]
    rw [show (a+(1/10:ℝ))+(9/10-a) = 1 by ring,Real.rpow_one]
  have hdUpper : d ≤ (3/2:ℝ)*L^(1/20:ℝ) := by
    dsimp [d]
    nlinarith [hLarge]
  have hnumLo : L^a*(d*q) ≤ (3/2:ℝ)*L := by
    have h1 := mul_le_mul_of_nonneg_left hhi
      (mul_nonneg ha.le hd.le)
    have h2 := mul_le_mul_of_nonneg_right hdUpper
      (mul_nonneg ha.le hb.le)
    change _ ≤ _ at h1
    dsimp only [q] at *
    nlinarith [hprod]
  have hdLower : (9/5:ℝ) ≤ d := by
    dsimp [d]
    have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hnumHi : (9/5:ℝ)*L ≤ L^(a+1/10)*(d*q) := by
    have h1 := mul_le_mul_of_nonneg_right hdLower hLp.le
    have h2 := mul_le_mul_of_nonneg_left hlo (mul_nonneg hd.le hc.le)
    dsimp only [q] at *
    nlinarith [hprod']
  constructor
  · change L^a ≤ (3/2:ℝ)*(L/(d*q))
    calc
      L^a ≤ ((3/2:ℝ)*L)/(d*q) := (le_div_iff₀ hden).mpr hnumLo
      _ = (3/2:ℝ)*(L/(d*q)) := by ring
  · change (9/5:ℝ)*(L/(d*q)) ≤ L^(a+1/10)
    calc
      (9/5:ℝ)*(L/(d*q)) = ((9/5:ℝ)*L)/(d*q) := by ring
      _ ≤ L^(a+1/10) := (div_le_iff₀ hden).mpr hnumHi

/-- Quantitative count of an actual rounded interval of natural indices. -/
theorem source_native_original_interior_card434
    (u a : ℝ) (hu : 40 ≤ u) (ha : 0 ≤ a) :
    u/40 ≤ ((Finset.Icc ⌈a*u⌉₊ ⌊(a+1/20)*u⌋₊).card:ℝ) := by
  have hu0 : 0 ≤ u := by linarith
  have harg : 0 ≤ a*u := mul_nonneg ha hu0
  have harg' : 0 ≤ (a+1/20)*u := mul_nonneg (by linarith) hu0
  have hceil : (⌈a*u⌉₊:ℝ) < a*u+1 := Nat.ceil_lt_add_one harg
  have hfloor : (a+1/20)*u < (⌊(a+1/20)*u⌋₊:ℝ)+1 :=
    Nat.lt_floor_add_one _
  have hle : ⌈a*u⌉₊ ≤ ⌊(a+1/20)*u⌋₊ := by
    apply (Nat.le_floor_iff harg').mpr
    nlinarith
  rw [Nat.card_Icc,Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
  nlinarith

/-- Two explicit interior windows lie in the actual full SMALL/BIG families. -/
theorem source_native_original_interior_subset434
    (r : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 1 < L)
    (hLarge : (22/15:ℝ)*(r:ℝ) ≤ L^(1/20:ℝ)) :
    (Finset.Icc ⌈(4/5:ℝ)*(Real.log L/Real.log 2)⌉₊
      ⌊(17/20:ℝ)*(Real.log L/Real.log 2)⌋₊ ⊆
      sourceNativeOriginalSmallIndices434 r L) ∧
    (Finset.Icc ⌈(3/5:ℝ)*(Real.log L/Real.log 2)⌉₊
      ⌊(13/20:ℝ)*(Real.log L/Real.log 2)⌋₊ ⊆
      sourceNativeOriginalBigIndices434 r L) := by
  classical
  have hu : 0 ≤ Real.log L/Real.log 2 :=
    div_nonneg (Real.log_nonneg hL.le) (Real.log_pos (by norm_num)).le
  constructor
  · intro j hj
    have hmem := Finset.mem_Icc.mp hj
    have hlo : (4/5:ℝ)*(Real.log L/Real.log 2) ≤ (j:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmem.1)
    have hhi : (j:ℝ) ≤ (17/20:ℝ)*(Real.log L/Real.log 2) :=
      (show (j:ℝ) ≤ (⌊(17/20:ℝ)*(Real.log L/Real.log 2)⌋₊:ℝ) by
        exact_mod_cast hmem.2).trans (Nat.floor_le (mul_nonneg (by norm_num) hu))
    have hp := source_native_original_dyadic_window434 L (4/5) (17/20) j hL.le hlo hhi
    have hb := source_native_original_interior_band434 r L (1/10) j hr hL.le hLarge
      (by norm_num at *; exact hp.1) (by norm_num at *; exact hp.2)
    have hband : L^(1/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale r L j ∧
        (9/5:ℝ)*sourceOriginalPGroupScale r L j ≤ L^(1/5:ℝ) := by
      norm_num at hb ⊢
      exact hb
    apply Finset.mem_filter.mpr
    exact ⟨(source_original_P_all_groups_mem_iff r L hr hL j).mpr (Or.inl hband),hband⟩
  · intro j hj
    have hmem := Finset.mem_Icc.mp hj
    have hlo : (3/5:ℝ)*(Real.log L/Real.log 2) ≤ (j:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmem.1)
    have hhi : (j:ℝ) ≤ (13/20:ℝ)*(Real.log L/Real.log 2) :=
      (show (j:ℝ) ≤ (⌊(13/20:ℝ)*(Real.log L/Real.log 2)⌋₊:ℝ) by
        exact_mod_cast hmem.2).trans (Nat.floor_le (mul_nonneg (by norm_num) hu))
    have hp := source_native_original_dyadic_window434 L (3/5) (13/20) j hL.le hlo hhi
    have hb := source_native_original_interior_band434 r L (3/10) j hr hL.le hLarge
      (by norm_num at *; exact hp.1) (by norm_num at *; exact hp.2)
    have hband : L^(3/10:ℝ) ≤ (3/2:ℝ)*sourceOriginalPGroupScale r L j ∧
        (9/5:ℝ)*sourceOriginalPGroupScale r L j ≤ L^(2/5:ℝ) := by
      norm_num at hb ⊢
      exact hb
    apply Finset.mem_filter.mpr
    exact ⟨(source_original_P_all_groups_mem_iff r L hr hL j).mpr (Or.inr hband),hband⟩

/-- Genuine separate lower counts for ALL original groups, with no prime-family
replacement and no equality of the SMALL/BIG cardinalities. The threshold
precedes all source comparison precisions, probe counts and selected indices. -/
theorem eventually_source_native_original_group_counts434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      Real.log L/(40*Real.log 2) ≤
        ((sourceNativeOriginalSmallIndices434 r L).card:ℝ) ∧
      Real.log L/(40*Real.log 2) ≤
        ((sourceNativeOriginalBigIndices434 r L).card:ℝ) := by
  have hpow : Tendsto (fun L : ℝ => L^(1/20:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hlarge := hpow.eventually (eventually_ge_atTop ((22/15:ℝ)*(r:ℝ)))
  filter_upwards [hlarge,eventually_ge_atTop (Real.exp (40*Real.log 2)),
    eventually_ge_atTop (2:ℝ)] with L hlarge hlogsize hL2
  have hL : 1 < L := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu : 40 ≤ Real.log L/Real.log 2 := by
    apply (le_div_iff₀ h2).mpr
    have hh := Real.log_le_log (Real.exp_pos _) hlogsize
    simpa only [Real.log_exp] using hh
  have hsub := source_native_original_interior_subset434 r L hr hL hlarge
  have hsmall := source_native_original_interior_card434
    (Real.log L/Real.log 2) (4/5) hu (by norm_num)
  have hbig := source_native_original_interior_card434
    (Real.log L/Real.log 2) (3/5) hu (by norm_num)
  have hsc : ((Finset.Icc ⌈(4/5:ℝ)*(Real.log L/Real.log 2)⌉₊
      ⌊(17/20:ℝ)*(Real.log L/Real.log 2)⌋₊).card:ℝ) ≤
      ((sourceNativeOriginalSmallIndices434 r L).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub.1
  have hbc : ((Finset.Icc ⌈(3/5:ℝ)*(Real.log L/Real.log 2)⌉₊
      ⌊(13/20:ℝ)*(Real.log L/Real.log 2)⌋₊).card:ℝ) ≤
      ((sourceNativeOriginalBigIndices434 r L).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub.2
  have hident : (Real.log L/Real.log 2)/40 = Real.log L/(40*Real.log 2) := by
    rw [div_div, mul_comm (Real.log 2) 40]
  simp only [show (4/5:ℝ)+1/20 = 17/20 by norm_num] at hsmall
  simp only [show (3/5:ℝ)+1/20 = 13/20 by norm_num] at hbig
  rw [hident] at hsmall hbig
  exact ⟨hsmall.trans hsc,hbig.trans hbc⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeOriginalBigPartition -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The entire original BIG family, with its own index type independent of SMALL. -/
abbrev sourceNativeOriginalBigType434 (r : ℕ) (L : ℝ) : Type :=
  {j : ℕ // j ∈ sourceNativeOriginalBigIndices434 r L}

/-- Half of the full original BIG family. This family rule depends only on r,L,
not on a comparison probe count, a precision, or a later mark selection. -/
def sourceNativeOriginalBigBlockA434 (r : ℕ) (L : ℝ) :
    Finset (sourceNativeOriginalBigType434 r L) :=
  Classical.choose (Finset.exists_subset_card_eq
    (Nat.div_le_self (Finset.univ : Finset (sourceNativeOriginalBigType434 r L)).card 2))

/-- All remaining original BIG groups, with no deletion from the full family. -/
def sourceNativeOriginalBigBlockB434 (r : ℕ) (L : ℝ) :
    Finset (sourceNativeOriginalBigType434 r L) :=
  Finset.univ \ sourceNativeOriginalBigBlockA434 r L

/-- Exact finite geometry: the two blocks partition the complete original BIG
index type, and their sizes are floor(n/2) and n-floor(n/2). -/
theorem source_native_original_big_partition434 (r : ℕ) (L : ℝ) :
    sourceNativeOriginalBigBlockA434 r L ∪ sourceNativeOriginalBigBlockB434 r L =
      (Finset.univ : Finset (sourceNativeOriginalBigType434 r L)) ∧
    Disjoint (sourceNativeOriginalBigBlockA434 r L)
      (sourceNativeOriginalBigBlockB434 r L) ∧
    (sourceNativeOriginalBigBlockA434 r L).card =
      (sourceNativeOriginalBigIndices434 r L).card / 2 ∧
    (sourceNativeOriginalBigBlockB434 r L).card =
      (sourceNativeOriginalBigIndices434 r L).card -
        (sourceNativeOriginalBigIndices434 r L).card / 2 := by
  classical
  have hchoice := Classical.choose_spec (Finset.exists_subset_card_eq
    (Nat.div_le_self (Finset.univ : Finset (sourceNativeOriginalBigType434 r L)).card 2))
  have hAcard : (sourceNativeOriginalBigBlockA434 r L).card =
      (sourceNativeOriginalBigIndices434 r L).card / 2 := by
    simpa only [sourceNativeOriginalBigBlockA434, Finset.card_univ,
      Fintype.card_coe] using hchoice.2
  have hunion : sourceNativeOriginalBigBlockA434 r L ∪
      sourceNativeOriginalBigBlockB434 r L =
      (Finset.univ : Finset (sourceNativeOriginalBigType434 r L)) := by
    ext g
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      by_cases ha : g ∈ sourceNativeOriginalBigBlockA434 r L
      · exact Finset.mem_union.mpr (Or.inl ha)
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ha⟩))
  have hdisj : Disjoint (sourceNativeOriginalBigBlockA434 r L)
      (sourceNativeOriginalBigBlockB434 r L) := by
    apply Finset.disjoint_left.mpr
    intro g hga hgb
    exact (Finset.mem_sdiff.mp hgb).2 hga
  have hsum := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hsum
  have hsum' : (sourceNativeOriginalBigIndices434 r L).card =
      (sourceNativeOriginalBigBlockA434 r L).card +
        (sourceNativeOriginalBigBlockB434 r L).card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hsum
  refine ⟨hunion,hdisj,hAcard,?_⟩
  omega

/-- Every literal original BIG index belongs to exactly one block. This
coverage statement rules out replacing the full family by a lower-count witness. -/
theorem source_native_original_big_partition_covers434
    (r : ℕ) (L : ℝ) (j : ℕ)
    (hj : j ∈ sourceNativeOriginalBigIndices434 r L) :
    let g : sourceNativeOriginalBigType434 r L := ⟨j,hj⟩
    (g ∈ sourceNativeOriginalBigBlockA434 r L ∨
      g ∈ sourceNativeOriginalBigBlockB434 r L) ∧
    ¬ (g ∈ sourceNativeOriginalBigBlockA434 r L ∧
      g ∈ sourceNativeOriginalBigBlockB434 r L) := by
  dsimp only
  have hp := source_native_original_big_partition434 r L
  constructor
  · apply Finset.mem_union.mp
    rw [hp.1]
    exact Finset.mem_univ _
  · rintro ⟨ha,hb⟩
    exact Finset.disjoint_left.mp hp.2.1 ha hb

/-- Genuine original BIG halves satisfy the C-root count requirement. The only
analytic-size input is the lower count already proved for the complete native
family; no requested block-size hypothesis is assumed here. -/
theorem eventually_source_native_original_big_partition434
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℝ in atTop,
      sourceNativeOriginalBigBlockA434 r L ∪ sourceNativeOriginalBigBlockB434 r L =
        (Finset.univ : Finset (sourceNativeOriginalBigType434 r L)) ∧
      Disjoint (sourceNativeOriginalBigBlockA434 r L)
        (sourceNativeOriginalBigBlockB434 r L) ∧
      Real.log L/(120*Real.log 2) ≤
        ((sourceNativeOriginalBigBlockA434 r L).card:ℝ) ∧
      Real.log L/(120*Real.log 2) ≤
        ((sourceNativeOriginalBigBlockB434 r L).card:ℝ) := by
  filter_upwards [eventually_source_native_original_group_counts434 r hr,
    eventually_ge_atTop (Real.exp (120*Real.log 2))] with L hcounts hL
  have hp := source_native_original_big_partition434 r L
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h40 : 0 < 40*Real.log 2 := mul_pos (by norm_num) h2
  have hlog : 120*Real.log 2 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos _) hL
    simpa only [Real.log_exp] using h
  have hthreeReal : (3:ℝ) ≤ (sourceNativeOriginalBigIndices434 r L).card := by
    apply le_trans _ hcounts.2
    apply (le_div_iff₀ h40).mpr
    nlinarith
  have hthree : 3 ≤ (sourceNativeOriginalBigIndices434 r L).card := by
    exact_mod_cast hthreeReal
  have hthirdA : (sourceNativeOriginalBigIndices434 r L).card ≤
      3*(sourceNativeOriginalBigBlockA434 r L).card := by
    rw [hp.2.2.1]
    omega
  have hthirdB : (sourceNativeOriginalBigIndices434 r L).card ≤
      3*(sourceNativeOriginalBigBlockB434 r L).card := by
    rw [hp.2.2.2]
    omega
  have hthirdAReal : ((sourceNativeOriginalBigIndices434 r L).card:ℝ) ≤
      3*((sourceNativeOriginalBigBlockA434 r L).card:ℝ) := by
    exact_mod_cast hthirdA
  have hthirdBReal : ((sourceNativeOriginalBigIndices434 r L).card:ℝ) ≤
      3*((sourceNativeOriginalBigBlockB434 r L).card:ℝ) := by
    exact_mod_cast hthirdB
  have hdiv : Real.log L/(120*Real.log 2) =
      (Real.log L/(40*Real.log 2))/3 := by
    rw [div_div]
    congr 1
    ring
  refine ⟨hp.1,hp.2.1,?_,?_⟩
  · rw [hdiv]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
    exact hcounts.2.trans (by nlinarith)
  · rw [hdiv]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
    exact hcounts.2.trans (by nlinarith)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualPatternDisjoint -/

section

open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace Green64Analytic.CorrelationSquare

/-- Membership in the literal two-block comparison family forces the two
freed probe sets to be disjoint whenever the original group blocks are. -/
theorem parity_two_block_probe_disjoint434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (hBlock : Disjoint blockA blockB)
    (m : ℕ) (nu : SourceOriginalProbePattern434 G m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m) :
    Disjoint nu.1 nu.2 := by
  classical
  obtain ⟨_,hA,_,hB⟩ :=
    (source_original_two_block_probe_pattern_mem434 blockA blockB m nu.1 nu.2).mp hnu
  apply Finset.disjoint_left.mpr
  intro z hzA hzB
  have hza : z.1 ∈ blockA := (Finset.mem_product.mp (hA hzA)).1
  have hzb : z.1 ∈ blockB := (Finset.mem_product.mp (hB hzB)).1
  exact Finset.disjoint_left.mp hBlock hza hzb

end Green64Analytic.CorrelationSquare
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare

/-- The actual complete Parity r20 comparison family satisfies disjointness
without adding a hypothesis. Both original BIG blocks remain unchanged. -/
theorem parity_actual_comparison_pattern_disjoint434
    (L : ℝ) (m : ℕ)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (hnu : nu ∈ sourceOriginalTwoBlockProbePatterns434
      (sourceNativeOriginalBigBlockA434 20 L)
      (sourceNativeOriginalBigBlockB434 20 L) m) :
    Disjoint nu.1 nu.2 :=
  parity_two_block_probe_disjoint434
    (sourceNativeOriginalBigBlockA434 20 L)
    (sourceNativeOriginalBigBlockB434 20 L)
    (source_native_original_big_partition434 20 L).2.1 m nu hnu

end Green64Analytic.SourceBlockSieve

end

end

/-! ## SourceNativeR6DyadicThreshold -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Exact arithmetic threshold for the REAL dyadic source group
lower index, with a rational constant c strictly between
consecutive powers of 2. No floating-point approximation. -/
theorem source_native_r6_dyadic_ge_iff434
    (c : ℝ) (n b j : ℕ)
    (hlo : (2:ℝ)^b < c)
    (hhi : c ≤ (2:ℝ)^(b+1)) :
    c*(2:ℝ)^n ≤ (2:ℝ)^j ↔ n+b+1 ≤ j := by
  have hp : 0 < (2:ℝ)^n := pow_pos (by norm_num) _
  have hpower (a t : ℕ) : (2:ℝ)^(a+t) =
      (2:ℝ)^a*(2:ℝ)^t := pow_add _ _ _
  constructor
  · intro h
    have hLo : (2:ℝ)^(n+b) <
        c*(2:ℝ)^n := by
      rw [hpower, mul_comm]
      exact mul_lt_mul_of_pos_right hlo hp
    have hIndex : n+b < j :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
        (hLo.trans_le h)
    omega
  · intro hIndex
    have hLe : (2:ℝ)^(n+(b+1)) ≤ (2:ℝ)^j :=
      (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mpr
        (by omega)
    have hHi : c*(2:ℝ)^n ≤ (2:ℝ)^(n+(b+1)) := by
      rw [hpower,mul_comm]
      convert mul_le_mul_of_nonneg_right hhi hp.le using 1 <;> ring
    exact hHi.trans hLe

/-- Upper endpoint for the source dyadic group index from an
EXACT rational threshold between two consecutive powers of 2. -/
theorem source_native_r6_dyadic_le_iff434
    (c : ℝ) (n b j : ℕ)
    (hlo : (2:ℝ)^b ≤ c)
    (hhi : c < (2:ℝ)^(b+1)) :
    (2:ℝ)^j ≤ c*(2:ℝ)^n ↔ j ≤ n+b := by
  have hp : 0 < (2:ℝ)^n := pow_pos (by norm_num) _
  have hpower (a t : ℕ) : (2:ℝ)^(a+t) =
      (2:ℝ)^a*(2:ℝ)^t := pow_add _ _ _
  constructor
  · intro h
    have hHi : c*(2:ℝ)^n <
        (2:ℝ)^(n+(b+1)) := by
      rw [hpower,mul_comm]
      convert mul_lt_mul_of_pos_right hhi hp using 1 <;> ring
    have hIndex : j < n+(b+1) :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
        (h.trans_lt hHi)
    omega
  · intro hIndex
    have hLe : (2:ℝ)^j ≤ (2:ℝ)^(n+b) :=
      (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mpr
        hIndex
    have hLo : (2:ℝ)^(n+b) ≤ c*(2:ℝ)^n := by
      rw [hpower,mul_comm]
      exact mul_le_mul_of_nonneg_right hlo hp.le
    exact hLe.trans hLo

/-- The genuine r=6 source geometric cofinal scale is chosen with
a RATIONAL tenth root u=(3/2)2^N, so all four true SMALL/BIG
band endpoints reduce to elementary RATIONAL inequalities.
The exact source thresholds are:
small lower (3/22)*(3/2)^8 is between 2 and 4,
small upper (5/44)*(3/2)^9 is between 4 and 8,
BIG lower (3/22)*(3/2)^6 is between 1 and 2,
BIG upper (5/44)*(3/2)^7 is between 1 and 2.
These are exact rational inequalities, not empirical approximations. -/
theorem source_native_r6_rational_thresholds434 :
    (2:ℝ) < (3/22:ℝ)*(3/2:ℝ)^8 ∧
    (3/22:ℝ)*(3/2:ℝ)^8 ≤ 4 ∧
    4 ≤ (5/44:ℝ)*(3/2:ℝ)^9 ∧
    (5/44:ℝ)*(3/2:ℝ)^9 < 8 ∧
    1 < (3/22:ℝ)*(3/2:ℝ)^6 ∧
    (3/22:ℝ)*(3/2:ℝ)^6 ≤ 2 ∧
    1 ≤ (5/44:ℝ)*(3/2:ℝ)^7 ∧
    (5/44:ℝ)*(3/2:ℝ)^7 < 2 := by
  norm_num
end Green64Analytic.SourceBlockSieve

end

end

