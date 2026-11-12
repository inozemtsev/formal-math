module

public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part002
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Green64.Library.Weights.Part012
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Logic.Function.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

/-!
# Weights / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGhostOrderedBirthDisintegration -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64MemoryGhostOp Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

theorem source_original_GHOST_birth_fibre_bag434
    {P U : Type} [Fintype P] [DecidableEq P] [Fintype U] [DecidableEq U]
    (b : ℕ) (s : Finset P) (f : SourceOriginalGhostBirthFibre434 b s) (e : P → U) :
    memoryTupleBag (fun i => e (f.1 i)) = ∑ p ∈ s, ({e p} : Multiset U) := by
  unfold memoryTupleBag
  calc
    _ = ∑ p ∈ Finset.univ.image f.1, ({e p} : Multiset U) := by
      symm
      exact Finset.sum_image (fun i hi j hj h => f.2.1 h)
    _ = _ := congrArg (fun t : Finset P => ∑ p ∈ t, ({e p} : Multiset U)) f.2.2

/-- The ordered OLD survivors are kept with all multiplicities. Only
orders of a prescribed distinct fresh set are collected. -/
theorem source_original_GHOST_old_birth_fibre_exact434
    {P U : Type} [Fintype P] [DecidableEq P] [Fintype U] [DecidableEq U]
    (old : List U) (zero : U → Prop) [DecidablePred zero]
    (A : Finset (Fin old.length)) (b : ℕ) (s : Finset P) (hs : s.card=b)
    (e : P → U) (alpha chi gamma : ℂ) (nu : U → ℂ)
    (F : Multiset U → Finset P → ℂ) :
    (∑ f : SourceOriginalGhostBirthFibre434 b s,
      sourceGhostTerm old zero A (fun i => e (f.1 i)) alpha chi gamma nu *
        F (afterGhost old A (fun i => e (f.1 i)) : Multiset U) (Finset.univ.image f.1)) =
    alpha^A.card * chi^((zeroOld old zero).card-A.card) * gamma^b *
      (∏ p ∈ s,nu (e p)) *
      F (memoryTupleBag (fun j : {j : Fin old.length // j ∉ A} => old.get j) +
        ∑ p ∈ s,({e p}:Multiset U)) s := by
  let T := alpha^A.card * chi^((zeroOld old zero).card-A.card) * gamma^b *
      (∏ p ∈ s,nu (e p)) *
      F (memoryTupleBag (fun j : {j : Fin old.length // j ∉ A} => old.get j) +
        ∑ p ∈ s,({e p}:Multiset U)) s
  have ht (f : SourceOriginalGhostBirthFibre434 b s) :
      sourceGhostTerm old zero A (fun i => e (f.1 i)) alpha chi gamma nu *
        F (afterGhost old A (fun i => e (f.1 i)) : Multiset U) (Finset.univ.image f.1) =
      (1/(b.factorial:ℂ))*T := by
    rw [memory_source_afterGhost_bag,
      source_original_GHOST_birth_fibre_bag434 b s f e,f.2.2]
    unfold sourceGhostTerm
    rw [source_original_GHOST_birth_fibre_product434 b s f (fun p => nu (e p))]
    dsimp [T]
    ring
  simp_rw [ht]
  rw [Finset.sum_const,Finset.card_univ,
    source_original_GHOST_birth_fibre_factorial434 b s hs,nsmul_eq_mul]
  change (b.factorial:ℂ)*((1/(b.factorial:ℂ))*T)=T
  have hb : (b.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  field_simp

theorem source_original_GHOST_fibre_numeric_births434
    {P : Type} [Fintype P] [DecidableEq P]
    (b : ℕ) (s : Finset P) (f : SourceOriginalGhostBirthFibre434 b s) (num : P → ℕ) :
    ((List.ofFn f.1).map num).toFinset = s.image num := by
  calc
    _ = (Finset.univ.image f.1).image num := by
      ext n
      simp
    _ = _ := congrArg (fun t : Finset P => t.image num) f.2.2

/-- Numeric distinctness is retained even when the atom type has several
residues over the same prime. No global injectivity of num is assumed. -/
theorem source_original_GHOST_fibre_numeric_gate434
    {P : Type} [Fintype P] [DecidableEq P]
    (b : ℕ) (s : Finset P) (f : SourceOriginalGhostBirthFibre434 b s)
    (num : P → ℕ) (seen : Finset ℕ) :
    (((List.ofFn f.1).map num).Nodup ∧
      Disjoint seen ((List.ofFn f.1).map num).toFinset) ↔
    Set.InjOn num (↑s : Set P) ∧ Disjoint seen (s.image num) := by
  rw [source_original_GHOST_fibre_numeric_births434 b s f num]
  have hi : ((List.ofFn f.1).map num).Nodup ↔ Set.InjOn num (↑s : Set P) := by
    rw [List.map_ofFn,List.nodup_ofFn]
    constructor
    · intro h p hp q hq hpq
      have hp' : p ∈ Finset.univ.image f.1 := by rw [f.2.2];exact hp
      have hq' : q ∈ Finset.univ.image f.1 := by rw [f.2.2];exact hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp'
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq'
      exact congrArg f.1 (h hpq)
    · intro h i j he
      apply f.2.1
      apply h
      · have hi : f.1 i ∈ Finset.univ.image f.1 :=
          Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
        change f.1 i ∈ s
        simpa only [f.2.2] using hi
      · have hj : f.1 j ∈ Finset.univ.image f.1 :=
          Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
        change f.1 j ∈ s
        simpa only [f.2.2] using hj
      · exact he
  exact and_congr_left (fun _ => hi)

theorem source_original_GHOST_distinct_fibre_decomposition434
    {P : Type} [Fintype P] [DecidableEq P] (b : ℕ) (W : (Fin b → P) → ℂ) :
    (∑ f : Fin b → P,if Function.Injective f then W f else 0) =
    ∑ s ∈ (Finset.univ : Finset (Finset P)).filter (fun s => s.card=b),
      ∑ f : SourceOriginalGhostBirthFibre434 b s,W f.1 := by
  let T : Finset (Fin b → P) := Finset.univ.filter (fun f => Function.Injective f)
  let S : Finset (Finset P) := Finset.univ.filter (fun s => s.card=b)
  have hm (f : Fin b → P) (hf : f ∈ T) : Finset.univ.image f ∈ S := by
    have hinj := (Finset.mem_filter.mp hf).2
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  have hb := Finset.sum_fiberwise_of_maps_to (s := T) (t := S)
    (g := fun f => Finset.univ.image f) hm W
  have hf (s : Finset P) :
      (∑ f ∈ T.filter (fun f => Finset.univ.image f=s),W f) =
      ∑ f : SourceOriginalGhostBirthFibre434 b s,W f.1 := by
    apply Finset.sum_subtype _ _ W
    intro f
    simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]
  calc
    _ = ∑ f ∈ T,W f := by simp [T,Finset.sum_filter]
    _ = ∑ s ∈ S,∑ f ∈ T.filter (fun f => Finset.univ.image f=s),W f := hb.symm
    _ = _ := by simp_rw [hf];rfl

/-- The literal OLD source term with its numeric birth gate, summed over
ALL ordered b-tuples, equals the unordered b-set expression. The original
factorial is cancelled exactly; an arbitrary joint multiset/seen test is
retained. -/
theorem source_original_GHOST_marked_old_birth_count434
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero]
    (A : Finset (Fin old.length)) (b : ℕ)
    (num : P → ℕ) (seen : Finset ℕ)
    (alpha chi gamma : ℂ) (nu : P → ℂ)
    (F : Multiset P → Finset ℕ → ℂ) :
    (∑ fresh : Fin b → P,
      if ((List.ofFn fresh).map num).Nodup ∧
          Disjoint seen ((List.ofFn fresh).map num).toFinset then
        sourceGhostTerm old zero A fresh alpha chi gamma nu *
          F (afterGhost old A fresh : Multiset P)
            (seen ∪ ((List.ofFn fresh).map num).toFinset)
      else 0) =
    ∑ s ∈ (Finset.univ : Finset (Finset P)).filter (fun s => s.card=b),
      if Set.InjOn num (↑s : Set P) ∧ Disjoint seen (s.image num) then
        alpha^A.card * chi^((zeroOld old zero).card-A.card) * gamma^b *
          (∏ p ∈ s,nu p) *
          F (memoryTupleBag (fun j : {j : Fin old.length // j ∉ A} => old.get j) +
            ∑ p ∈ s,({p}:Multiset P)) (seen ∪ s.image num)
      else 0 := by
  let W : (Fin b → P) → ℂ := fun fresh =>
      if ((List.ofFn fresh).map num).Nodup ∧
          Disjoint seen ((List.ofFn fresh).map num).toFinset then
        sourceGhostTerm old zero A fresh alpha chi gamma nu *
          F (afterGhost old A fresh : Multiset P)
            (seen ∪ ((List.ofFn fresh).map num).toFinset)
      else 0
  have hw (fresh : Fin b → P) : W fresh =
      if Function.Injective fresh then W fresh else 0 := by
    by_cases hi : Function.Injective fresh
    · simp [hi]
    · have hn : ¬((List.ofFn fresh).map num).Nodup := by
        intro h
        exact hi (List.nodup_ofFn.mp (List.Nodup.of_map num h))
      simp only [W,hn,false_and,if_false,hi]
  change (∑ fresh : Fin b → P,W fresh)=_
  have hsum : (∑ fresh : Fin b → P,W fresh) =
      ∑ fresh : Fin b → P,if Function.Injective fresh then W fresh else 0 :=
    Finset.sum_congr rfl (fun fresh _ => hw fresh)
  rw [hsum,source_original_GHOST_distinct_fibre_decomposition434]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard : s.card=b := (Finset.mem_filter.mp hs).2
  by_cases hg : Set.InjOn num (↑s:Set P) ∧ Disjoint seen (s.image num)
  · simp only [if_pos hg]
    have hwf (f : SourceOriginalGhostBirthFibre434 b s) :
        W f.1 = sourceGhostTerm old zero A f.1 alpha chi gamma nu *
          F (afterGhost old A f.1 : Multiset P) (seen ∪ Finset.image num (Finset.univ.image f.1)) := by
      have hgate := (source_original_GHOST_fibre_numeric_gate434 b s f num seen).mpr hg
      dsimp only [W]
      rw [if_pos hgate,source_original_GHOST_fibre_numeric_births434 b s f num,f.2.2]
    simp_rw [hwf]
    exact source_original_GHOST_old_birth_fibre_exact434 old zero A b s hcard
      (fun p => p) alpha chi gamma nu (fun bag t => F bag (seen ∪ t.image num))
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro f hf
    have hgate : ¬(((List.ofFn f.1).map num).Nodup ∧
        Disjoint seen ((List.ofFn f.1).map num).toFinset) :=
      fun h => hg ((source_original_GHOST_fibre_numeric_gate434 b s f num seen).mp h)
    simp only [W,if_neg hgate]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalGlobalLogLoss -/

section

namespace Green64Analytic.CorrelationSquare

/-- Actual log-power bound for the predecessor four-dyad count,
derived from the original natural support cap N <= x^2. -/
theorem source_original_natural_cap_log_budget434
    (N : ℕ) (x L : ℝ) (hN : 0 < N) (hx : 0 < x)
    (hLog : L = Real.log x) (hL : 1 ≤ L) (hCap : (N:ℝ) ≤ x^2) :
    (N.log2+1:ℝ) ≤ (1+2/Real.log 2)*L := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNReal : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (2:ℝ)^N.log2 ≤ (N:ℝ) := by
    exact_mod_cast Nat.log2_self_le (Nat.ne_of_gt hN)
  have hLower := Real.log_le_log (by positivity : (0:ℝ) < 2^N.log2) hpow
  rw [Real.log_pow] at hLower
  have hUpper : Real.log (N:ℝ) ≤ 2*L := by
    calc
      _ ≤ Real.log (x^2) := Real.log_le_log hNReal hCap
      _ = 2*L := by rw [Real.log_pow,←hLog]; ring
  have hRatio : (N.log2:ℝ) ≤ 2*L/Real.log 2 :=
    (le_div_iff₀ htwo).mpr (hLower.trans hUpper)
  calc
    _ ≤ 2*L/Real.log 2 + L := by linarith
    _ = _ := by ring

/-- The precise fixed logarithmic loss in the NEW global physical
mean-square theorem. Requesting Dbox=Aout+2 cm+8 is sufficient. -/
theorem source_original_global_log_loss434
    (L Vs vmin K : ℝ) (den N : ℕ) (cm Aout : ℕ)
    (hL : 1 ≤ L) (hv : 0 < vmin) (hVs : vmin ≤ Vs)
    (hK : 0 ≤ K) (hDen : (den:ℝ) ≤ L^cm)
    (hCount : (N.log2+1:ℝ) ≤ K*L) :
    (1/Vs)^2 * (den:ℝ)^2 * (((N.log2+1)^4:ℕ):ℝ)^2 *
      (L^(Aout+2*cm+8))⁻¹ ≤
      (1/vmin)^2 * K^8 * (L^Aout)⁻¹ := by
  have hLpos : 0 < L := by linarith
  have hVspos : 0 < Vs := hv.trans_le hVs
  have hInv : 1/Vs ≤ 1/vmin := one_div_le_one_div_of_le hv hVs
  have hInvNonneg : 0 ≤ 1/Vs := by positivity
  have hCast : (((N.log2+1)^4:ℕ):ℝ) = (N.log2+1:ℝ)^4 := by norm_cast
  rw [hCast]
  calc
    _ ≤ (1/vmin)^2 * (L^cm)^2 * ((K*L)^4)^2 *
        (L^(Aout+2*cm+8))⁻¹ := by
      gcongr
    _ = _ := by
      have hexp : Aout+2*cm+8 = Aout+(cm*2+8) := by omega
      rw [hexp]
      simp only [pow_add,pow_mul,mul_pow]
      field_simp
      <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalArcLowBudget -/

section

namespace Green64Analytic.CorrelationSquare

/-- The original low-time term, including all four dyads and rational
characters, has fixed loss 2*cm+8; the physical Y is unchanged. -/
theorem source_original_arc_low_budget434
    (N den cm Aout : ℕ) (x L Y Vs vmin : ℝ)
    (hN : 0 < N) (hx : 0 < x) (hLog : L = Real.log x)
    (hL : 1 ≤ L) (hCap : (N:ℝ) ≤ x^2)
    (hY : 0 ≤ Y) (hv : 0 < vmin) (hVs : vmin ≤ Vs)
    (hDen : (den:ℝ) ≤ L^cm) :
    Y*((1/Vs)^2*(den:ℝ)^2*(((N.log2+1)^4:ℕ):ℝ)^2*
      (L^(Aout+2*cm+8))⁻¹) ≤
    (1/vmin)^2*(1+2/Real.log 2)^8*Y*(L^Aout)⁻¹ := by
  have hCount := source_original_natural_cap_log_budget434
    N x L hN hx hLog hL hCap
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hBound := source_original_global_log_loss434 L Vs vmin
    (1+2/Real.log 2) den N cm Aout hL hv hVs
    (by positivity) hDen hCount
  have hScaled := mul_le_mul_of_nonneg_left hBound hY
  convert hScaled using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGroupSquareMass -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare

/-- Entire original prime group: its reciprocal mass replaces the
unnecessary dyadic upper endpoint. No square-peeling identity is changed. -/
theorem source_original_group_square_mass434
    (S : Finset ℕ) (L a V : ℝ)
    (hmin : ∀ p ∈ S, Real.exp (L^a) ≤ (p:ℝ))
    (hMass : (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ V) :
    (∑ p ∈ S, (1:ℝ)/(p:ℝ)^2) ≤ V*Real.exp (-(L^a)) := by
  have hEach (p : ℕ) (hp : p ∈ S) :
      (1:ℝ)/(p:ℝ)^2 ≤ ((1:ℝ)/(p:ℝ))*Real.exp (-(L^a)) := by
    have hpPos : (0:ℝ) < p := (Real.exp_pos _).trans_le (hmin p hp)
    have hInv : (1:ℝ)/(p:ℝ) ≤ Real.exp (-(L^a)) := by
      simpa only [Real.exp_neg, one_div] using
        one_div_le_one_div_of_le (Real.exp_pos (L^a)) (hmin p hp)
    have h := mul_le_mul_of_nonneg_left hInv (by positivity : (0:ℝ) ≤ 1/(p:ℝ))
    convert h using 1 <;> field_simp <;> ring
  calc
    _ ≤ ∑ p ∈ S, ((1:ℝ)/(p:ℝ))*Real.exp (-(L^a)) :=
      Finset.sum_le_sum hEach
    _ = (∑ p ∈ S, (1:ℝ)/(p:ℝ))*Real.exp (-(L^a)) := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hMass (Real.exp_pos _).le
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLogCellEmbedding -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 6500000

/-- Original logarithmic cell, with its finite product support retained. -/
noncomputable def sourceOriginalLogCellMask434 (F : Finset ℕ) (U h : ℝ)
    (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ F ∧ 0 < n ∧ Real.log U ≤ Real.log (n:ℝ) ∧
    Real.log (n:ℝ) < Real.log U+h then b n else 0

/-- A width-at-most-one SOURCE cell is contained in the actual three-block
integer cover. Rounding the lower endpoint does not change any nonzero term. -/
theorem source_original_logcell_integer_cover434 (U h : ℝ) (hU : 0 < U) (hh : h ≤ 1)
    (n : ℕ) (hn : 0 < n) (hlo : Real.log U ≤ Real.log (n:ℝ))
    (hhi : Real.log (n:ℝ) < Real.log U+h) :
    n ∈ Finset.Ico (Nat.ceil U) (Nat.ceil U+3*Nat.ceil U) := by
  have hnp : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hLow : U ≤ (n:ℝ) := by
    simpa only [Real.exp_log hU,Real.exp_log hnp] using Real.exp_le_exp.mpr hlo
  have hHigh : (n:ℝ) < U*Real.exp h := by
    simpa only [Real.exp_add,Real.exp_log hU,Real.exp_log hnp] using Real.exp_lt_exp.mpr hhi
  have hExp : Real.exp h < 3 := (Real.exp_le_exp.mpr hh).trans_lt Real.exp_one_lt_three
  have hCeil : U ≤ (Nat.ceil U:ℝ) := Nat.le_ceil U
  have hCover : (n:ℝ) < ((Nat.ceil U+3*Nat.ceil U:ℕ):ℝ) := by
    push_cast
    nlinarith
  exact Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hLow,by exact_mod_cast hCover⟩

theorem source_original_logcell_mask_support434 (F : Finset ℕ) (U h : ℝ)
    (b : ℕ → ℂ) (hU : 0 < U) (hh : h ≤ 1) (n : ℕ)
    (hne : sourceOriginalLogCellMask434 F U h b n ≠ 0) :
    n ∈ Finset.Ico (Nat.ceil U) (Nat.ceil U+3*Nat.ceil U) := by
  unfold sourceOriginalLogCellMask434 at hne
  split_ifs at hne with hp
  · exact source_original_logcell_integer_cover434 U h hU hh n hp.2.1 hp.2.2.1 hp.2.2.2
  · exact (hne rfl).elim

theorem source_original_logcell_mask_norm434 (F : Finset ℕ) (U h : ℝ)
    (b : ℕ → ℂ) (hb : ∀ n ∈ F, ‖b n‖ ≤ 1) (n : ℕ) :
    ‖sourceOriginalLogCellMask434 F U h b n‖ ≤ 1 := by
  unfold sourceOriginalLogCellMask434
  split_ifs with hp
  · exact hb n hp.1
  · norm_num

/-- Exact finite-law expectation on an original cell, not an assumption that
the law is dyadic. The cell and source product-support masks are unchanged. -/
theorem source_original_logcell_sum_reindex434 (F : Finset ℕ) (U h : ℝ)
    (b phi : ℕ → ℂ) (mass : ℕ → ℝ) (hU : 0 < U) (hh : h ≤ 1) :
    (∑ n ∈ F, (mass n:ℂ)*sourceOriginalLogCellMask434 F U h b n*phi n) =
    ∑ i ∈ Finset.range (3*Nat.ceil U),
      (mass (Nat.ceil U+i):ℂ)*sourceOriginalLogCellMask434 F U h b (Nat.ceil U+i)*
        phi (Nat.ceil U+i) := by
  classical
  let M := Nat.ceil U
  let f := fun n => (mass n:ℂ)*sourceOriginalLogCellMask434 F U h b n*phi n
  have hOutsideF : ∀ n, n ∉ F → f n = 0 := by
    intro n hn
    simp [f,sourceOriginalLogCellMask434,hn]
  have hOutsideI : ∀ n, n ∉ Finset.Ico M (M+3*M) → f n = 0 := by
    intro n hn
    have hz : sourceOriginalLogCellMask434 F U h b n = 0 := by
      by_contra hne
      exact hn (source_original_logcell_mask_support434 F U h b hU hh n hne)
    simp only [f,hz,mul_zero,zero_mul]
  have hEq : (∑ n ∈ F, f n) = ∑ n ∈ Finset.Ico M (M+3*M), f n := by
    calc
      _ = ∑ n ∈ F ∪ Finset.Ico M (M+3*M), f n :=
        Finset.sum_subset (Finset.subset_union_left) (fun n hn hnot => hOutsideF n hnot)
      _ = _ := (Finset.sum_subset (Finset.subset_union_right)
        (fun n hn hnot => hOutsideI n hnot)).symm
  have hInterval : Finset.Ico M (M+3*M) =
      (Finset.range (3*M)).image (fun i => M+i) := by
    ext n
    simp only [Finset.mem_Ico,Finset.mem_image,Finset.mem_range]
    constructor
    · intro hn
      exact ⟨n-M,by omega,by omega⟩
    · rintro ⟨i,hi,rfl⟩
      omega
  change (∑ n ∈ F, f n) = _
  rw [hEq,hInterval,Finset.sum_image]
  intro i hi j hj hij
  exact Nat.add_left_cancel hij

/-- Exact TWO independent original product-law expectations, including hard
log-cell gates, as the rectangle already estimated by C. No phase convention
or endpoint correlation is changed by this reindexing. -/
theorem source_original_logcell_product_reindex434
    (F1 F2 : Finset ℕ) (U1 U2 h1 h2 : ℝ)
    (b1 b2 : ℕ → ℂ) (u v : ℕ → ℝ) (B : ℕ → ℕ → ℂ)
    (hU1 : 0 < U1) (hU2 : 0 < U2) (hh1 : h1 ≤ 1) (hh2 : h2 ≤ 1) :
    (∑ m ∈ F1, (u m:ℂ)*sourceOriginalLogCellMask434 F1 U1 h1 b1 m*
      (∑ n ∈ F2, (v n:ℂ)*sourceOriginalLogCellMask434 F2 U2 h2 b2 n*B m n)) =
    ∑ ij ∈ (Finset.range (3*Nat.ceil U1)).product (Finset.range (3*Nat.ceil U2)),
      sourceProductShiftCoefficient434 (Nat.ceil U1) (Nat.ceil U2) u v
        (sourceOriginalLogCellMask434 F1 U1 h1 b1)
        (sourceOriginalLogCellMask434 F2 U2 h2 b2) ij *
          B (Nat.ceil U1+ij.1) (Nat.ceil U2+ij.2) := by
  rw [source_original_logcell_sum_reindex434 F1 U1 h1 b1
    (fun m => ∑ n ∈ F2, (v n:ℂ)*sourceOriginalLogCellMask434 F2 U2 h2 b2 n*B m n)
    u hU1 hh1]
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [source_original_logcell_sum_reindex434 F2 U2 h2 b2
    (B (Nat.ceil U1+i)) v hU2 hh2,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [sourceProductShiftCoefficient434,Complex.ofReal_mul]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLowWindow -/

section

open MeasureTheory
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 900000

/-- EXACT low-source window comparison: original literal-cell theorem
controls [-2T,2T], whereas actual full-time collar uses [-T,T].
The low-energy datum here must be supplied by the actual
SourceOriginalLiteralGlobalTerminal434 theorem; this is merely an
analytic conversion with physical Y normalization, not a replacement
source-saving hypothesis. -/
theorem source_original_low_time_Y_conversion434
    (P : ℝ → ℂ) (hP : Continuous P)
    (Y T E : ℝ) (hY : 0 ≤ Y) (hT : 0 ≤ T)
    (hOriginalLow : (∫ t in Set.Icc (-2*T) (2*T), ‖P t‖^2) ≤ E) :
    (∫ t in Set.Icc (-T) T, ‖(Y:ℂ)*P t‖^2) ≤ Y^2 * E := by
  have hSub : Set.Icc (-T) T ⊆ Set.Icc (-2*T) (2*T) := by
    intro t ht
    rcases Set.mem_Icc.mp ht with ⟨hl,hr⟩
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hInt : IntegrableOn (fun t : ℝ => ‖P t‖^2)
      (Set.Icc (-2*T) (2*T)) :=
    (hP.norm.pow 2).integrableOn_Icc
  have hPos : ∀ᵐ t ∂(volume.restrict (Set.Icc (-2*T) (2*T)) :
        Measure ℝ), 0 ≤ ‖P t‖^2 :=
    Filter.Eventually.of_forall (fun t => sq_nonneg _)
  have hMono :
    (∫ t in Set.Icc (-T) T, ‖P t‖^2) ≤
      ∫ t in Set.Icc (-2*T) (2*T), ‖P t‖^2 :=
    setIntegral_mono_set hInt hPos (Filter.Eventually.of_forall hSub)
  have hPoint (t : ℝ) : ‖(Y:ℂ)*P t‖^2 = Y^2*‖P t‖^2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hY]
    ring
  calc
    _ = ∫ t in Set.Icc (-T) T, Y^2 * ‖P t‖^2 := by
      apply integral_congr_ae
      filter_upwards with t
      exact hPoint t
    _ = Y^2*(∫ t in Set.Icc (-T) T, ‖P t‖^2) :=
      integral_const_mul _ _
    _ ≤ Y^2*(∫ t in Set.Icc (-2*T) (2*T), ‖P t‖^2) :=
      mul_le_mul_of_nonneg_left hMono (sq_nonneg _)
    _ ≤ Y^2*E :=
      mul_le_mul_of_nonneg_left hOriginalLow (sq_nonneg _)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeFamily -/

section

namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Literal SOURCE03 residual comparison index: one selected nonempty
set of target probes and one selected nonempty set of source probes. -/
abbrev SourceOriginalProbePattern434 (G : Type) (m : ℕ) :=
  Finset (G × Fin m) × Finset (G × Fin m)

/-- The EXACT finite set of designated first-m probe positions in one
block of original big groups; it does not grow with J. -/
noncomputable def sourceOriginalProbeBlock434
    {G : Type} [DecidableEq G] (block : Finset G) (m : ℕ) :
    Finset (G × Fin m) :=
  block.product Finset.univ

/-- The SOURCE residual comparisons are indexed by a nonempty freed
subset of each of the two DISJOINT designated probe blocks.
The raw pattern is not part of this finite family. -/
noncomputable def sourceOriginalTwoBlockProbePatterns434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ) :
    Finset (Finset (G × Fin m) × Finset (G × Fin m)) := by
  classical
  exact ((sourceOriginalProbeBlock434 blockA m).powerset.filter
    Finset.Nonempty).product
      ((sourceOriginalProbeBlock434 blockB m).powerset.filter
        Finset.Nonempty)

/-- The source comparison family has at most 2^(m (s1+s2))
terms, independent of the number J of shared slots. -/
theorem source_original_two_block_probe_pattern_card434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ) :
    (sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card ≤
      2 ^ (m * (blockA.card + blockB.card)) := by
  classical
  let IA := sourceOriginalProbeBlock434 blockA m
  let IB := sourceOriginalProbeBlock434 blockB m
  have hA : (IA.powerset.filter Finset.Nonempty).card ≤
      IA.powerset.card := Finset.card_filter_le _ _
  have hB : (IB.powerset.filter Finset.Nonempty).card ≤
      IB.powerset.card := Finset.card_filter_le _ _
  have hCount :
      (sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card ≤
      2 ^ (IA.card + IB.card) := by
    calc
      _ = (IA.powerset.filter Finset.Nonempty).card *
          (IB.powerset.filter Finset.Nonempty).card := by
            simp [sourceOriginalTwoBlockProbePatterns434, IA, IB,
              Finset.card_product]
      _ ≤ IA.powerset.card * IB.powerset.card := Nat.mul_le_mul hA hB
      _ = 2 ^ (IA.card + IB.card) := by
        simp only [Finset.card_powerset, pow_add]
  have hIA : IA.card = blockA.card * m := by
    simp [IA, sourceOriginalProbeBlock434, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
  have hIB : IB.card = blockB.card * m := by
    simp [IB, sourceOriginalProbeBlock434, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
  have hExp : IA.card + IB.card =
      m * (blockA.card + blockB.card) := by
    rw [hIA, hIB, Nat.mul_add]
    simp only [Nat.mul_comm]
  simpa only [hExp] using hCount
/-- The ORIGINAL source comparison has exactly one pattern for
each ordered pair of NONEMPTY freed probe subsets. No duplicate
index is introduced by this enumeration. -/
theorem source_original_two_block_probe_pattern_mem434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (A B : Finset (G × Fin m)) :
    (A,B) ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m ↔
      A.Nonempty ∧ A ⊆ sourceOriginalProbeBlock434 blockA m ∧
      B.Nonempty ∧ B ⊆ sourceOriginalProbeBlock434 blockB m := by
  classical
  simp [sourceOriginalTwoBlockProbePatterns434,
    Finset.mem_product, Finset.mem_filter, Finset.mem_powerset,
    and_left_comm, and_assoc, and_comm]

/-- EXACT number of literal two-block comparison patterns:
(2^(m s1)-1)(2^(m s2)-1), not merely a bound depending on J. -/
theorem source_original_two_block_probe_pattern_exact_card434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ) :
    (sourceOriginalTwoBlockProbePatterns434 blockA blockB m).card =
      (2 ^ (blockA.card*m) - 1) * (2 ^ (blockB.card*m) - 1) := by
  classical
  let IA := sourceOriginalProbeBlock434 blockA m
  let IB := sourceOriginalProbeBlock434 blockB m
  have hf (I : Finset (G × Fin m)) :
      (I.powerset.filter Finset.Nonempty).card = 2 ^ I.card - 1 := by
    have heq : I.powerset.filter Finset.Nonempty =
        I.powerset.erase ∅ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_erase,
        Finset.nonempty_iff_ne_empty]
      exact and_comm
    rw [heq, Finset.card_erase_of_mem (by simp), Finset.card_powerset]
  have hIA : IA.card = blockA.card * m := by
    simp [IA, sourceOriginalProbeBlock434, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
  have hIB : IB.card = blockB.card * m := by
    simp [IB, sourceOriginalProbeBlock434, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
  calc
    _ = (IA.powerset.filter Finset.Nonempty).card *
        (IB.powerset.filter Finset.Nonempty).card := by
          simp [sourceOriginalTwoBlockProbePatterns434,
            IA,IB,Finset.card_product]
    _ = (2 ^ IA.card - 1)*(2 ^ IB.card - 1) := by rw [hf IA, hf IB]
    _ = _ := by rw [hIA,hIB]

end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalIdealProbeCancellation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Alternating sum on every NONEMPTY subset of a genuine
source03 designated probe block. No extra subset-count loss:
the sum is exactly -1 for each nonempty missing-probe set.
This is the arithmetic inclusion-exclusion sign of the source
comparison family, not an absolute majorant. -/
theorem source_original_probe_nonempty_alternation434
    {α : Type} [DecidableEq α] (U : Finset α) :
    (∑ A ∈ U.powerset.filter Finset.Nonempty,
      (-1 : ℤ)^A.card) = if U.Nonempty then -1 else 0 := by
  classical
  have hfilter :
      U.powerset.filter Finset.Nonempty =
      U.powerset.erase ∅ := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_erase,
      Finset.nonempty_iff_ne_empty]
    tauto
  rw [hfilter]
  have htotal := Finset.sum_powerset_neg_one_pow_card (x:=U)
  have hsum := Finset.sum_erase_add (U.powerset)
    (fun A : Finset α => (-1:ℤ)^A.card)
    (Finset.empty_mem_powerset U)
  by_cases hU : U = ∅
  · subst U
    simp at *
  · have hn : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
    rw [if_pos hn]
    simp [hU] at htotal
    have hsum' :
        (∑ A ∈ U.powerset.erase ∅, (-1:ℤ)^A.card) + 1 = 0 := by
      simpa only [Finset.card_empty, pow_zero] using hsum.trans htotal
    omega
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalIdealMissingProbeCancellation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- Literal SOURCE03 TWO-BLOCK canonical signed comparison
coefficient evaluated against an Efron–Stein pair with the
MISSING probe coordinates U and V. Comparison patterns
with free sets outside U or V vanish on the corresponding
conditional mean-zero probe components. The signed sum
below is exactly one iff BOTH missing sets are nonempty.
No absolute subset-count loss, Fourier character or prime
distribution assumption is used. -/
theorem source_original_canonical_missing_probe_pair_sum434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (U V : Finset (G × Fin m))
    (hU : U ⊆ sourceOriginalProbeBlock434 blockA m)
    (hV : V ⊆ sourceOriginalProbeBlock434 blockB m) :
    (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434
       blockA blockB m,
      if ν.1 ⊆ U ∧ ν.2 ⊆ V
        then (-1:ℤ)^(ν.1.card+ν.2.card) else 0) =
    if U.Nonempty ∧ V.Nonempty then 1 else 0 := by
  classical
  let IA := sourceOriginalProbeBlock434 blockA m
  let IB := sourceOriginalProbeBlock434 blockB m
  let Aset := IA.powerset.filter Finset.Nonempty
  let Bset := IB.powerset.filter Finset.Nonempty
  let a (A : Finset (G × Fin m)) : ℤ :=
    if A ⊆ U then (-1)^A.card else 0
  let b (B : Finset (G × Fin m)) : ℤ :=
    if B ⊆ V then (-1)^B.card else 0
  have hfactor (A B : Finset (G × Fin m)) :
      (if A ⊆ U ∧ B ⊆ V
         then (-1:ℤ)^(A.card+B.card) else 0) =
      a A * b B := by
    dsimp only [a,b]
    by_cases ha : A ⊆ U <;> by_cases hb : B ⊆ V
    <;> simp [ha,hb,pow_add]
  have haSet : Aset.filter (fun A => A ⊆ U) =
        U.powerset.filter Finset.Nonempty := by
    ext A
    simp only [Aset, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hIA, hNE⟩,hAU⟩
      exact ⟨hAU,hNE⟩
    · rintro ⟨hAU,hNE⟩
      exact ⟨⟨hAU.trans hU,hNE⟩,hAU⟩
  have hbSet : Bset.filter (fun B => B ⊆ V) =
        V.powerset.filter Finset.Nonempty := by
    ext B
    simp only [Bset, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hIB, hNE⟩,hBV⟩
      exact ⟨hBV,hNE⟩
    · rintro ⟨hBV,hNE⟩
      exact ⟨⟨hBV.trans hV,hNE⟩,hBV⟩
  have hASum : (∑ A ∈ Aset, a A) =
        if U.Nonempty then -1 else 0 := by
    dsimp only [a]
    rw [← Finset.sum_filter, haSet]
    exact source_original_probe_nonempty_alternation434 U
  have hBSum : (∑ B ∈ Bset, b B) =
        if V.Nonempty then -1 else 0 := by
    dsimp only [b]
    rw [← Finset.sum_filter, hbSet]
    exact source_original_probe_nonempty_alternation434 V
  calc
    _ = ∑ A ∈ Aset, ∑ B ∈ Bset, a A * b B := by
      change (∑ ν ∈ Aset.product Bset,
         if ν.1 ⊆ U ∧ ν.2 ⊆ V then
           (-1:ℤ)^(ν.1.card+ν.2.card) else 0) = _
      calc
        _ = ∑ A ∈ Aset, ∑ B ∈ Bset,
            (if A ⊆ U ∧ B ⊆ V then
              (-1:ℤ)^(A.card+B.card) else 0) :=
            Finset.sum_product Aset Bset _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro A hA
          apply Finset.sum_congr rfl
          intro B hB
          exact hfactor A B
    _ = (∑ A ∈ Aset, a A) * (∑ B ∈ Bset, b B) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.mul_sum]
    _ = _ := by
      rw [hASum,hBSum]
      by_cases hu : U.Nonempty <;> by_cases hv : V.Nonempty
      <;> simp [hu,hv]

/-- On the actual SOURCE03 canonical raw-plus-signed-comparison
family, the algebraic residual coefficient is EXACTLY the
indicator that at least one block has NO missing probe.
The SOURCE ideal theorem then needs only quantitative estimates
of the all-probe components and actual character/cell
approximation errors; those remain independent analytical tasks. -/
theorem source_original_canonical_raw_comparison_residual434
    {G : Type} [DecidableEq G]
    (blockA blockB : Finset G) (m : ℕ)
    (U V : Finset (G × Fin m))
    (hU : U ⊆ sourceOriginalProbeBlock434 blockA m)
    (hV : V ⊆ sourceOriginalProbeBlock434 blockB m) :
    (1:ℤ) -
      (∑ ν ∈ sourceOriginalTwoBlockProbePatterns434
         blockA blockB m,
       if ν.1 ⊆ U ∧ ν.2 ⊆ V
         then (-1:ℤ)^(ν.1.card+ν.2.card) else 0) =
    if U.Nonempty ∧ V.Nonempty then 0 else 1 := by
  rw [source_original_canonical_missing_probe_pair_sum434
    blockA blockB m U V hU hV]
  by_cases hu : U.Nonempty <;> by_cases hv : V.Nonempty
  <;> simp [hu,hv]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingSharpFraction -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- SHARP uniform-in-J combinatorial suppression of the
actual SOURCE03 Hoeffding component: among every M-coordinate
set of j occupied slots, prescribing m particular probes
to be present and ell particular trailing coordinates absent
has probability at most 1 / choose(m+ell,m), with NO lower
bound on M beyond m+ell≤M. This improves the source's
sufficient large-M estimate 2 ell^ell / m^ell.
It follows directly from the genuine Vandermonde identity:
choose(M,j) counts all ways to choose the first m of the
m+ell designated slots and the remaining j-m outside them. -/
theorem source_original_hoeffding_vandermonde_sharp434
    (M m ell j : ℕ)
    (hM : m+ell ≤ M) (hmj : m ≤ j) :
    (m+ell).choose m * (M-(m+ell)).choose (j-m) ≤
      M.choose j := by
  let R := M-(m+ell)
  have hMR : m+ell+R = M := Nat.add_sub_of_le hM
  have hj : m + (j-m) = j := Nat.add_sub_of_le hmj
  have hmem : (m,j-m) ∈ Finset.HasAntidiagonal.antidiagonal j := by
    exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hj
  have hsum : (m+ell).choose m * R.choose (j-m) ≤
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal j,
        (m+ell).choose ij.1 * R.choose ij.2 := by
    have hs := Finset.single_le_sum
      (s := Finset.HasAntidiagonal.antidiagonal j)
      (f := fun ij : ℕ × ℕ =>
        (m+ell).choose ij.1 * R.choose ij.2)
      (by intro ij hij; exact Nat.zero_le _)
      hmem
    exact hs
  rw [← Nat.add_choose_eq] at hsum
  simpa [R,hMR] using hsum

/-- The true Hoeffding cardinal ratio is ≤1/choose(m+ell,m).
This estimate is independent of M=J+ell and of component degree j
so it tensorizes over all source BIG groups. -/
theorem source_original_hoeffding_fraction_sharp434
    (M m ell j : ℕ)
    (hM : m+ell ≤ M) (hmj : m ≤ j) (hjM : j ≤ M) :
    ((M-(m+ell)).choose (j-m) : ℝ) /
        (M.choose j : ℝ) ≤
      1 / (((m+ell).choose m : ℕ) : ℝ) := by
  have hNum := source_original_hoeffding_vandermonde_sharp434
    M m ell j hM hmj
  have hden : (0:ℝ) < (M.choose j : ℝ) := by
    exact_mod_cast Nat.choose_pos hjM
  have hcomp : (0:ℝ) <
      ((m+ell).choose m : ℕ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right m ell)
  have hReal : (((m+ell).choose m:ℕ):ℝ) *
      (((M-(m+ell)).choose (j-m) : ℕ):ℝ) ≤
      ((M.choose j:ℕ):ℝ) := by exact_mod_cast hNum
  have hsmall :
      (((M-(m+ell)).choose (j-m):ℕ):ℝ) ≤
      (M.choose j : ℝ) / (((m+ell).choose m : ℕ):ℝ) :=
    (le_div_iff₀ hcomp).2 (by
      simpa [mul_comm] using hReal)
  apply (div_le_iff₀ hden).2
  simpa [div_eq_mul_inv, mul_comm] using hsmall
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingGroupTensor -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- Source survivor count at degree j, zero if j< m:
do not use a truncated natural subtraction as actual count. -/
def sourceOriginalHoeffdingSurvivor434
    (M m ell j : ℕ) : ℕ :=
  if m ≤ j then (M-(m+ell)).choose (j-m) else 0

/-- Every source survivor cardinal is bounded by the total
j-subset count, divided by choose(m+ell,m). -/
theorem source_original_hoeffding_survivor_group434
    (M m ell j : ℕ) (hM : m+ell ≤ M) :
    sourceOriginalHoeffdingSurvivor434 M m ell j *
       (m+ell).choose m ≤ M.choose j := by
  unfold sourceOriginalHoeffdingSurvivor434
  by_cases hmj : m ≤ j
  · simp only [if_pos hmj]
    simpa [Nat.mul_comm] using
      source_original_hoeffding_vandermonde_sharp434
        M m ell j hM hmj
  · simp [hmj]

theorem source_original_hoeffding_choose_probe_growth434
    (m ell : ℕ) (hell : 1 ≤ ell) :
    m+1 ≤ (m+ell).choose m := by
  have h1 : m+1 ≤ m+ell := Nat.add_le_add_left hell m
  have hchoose :
      (m+1).choose m = m+1 := by
    rw [Nat.choose_symm_add]
    simp
  calc
    m+1 = (m+1).choose m := hchoose.symm
    _ ≤ (m+ell).choose m := Nat.choose_le_choose m h1
/-- Pointwise tensor estimate on the original BIG group
Hoeffding degrees; no product assumption on the energy. -/
theorem source_original_hoeffding_all_group_tensor434
    {G : Type} [Fintype G]
    (M j : G → ℕ) (m ell : ℕ)
    (hM : ∀ g, m+ell ≤ M g) :
    (∏ g : G,
      (sourceOriginalHoeffdingSurvivor434
          (M g) m ell (j g) : ℝ)) *
      (((m+ell).choose m : ℕ) : ℝ)^(Fintype.card G) ≤
    (∏ g : G, ((M g).choose (j g) : ℝ)) := by
  have hbound (g : G) :
      ((sourceOriginalHoeffdingSurvivor434
          (M g) m ell (j g) : ℕ):ℝ) *
      (((m+ell).choose m : ℕ):ℝ) ≤
      (((M g).choose (j g):ℕ):ℝ) := by
    exact_mod_cast source_original_hoeffding_survivor_group434
      (M g) m ell (j g) (hM g)
  have hprod :
      (∏ g : G,
        (sourceOriginalHoeffdingSurvivor434
           (M g) m ell (j g):ℝ) *
        (((m+ell).choose m : ℕ):ℝ)) ≤
      (∏ g : G, ((M g).choose (j g):ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro g hg
      positivity
    · intro g hg
      exact hbound g
  simpa only [Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ] using hprod
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingBlockEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- Original BIG group selection: in the probe block, retain
only components using ALL marked probes and no trailing slots;
outside the block, retain every Hoeffding coordinate subset.
No independence across groups is assumed. -/
def sourceOriginalHoeffdingBlockWeight434
    {G : Type} [DecidableEq G]
    (block : Finset G) (M j : G → ℕ) (m ell : ℕ)
    (g : G) : ℝ :=
  if g ∈ block then
    (sourceOriginalHoeffdingSurvivor434 (M g) m ell (j g):ℝ)
  else ((M g).choose (j g):ℝ)
/-- Exact combinatorial suppression of one SOURCE03 probe
block, with all OTHER BIG group degrees unconstrained.
The bound is uniform in J and the fixed background group degrees. -/
theorem source_original_hoeffding_block_tensor434
    {G : Type} [Fintype G] [DecidableEq G]
    (block : Finset G)
    (M j : G → ℕ) (m ell : ℕ)
    (hM : ∀ g, m+ell ≤ M g) :
    (∏ g : G,
      sourceOriginalHoeffdingBlockWeight434 block M j m ell g) *
      (((m+ell).choose m : ℕ) : ℝ)^block.card ≤
    (∏ g : G, ((M g).choose (j g):ℝ)) := by
  let C : ℝ := (((m+ell).choose m : ℕ) : ℝ)
  let W := sourceOriginalHoeffdingBlockWeight434 block M j m ell
  have hgroup (g : G) :
      W g * (if g ∈ block then C else 1) ≤
        ((M g).choose (j g):ℝ) := by
    by_cases hg : g ∈ block
    · simp only [W,sourceOriginalHoeffdingBlockWeight434,
        if_pos hg]
      dsimp only [C]
      exact_mod_cast source_original_hoeffding_survivor_group434
        (M g) m ell (j g) (hM g)
    · simp [W,sourceOriginalHoeffdingBlockWeight434,hg]
  have hprod :
      (∏ g : G, W g * (if g ∈ block then C else 1)) ≤
        (∏ g : G, ((M g).choose (j g):ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro g hg
      dsimp [W,sourceOriginalHoeffdingBlockWeight434]
      split_ifs <;> positivity
    · intro g hg
      exact hgroup g
  calc
    (∏ g : G, W g) * C^block.card =
        (∏ g : G, W g) *
          (∏ g : G, if g ∈ block then C else 1) := by
            simp [Finset.prod_ite,Finset.prod_const]
    _ = (∏ g : G, W g * (if g ∈ block then C else 1)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ _ := hprod

/-- Arbitrarily CORRELATED nonnegative Hoeffding energies
across all BIG groups still obey the probe-block suppression.
This is the exact useful form for the source symmetrized ideal
operator, after Parseval in the orthogonal degree components. -/
theorem source_original_hoeffding_block_energy434
    {G : Type} [Fintype G] [DecidableEq G]
    (block : Finset G) (M : G → ℕ) (m ell : ℕ)
    (hM : ∀ g, m+ell ≤ M g)
    (E : ((g : G) → Fin (M g+1)) → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G,
        sourceOriginalHoeffdingBlockWeight434 block M
          (fun g => (j g).val) m ell g) * E j) *
      (((m+ell).choose m : ℕ):ℝ)^block.card ≤
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, ((M g).choose (j g).val:ℝ)) * E j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hpoint := source_original_hoeffding_block_tensor434
    block M (fun g => (j g).val) m ell hM
  calc
    _ = ((∏ g : G,
      sourceOriginalHoeffdingBlockWeight434 block M
       (fun g => (j g).val) m ell g) *
      (((m+ell).choose m : ℕ):ℝ)^block.card) * E j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpoint (hE j)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingBlockSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 5700000

/-- Original source Hoeffding orthogonal degree-energy estimate
with a concrete full-probe saving of (m+1)^(-number of groups).
NO group-factorization of the squared energies is assumed. -/
theorem source_original_hoeffding_block_energy_probe_power434
    {G : Type} [Fintype G] [DecidableEq G]
    (block : Finset G) (M : G → ℕ) (m ell : ℕ)
    (hM : ∀ g, m+ell ≤ M g) (hell : 1 ≤ ell)
    (E : ((g : G) → Fin (M g+1)) → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, sourceOriginalHoeffdingBlockWeight434 block M
         (fun g => (j g).val) m ell g) * E j) *
      ((m+1:ℕ):ℝ)^block.card ≤
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, ((M g).choose (j g).val:ℝ)) * E j) := by
  have hchoose := source_original_hoeffding_choose_probe_growth434
    m ell hell
  have hpow : (((m+1:ℕ):ℝ)^block.card) ≤
      ((((m+ell).choose m : ℕ):ℝ)^block.card) := by
    gcongr
  have hweight (j : ((g : G) → Fin (M g+1))) :
      0 ≤ (∏ g : G,
        sourceOriginalHoeffdingBlockWeight434 block M
          (fun g => (j g).val) m ell g) := by
    apply Finset.prod_nonneg
    intro g hg
    dsimp [sourceOriginalHoeffdingBlockWeight434]
    split_ifs <;> positivity
  have hsum : 0 ≤ (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, sourceOriginalHoeffdingBlockWeight434 block M
        (fun g => (j g).val) m ell g) * E j) :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hweight j) (hE j))
  calc
    _ ≤ (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, sourceOriginalHoeffdingBlockWeight434 block M
        (fun g => (j g).val) m ell g) * E j) *
      ((((m+ell).choose m : ℕ):ℝ)^block.card) :=
        mul_le_mul_of_nonneg_left hpow hsum
    _ ≤ _ := source_original_hoeffding_block_energy434
      block M m ell hM E hE
/-- The actual logarithmic number of BIG groups and fixed m
turn m+1 suppression per group into ANY prescribed L^-A.
This source scaling argument is uniform in J and contains
NO prime-character or ideal-operator cancellation claim. -/
theorem source_original_hoeffding_log_power434
    (L A c : ℝ) (m s : ℕ)
    (hL : 1 ≤ L) (hc : 0 ≤ c) (hm : 1 ≤ m)
    (hcount : c * Real.log L ≤ (s:ℝ))
    (hbudget : A ≤ c * Real.log ((m+1:ℕ):ℝ)) :
    L^A ≤ (((m+1:ℕ):ℝ)^s) := by
  have hLpos : 0 < L := by linarith
  have hml : (1:ℝ) < (m+1:ℕ) := by
    exact_mod_cast (by omega : 1 < m+1)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogm : 0 ≤ Real.log ((m+1:ℕ):ℝ) :=
    Real.log_nonneg hml.le
  have h1 := mul_le_mul_of_nonneg_right hbudget hlogL
  have h2 := mul_le_mul_of_nonneg_right hcount hlogm
  have hlog : Real.log L*A ≤
      Real.log ((m+1:ℕ):ℝ)*(s:ℝ) := by
    nlinarith [h1,h2]
  calc
    L^A = Real.exp (Real.log L*A) :=
      Real.rpow_def_of_pos hLpos A
    _ ≤ Real.exp (Real.log ((m+1:ℕ):ℝ)*(s:ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (((m+1:ℕ):ℝ)^s) := by
      rw [← Real.rpow_def_of_pos (by linarith : (0:ℝ)<(m+1:ℕ)) (s:ℝ)]
      exact Real.rpow_natCast _ _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingActualLogEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The genuine source03 two-block Hoeffding saving on the
finite nonnegative degree-energy distribution, without
factorization of energies between BIG groups and uniformly
in the shared-slot number J. Requires source symmetric
exchangeability when identifying actual L² squared norms with
these degree energies; that identification is not postulated
or proved by this standalone theorem. -/
theorem source_original_hoeffding_block_log_energy434
    {G : Type} [Fintype G] [DecidableEq G]
    (block : Finset G) (M : G → ℕ) (m ell : ℕ)
    (hM : ∀ g, m+ell ≤ M g) (hell : 1 ≤ ell)
    (L A c : ℝ) (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hm : 1 ≤ m)
    (hcount : c*Real.log L ≤ (block.card:ℝ))
    (hbudget : A ≤ c*Real.log ((m+1:ℕ):ℝ))
    (E : ((g : G) → Fin (M g+1)) → ℝ)
    (hE : ∀ j, 0 ≤ E j) :
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, sourceOriginalHoeffdingBlockWeight434
        block M (fun g => (j g).val) m ell g) * E j) *
      L^A ≤
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, ((M g).choose (j g).val:ℝ)) * E j) := by
  have hp := source_original_hoeffding_log_power434
    L A c m block.card hL hc hm hcount hbudget
  have hactual := source_original_hoeffding_block_energy_probe_power434
    block M m ell hM hell E hE
  have hcoeff (j : ((g : G) → Fin (M g+1))) :
      0 ≤ (∏ g : G,
        sourceOriginalHoeffdingBlockWeight434 block M
          (fun g => (j g).val) m ell g) := by
    apply Finset.prod_nonneg
    intro g hg
    dsimp [sourceOriginalHoeffdingBlockWeight434]
    split_ifs <;> positivity
  have hsurv : 0 ≤
    (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, sourceOriginalHoeffdingBlockWeight434
        block M (fun g => (j g).val) m ell g) * E j) :=
    Finset.sum_nonneg
      (fun j hj => mul_nonneg (hcoeff j) (hE j))
  calc
    _ ≤ (∑ j : ((g : G) → Fin (M g+1)),
      (∏ g : G, sourceOriginalHoeffdingBlockWeight434
        block M (fun g => (j g).val) m ell g) * E j) *
      ((m+1:ℕ):ℝ)^block.card :=
        mul_le_mul_of_nonneg_left hp hsurv
    _ ≤ _ := hactual
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigCoordinateMean -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Actual iid BIG-prime coordinate conditional average: mu
can be instantiated as the source's exact reciprocal-prime
mass 1/(p V_g). It is not an abstract projection axiom. -/
noncomputable def sourceOriginalCoordinateMean434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (i : Fin M)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) : ℂ :=
  ∑ p : P, mu p * f (Function.update x i p)

/-- Conditional averaging preserves an i-independent test,
provided the actual one-prime law is normalized. -/
theorem source_original_coordinate_mean_invariant434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ)
    (hfi : ∀ x p, f (Function.update x i p) = f x)
    (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i f x = f x := by
  unfold sourceOriginalCoordinateMean434
  simp_rw [hfi]
  rw [← Finset.sum_mul, hmu]
  ring

/-- SOURCE-REAL conditional averaging is an exact algebraic
projection; it uses only the genuine normalization of mu. -/
theorem source_original_coordinate_mean_idempotent434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ)
    (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (sourceOriginalCoordinateMean434 mu i f) x =
    sourceOriginalCoordinateMean434 mu i f x := by
  unfold sourceOriginalCoordinateMean434
  simp_rw [Function.update_idem]
  rw [← Finset.sum_mul, hmu]
  ring

/-- The actual coordinate mean-zero component has zero
conditional average over precisely its marked prime slot.
This is the original Efron–Stein annihilation mechanism. -/
theorem source_original_coordinate_centered_mean_zero434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ)
    (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (fun z => f z - sourceOriginalCoordinateMean434 mu i f z)
      x = 0 := by
  unfold sourceOriginalCoordinateMean434
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have h := source_original_coordinate_mean_idempotent434
    mu hmu i f x
  dsimp [sourceOriginalCoordinateMean434] at h
  rw [h]
  exact sub_self _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigCoordinateCommutation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The ACTUAL original iid BIG prime one-coordinate averages
commute for distinct slot positions. No assumption that the
complex input test f is a product of individual primes.
Each coordinate uses the same source reciprocal-prime law mu. -/
theorem source_original_coordinate_means_commute434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (i j : Fin M) (hij : i ≠ j)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
       (sourceOriginalCoordinateMean434 mu j f) x =
    sourceOriginalCoordinateMean434 mu j
       (sourceOriginalCoordinateMean434 mu i f) x := by
  unfold sourceOriginalCoordinateMean434
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro p hp
  rw [Function.update_comm hij]
  ring

/-- Source one-coordinate averaging is complex-linear even when
the global tuple test depends on all other shared/free slots. -/
theorem source_original_coordinate_mean_linear434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (i : Fin M)
    (a b : ℂ) (f g : (Fin M → P) → ℂ)
    (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
        (fun z => a*f z+b*g z) x =
    a*sourceOriginalCoordinateMean434 mu i f x +
    b*sourceOriginalCoordinateMean434 mu i g x := by
  unfold sourceOriginalCoordinateMean434
  calc
    _ = (∑ p : P, a*(mu p * f (Function.update x i p))) +
        (∑ p : P, b*(mu p * g (Function.update x i p))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
    _ = _ := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigPermutationMean -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The original BIG slot permutation transports a resampling
of physical indexed target slot i to its precise inverse image.
Neither numeric prime labels nor the product law change. -/
theorem source_original_big_update_permutation434
    {P : Type} {M : ℕ}
    (σ : Equiv.Perm (Fin M)) (i : Fin M)
    (x : Fin M → P) (p : P) :
    (fun j => Function.update x i p (σ j)) =
      Function.update (fun j => x (σ j)) (σ.symm i) p := by
  classical
  funext j
  simp only [Function.update_apply]
  by_cases h : σ j = i
  · have heq : j = σ.symm i := by
      calc
        j = σ.symm (σ j) := (σ.symm_apply_apply j).symm
        _ = _ := by rw [h]
    simp [h,heq]
  · have hne : j ≠ σ.symm i := by
      intro heq
      apply h
      rw [heq, σ.apply_symm_apply]
    simp [h,hne]

/-- The TRUE iid reciprocal-prime coordinate expectation
is covariant under the independently drawn original BIG
source/target permutation. Works for an ARBITRARY complex
tuple observable, not only separable prime-character tests. -/
theorem source_original_big_coordinate_permutation_covariant434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (σ : Equiv.Perm (Fin M)) (i : Fin M)
    (f : (Fin M → P) → ℂ)
    (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (fun z => f (fun j => z (σ j))) x =
    sourceOriginalCoordinateMean434 mu (σ.symm i)
      f (fun j => x (σ j)) := by
  unfold sourceOriginalCoordinateMean434
  apply Finset.sum_congr rfl
  intro p _
  change mu p * f (fun j => Function.update x i p (σ j)) =
    mu p * f (Function.update (fun j => x (σ j)) (σ.symm i) p)
  rw [source_original_big_update_permutation434 σ i x p]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPrimeHarmonicProduct -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Literal source BIG prime law, as a probability mass on
the FINITE labelled prime support P. This preserves p and V,
not a uniform or asymptotic replacement. -/
noncomputable def sourceOriginalHarmonicPrimeMu434
    {P : Type} (prime : P → ℕ) (V : ℝ) (p : P) : ℝ :=
  (1 / (prime p:ℝ)) / V

/-- The ORIGINAL normalized reciprocal-prime law really sums
to 1 whenever its V is the original reciprocal-prime mass. -/
theorem source_original_harmonic_prime_normalized434
    {P : Type} [Fintype P]
    (prime : P → ℕ) (V : ℝ) (hV : 0 < V)
    (hEq : V = ∑ p : P, 1/(prime p:ℝ)) :
    (∑ p : P, sourceOriginalHarmonicPrimeMu434 prime V p) = 1 := by
  unfold sourceOriginalHarmonicPrimeMu434
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simp only [one_mul, one_div] at hEq ⊢
  rw [← hEq]
  exact mul_inv_cancel₀ (ne_of_gt hV)

/-- The actual reciprocal-prime law is nonnegative on genuine
BIG prime supports; no PNT or Siegel–Walfisz is needed here. -/
theorem source_original_harmonic_prime_nonneg434
    {P : Type} (prime : P → ℕ)
    (V : ℝ) (hV : 0 < V) (p : P) :
    0 ≤ sourceOriginalHarmonicPrimeMu434 prime V p := by
  unfold sourceOriginalHarmonicPrimeMu434
  positivity

/-- The original independently indexed full BIG group prime
mass: each position carries the literal 1/(p V) law, allowing
repeated numerical primes in different indexed slots. -/
noncomputable def sourceOriginalHarmonicProductMass434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ) (V : ℝ)
    (x : Fin M → P) : ℝ :=
  ∏ i : Fin M, sourceOriginalHarmonicPrimeMu434 prime V (x i)

/-- The actual full BIG product measure has mass exactly one
without any replacement of prime weights or distinctness gate. -/
theorem source_original_harmonic_product_mass_one434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ)
    (V : ℝ) (hV : 0 < V)
    (hEq : V = ∑ p : P, 1/(prime p:ℝ)) :
    (∑ x : Fin M → P,
      sourceOriginalHarmonicProductMass434 prime V x) = 1 := by
  unfold sourceOriginalHarmonicProductMass434
  rw [← Fintype.prod_sum]
  simp [source_original_harmonic_prime_normalized434 prime V hV hEq]

/-- Original source BIG labelled-product weight is invariant
under EVERY independent endpoint permutation; this is the
measure-preservation property needed for true Hilbert orbit
equality, not an assumed exchangeability axiom. -/
theorem source_original_harmonic_mass_permutation434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ) (V : ℝ)
    (σ : Equiv.Perm (Fin M)) (x : Fin M → P) :
    sourceOriginalHarmonicProductMass434 prime V
       (fun i => x (σ i)) =
    sourceOriginalHarmonicProductMass434 prime V x := by
  unfold sourceOriginalHarmonicProductMass434
  exact Fintype.prod_equiv σ
    (fun i => sourceOriginalHarmonicPrimeMu434 prime V (x (σ i)))
    (fun i => sourceOriginalHarmonicPrimeMu434 prime V (x i))
    (fun _ => rfl)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigResamplingBalance -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact original BIG product law for arbitrary real one-prime
mass; instantiate mu with the genuine reciprocal-prime weight.
Repeated numerical primes are explicitly allowed. -/
noncomputable def sourceOriginalRealBigProductMass434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (x : Fin M → P) : ℝ :=
  ∏ j : Fin M, mu (x j)

/-- A full original source BIG product mass is exactly its
single marked prime factor times the product of all other
independently sampled slots, WITHOUT a uniform-prime proxy. -/
theorem source_original_mass_single_prime_factor434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (i : Fin M) (x : Fin M → P) :
    sourceOriginalRealBigProductMass434 mu x =
      mu (x i) *
        (∏ j ∈ (Finset.univ : Finset (Fin M)).erase i,
          mu (x j)) := by
  unfold sourceOriginalRealBigProductMass434
  exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin M))
    (fun j => mu (x j)) (Finset.mem_univ i)).symm
/-- Resampling one ACTUAL source BIG prime leaves the product
of every other source prime mass unchanged. -/
theorem source_original_mass_rest_resample434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (i : Fin M) (x : Fin M → P) (p : P) :
    (∏ j ∈ (Finset.univ : Finset (Fin M)).erase i,
      mu (Function.update x i p j)) =
    (∏ j ∈ (Finset.univ : Finset (Fin M)).erase i,
      mu (x j)) := by
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update_apply, hne]

/-- Exact microscopic detailed balance for REAL source BIG
resampling under product harmonic measure: probability of
the ordered pair (original x, new p) is invariant under
exchanging the old prime x_i with its freshly resampled p.
This is the analytic foundation for self-adjoint conditional
expectation E_i in the TRUE weighted L2 space. -/
theorem source_original_big_resampling_detailed_balance434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (i : Fin M) (x : Fin M → P) (p : P) :
    sourceOriginalRealBigProductMass434 mu x * mu p =
    sourceOriginalRealBigProductMass434 mu
      (Function.update x i p) * mu (x i) := by
  let R : ℝ := ∏ j ∈ (Finset.univ : Finset (Fin M)).erase i,
      mu (x j)
  have hx : sourceOriginalRealBigProductMass434 mu x =
      mu (x i) * R :=
    source_original_mass_single_prime_factor434 mu i x
  have hxp :
      sourceOriginalRealBigProductMass434 mu
         (Function.update x i p) = mu p * R := by
    rw [source_original_mass_single_prime_factor434
      mu i (Function.update x i p)]
    rw [source_original_mass_rest_resample434 mu i x p]
    simp only [Function.update_apply, ↓reduceIte]
    rfl
  rw [hx,hxp]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigResamplingSwap -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Swapping one true source BIG label with one independently
resampled prime is an involution of the finite physical
sample space. All original indexed prime slots remain distinct
coordinates even if their numerical prime values coincide. -/
noncomputable def sourceOriginalPrimeResampleSwap434
    {P : Type} {M : ℕ} (i : Fin M) :
    ((Fin M → P) × P) ≃ ((Fin M → P) × P) where
  toFun t := (Function.update t.1 i t.2, t.1 i)
  invFun t := (Function.update t.1 i t.2, t.1 i)
  left_inv := by
    rintro ⟨x,p⟩
    apply Prod.ext
    · change Function.update (Function.update x i p) i (x i) = x
      funext j
      by_cases hj : j = i
      · subst j
        simp [Function.update_apply]
      · simp [Function.update_apply,hj]
    · simp [Function.update_apply]
  right_inv := by
    rintro ⟨x,p⟩
    apply Prod.ext
    · change Function.update (Function.update x i p) i (x i) = x
      funext j
      by_cases hj : j = i
      · subst j
        simp [Function.update_apply]
      · simp [Function.update_apply,hj]
    · simp [Function.update_apply]

/-- At every point the TRUE product source BIG prime mass,
including the density of the NEW prime, is unchanged by
the swap map. This is the exact detailed-balance identity
for the physical resampling kernel. -/
theorem source_original_big_resample_swap_preserves_mass434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (i : Fin M) (t : (Fin M → P) × P) :
    sourceOriginalRealBigProductMass434 mu
      (sourceOriginalPrimeResampleSwap434 i t).1 *
      mu ((sourceOriginalPrimeResampleSwap434 i t).2) =
    sourceOriginalRealBigProductMass434 mu t.1 * mu t.2 := by
  rcases t with ⟨x,p⟩
  change sourceOriginalRealBigProductMass434 mu
    (Function.update x i p) * mu (x i) =
    sourceOriginalRealBigProductMass434 mu x * mu p
  exact (source_original_big_resampling_detailed_balance434 mu i x p).symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigResamplingSymmetry -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- Source TRUE two-endpoint resampling pairing. This is a
finite Markov coupling under the actual iid BIG prime law,
not an assumed symmetric probability kernel. -/
noncomputable def sourceOriginalResamplingPairing434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ) (i : Fin M)
    (F : (Fin M → P) → (Fin M → P) → ℂ) : ℂ :=
  ∑ x : Fin M → P, ∑ p : P,
    ((sourceOriginalRealBigProductMass434 mu x * mu p):ℂ) *
      F x (Function.update x i p)

/-- Swapping the real old and freshly resampled labelled BIG
primes leaves the entire two-endpoint source coupling
unchanged even for ARBITRARY complex tests F(x,z).
This is a true physical detailed-balance / reversal theorem. -/
theorem source_original_resampling_pairing_symmetric434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ) (i : Fin M)
    (F : (Fin M → P) → (Fin M → P) → ℂ) :
    sourceOriginalResamplingPairing434 mu i F =
    sourceOriginalResamplingPairing434 mu i
      (fun x z => F z x) := by
  let T := (Fin M → P) × P
  let e := sourceOriginalPrimeResampleSwap434 (P := P) i
  let G : T → ℂ := fun t =>
    ((sourceOriginalRealBigProductMass434 mu t.1 * mu t.2):ℂ) *
      F t.1 (Function.update t.1 i t.2)
  have hflip (t : T) :
      G (e t) =
      ((sourceOriginalRealBigProductMass434 mu t.1 * mu t.2):ℂ) *
        F (Function.update t.1 i t.2) t.1 := by
    rcases t with ⟨x,p⟩
    have hr := source_original_big_resampling_detailed_balance434
      mu i x p
    have hu : Function.update (Function.update x i p) i
        (x i) = x := by
      funext j
      by_cases hj : j = i
      · subst j
        simp [Function.update_apply]
      · simp [Function.update_apply,hj]
    change
      ((sourceOriginalRealBigProductMass434 mu
        (Function.update x i p) * mu (x i)):ℂ) *
         F (Function.update x i p)
           (Function.update (Function.update x i p) i (x i)) =
      ((sourceOriginalRealBigProductMass434 mu x * mu p):ℂ) *
         F (Function.update x i p) x
    rw [hu]
    simpa only [Complex.ofReal_mul] using
      congrArg (fun r : ℝ =>
        (r:ℂ) * F (Function.update x i p) x) hr.symm
  unfold sourceOriginalResamplingPairing434
  calc
    (∑ x : Fin M → P, ∑ p : P,
      ((sourceOriginalRealBigProductMass434 mu x * mu p):ℂ) *
        F x (Function.update x i p)) =
      ∑ t : T, G t := (Fintype.sum_prod_type G).symm
    _ = ∑ t : T, G (e t) := (Equiv.sum_comp e G).symm
    _ = ∑ x : Fin M → P, ∑ p : P,
      ((sourceOriginalRealBigProductMass434 mu x * mu p):ℂ) *
        F (Function.update x i p) x := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro p _
      exact hflip (x,p)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigWeightedAdjoint -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The TRUE weighted complex BIG-slot L2 pairing under iid
real source prime masses, with the exact product law.
The mass is not assumed uniform or positive in the identity. -/
noncomputable def sourceOriginalBigWeightedPairing434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (f g : (Fin M → P) → ℂ) : ℂ :=
  ∑ x : Fin M → P,
    (sourceOriginalRealBigProductMass434 mu x:ℂ) *
      star (f x) * g x

/-- The first endpoint averaged physical BIG pairing is
EXACTLY the real reversible two-point source coupling. -/
theorem source_original_big_left_average_pairing434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ) (i : Fin M)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
      (sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f)
      g =
    sourceOriginalResamplingPairing434 mu i
      (fun x z => star (f z) * g x) := by
  unfold sourceOriginalBigWeightedPairing434
    sourceOriginalResamplingPairing434
    sourceOriginalCoordinateMean434
  apply Finset.sum_congr rfl
  intro x _
  have hc :
      star (∑ p : P,
        (mu p:ℂ) * f (Function.update x i p)) =
      ∑ p : P, (mu p:ℂ) *
        star (f (Function.update x i p)) := by
    rw [star_sum]
    simp_rw [star_mul]
    simp [Complex.star_def, Complex.conj_ofReal, mul_comm]
  rw [hc]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  push_cast
  ring

/-- The second endpoint averaged source pairing uses the
SAME coupled resampling mass and ordinary product transpose. -/
theorem source_original_big_right_average_pairing434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ) (i : Fin M)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu f
      (sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i g) =
    sourceOriginalResamplingPairing434 mu i
      (fun x z => star (f x) * g z) := by
  unfold sourceOriginalBigWeightedPairing434
    sourceOriginalResamplingPairing434
    sourceOriginalCoordinateMean434
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  push_cast
  ring

/-- ACTUAL product-harmonic-measure conditional expectation
is SELF-ADJOINT in the TRUE weighted complex L2 Hilbert
pairing; follows from checked microscopic BIG detailed balance,
not an assumed orthogonality of Hoeffding components. -/
theorem source_original_big_coordinate_selfadjoint434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ) (i : Fin M)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
      (sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f)
      g =
    sourceOriginalBigWeightedPairing434 mu f
      (sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i g) := by
  rw [source_original_big_left_average_pairing434,
    source_original_big_right_average_pairing434]
  exact source_original_resampling_pairing_symmetric434 mu i
    (fun x z => star (f z) * g x)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigCoordinateOrthogonal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Original normalisation of real reciprocal-prime probabilities
makes each exact coordinate mean E_i an orthogonal PROJECTION in
the true weighted complex pairing. The orthogonality is to the
true centered residual f-E_i f, NOT a manufactured degree energy. -/
theorem source_original_big_one_coordinate_orthogonal434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
      (sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f)
      (fun x => f x -
        sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f x) =
    0 := by
  let E := sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f
  have hmuC : (∑ p : P, (mu p:ℂ)) = 1 := by exact_mod_cast hmu
  have hproj : sourceOriginalCoordinateMean434
      (fun p => (mu p:ℂ)) i E = E := by
    funext x
    exact source_original_coordinate_mean_idempotent434
      (fun p => (mu p:ℂ)) hmuC i f x
  have hs := source_original_big_coordinate_selfadjoint434
    mu i E f
  rw [hproj] at hs
  calc
    _ = sourceOriginalBigWeightedPairing434 mu E f -
        sourceOriginalBigWeightedPairing434 mu E E := by
          unfold sourceOriginalBigWeightedPairing434
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          dsimp [E]
          ring
    _ = 0 := by rw [hs]; exact sub_self _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigPermutationEnergy -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9500000

/-- The original source BIG-coordinate permutation is an
actual bijection on ordered physical prime lists, including
repeated numerical prime labels. -/
noncomputable def sourceOriginalBigRelabelEquiv434
    {P : Type} {M : ℕ}
    (σ : Equiv.Perm (Fin M)) :
    (Fin M → P) ≃ (Fin M → P) where
  toFun x := fun j => x (σ j)
  invFun x := fun j => x (σ.symm j)
  left_inv := by
    intro x
    funext j
    simp
  right_inv := by
    intro x
    funext j
    simp

/-- Exact actual iid BIG product mass invariance under the
original independently drawn source or target permutations.
This holds for the literal reciprocal-prime mu(p)=1/(pV),
and in fact any common coordinate mass mu. -/
theorem source_original_big_real_product_permutation434
    {P : Type} {M : ℕ} (mu : P → ℝ)
    (σ : Equiv.Perm (Fin M)) (x : Fin M → P) :
    sourceOriginalRealBigProductMass434 mu
      ((sourceOriginalBigRelabelEquiv434 σ) x) =
    sourceOriginalRealBigProductMass434 mu x := by
  unfold sourceOriginalRealBigProductMass434
  exact Fintype.prod_equiv σ
    (fun i => mu (x (σ i)))
    (fun i => mu (x i))
    (fun _ => rfl)

/-- TRUE L² energy, not a formal combination of subset
cardinalities. Positivity is inherited from source BIG
reciprocal-prime masses (all prime factors are positive). -/
noncomputable def sourceOriginalBigActualEnergy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (f : (Fin M → P) → ℂ) : ℝ :=
  ∑ x : Fin M → P,
    sourceOriginalRealBigProductMass434 mu x *
      Complex.normSq (f x)

/-- Actual original source BIG L² norm is EXACTLY invariant
under independently permuting the labelled prime coordinates.
No assumed symmetry of a generic degree-energy array enters. -/
theorem source_original_big_actual_energy_permutation434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (σ : Equiv.Perm (Fin M))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434 mu
      (fun x => f ((sourceOriginalBigRelabelEquiv434 σ) x)) =
    sourceOriginalBigActualEnergy434 mu f := by
  unfold sourceOriginalBigActualEnergy434
  have h := Fintype.sum_equiv
    (sourceOriginalBigRelabelEquiv434 (P := P) σ)
    (fun x : Fin M → P =>
      sourceOriginalRealBigProductMass434 mu x *
        Complex.normSq (f ((sourceOriginalBigRelabelEquiv434 σ) x)))
    (fun x : Fin M → P =>
      sourceOriginalRealBigProductMass434 mu x *
        Complex.normSq (f x))
    (by
      intro x
      rw [source_original_big_real_product_permutation434 mu σ x])
  exact h
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigWeightedHermitian -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ACTUAL source BIG prime-product L² pairing is Hermitian:
no abstract inner product structure or uniform prime law is
assumed. The sole input is real-valued source prime weights. -/
theorem source_original_big_weighted_hermitian434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu f g =
    star (sourceOriginalBigWeightedPairing434 mu g f) := by
  unfold sourceOriginalBigWeightedPairing434
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [star_mul, star_star]
  have hm :
      star ((sourceOriginalRealBigProductMass434 mu x:ℝ):ℂ) =
        (sourceOriginalRealBigProductMass434 mu x:ℂ) := by
    simp [Complex.star_def, Complex.conj_ofReal]
  rw [hm]
  ring

/-- The true centered BIG component is orthogonal to the
averaged component also in the REVERSE pairing orientation.
This follows from source-real Hermitian symmetry and the
checked BIG detailed-balance theorem. -/
theorem source_original_big_one_coordinate_orthogonal_reverse434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
      (fun x => f x -
        sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f x)
      (sourceOriginalCoordinateMean434
        (fun p => (mu p:ℂ)) i f) = 0 := by
  rw [source_original_big_weighted_hermitian434]
  rw [source_original_big_one_coordinate_orthogonal434 mu hmu i f]
  simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigPythagoras -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The actual source BIG weighted pairing, rather than a
formal degree model, has diagonal equal to the REAL weighted
norm-square under the true iid prime-product law. -/
theorem source_original_big_pairing_is_actual_energy434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu f f =
      (sourceOriginalBigActualEnergy434 mu f:ℂ) := by
  unfold sourceOriginalBigWeightedPairing434
    sourceOriginalBigActualEnergy434
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hh : ((Complex.normSq (f x)):ℂ) =
      star (f x) * f x := by
    simpa only [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := f x))
  rw [Complex.ofReal_mul,hh]
  ring

/-- All positive source BIG prime laws give nonnegative
physical squared L2 energy, for any arbitrary complex tuple
observable (no separability or independence of f). -/
theorem source_original_big_actual_energy_nonneg434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : ∀ p, 0 ≤ mu p)
    (f : (Fin M → P) → ℂ) :
    0 ≤ sourceOriginalBigActualEnergy434 mu f := by
  unfold sourceOriginalBigActualEnergy434
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg
  · unfold sourceOriginalRealBigProductMass434
    apply Finset.prod_nonneg
    intro i hi
    exact hmu (x i)
  · exact Complex.normSq_nonneg (f x)

/-- REAL-source E_i is now a true orthogonal projection.
Pythagoras for E_i and I-E_i holds in the ACTUAL weighted
BIG product prime L² norm, not a hypothetical symmetric
Hoeffding degree-energy. No losses, no extra factors. -/
theorem source_original_big_coordinate_pythagoras434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434 mu f =
      sourceOriginalBigActualEnergy434 mu
        (sourceOriginalCoordinateMean434
          (fun p => (mu p:ℂ)) i f) +
      sourceOriginalBigActualEnergy434 mu
        (fun x => f x - sourceOriginalCoordinateMean434
          (fun p => (mu p:ℂ)) i f x) := by
  let E : (Fin M → P) → ℂ :=
    sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f
  let R : (Fin M → P) → ℂ := fun x => f x - E x
  have horth := source_original_big_one_coordinate_orthogonal434
    mu hmu i f
  have horthRev :=
    source_original_big_one_coordinate_orthogonal_reverse434
      mu hmu i f
  have hExpand :
      sourceOriginalBigWeightedPairing434 mu f f =
      sourceOriginalBigWeightedPairing434 mu E E +
      sourceOriginalBigWeightedPairing434 mu E R +
      sourceOriginalBigWeightedPairing434 mu R E +
      sourceOriginalBigWeightedPairing434 mu R R := by
    unfold sourceOriginalBigWeightedPairing434
    rw [← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hf : f x = E x + R x := by dsimp [R]; ring
    rw [hf]
    simp only [star_add]
    ring
  have hPair :
      sourceOriginalBigWeightedPairing434 mu f f =
      sourceOriginalBigWeightedPairing434 mu E E +
      sourceOriginalBigWeightedPairing434 mu R R := by
    simpa only [E,R, horth, horthRev,
      add_zero, zero_add, add_assoc] using hExpand
  rw [source_original_big_pairing_is_actual_energy434] at hPair
  rw [source_original_big_pairing_is_actual_energy434,
      source_original_big_pairing_is_actual_energy434] at hPair
  exact_mod_cast hPair
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHarmonicCoordinateProjection -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Instantiate the algebraic BIG coordinate averaging operator
with the LITERAL source03 harmonic prime probability mass
mu(p)=(1/p)/V on genuine source prime support P.
No independent uniform-prime distribution is introduced. -/
noncomputable def sourceOriginalHarmonicPrimeCoordinateMean434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ) (V : ℝ) (i : Fin M)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) : ℂ :=
  sourceOriginalCoordinateMean434
    (fun p => (sourceOriginalHarmonicPrimeMu434 prime V p:ℂ))
    i f x

/-- True exact source reciprocal-prime coordinate mean is an
orthogonal projection in the ACTUAL physical weighted L²
prime product space, with the source normalization V=sum 1/p.
All observables f are arbitrary entire indexed BIG tuple tests. -/
theorem source_original_harmonic_prime_coordinate_pythagoras434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ)
    (V : ℝ) (hV : 0 < V)
    (hEq : V = ∑ p : P, 1/(prime p:ℝ))
    (i : Fin M) (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V) f =
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V)
      (sourceOriginalHarmonicPrimeCoordinateMean434 prime V i f) +
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V)
      (fun x => f x -
        sourceOriginalHarmonicPrimeCoordinateMean434
          prime V i f x) := by
  unfold sourceOriginalHarmonicPrimeCoordinateMean434
  exact source_original_big_coordinate_pythagoras434
    (sourceOriginalHarmonicPrimeMu434 prime V)
    (source_original_harmonic_prime_normalized434
      prime V hV hEq) i f

/-- Full true source BIG weighted energy of the real physical
reciprocal-prime tuple is unchanged by EVERY permutation of
its indices. This is the exact orbit-equality starting point
for the original symmetrized Hoeffding probes in source03. -/
theorem source_original_harmonic_prime_energy_permutation434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ) (V : ℝ)
    (σ : Equiv.Perm (Fin M))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V)
      (fun x => f ((sourceOriginalBigRelabelEquiv434 σ) x)) =
    sourceOriginalBigActualEnergy434
      (sourceOriginalHarmonicPrimeMu434 prime V) f := by
  exact source_original_big_actual_energy_permutation434
    (sourceOriginalHarmonicPrimeMu434 prime V) σ f
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalBigMixedModeOrthogonality -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7500000

/-- The TRUE weighted BIG-prime L² pairing of a mean-zero
component (I-E_i)f and an i-independent component E_i g
is identically zero for ALL arbitrary COMPLEX global tests
f,g, with no assumption of independence of other BIG slots.
This is the actual mutual-orthogonality ingredient for
distinct source Efron–Stein / Hoeffding subset components. -/
theorem source_original_big_centered_vs_averaged_orthogonal434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
      (fun z => f z -
        sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f z)
      (sourceOriginalCoordinateMean434
        (fun p => (mu p:ℂ)) i g) = 0 := by
  let R : (Fin M → P) → ℂ :=
    fun z => f z -
      sourceOriginalCoordinateMean434 (fun p => (mu p:ℂ)) i f z
  have hmuC : (∑ p : P, (mu p:ℂ)) = 1 := by
    exact_mod_cast hmu
  have hzero : sourceOriginalCoordinateMean434
      (fun p => (mu p:ℂ)) i R = fun _ => 0 := by
    funext x
    exact source_original_coordinate_centered_mean_zero434
      (fun p => (mu p:ℂ)) hmuC i f x
  have hself := source_original_big_coordinate_selfadjoint434
    mu i R g
  rw [hzero] at hself
  have hz : sourceOriginalBigWeightedPairing434 mu
      (fun _ => 0) g = 0 := by
    simp [sourceOriginalBigWeightedPairing434]
  rw [hz] at hself
  exact hself.symm

/-- The above mixed-mode orthogonality for the LITERAL
reciprocal-prime measure of the actual source03 BIG groups. -/
theorem source_original_harmonic_mixed_mode_orthogonal434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (prime : P → ℕ)
    (V : ℝ) (hV : 0 < V)
    (hEq : V = ∑ p : P, 1/(prime p:ℝ))
    (i : Fin M) (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434
       (sourceOriginalHarmonicPrimeMu434 prime V)
      (fun z => f z -
        sourceOriginalHarmonicPrimeCoordinateMean434
          prime V i f z)
      (sourceOriginalHarmonicPrimeCoordinateMean434
        prime V i g) = 0 := by
  unfold sourceOriginalHarmonicPrimeCoordinateMean434
  exact source_original_big_centered_vs_averaged_orthogonal434
    (sourceOriginalHarmonicPrimeMu434 prime V)
    (source_original_harmonic_prime_normalized434
      prime V hV hEq) i f g
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingCoordinateModes -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The ACTUAL centered coordinate mode I-E_i on literal
source BIG prime tuples. -/
noncomputable def sourceOriginalBigCoordinateDiff434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (i : Fin M)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) : ℂ :=
  f x - sourceOriginalCoordinateMean434 mu i f x

/-- TRUE source conditional averaging commutes with DIFFERENT
coordinate's centered operation, for arbitrary global f. -/
theorem source_original_big_average_diff_commute434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (i j : Fin M) (hij : i ≠ j)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (sourceOriginalBigCoordinateDiff434 mu j f) x =
    sourceOriginalBigCoordinateDiff434 mu j
      (sourceOriginalCoordinateMean434 mu i f) x := by
  unfold sourceOriginalBigCoordinateDiff434
  unfold sourceOriginalCoordinateMean434
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  exact congrArg (fun z => (∑ p : P, mu p * f (Function.update x i p)) - z)
    (source_original_coordinate_means_commute434 mu i j hij f x)

/-- TRUE source mean-zero mode: E_i (I-E_i) = 0. -/
theorem source_original_big_average_diff_self_zero434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (sourceOriginalBigCoordinateDiff434 mu i f) x = 0 := by
  exact source_original_coordinate_centered_mean_zero434
    mu hmu i f x

/-- Complementary source projection D_i satisfies D_i²=D_i. -/
theorem source_original_big_diff_idempotent434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p : P, mu p) = 1)
    (i : Fin M) (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalBigCoordinateDiff434 mu i
      (sourceOriginalBigCoordinateDiff434 mu i f) x =
    sourceOriginalBigCoordinateDiff434 mu i f x := by
  change f x - sourceOriginalCoordinateMean434 mu i f x -
      sourceOriginalCoordinateMean434 mu i
        (sourceOriginalBigCoordinateDiff434 mu i f) x =
      f x - sourceOriginalCoordinateMean434 mu i f x
  rw [source_original_big_average_diff_self_zero434 mu hmu i f x]
  ring

/-- Arbitrary source E_i, D_i are both complex-linear. -/
theorem source_original_big_diff_linear434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (i : Fin M)
    (a b : ℂ) (f g : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalBigCoordinateDiff434 mu i
      (fun z => a*f z+b*g z) x =
    a*sourceOriginalBigCoordinateDiff434 mu i f x +
    b*sourceOriginalBigCoordinateDiff434 mu i g x := by
  unfold sourceOriginalBigCoordinateDiff434
  rw [source_original_coordinate_mean_linear434]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingList -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The two REAL source BIG conditional projections E_i and
I-E_i, chosen by whether the Efron–Stein probe i is centered. -/
noncomputable def sourceOriginalHoeffdingMode434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (i : Fin M) (f : (Fin M → P) → ℂ) :
    (Fin M → P) → ℂ :=
  if i ∈ S then sourceOriginalBigCoordinateDiff434 mu i f
  else sourceOriginalCoordinateMean434 mu i f

/-- GENUINE ordered simultaneous Hoeffding projection:
every designated source BIG coordinate applies its actual
conditional E_i or its centered complement I-E_i.
The list order matters syntactically; mathematical
independence of order follows from commutation below. -/
noncomputable def sourceOriginalHoeffdingList434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M)) :
    List (Fin M) → ((Fin M → P) → ℂ) → ((Fin M → P) → ℂ)
  | [], f => f
  | i :: L, f =>
    sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S i f)

/-- Each original source BIG Efron–Stein factor is linear
on arbitrary complex-valued full tuples. -/
theorem source_original_hoeffding_mode_add434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (i : Fin M) (f g : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingMode434 mu S i
       (fun x => f x + g x) =
    (fun x => sourceOriginalHoeffdingMode434 mu S i f x +
      sourceOriginalHoeffdingMode434 mu S i g x) := by
  funext x
  have ha := source_original_coordinate_mean_linear434
    mu i 1 1 f g x
  simp only [one_mul] at ha
  by_cases hi : i ∈ S
  · simp only [sourceOriginalHoeffdingMode434, if_pos hi,
      sourceOriginalBigCoordinateDiff434]
    rw [ha]
    ring
  · simp only [sourceOriginalHoeffdingMode434, if_neg hi]
    exact ha

/-- Every source centered/averaging BIG factor sends zero
to zero exactly; no L² normalization assumed. -/
theorem source_original_hoeffding_mode_zero434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (i : Fin M) :
    sourceOriginalHoeffdingMode434 mu S i (fun _ => 0) =
      (fun _ => 0) := by
  funext x
  by_cases hi : i ∈ S
  · simp [sourceOriginalHoeffdingMode434, hi,
      sourceOriginalBigCoordinateDiff434,
      sourceOriginalCoordinateMean434]
  · simp [sourceOriginalHoeffdingMode434, hi,
      sourceOriginalCoordinateMean434]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingListAlgebra -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- A TRUE source conditional E_i commutes with either
coordinate mode on a DIFFERENT physical BIG slot j. -/
theorem source_original_hoeffding_average_mode_commute434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (i j : Fin M) (hij : i ≠ j)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (sourceOriginalHoeffdingMode434 mu S j f) x =
    sourceOriginalHoeffdingMode434 mu S j
      (sourceOriginalCoordinateMean434 mu i f) x := by
  by_cases hj : j ∈ S
  · simp only [sourceOriginalHoeffdingMode434, if_pos hj]
    exact source_original_big_average_diff_commute434
      mu i j hij f x
  · simp only [sourceOriginalHoeffdingMode434, if_neg hj]
    exact source_original_coordinate_means_commute434
      mu i j hij f x

/-- The whole original source multi-slot Hoeffding projection
preserves zero input. -/
theorem source_original_hoeffding_list_zero434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (L : List (Fin M)) :
    sourceOriginalHoeffdingList434 mu S L (fun _ => 0) =
      (fun _ => 0) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S i (fun _ => 0)) =
      (fun _ => 0)
    rw [source_original_hoeffding_mode_zero434]
    exact ih

/-- TRUE source multi-slot Hoeffding operators are additive
on arbitrary nonseparable BIG prime tuple tests. -/
theorem source_original_hoeffding_list_add434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (L : List (Fin M))
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu S L
        (fun x => f x+g x) =
    (fun x => sourceOriginalHoeffdingList434 mu S L f x +
       sourceOriginalHoeffdingList434 mu S L g x) := by
  induction L generalizing f g with
  | nil => rfl
  | cons i L ih =>
    change sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalHoeffdingMode434 mu S i
        (fun x => f x+g x)) =
      (fun x => sourceOriginalHoeffdingList434 mu S L
         (sourceOriginalHoeffdingMode434 mu S i f) x +
        sourceOriginalHoeffdingList434 mu S L
         (sourceOriginalHoeffdingMode434 mu S i g) x)
    rw [source_original_hoeffding_mode_add434]
    exact ih _ _

/-- A Hoeffding operator only reads the source centered-slot
set S on coordinates that really occur in its physical list. -/
theorem source_original_hoeffding_list_subset_ext434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (S T : Finset (Fin M)) (L : List (Fin M))
    (hST : ∀ i ∈ L, (i ∈ S ↔ i ∈ T))
    (f : (Fin M → P) → ℂ) :
    sourceOriginalHoeffdingList434 mu S L f =
    sourceOriginalHoeffdingList434 mu T L f := by
  induction L generalizing f with
  | nil => rfl
  | cons i L ih =>
    have hi : (i ∈ S ↔ i ∈ T) := hST i (by simp)
    have ht : ∀ j ∈ L, (j∈S ↔ j∈T) := by
      intro j hj
      exact hST j (by simp [hj])
    have hmode : sourceOriginalHoeffdingMode434 mu S i f =
      sourceOriginalHoeffdingMode434 mu T i f := by
      unfold sourceOriginalHoeffdingMode434
      simp only [← hi]
    change sourceOriginalHoeffdingList434 mu S L
       (sourceOriginalHoeffdingMode434 mu S i f) =
      sourceOriginalHoeffdingList434 mu T L
       (sourceOriginalHoeffdingMode434 mu T i f)
    rw [hmode]
    exact ih ht _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingEigen -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Once a coordinate has NOT yet been processed by the
actual source BIG Hoeffding list operator, its genuine
physical average commutes through all processed modes. -/
theorem source_original_hoeffding_average_list_commute434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (S : Finset (Fin M))
    (i : Fin M) (L : List (Fin M)) (hi : i ∉ L)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (sourceOriginalHoeffdingList434 mu S L f) x =
    sourceOriginalHoeffdingList434 mu S L
      (sourceOriginalCoordinateMean434 mu i f) x := by
  induction L generalizing f with
  | nil => rfl
  | cons j L ih =>
    have hij : i ≠ j := by
      intro h
      apply hi
      simp [h]
    have hit : i ∉ L := by
      intro h
      exact hi (by simp [h])
    change sourceOriginalCoordinateMean434 mu i
      (sourceOriginalHoeffdingList434 mu S L
        (sourceOriginalHoeffdingMode434 mu S j f)) x =
      sourceOriginalHoeffdingList434 mu S L
        (sourceOriginalHoeffdingMode434 mu S j
          (sourceOriginalCoordinateMean434 mu i f)) x
    rw [ih hit (sourceOriginalHoeffdingMode434 mu S j f)]
    have hh : sourceOriginalCoordinateMean434 mu i
         (sourceOriginalHoeffdingMode434 mu S j f) =
       sourceOriginalHoeffdingMode434 mu S j
         (sourceOriginalCoordinateMean434 mu i f) := by
      funext y
      exact source_original_hoeffding_average_mode_commute434
        mu S i j hij f y
    rw [hh]

/-- For a GENUINE nodup ordered list of source BIG prime
coordinates, every Hoeffding component H_S is exactly
mean ZERO at each marked centered slot and is FIXED by E_i
at every unmarked slot. No degree-energy model is used. -/
theorem source_original_hoeffding_list_mode_eigen434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ) (hmu : (∑ p : P, mu p) = 1)
    (S : Finset (Fin M)) (L : List (Fin M))
    (hL : L.Nodup) (i : Fin M) (hi : i ∈ L)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    sourceOriginalCoordinateMean434 mu i
      (sourceOriginalHoeffdingList434 mu S L f) x =
    if i ∈ S then 0
    else sourceOriginalHoeffdingList434 mu S L f x := by
  induction L generalizing f with
  | nil => simp at hi
  | cons j L ih =>
    obtain ⟨hjnot, htl⟩ := List.nodup_cons.mp hL
    rcases List.mem_cons.mp hi with hij | hit
    · subst j
      change sourceOriginalCoordinateMean434 mu i
        (sourceOriginalHoeffdingList434 mu S L
          (sourceOriginalHoeffdingMode434 mu S i f)) x =
        if i ∈ S then 0 else
          sourceOriginalHoeffdingList434 mu S L
            (sourceOriginalHoeffdingMode434 mu S i f) x
      rw [source_original_hoeffding_average_list_commute434
        mu S i L hjnot (sourceOriginalHoeffdingMode434 mu S i f) x]
      by_cases hS : i ∈ S
      · have hmean : sourceOriginalCoordinateMean434 mu i
            (sourceOriginalHoeffdingMode434 mu S i f) =
          (fun _ => 0) := by
          funext y
          simp only [sourceOriginalHoeffdingMode434, if_pos hS]
          exact source_original_big_average_diff_self_zero434
            mu hmu i f y
        rw [hmean, source_original_hoeffding_list_zero434]
        simp [hS]
      · have hmean : sourceOriginalCoordinateMean434 mu i
            (sourceOriginalHoeffdingMode434 mu S i f) =
          sourceOriginalHoeffdingMode434 mu S i f := by
          funext y
          simp only [sourceOriginalHoeffdingMode434, if_neg hS]
          exact source_original_coordinate_mean_idempotent434
            mu hmu i f y
        rw [hmean]
        simp [hS]
    · change sourceOriginalCoordinateMean434 mu i
        (sourceOriginalHoeffdingList434 mu S L
          (sourceOriginalHoeffdingMode434 mu S j f)) x =
       if i ∈ S then 0 else
         sourceOriginalHoeffdingList434 mu S L
           (sourceOriginalHoeffdingMode434 mu S j f) x
      exact ih htl hit _
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingOrthogonality -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Distinct source actual Hoeffding sectors centered in i
versus averaged in i are orthogonal in the TRUE BIG
reciprocal-prime complex L2 pairing. -/
theorem source_original_hoeffding_sector_orthogonal_at434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (S T : Finset (Fin M)) (L : List (Fin M))
    (hL : L.Nodup)
    (i : Fin M) (hi : i ∈ L)
    (hS : i ∈ S) (hT : i ∉ T)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
       (sourceOriginalHoeffdingList434
          (fun p => (mu p:ℂ)) S L f)
       (sourceOriginalHoeffdingList434
          (fun p => (mu p:ℂ)) T L g) = 0 := by
  let w : P → ℂ := fun p => (mu p:ℂ)
  have hw : (∑ p : P, w p) = 1 := by
    change (∑ p : P, (mu p : ℂ)) = 1
    exact_mod_cast hmu
  let F := sourceOriginalHoeffdingList434 w S L f
  let G := sourceOriginalHoeffdingList434 w T L g
  have hEF : sourceOriginalCoordinateMean434 w i F =
      (fun _ => 0) := by
    funext x
    have he := source_original_hoeffding_list_mode_eigen434
      w hw S L hL i hi f x
    simpa only [F, if_pos hS] using he
  have hEG : sourceOriginalCoordinateMean434 w i G = G := by
    funext x
    have he := source_original_hoeffding_list_mode_eigen434
      w hw T L hL i hi g x
    simpa only [G, if_neg hT] using he
  have hAdj := source_original_big_coordinate_selfadjoint434
    mu i F G
  rw [hEF, hEG] at hAdj
  have hz : sourceOriginalBigWeightedPairing434 mu
     (fun _ => (0:ℂ)) G = 0 := by
    simp [sourceOriginalBigWeightedPairing434]
  rw [hz] at hAdj
  exact hAdj.symm

/-- Actual source BIG orthogonality for ANY two distinct
Hoeffding subsets of a full nodup coordinate list,
without postulated orthogonal projections. -/
theorem source_original_hoeffding_distinct_orthogonal434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (S T : Finset (Fin M)) (L : List (Fin M))
    (hL : L.Nodup)
    (hS : S ⊆ L.toFinset) (hT : T ⊆ L.toFinset)
    (hST : S ≠ T)
    (f g : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
       (sourceOriginalHoeffdingList434
         (fun p => (mu p:ℂ)) S L f)
       (sourceOriginalHoeffdingList434
         (fun p => (mu p:ℂ)) T L g) = 0 := by
  have hdiff : ∃ i : Fin M,
      (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
    by_contra hh
    apply hST
    ext i
    constructor
    · intro hi
      by_contra hnot
      exact hh ⟨i, Or.inl ⟨hi,hnot⟩⟩
    · intro hi
      by_contra hnot
      exact hh ⟨i, Or.inr ⟨hi,hnot⟩⟩
  obtain ⟨i, hsep⟩ := hdiff
  rcases hsep with ⟨hiS, hiT⟩ | ⟨hiT,hiS⟩
  · have hiL : i ∈ L := List.mem_toFinset.mp (hS hiS)
    exact source_original_hoeffding_sector_orthogonal_at434
      mu hmu S T L hL i hiL hiS hiT f g
  · have hiL : i ∈ L := List.mem_toFinset.mp (hT hiT)
    have hh := source_original_hoeffding_sector_orthogonal_at434
      mu hmu T S L hL i hiL hiT hiS g f
    rw [source_original_big_weighted_hermitian434] at hh
    simpa using congrArg star hh
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingExpansion -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Original source Hoeffding components, indexed by every
centered-subset S of a NODUP physical BIG slot list, reconstruct
the original full complex test exactly, not a degree proxy.
Commuting conditional expectations are the REAL source
weighted one-prime resampling operators from C32. -/
theorem source_original_hoeffding_list_expansion434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℂ)
    (L : List (Fin M)) (hL : L.Nodup)
    (f : (Fin M → P) → ℂ) (x : Fin M → P) :
    (∑ S ∈ L.toFinset.powerset,
       sourceOriginalHoeffdingList434 mu S L f x) = f x := by
  induction L generalizing f with
  | nil =>
    simp [sourceOriginalHoeffdingList434]
  | cons i L ih =>
    obtain ⟨hni, hNodup⟩ := List.nodup_cons.mp hL
    let s : Finset (Fin M) := L.toFinset
    have hnot : i ∉ s := by
      simpa only [s, List.mem_toFinset] using hni
    have hdisj :
        Disjoint s.powerset
          (s.powerset.image (insert i)) := by
      apply Finset.disjoint_left.mpr
      intro S hS hSI
      have hSub : S ⊆ s := Finset.mem_powerset.mp hS
      have hiS : i ∉ S := fun h => hnot (hSub h)
      obtain ⟨T,hT,hEq⟩ := Finset.mem_image.mp hSI
      have hiSI : i ∈ S := by
        rw [← hEq]
        exact Finset.mem_insert_self i T
      exact hiS hiSI
    have hinj :
        Set.InjOn (insert i : Finset (Fin M) → Finset (Fin M))
          (s.powerset : Set (Finset (Fin M))) := by
      intro S hS T hT heq
      have hsi : i ∉ S := by
        have hs : S ⊆ s := Finset.mem_powerset.mp hS
        exact fun h => hnot (hs h)
      have hti : i ∉ T := by
        have ht : T ⊆ s := Finset.mem_powerset.mp hT
        exact fun h => hnot (ht h)
      have he := congrArg (fun U : Finset (Fin M) => U.erase i) heq
      simpa [hsi,hti] using he
    have hsplit :
        (∑ S ∈ (insert i s).powerset,
          sourceOriginalHoeffdingList434 mu S (i::L) f x) =
        (∑ S ∈ s.powerset,
          sourceOriginalHoeffdingList434 mu S (i::L) f x) +
        (∑ S ∈ s.powerset,
          sourceOriginalHoeffdingList434 mu
            (insert i S) (i::L) f x) := by
      rw [Finset.powerset_insert]
      rw [Finset.sum_union hdisj]
      rw [Finset.sum_image hinj]
    have hleft :
        (∑ S ∈ s.powerset,
          sourceOriginalHoeffdingList434 mu S (i::L) f x) =
        (∑ S ∈ s.powerset,
          sourceOriginalHoeffdingList434 mu S L
            (sourceOriginalCoordinateMean434 mu i f) x) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hiS : i ∉ S := by
        intro h
        exact hnot ((Finset.mem_powerset.mp hS) h)
      change sourceOriginalHoeffdingList434 mu S L
        (sourceOriginalHoeffdingMode434 mu S i f) x =
        sourceOriginalHoeffdingList434 mu S L
          (sourceOriginalCoordinateMean434 mu i f) x
      simp only [sourceOriginalHoeffdingMode434, if_neg hiS]
    have hright :
        (∑ S ∈ s.powerset,
          sourceOriginalHoeffdingList434 mu
            (insert i S) (i::L) f x) =
        (∑ S ∈ s.powerset,
          sourceOriginalHoeffdingList434 mu S L
            (sourceOriginalBigCoordinateDiff434 mu i f) x) := by
      apply Finset.sum_congr rfl
      intro S hS
      change sourceOriginalHoeffdingList434 mu (insert i S) L
        (sourceOriginalHoeffdingMode434 mu (insert i S) i f) x =
        sourceOriginalHoeffdingList434 mu S L
          (sourceOriginalBigCoordinateDiff434 mu i f) x
      rw [show sourceOriginalHoeffdingMode434 mu (insert i S) i f =
          sourceOriginalBigCoordinateDiff434 mu i f by
        simp [sourceOriginalHoeffdingMode434]]
      have hmem : ∀ j ∈ L, (j ∈ insert i S ↔ j ∈ S) := by
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst j
          exact hni hj
        simp [hji]
      exact congrFun (source_original_hoeffding_list_subset_ext434
        mu (insert i S) S L hmem
        (sourceOriginalBigCoordinateDiff434 mu i f)) x
    simp only [List.toFinset_cons]
    change (∑ S ∈ (insert i s).powerset,
        sourceOriginalHoeffdingList434 mu S (i::L) f x) = f x
    rw [hsplit,hleft,hright,ih hNodup,ih hNodup]
    unfold sourceOriginalBigCoordinateDiff434
    ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalHoeffdingPairingParseval -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Actual BIG-prime weighted complex pairing is bilinear
for arbitrary finite lists of physical BIG tuple observables. -/
theorem source_original_big_pairing_double_sum434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    {A B : Type} (S : Finset A) (T : Finset B)
    (F : A → (Fin M → P) → ℂ)
    (G : B → (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu
      (fun x => ∑ a ∈ S, F a x)
      (fun x => ∑ b ∈ T, G b x) =
    ∑ a ∈ S, ∑ b ∈ T,
      sourceOriginalBigWeightedPairing434 mu (F a) (G b) := by
  unfold sourceOriginalBigWeightedPairing434
  have hpoint (x : Fin M → P) :
      (sourceOriginalRealBigProductMass434 mu x:ℂ) *
          star (∑ a ∈ S, F a x) * (∑ b ∈ T, G b x) =
      ∑ a ∈ S, ∑ b ∈ T,
        (sourceOriginalRealBigProductMass434 mu x:ℂ) *
          star (F a x) * G b x := by
    rw [star_sum]
    calc
      _ = ∑ a ∈ S,
            (sourceOriginalRealBigProductMass434 mu x:ℂ) *
            star (F a x) * (∑ b ∈ T, G b x) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
  calc
    _ = ∑ x : Fin M → P, ∑ a ∈ S, ∑ b ∈ T,
           (sourceOriginalRealBigProductMass434 mu x:ℂ) *
             star (F a x) * G b x := by
      apply Finset.sum_congr rfl
      intro x _
      exact hpoint x
    _ = ∑ a ∈ S, ∑ x : Fin M → P, ∑ b ∈ T,
           (sourceOriginalRealBigProductMass434 mu x:ℂ) *
             star (F a x) * G b x := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

/-- True original BIG product harmonic coupling: ALL Hoeffding
subsets are a pairwise orthogonal resolution of identity in
the ACTUAL weighted complex pairing, with no abstract energy
realisation hypothesis. -/
theorem source_original_big_hoeffding_pairing_parseval434
    {P : Type} [Fintype P] [DecidableEq P]
    {M : ℕ} (mu : P → ℝ)
    (hmu : (∑ p : P, mu p) = 1)
    (L : List (Fin M)) (hL : L.Nodup)
    (f : (Fin M → P) → ℂ) :
    sourceOriginalBigWeightedPairing434 mu f f =
      ∑ S ∈ L.toFinset.powerset,
        sourceOriginalBigWeightedPairing434 mu
          (sourceOriginalHoeffdingList434
            (fun p => (mu p:ℂ)) S L f)
          (sourceOriginalHoeffdingList434
            (fun p => (mu p:ℂ)) S L f) := by
  let I : Finset (Finset (Fin M)) := L.toFinset.powerset
  let H : Finset (Fin M) → (Fin M → P) → ℂ :=
    fun S => sourceOriginalHoeffdingList434
      (fun p => (mu p:ℂ)) S L f
  have hexp : (fun x => ∑ S ∈ I, H S x) = f := by
    funext x
    exact source_original_hoeffding_list_expansion434
      (fun p => (mu p:ℂ)) L hL f x
  have hor (S T : Finset (Fin M))
      (hS : S ∈ I) (hT : T ∈ I) (hne : S ≠ T) :
      sourceOriginalBigWeightedPairing434 mu (H S) (H T) = 0 :=
    source_original_hoeffding_distinct_orthogonal434
      mu hmu S T L hL
        (Finset.mem_powerset.mp hS)
        (Finset.mem_powerset.mp hT) hne f f
  have hdiag (S : Finset (Fin M)) (hS : S ∈ I) :
      (∑ T ∈ I, sourceOriginalBigWeightedPairing434 mu
        (H S) (H T)) =
      sourceOriginalBigWeightedPairing434 mu (H S) (H S) := by
    rw [← Finset.add_sum_erase I
       (fun T => sourceOriginalBigWeightedPairing434 mu
         (H S) (H T)) hS]
    have hz : (∑ T ∈ I.erase S,
      sourceOriginalBigWeightedPairing434 mu (H S) (H T)) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      exact hor S T hS (Finset.mem_of_mem_erase hT)
        (Ne.symm (Finset.ne_of_mem_erase hT))
    rw [hz]
    simp
  calc
    _ = sourceOriginalBigWeightedPairing434 mu
        (fun x => ∑ S ∈ I, H S x)
        (fun x => ∑ T ∈ I, H T x) := by
          rw [hexp]
    _ = ∑ S ∈ I, ∑ T ∈ I,
        sourceOriginalBigWeightedPairing434 mu (H S) (H T) :=
          source_original_big_pairing_double_sum434 mu I I H H
    _ = ∑ S ∈ I, sourceOriginalBigWeightedPairing434 mu
        (H S) (H S) := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hdiag S hS
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

