module

public import Green64.Library.Weights.Part016
public import Green64.Library.Correlation.Part005

@[expose] public section

/-!
# Weights / GhostJointPushforward

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGhostJointPushforward -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact finite tensor disintegration for an arbitrary JOINT test.
This is finite algebra, with no norm or factorization premise on H. -/
theorem source_original_GHOST_joint_pushforward434
    {I : Type} [Fintype I] [DecidableEq I]
    (A X : I → Type) [∀ i,Fintype (A i)] [∀ i,Fintype (X i)]
    (e : (i : I) → A i → X i) (w : (i : I) → A i → ℂ)
    (H : ((i : I) → X i) → ℂ) :
    (∑ a : (i : I) → A i, (∏ i,w i (a i))*H (fun i => e i (a i))) =
    ∑ x : (i : I) → X i,
      (∏ i,∑ a : A i,if e i a=x i then w i a else 0)*H x := by
  classical
  have hp (x : (i : I) → X i) :
      (∏ i,∑ a : A i,if e i a=x i then w i a else 0) =
      ∑ a : (i : I) → A i,∏ i,if e i (a i)=x i then w i (a i) else 0 :=
    Fintype.prod_sum (fun i a => if e i a=x i then w i a else 0)
  symm
  simp_rw [hp,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hprod (x : (i : I) → X i) :
      (∏ i,if e i (a i)=x i then w i (a i) else 0) =
      if (fun i => e i (a i))=x then ∏ i,w i (a i) else 0 := by
    by_cases he : (fun i => e i (a i))=x
    · subst x
      simp
    · rw [if_neg he]
      have hn : ∃ i,e i (a i) ≠ x i := by
        by_contra h
        push_neg at h
        exact he (funext h)
      obtain ⟨i,hi⟩ := hn
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [if_neg hi])
  simp_rw [hprod]
  simp

theorem source_original_GHOST_joint_exact_transfer434
    {I : Type} [Fintype I] [DecidableEq I]
    (A X : I → Type) [∀ i,Fintype (A i)] [∀ i,Fintype (X i)]
    (e : (i : I) → A i → X i) (w : (i : I) → A i → ℂ)
    (v : (i : I) → X i → ℂ)
    (h : ∀ i (F : X i → ℂ), (∑ a : A i,w i a*F (e i a)) =
      ∑ x : X i,v i x*F x)
    (H : ((i : I) → X i) → ℂ) :
    (∑ a : (i : I) → A i,(∏ i,w i (a i))*H (fun i => e i (a i))) =
    ∑ x : (i : I) → X i,(∏ i,v i (x i))*H x := by
  classical
  have hf (i : I) (x : X i) :
      (∑ a : A i,if e i a=x then w i a else 0)=v i x := by
    have hh := h i (fun y => if y=x then 1 else 0)
    simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,
      if_true] using hh
  rw [source_original_GHOST_joint_pushforward434]
  simp_rw [hf]

abbrev SourceOriginalGhostSetChoice434
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero] :=
  {A : Finset (Fin old.length) // A ∈ (zeroOld old zero).powerset} × Finset P

def sourceOriginalGhostSetProjection434
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero] (B : ℕ)
    (c : GhostWitnessChoice old zero B) : SourceOriginalGhostSetChoice434 old zero :=
  (c.1,Finset.univ.image c.2.2)

def sourceOriginalGhostDistinctCoefficient434
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : P → ℂ)
    (c : GhostWitnessChoice old zero B) : ℂ :=
  if Function.Injective c.2.2 then sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu else 0

def sourceOriginalGhostSetCoefficient434
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : P → ℂ)
    (d : SourceOriginalGhostSetChoice434 old zero) : ℂ :=
  if d.2.card ≤ B then
    alpha^d.1.1.card * chi^((zeroOld old zero).card-d.1.1.card) *
      gamma^d.2.card * (∏ p ∈ d.2,nu p)
  else 0

private theorem fixed_birth_count
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero]
    (A : Finset (Fin old.length)) (b : ℕ)
    (alpha chi gamma : ℂ) (nu : P → ℂ) (H : Finset P → ℂ) :
    (∑ fresh : Fin b → P,if Function.Injective fresh then
      sourceGhostTerm old zero A fresh alpha chi gamma nu * H (Finset.univ.image fresh) else 0) =
    ∑ s ∈ (Finset.univ : Finset (Finset P)).filter (fun s => s.card=b),
      alpha^A.card*chi^((zeroOld old zero).card-A.card)*gamma^b*
        (∏ p ∈ s,nu p)*H s := by
  rw [source_original_GHOST_distinct_fibre_decomposition434]
  apply Finset.sum_congr rfl
  intro s hs
  exact source_original_GHOST_old_birth_fibre_exact434 old zero A b s
    (Finset.mem_filter.mp hs).2 (fun p => p) alpha chi gamma nu (fun _ t => H t)

/-- Actual single-group source G pushforward, including all legal OLD
subsets and all birth counts through the original cutoff. Its only
quotient is the exact ordered-birth fibre, whose b! cancels the original
1/b!. This identity is uniform for every test on the finite outcome. -/
theorem source_original_GHOST_group_set_pushforward434
    {P : Type} [Fintype P] [DecidableEq P]
    (old : List P) (zero : P → Prop) [DecidablePred zero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : P → ℂ)
    (H : SourceOriginalGhostSetChoice434 old zero → ℂ) :
    (∑ c : GhostWitnessChoice old zero B,
      sourceOriginalGhostDistinctCoefficient434 old zero B alpha chi gamma nu c *
        H (sourceOriginalGhostSetProjection434 old zero B c)) =
    ∑ d : SourceOriginalGhostSetChoice434 old zero,
      sourceOriginalGhostSetCoefficient434 old zero B alpha chi gamma nu d*H d := by
  unfold sourceOriginalGhostDistinctCoefficient434 sourceOriginalGhostSetProjection434
    sourceOriginalGhostSetCoefficient434
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [ite_mul,zero_mul]
  let W : ℕ → ℂ := fun b => ∑ fresh : Fin b → P,
    if Function.Injective fresh then
      sourceGhostTerm old zero A.1 fresh alpha chi gamma nu * H (A,Finset.univ.image fresh)
    else 0
  change (∑ b : Fin (B+1),W b.val)=_
  rw [Fin.sum_univ_eq_sum_range W (B+1)]
  dsimp only [W]
  simp_rw [fixed_birth_count (old := old) (zero := zero) (A := A.1)
    (alpha := alpha) (chi := chi) (gamma := gamma) (nu := nu) (H := fun s => H (A,s))]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff,ite_mul,zero_mul]
end Green64Analytic.CorrelationSquare

end

end

