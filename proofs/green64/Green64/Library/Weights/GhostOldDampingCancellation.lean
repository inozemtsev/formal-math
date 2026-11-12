module

public import Green64.Library.Weights.Part002

@[expose] public section

/-!
# Weights / GhostOldDampingCancellation

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGhostOldDampingCancellation -/

section

open Classical
open scoped BigOperators
namespace Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {P : Type} [Fintype P] [DecidableEq P]

private theorem count_finRange434 (n : ℕ) (p : Fin n → Prop)
    [DecidablePred p] :
    (List.finRange n).countP (fun i => decide (p i)) =
      (Finset.univ.filter p).card := by
  rw [List.countP_eq_length_filter]
  have h := List.toFinset_card_of_nodup
    ((List.nodup_finRange n).filter (fun i => decide (p i)))
  simpa only [List.toFinset_filter, List.toFinset_finRange,
    decide_eq_true_eq] using h.symm

private theorem zeroOld_card_count434
    (old : List P) (atZero : P → Prop) [DecidablePred atZero] :
    (zeroOld old atZero).card =
      old.countP (fun p => decide (atZero p)) := by
  calc
    _ = (List.finRange old.length).countP
        (fun i => decide (atZero (old.get i))) :=
      by simpa only [zeroOld] using
        (count_finRange434 old.length (fun i => atZero (old.get i))).symm
    _ = ((List.finRange old.length).map old.get).countP
        (fun p => decide (atZero p)) := by rw [List.countP_map]; rfl
    _ = _ := by rw [← List.ofFn_eq_map, List.ofFn_get]

/-- The actual OLD-index deletion and fresh zero births have exactly
this output zero count. Repeated numerical values remain distinct
indices; no squarefree or global-Nodup premise is inserted. -/
theorem source_original_GHOST_zero_count_exact434
    (old : List P) (atZero : P → Prop) [DecidablePred atZero]
    (A : Finset (Fin old.length)) (hA : A ⊆ zeroOld old atZero)
    {b : ℕ} (fresh : Fin b → P) (hf : ∀ i, atZero (fresh i)) :
    (zeroOld (afterGhost old A fresh) atZero).card =
      (zeroOld old atZero).card - A.card + b := by
  rw [zeroOld_card_count434]
  unfold afterGhost
  rw [List.countP_append, List.countP_map, List.countP_filter]
  have hOld :
      (List.finRange old.length).countP
        (fun i => decide (atZero (old.get i)) && decide (i ∉ A)) =
      (zeroOld old atZero \ A).card := by
    have h := count_finRange434 old.length
      (fun i => atZero (old.get i) ∧ i ∉ A)
    calc
      _ = (Finset.univ.filter
          (fun i => atZero (old.get i) ∧ i ∉ A)).card := by
        simpa only [Bool.decide_and] using h
      _ = _ := by
        congr 1
        ext i
        simp [zeroOld]
  have hFresh : (List.ofFn fresh).countP
      (fun p => decide (atZero p)) = b := by
    simp [List.ofFn_eq_map, List.countP_map, hf, Function.comp_def]
  change
    (List.finRange old.length).countP
      (fun i => decide (atZero (old.get i)) && decide (i ∉ A)) +
      (List.ofFn fresh).countP (fun p => decide (atZero p)) = _
  rw [hOld, hFresh, Finset.card_sdiff_of_subset hA]

/-- REAL original sourceGhostTerm: both endpoint rho dampings
cancel precisely the rho denominators of deletion, zero survival
and birth. The original signs, 1/b!, prime law and OLD indices
are unchanged. This is a coherent identity, not a norm estimate. -/
theorem source_original_GHOST_rho_term_cancellation434
    (old : List P) (atZero : P → Prop) [DecidablePred atZero]
    (A : Finset (Fin old.length)) (hA : A ⊆ zeroOld old atZero)
    {b : ℕ} (fresh : Fin b → P) (hf : ∀ i, atZero (fresh i))
    (rho α χ γ : ℂ) (hrho : rho ≠ 0) (nu : P → ℂ) :
    rho ^ (zeroOld old atZero).card *
      sourceGhostTerm old atZero A fresh
        (α/rho) (χ/rho^2) (γ/rho) nu *
      rho ^ (zeroOld (afterGhost old A fresh) atZero).card =
    sourceGhostTerm old atZero A fresh α χ γ nu := by
  rw [source_original_GHOST_zero_count_exact434 old atZero A hA fresh hf]
  unfold sourceGhostTerm
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Finset.card_le_card hA)
  rw [hr, Nat.add_sub_cancel_left]
  simp only [pow_add, div_pow, pow_two, mul_pow]
  have hfact : (Nat.factorial b : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero b
  field_simp
  <;> ring

/-- Complete original finite ghost kernel, retaining every deletion
and birth witness. Birth measure support at zero is the REAL source
property. Hence R_rho G_rho R_rho = G_1 for arbitrary complex
source coefficients; no termwise absolute bounds are taken. -/
theorem source_original_GHOST_rho_kernel_cancellation434
    (old next : List P) (atZero : P → Prop) [DecidablePred atZero]
    (B : ℕ) (rho α χ γ : ℂ) (hrho : rho ≠ 0)
    (nu : P → ℂ) (hnu : ∀ p, ¬atZero p → nu p = 0) :
    rho ^ (zeroOld old atZero).card *
      finiteGhostKernel old next atZero B
        (α/rho) (χ/rho^2) (γ/rho) nu *
      rho ^ (zeroOld next atZero).card =
    finiteGhostKernel old next atZero B α χ γ nu := by
  classical
  unfold finiteGhostKernel
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro fresh hfresh
  by_cases hout : afterGhost old A fresh = next
  · simp only [if_pos hout]
    by_cases hz : ∀ i, atZero (fresh i)
    · rw [← hout]
      exact source_original_GHOST_rho_term_cancellation434
        old atZero A (Finset.mem_powerset.mp hA) fresh hz
        rho α χ γ hrho nu
    · obtain ⟨i, hi⟩ := not_forall.mp hz
      have hprod : (∏ j : Fin b, nu (fresh j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (hnu (fresh i) hi)
      simp only [sourceGhostTerm, hprod, mul_zero, zero_mul]
  · simp only [if_neg hout, mul_zero, zero_mul]

/-- The original ordered Fock zero count agrees with the count on its
actual OLD list, including every repeated prime/residue atom. -/
theorem source_original_GHOST_Fock_zero_count434
    {modulus : P → ℕ} [∀ p, NeZero (modulus p)] {B : ℕ}
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    (zeroOld (Green64Fock.fockToList s)
      (fun a : Green64Fock.Atom P modulus => a.2 = 0)).card =
    Green64PhysicalEdge.oldZeroCount s := by
  rw [zeroOld_card_count434]
  unfold Green64Fock.fockToList
  rw [List.ofFn_eq_map, List.countP_map]
  exact count_finRange434 s.1.val (fun i => (s.2 i).2 = 0)

theorem source_original_GHOST_Fock_list_count434
    {modulus : P → ℕ} [∀ p, NeZero (modulus p)] {B : ℕ}
    (s : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    (Green64Fock.fockToList s).countP (fun a => decide (a.2 = 0)) =
      Green64PhysicalEdge.oldZeroCount s := by
  rw [← zeroOld_card_count434]
  exact source_original_GHOST_Fock_zero_count434 s

/-- ORIGINAL G_(i,g) coefficients, with true sourceBirthNu and
ordered finite Fock states. The support premise of the preceding
kernel identity is discharged by the original zero-residue birth law.
Take q=q_i and eta=1-q_i for the literal Memory equation. -/
theorem source_original_GHOST_actual_Fock_rho_cancellation434
    {modulus : P → ℕ} [∀ p, NeZero (modulus p)] {B : ℕ}
    (rho q eta V : ℝ) (hrho : rho ≠ 0) (mu : P → ℝ)
    (s t : Green64Fock.FockState (Green64Fock.Atom P modulus) B) :
    (rho : ℂ) ^ Green64PhysicalEdge.oldZeroCount s *
      Green64Fock.fockGhostKernel
        (fun a : Green64Fock.Atom P modulus => a.2 = 0)
        (-(eta : ℂ)/(rho : ℂ)) ((q : ℂ)/(rho : ℂ)^2)
        (-(eta : ℂ)*(V : ℂ)/(rho : ℂ))
        (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ))) s t *
      (rho : ℂ) ^ Green64PhysicalEdge.oldZeroCount t =
    Green64Fock.fockGhostKernel
      (fun a : Green64Fock.Atom P modulus => a.2 = 0)
      (-(eta : ℂ)) (q : ℂ) (-(eta : ℂ)*(V : ℂ))
      (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ))) s t := by
  have hr : (rho : ℂ) ≠ 0 := by exact_mod_cast hrho
  have h := source_original_GHOST_rho_kernel_cancellation434
    (Green64Fock.fockToList s) (Green64Fock.fockToList t)
    (fun a : Green64Fock.Atom P modulus => a.2 = 0) B
    (rho : ℂ) (-(eta : ℂ)) (q : ℂ) (-(eta : ℂ)*(V : ℂ)) hr
    (Green64Fock.sourceBirthNu (fun p => (mu p : ℂ)))
    (fun a ha => Green64Fock.birthMass_nonzero_residue _ a ha)
  simpa only [Green64Fock.fockGhostKernel,
    source_original_GHOST_Fock_zero_count434] using h
end Green64MemoryGhostOp

end

