module

public import Green64.Library.Weights.IntegerPositionBlocks
public import Green64.Library.Correlation.ArbitraryRootCompression

@[expose] public section

/-!
# Correlation / PositionRootCompression

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PositionRootCompression -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The complete physical mark-fibre vector with its original common state
weight w. It is never divided by its norm or by the size of the fibre. -/
def b652PositionRoot434 {α : Type*} [Fintype α]
    (pos : α → ℤ) (w : ℂ) (n : ℤ) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun x => if pos x=n then w else 0)

/-- A literal position-constant first endpoint, supported on I. The second
endpoint in the eventual pairing theorem remains arbitrary on all marks. -/
def b652FirstPositionVector434 {α : Type*} [Fintype α]
    (pos : α → ℤ) (w : ℂ) (I : Finset ℤ) (c : ℤ → ℂ) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun x => if pos x∈I then c (pos x)*w else 0)

/-- The true fibre norms depend on the number of states at the position. -/
theorem b652_position_root_norm_sq434
    {α : Type*} [Fintype α] (pos : α → ℤ) (w : ℂ) (n : ℤ) :
    ‖b652PositionRoot434 pos w n‖^2 =
      ((Finset.univ.filter (fun x : α => pos x=n)).card : ℝ)*‖w‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have he (x : α) : ‖(b652PositionRoot434 pos w n).ofLp x‖^2 =
      if pos x=n then ‖w‖^2 else 0 := by
    by_cases h : pos x=n <;> simp [b652PositionRoot434,h]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]

/-- An integer quotient block contains at most H POSITIONS. Mark-state
multiplicities do not enter this cardinality statement. -/
theorem b652_position_fibre_card434
    (I : Finset ℤ) (H j : ℤ) (hH : 1≤H) :
    (I.filter (fun n => n/H=j)).card ≤ H.toNat := by
  have hHpos : 0<H := by omega
  calc
    _ ≤ (Finset.Icc (j*H) ((j+1)*H-1)).card := by
      apply Finset.card_le_card
      intro n hn
      have hq := (Finset.mem_filter.mp hn).2
      have he := Int.ediv_mul_add_emod n H
      rw [hq] at he
      have hr0 := Int.emod_nonneg n hHpos.ne'
      have hr1 := Int.emod_lt_of_pos n hHpos
      have hrle : n%H≤H-1 := by omega
      exact Finset.mem_Icc.mpr ⟨by nlinarith,by nlinarith⟩
    _ = H.toNat := by
      rw [Int.card_Icc]
      congr 1
      ring

/-- The original positional coefficient mass costs H times the squared
pointwise bound, without a mark-fibre factor. -/
theorem b652_position_block_coefficient_mass434
    (I : Finset ℤ) (H j : ℤ) (hH : 1≤H) (c : ℤ → ℂ) (C : ℝ)
    (hC : ∀ n∈I, ‖c n‖≤C) :
    (∑ n ∈ I.filter (fun n => n/H=j), ‖c n‖^2) ≤ (H:ℝ)*C^2 := by
  have hcast : (H.toNat:ℝ)=(H:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0≤H)
  calc
    _ ≤ ∑ _n ∈ I.filter (fun n => n/H=j), C^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hC n (Finset.mem_filter.mp hn).1) 2
    _ = ((I.filter (fun n => n/H=j)).card : ℝ)*C^2 := by simp
    _ ≤ (H.toNat:ℝ)*C^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg C)
      exact_mod_cast b652_position_fibre_card434 I H j hH
    _ = _ := by rw [hcast]

/-- The first endpoint is exactly the sum of the complete root fibres,
using the actual positional coefficients and the unchanged state weight. -/
theorem b652_first_position_frame434
    {α : Type*} [Fintype α] (pos : α → ℤ) (w : ℂ) (I : Finset ℤ) (c : ℤ → ℂ) :
    b652FirstPositionVector434 pos w I c =
      ∑ n ∈ I, c n • b652PositionRoot434 pos w n := by
  apply (WithLp.linearEquiv 2 ℂ (α → ℂ)).injective
  funext x
  change (if pos x∈I then c (pos x)*w else 0)=
    ((WithLp.linearEquiv 2 ℂ (α → ℂ)) (∑ n ∈ I, c n • b652PositionRoot434 pos w n)) x
  rw [map_sum]
  simp only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  change (if pos x∈I then c (pos x)*w else 0)=
    ∑ n ∈ I, c n*(if pos x=n then w else 0)
  have he (n : ℤ) : c n*(if pos x=n then w else 0) =
      if pos x=n then c (pos x)*w else 0 := by
    by_cases hn : pos x=n
    · subst n
      simp
    · simp [hn]
  simp_rw [he]
  simp

private theorem b652_first_position_block434
    {α : Type*} [Fintype α] (pos : α → ℤ) (w : ℂ) (I : Finset ℤ)
    (c : ℤ → ℂ) (H j : ℤ) :
    b652PositionBlock434 pos H j (b652FirstPositionVector434 pos w I c) =
      b652FirstPositionVector434 pos w (I.filter (fun n => n/H=j)) c := by
  apply (WithLp.linearEquiv 2 ℂ (α → ℂ)).injective
  funext x
  by_cases hm : pos x∈I <;> by_cases hq : pos x/H=j <;>
    simp [b652PositionBlock434,b652FirstPositionVector434,hm,hq]

/-- Complete position-root compression of the sum of localized moments.
The only coefficient input is its literal pointwise bound on positions.
The root vectors keep their actual unequal norms, and every diagonal
moment of T^R at a root is counted at most once. -/
theorem b652_position_root_block_moment434
    {α : Type*} [Fintype α] (pos : α → ℤ) (w : ℂ) (I : Finset ℤ)
    (c : ℤ → ℂ) (C : ℝ) (hC : ∀ n∈I, ‖c n‖≤C)
    (H : ℤ) (hH : 1≤H) (T : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α)
    (hT : T.IsPositive) (R : ℕ) :
    (∑ j ∈ b652PositionBlocks434 pos H,
      (inner ℂ (b652PositionBlock434 pos H j (b652FirstPositionVector434 pos w I c))
        ((T^R) (b652PositionBlock434 pos H j (b652FirstPositionVector434 pos w I c)))).re) ≤
      ((H:ℝ)*C^2) * ∑ n ∈ I,
        (inner ℂ (b652PositionRoot434 pos w n) ((T^R) (b652PositionRoot434 pos w n))).re := by
  let J := b652PositionBlocks434 pos H
  let d := fun n =>
    (inner ℂ (b652PositionRoot434 pos w n) ((T^R) (b652PositionRoot434 pos w n))).re
  have hd (n : ℤ) : 0≤d n := (b649_positive_power434 T hT R).re_inner_nonneg_right _
  have hloc (j : ℤ) :
      (inner ℂ (b652PositionBlock434 pos H j (b652FirstPositionVector434 pos w I c))
        ((T^R) (b652PositionBlock434 pos H j (b652FirstPositionVector434 pos w I c)))).re ≤
      ((H:ℝ)*C^2) * ∑ n ∈ I.filter (fun n => n/H=j), d n := by
    have hf := (b652_first_position_block434 pos w I c H j).trans
      (b652_first_position_frame434 pos w (I.filter (fun n => n/H=j)) c)
    have hc := b649_arbitrary_root_power_compression434
      (I.filter (fun n => n/H=j)) c (b652PositionRoot434 pos w) T hT R
    rw [hf]
    refine hc.trans ?_
    exact mul_le_mul_of_nonneg_right (b652_position_block_coefficient_mass434 I H j hH c C hC)
      (Finset.sum_nonneg fun n _ => hd n)
  have hsum : (∑ j ∈ J, ∑ n ∈ I.filter (fun n => n/H=j), d n) ≤ ∑ n ∈ I, d n := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n _
    by_cases h : n/H∈J
    · simp [h]
    · simp [h]
      exact hd n
  calc
    _ ≤ ∑ j ∈ J, ((H:ℝ)*C^2) * ∑ n ∈ I.filter (fun n => n/H=j), d n :=
      Finset.sum_le_sum fun j _ => hloc j
    _ = ((H:ℝ)*C^2) * ∑ j ∈ J, ∑ n ∈ I.filter (fun n => n/H=j), d n :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by exact_mod_cast (show 0≤H by omega)) (sq_nonneg C))
end Green64Analytic.SpectralEndpoint

end

end

