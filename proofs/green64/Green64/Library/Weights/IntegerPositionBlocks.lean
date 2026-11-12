module

public import Mathlib

@[expose] public section

/-!
# Weights / IntegerPositionBlocks

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## IntegerPositionBlocks -/

section

open scoped BigOperators
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Integer physical-position blocks. Every mark state at one position has
the same block, with no enumeration or normalization by the number of marks. -/
def b652PositionBlocks434 {α : Type*} [Fintype α] (pos : α → ℤ) (H : ℤ) : Finset ℤ :=
  Finset.univ.image (fun x => pos x/H)

def b652PositionBlock434 {α : Type*} [Fintype α]
    (pos : α → ℤ) (H j : ℤ) (f : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun x => if pos x/H=j then f x else 0)

/-- The exact union of the previous, current, and next integer-position
blocks. This contains the H-neighborhood of the length-H block when H>=1. -/
def b652PositionNearBlock434 {α : Type*} [Fintype α]
    (pos : α → ℤ) (H j : ℤ) (g : EuclideanSpace ℂ α) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun x => if |pos x/H-j|≤1 then g x else 0)

/-- A genuine step bound in integer positions implies adjacency of quotient
blocks, including negative positions and every boundary point. -/
theorem b652_integer_step_blocks434
    (a b H : ℤ) (hH : 1≤H) (hstep : |a-b|≤H) : |a/H-b/H|≤1 := by
  have hHpos : 0<H := by omega
  rcases abs_le.mp hstep with ⟨hl,hu⟩
  have ha : a≤b+H := by omega
  have hb : b≤a+H := by omega
  have hqa := Int.ediv_le_ediv hHpos ha
  have hqb := Int.ediv_le_ediv hHpos hb
  have hea : (a+H)/H=a/H+1 := by simpa using Int.add_mul_ediv_right a 1 hHpos.ne'
  have heb : (b+H)/H=b/H+1 := by simpa using Int.add_mul_ediv_right b 1 hHpos.ne'
  rw [heb] at hqa
  rw [hea] at hqb
  exact abs_le.mpr ⟨by omega,by omega⟩

private theorem b652_position_block_mem434
    {α : Type*} [Fintype α] (pos : α → ℤ) (H : ℤ) (x : α) :
    pos x/H ∈ b652PositionBlocks434 pos H := by
  exact Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩

/-- Exact finite vector partition over physical positions, retaining every
mark coordinate of the original Hilbert vector. -/
theorem b652_position_blocks_sum434
    {α : Type*} [Fintype α] (pos : α → ℤ) (H : ℤ) (f : EuclideanSpace ℂ α) :
    ∑ j ∈ b652PositionBlocks434 pos H, b652PositionBlock434 pos H j f = f := by
  apply (WithLp.linearEquiv 2 ℂ (α → ℂ)).injective
  funext x
  change ((WithLp.linearEquiv 2 ℂ (α → ℂ))
    (∑ j ∈ b652PositionBlocks434 pos H, b652PositionBlock434 pos H j f)) x = f x
  rw [map_sum]
  simp only [Finset.sum_apply]
  change (∑ j ∈ b652PositionBlocks434 pos H, if pos x/H=j then f x else 0)=f x
  simp [b652_position_block_mem434 pos H x]

/-- Parseval across the disjoint integer-position blocks. There is exactly
one contribution from each physical mark state, with no mark-size loss. -/
theorem b652_position_blocks_norm_sq434
    {α : Type*} [Fintype α] (pos : α → ℤ) (H : ℤ) (f : EuclideanSpace ℂ α) :
    (∑ j ∈ b652PositionBlocks434 pos H, ‖b652PositionBlock434 pos H j f‖^2) = ‖f‖^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have he (j : ℤ) : ‖(b652PositionBlock434 pos H j f).ofLp x‖^2 =
      if pos x/H=j then ‖f x‖^2 else 0 := by
    by_cases h : pos x/H=j <;> simp [b652PositionBlock434,h]
  simp_rw [he]
  simp [b652_position_block_mem434 pos H x]

/-- Each state is contained in at most three neighboring quotient blocks.
The bound counts block indices, never states or marks. -/
theorem b652_near_block_count434 (s : Finset ℤ) (q : ℤ) :
    (s.filter (fun j => |q-j|≤1)).card ≤ 3 := by
  calc
    _ ≤ (Finset.Icc (q-1) (q+1)).card := by
      apply Finset.card_le_card
      intro j hj
      have h := abs_le.mp (Finset.mem_filter.mp hj).2
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    _ = 3 := by rw [Int.card_Icc]; omega

/-- True bounded overlap in the physical-state Hilbert norm. The terminal
vector g is arbitrary on every mark fibre, and the constant is exactly 3. -/
theorem b652_near_blocks_norm_sq_le434
    {α : Type*} [Fintype α] (pos : α → ℤ) (H : ℤ) (s : Finset ℤ)
    (g : EuclideanSpace ℂ α) :
    (∑ j ∈ s, ‖b652PositionNearBlock434 pos H j g‖^2) ≤ 3*‖g‖^2 := by
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have he (j : ℤ) : ‖(b652PositionNearBlock434 pos H j g).ofLp x‖^2 =
      if |pos x/H-j|≤1 then ‖g x‖^2 else 0 := by
    by_cases h : |pos x/H-j|≤1 <;> simp [b652PositionNearBlock434,h]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast b652_near_block_count434 s (pos x/H)
end Green64Analytic.SpectralEndpoint

end

end

