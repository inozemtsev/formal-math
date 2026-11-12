module

public import Green64.Library.Weights.MarkedRefreshHilbert

@[expose] public section

/-!
# Weights / MarkedPacketHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedPacketHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {X U : Type} [Fintype X] [Fintype U] [DecidableEq U]

/-- A genuine packet is sampled once and all its numerical labels are
added to the same cumulative history. K may couple the complete two packets. -/
def sourceOriginalMarkedPacket434 (w : X → ℝ) (birth : X → Finset U)
    (K : X → Finset U → X → ℂ) (f : X → Finset U → ℂ)
    (x : X) (S : Finset U) : ℂ :=
  if birth x ⊆ S then
    ∑ y : X,if Disjoint S (birth y) then
      (w y:ℂ)*(K x S y*f y (S ∪ birth y)) else 0
  else 0

def sourceOriginalMarkedPacketEnergy434 (w : X → ℝ)
    (f : X → Finset U → ℂ) : ℝ :=
  ∑ S : Finset U,∑ x : X,w x*‖f x S‖^2

private theorem packet_history_inj (F : Finset U) :
    Set.InjOn (fun S : Finset U => S ∪ F)
      (↑((Finset.univ : Finset (Finset U)).filter (fun S => Disjoint S F))) := by
  intro S hS T hT h
  have hs := (Finset.mem_filter.mp hS).2
  have ht := (Finset.mem_filter.mp hT).2
  change S ∪ F = T ∪ F at h
  ext p
  constructor
  · intro hp
    have hu : p ∈ T ∪ F := by rw [←h]; exact Finset.mem_union_left F hp
    rcases Finset.mem_union.mp hu with hpT|hpF
    · exact hpT
    · exact False.elim (Finset.disjoint_left.mp hs hp hpF)
  · intro hp
    have hu : p ∈ S ∪ F := by rw [h]; exact Finset.mem_union_left F hp
    rcases Finset.mem_union.mp hu with hpS|hpF
    · exact hpS
    · exact False.elim (Finset.disjoint_left.mp ht hp hpF)

private theorem packet_history_energy (F : Finset U) (f : Finset U → ℂ) :
    (∑ S : Finset U,if Disjoint S F then ‖f (S ∪ F)‖^2 else 0) ≤
      ∑ T : Finset U,‖f T‖^2 := by
  classical
  let A := (Finset.univ : Finset (Finset U)).filter (fun S => Disjoint S F)
  calc
    _ = ∑ S ∈ A,‖f (S ∪ F)‖^2 := by rw [Finset.sum_filter]
    _ = ∑ T ∈ A.image (fun S => S ∪ F),‖f T‖^2 :=
      (Finset.sum_image (f:=fun T : Finset U => ‖f T‖^2)
        (s:=A) (g:=fun S => S ∪ F) (packet_history_inj F)).symm
    _ ≤ ∑ T : Finset U,‖f T‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun T _ _ => sq_nonneg _)

/-- Sharp packet Schur transfer retaining the same seen set on both sides.
The two packet masses are conditional on complementary parts of that set.
The application to the original BIG product law evaluates this premise. -/
theorem source_original_MARKED_PACKET_Hilbert434
    (w : X → ℝ) (hw : ∀ x,0 ≤ w x) (birth : X → Finset U)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hsplit : ∀ S : Finset U,
      (∑ x : X,if birth x ⊆ S then w x else 0) *
      (∑ y : X,if Disjoint S (birth y) then w y else 0) ≤ δ)
    (K : X → Finset U → X → ℂ) (hK : ∀ x S y,‖K x S y‖ ≤ 1)
    (f : X → Finset U → ℂ) :
    sourceOriginalMarkedPacketEnergy434 w (sourceOriginalMarkedPacket434 w birth K f) ≤
      δ*sourceOriginalMarkedPacketEnergy434 w f := by
  classical
  let a (S : Finset U) := ∑ x : X,if birth x ⊆ S then w x else 0
  let b (S : Finset U) := ∑ y : X,if Disjoint S (birth y) then w y else 0
  let B (S : Finset U) := ∑ y : X,if Disjoint S (birth y) then
    w y*‖f y (S ∪ birth y)‖^2 else 0
  have hB (S : Finset U) : 0 ≤ B S := by
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact mul_nonneg (hw y) (sq_nonneg _)
    · exact le_rfl
  have hrow (S : Finset U) (x : X) :
      ‖sourceOriginalMarkedPacket434 w birth K f x S‖^2 ≤
      if birth x ⊆ S then b S*B S else 0 := by
    by_cases hx : birth x ⊆ S
    · simp only [sourceOriginalMarkedPacket434,if_pos hx]
      let v (y : X) := if Disjoint S (birth y) then w y else 0
      have hv (y : X) : 0 ≤ v y := by
        dsimp only [v]
        split_ifs
        · exact hw y
        · exact le_rfl
      have hcs := source_original_finite_weighted_complex_kernel_CS434
        v hv (K x S) (fun y => f y (S ∪ birth y))
      have hk : (∑ y : X,v y*‖K x S y‖^2) ≤ b S := by
        apply Finset.sum_le_sum
        intro y hy
        exact (mul_le_mul_of_nonneg_left
          (by nlinarith [hK x S y,norm_nonneg (K x S y)]) (hv y)).trans_eq (mul_one _)
      have he : (∑ y : X,v y*‖f y (S ∪ birth y)‖^2)=B S := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp only [v]
        split_ifs <;> simp
      have hh := hcs.trans (mul_le_mul_of_nonneg_right hk
        (Finset.sum_nonneg (fun y _ => mul_nonneg (hv y) (sq_nonneg _))))
      rw [he] at hh
      convert hh using 1
      congr 2
      apply Finset.sum_congr rfl
      intro y hy
      dsimp only [v]
      split_ifs <;> simp
    · simp [sourceOriginalMarkedPacket434,hx]
  have hlocal (S : Finset U) :
      (∑ x : X,w x*‖sourceOriginalMarkedPacket434 w birth K f x S‖^2) ≤ δ*B S := by
    calc
      _ ≤ ∑ x : X,w x*(if birth x ⊆ S then b S*B S else 0) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrow S x) (hw x))
      _ = a S*(b S*B S) := by
        calc
          _ = ∑ x : X,(if birth x ⊆ S then w x else 0)*(b S*B S) := by
            apply Finset.sum_congr rfl
            intro x hx
            split_ifs <;> simp
          _ = _ := (Finset.sum_mul _ _ _).symm
      _ = (a S*b S)*B S := by ring
      _ ≤ δ*B S := mul_le_mul_of_nonneg_right (hsplit S) (hB S)
  have htotal : (∑ S : Finset U,B S) ≤ sourceOriginalMarkedPacketEnergy434 w f := by
    unfold B
    rw [Finset.sum_comm]
    calc
      _ = ∑ y : X,w y*(∑ S : Finset U,
          if Disjoint S (birth y) then ‖f y (S ∪ birth y)‖^2 else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        split_ifs <;> simp
      _ ≤ ∑ y : X,w y*(∑ S : Finset U,‖f y S‖^2) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
          (packet_history_energy (birth y) (f y)) (hw y))
      _ = sourceOriginalMarkedPacketEnergy434 w f := by
        simp only [Finset.mul_sum,sourceOriginalMarkedPacketEnergy434]
        rw [Finset.sum_comm]
  calc
    _ ≤ ∑ S : Finset U,δ*B S := Finset.sum_le_sum (fun S _ => hlocal S)
    _ = δ*(∑ S : Finset U,B S) := (Finset.mul_sum _ _ _).symm
    _ ≤ δ*sourceOriginalMarkedPacketEnergy434 w f :=
      mul_le_mul_of_nonneg_left htotal hδ

end Green64Analytic.CorrelationSquare

end

end

