module

public import Green64.Library.Weights.Part018
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Weights / MarkedRefreshHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMarkedRefreshHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {P : Type} [Fintype P] [DecidableEq P]

/-- The active tuple and its actual cumulative history use one density:
the product of the original prime weights, with counting measure in seen. -/
def sourceOriginalRefreshTupleMass434 (r : ℕ) (mu : P → ℝ)
    (x : Fin r → P) : ℝ := ∏ i,mu (x i)

def sourceOriginalRefreshSeen434 (r : ℕ) (x : Fin r → P) : Finset P :=
  Finset.univ.image x

/-- A literal fresh batch: every old active label was already seen and
every new target label is outside seen. The future reads the updated seen.
Additional legality, distinctness and joint complex coefficients belong to K. -/
def sourceOriginalMarkedRefresh434 (r : ℕ) (mu : P → ℝ)
    (K : (Fin r → P) → Finset P → (Fin r → P) → ℂ)
    (f : (Fin r → P) → Finset P → ℂ)
    (x : Fin r → P) (S : Finset P) : ℂ :=
  if ∀ i,x i ∈ S then
    ∑ y : Fin r → P,
      if Disjoint S (sourceOriginalRefreshSeen434 r y) then
        (sourceOriginalRefreshTupleMass434 r mu y : ℂ) *
          (K x S y * f y (S ∪ sourceOriginalRefreshSeen434 r y))
      else 0
  else 0

def sourceOriginalMarkedRefreshEnergy434 (r : ℕ) (mu : P → ℝ)
    (f : (Fin r → P) → Finset P → ℂ) : ℝ :=
  ∑ S : Finset P,∑ x : Fin r → P,
    sourceOriginalRefreshTupleMass434 r mu x * ‖f x S‖^2

private theorem tuple_mass_nonneg (r : ℕ) (mu : P → ℝ)
    (hmu : ∀ p,0 ≤ mu p) (x : Fin r → P) :
    0 ≤ sourceOriginalRefreshTupleMass434 r mu x :=
  Finset.prod_nonneg (fun i _ => hmu (x i))

private theorem tuple_mass_restricted (r : ℕ) (mu : P → ℝ)
    (S : Finset P) :
    (∑ x : Fin r → P,
      if ∀ i,x i ∈ S then sourceOriginalRefreshTupleMass434 r mu x else 0) =
      (∑ p ∈ S,mu p)^r := by
  classical
  have hi (x : Fin r → P) :
      (if ∀ i,x i ∈ S then sourceOriginalRefreshTupleMass434 r mu x else 0) =
      ∏ i : Fin r,if x i ∈ S then mu (x i) else 0 := by
    by_cases hx : ∀ i,x i ∈ S
    · simp only [if_pos hx,sourceOriginalRefreshTupleMass434,if_pos (hx _)]
    · rw [if_neg hx]
      obtain ⟨i,hi⟩ := not_forall.mp hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp_rw [hi]
  calc
    _ = ∏ i : Fin r,∑ p : P,if p ∈ S then mu p else 0 :=
      (Fintype.prod_sum (fun (_ : Fin r) (p : P) => if p ∈ S then mu p else 0)).symm
    _ = _ := by simp [←Finset.sum_filter]

private theorem fresh_iff (r : ℕ) (S : Finset P) (y : Fin r → P) :
    Disjoint S (sourceOriginalRefreshSeen434 r y) ↔ ∀ i,y i ∈ Sᶜ := by
  classical
  constructor
  · intro hd i
    apply Finset.mem_compl.mpr
    intro hi
    exact Finset.disjoint_left.mp hd hi
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · intro hy
    apply Finset.disjoint_left.mpr
    intro p hp hpy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hpy
    exact (Finset.mem_compl.mp (hy i)) hp

private theorem seen_update_injective (F : Finset P) :
    Set.InjOn (fun S : Finset P => S ∪ F)
      (↑((Finset.univ : Finset (Finset P)).filter (fun S => Disjoint S F))) := by
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

private theorem seen_update_energy_le (F : Finset P) (f : Finset P → ℂ) :
    (∑ S : Finset P,if Disjoint S F then ‖f (S ∪ F)‖^2 else 0) ≤
      ∑ T : Finset P,‖f T‖^2 := by
  classical
  let A := (Finset.univ : Finset (Finset P)).filter (fun S => Disjoint S F)
  calc
    _ = ∑ S ∈ A,‖f (S ∪ F)‖^2 := by
      rw [Finset.sum_filter]
    _ = ∑ T ∈ A.image (fun S => S ∪ F),‖f T‖^2 :=
      (Finset.sum_image (f := fun T : Finset P => ‖f T‖^2)
        (s := A) (g := fun S => S ∪ F) (seen_update_injective F)).symm
    _ ≤ ∑ T : Finset P,‖f T‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun T _ _ => sq_nonneg _)

/-- True no-rebirth L2 gain for an entire fresh batch and every complex
future on active x seen. It uses the complementary seen/unseen masses;
there is no cardinality of histories and no bound on the future. -/
theorem source_original_MARKED_REFRESH_Hilbert434
    (r : ℕ) (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p)
    (K : (Fin r → P) → Finset P → (Fin r → P) → ℂ)
    (hK : ∀ x S y,‖K x S y‖ ≤ 1)
    (f : (Fin r → P) → Finset P → ℂ) :
    sourceOriginalMarkedRefreshEnergy434 r mu
      (sourceOriginalMarkedRefresh434 r mu K f) ≤
      (((∑ p : P,mu p)^2 / 4)^r) *
        sourceOriginalMarkedRefreshEnergy434 r mu f := by
  classical
  let w := sourceOriginalRefreshTupleMass434 r mu
  let a : Finset P → ℝ := fun S => ∑ p ∈ S,mu p
  let b : Finset P → ℝ := fun S => ∑ p ∈ Sᶜ,mu p
  let B : Finset P → ℝ := fun S =>
    ∑ y : Fin r → P,if Disjoint S (sourceOriginalRefreshSeen434 r y) then
      w y * ‖f y (S ∪ sourceOriginalRefreshSeen434 r y)‖^2 else 0
  let C : ℝ := ((∑ p : P,mu p)^2 / 4)^r
  have hw (x : Fin r → P) : 0 ≤ w x := tuple_mass_nonneg r mu hmu x
  have hB (S : Finset P) : 0 ≤ B S := by
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact mul_nonneg (hw y) (sq_nonneg _)
    · exact le_rfl
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (S : Finset P) (x : Fin r → P) :
      ‖sourceOriginalMarkedRefresh434 r mu K f x S‖^2 ≤
      if ∀ i,x i ∈ S then (b S)^r * B S else 0 := by
    by_cases hx : ∀ i,x i ∈ S
    · simp only [sourceOriginalMarkedRefresh434,if_pos hx]
      let v : (Fin r → P) → ℝ := fun y =>
        if Disjoint S (sourceOriginalRefreshSeen434 r y) then w y else 0
      have hv (y : Fin r → P) : 0 ≤ v y := by
        dsimp only [v]
        split_ifs
        · exact hw y
        · exact le_rfl
      have hcs := source_original_finite_weighted_complex_kernel_CS434
        v hv (K x S) (fun y => f y (S ∪ sourceOriginalRefreshSeen434 r y))
      have hvsum : (∑ y : Fin r → P,v y) = (b S)^r := by
        simp_rw [v,fresh_iff]
        exact tuple_mass_restricted r mu Sᶜ
      have hk : (∑ y : Fin r → P,v y * ‖K x S y‖^2) ≤ (b S)^r := by
        rw [←hvsum]
        apply Finset.sum_le_sum
        intro y hy
        exact (mul_le_mul_of_nonneg_left
          (by nlinarith [hK x S y,norm_nonneg (K x S y)]) (hv y)).trans_eq (mul_one _)
      have he : (∑ y : Fin r → P,v y *
          ‖f y (S ∪ sourceOriginalRefreshSeen434 r y)‖^2) = B S := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [v,B]
        split_ifs <;> simp
      have hh := hcs.trans (mul_le_mul_of_nonneg_right hk
        (Finset.sum_nonneg (fun y _ => mul_nonneg (hv y) (sq_nonneg _))))
      rw [he] at hh
      convert hh using 1
      congr 2
      apply Finset.sum_congr rfl
      intro y hy
      dsimp only [v,w]
      split_ifs <;> simp
    · simp [sourceOriginalMarkedRefresh434,hx]
  have hab (S : Finset P) : (a S)^r * (b S)^r ≤ C := by
    have ha : 0 ≤ a S := Finset.sum_nonneg (fun p _ => hmu p)
    have hb : 0 ≤ b S := Finset.sum_nonneg (fun p _ => hmu p)
    have hs : a S+b S=∑ p : P,mu p := Finset.sum_add_sum_compl S mu
    rw [←mul_pow]
    apply pow_le_pow_left₀ (mul_nonneg ha hb)
    nlinarith [sq_nonneg (a S-b S)]
  have hlocal (S : Finset P) :
      (∑ x : Fin r → P,w x *
        ‖sourceOriginalMarkedRefresh434 r mu K f x S‖^2) ≤ C*B S := by
    calc
      _ ≤ ∑ x : Fin r → P,w x *
          (if ∀ i,x i ∈ S then (b S)^r*B S else 0) :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrow S x) (hw x))
      _ = (∑ x : Fin r → P,if ∀ i,x i ∈ S then w x else 0) *
          ((b S)^r*B S) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> simp
      _ = ((a S)^r*(b S)^r)*B S := by
        rw [tuple_mass_restricted]
        dsimp only [a]
        ring
      _ ≤ C*B S := mul_le_mul_of_nonneg_right (hab S) (hB S)
  have htotal : (∑ S : Finset P,B S) ≤ sourceOriginalMarkedRefreshEnergy434 r mu f := by
    unfold B
    rw [Finset.sum_comm]
    calc
      _ = ∑ y : Fin r → P,w y *
          (∑ S : Finset P,if Disjoint S (sourceOriginalRefreshSeen434 r y) then
            ‖f y (S ∪ sourceOriginalRefreshSeen434 r y)‖^2 else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        split_ifs <;> simp
      _ ≤ ∑ y : Fin r → P,w y * (∑ S : Finset P,‖f y S‖^2) :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
          (seen_update_energy_le (sourceOriginalRefreshSeen434 r y) (f y)) (hw y))
      _ = sourceOriginalMarkedRefreshEnergy434 r mu f := by
        simp only [Finset.mul_sum,sourceOriginalMarkedRefreshEnergy434,w]
        rw [Finset.sum_comm]
  calc
    _ ≤ ∑ S : Finset P,C*B S := Finset.sum_le_sum (fun S _ => hlocal S)
    _ = C*(∑ S : Finset P,B S) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*sourceOriginalMarkedRefreshEnergy434 r mu f :=
      mul_le_mul_of_nonneg_left htotal hC

/-- Under the original normalized harmonic law, each fresh active slot
contributes the exact squared-norm factor 1/4, even for a history-dependent
joint complex multiplier of modulus at most one. -/
theorem source_original_MARKED_REFRESH_normalized_Hilbert434
    (r : ℕ) (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p)
    (hmass : ∑ p : P,mu p=1)
    (K : (Fin r → P) → Finset P → (Fin r → P) → ℂ)
    (hK : ∀ x S y,‖K x S y‖ ≤ 1)
    (f : (Fin r → P) → Finset P → ℂ) :
    sourceOriginalMarkedRefreshEnergy434 r mu
      (sourceOriginalMarkedRefresh434 r mu K f) ≤
      (1/4:ℝ)^r * sourceOriginalMarkedRefreshEnergy434 r mu f := by
  simpa only [hmass,one_pow] using
    source_original_MARKED_REFRESH_Hilbert434 r mu hmu K hK f

end Green64Analytic.CorrelationSquare

end

end

