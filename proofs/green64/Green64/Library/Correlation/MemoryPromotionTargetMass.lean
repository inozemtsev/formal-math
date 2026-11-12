module

public import Green64.Library.Correlation.Part043
public import Green64.Library.Correlation.Part001

@[expose] public section

/-!
# Correlation / MemoryPromotionTargetMass

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryPromotionTargetMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

private theorem real_fixed_target_total434
    {I P : Type} [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]
    (S : Finset I) (a : I → P) (mu : P → ℝ) :
    (∑ t : I → P,∏ i : I,if i ∈ S then
      (if t i=a i then (1:ℝ) else 0) else mu (t i)) =
      (∑ p : P,mu p)^((Finset.univ \ S).card) := by
  have he : (∑ t : I → P,∏ i : I,if i ∈ S then
      (if t i=a i then (1:ℝ) else 0) else mu (t i)) =
      ∏ i : I,∑ p : P,if i ∈ S then (if p=a i then (1:ℝ) else 0) else mu p := by
    simpa using (Fintype.prod_sum (fun (i : I) (p : P) =>
      if i ∈ S then (if p=a i then (1:ℝ) else 0) else mu p)).symm
  rw [he]
  have hc (i : I) :
      (∑ p : P,if i ∈ S then (if p=a i then (1:ℝ) else 0) else mu p) =
      if i ∈ S then 1 else ∑ p : P,mu p := by
    by_cases hi : i ∈ S <;> simp [hi]
  simp_rw [hc]
  simp [Finset.prod_ite,Finset.prod_const,Finset.filter_notMem_eq_sdiff]

/-- Exact target product law with arbitrary fixed shared/promoted labels
in the actual independently permuted target coordinates. -/
theorem source_original_memory_oriented_fixed_target_total434
    {P : Type} [Fintype P] [DecidableEq P] (M : ℕ)
    (S : Finset (Fin M)) (a : Fin M → P)
    (tau : Equiv.Perm (Fin M)) (mu : P → ℝ) :
    (∑ t : Fin M → P,∏ i : Fin M,if tau.symm i ∈ S then
      (if t i=a (tau.symm i) then (1:ℝ) else 0) else mu (t i)) =
      (∑ p : P,mu p)^(M-S.card) := by
  let T := S.map tau.toEmbedding
  have hMem (i : Fin M) : i ∈ T ↔ tau.symm i ∈ S := Finset.mem_map_equiv
  have hh := real_fixed_target_total434 T (fun i => a (tau.symm i)) mu
  simp_rw [hMem] at hh
  simpa [T,Finset.card_sdiff] using hh

private theorem real_fixed_target_product434
    {P : Type} [Fintype P] [DecidableEq P] (M : ℕ)
    (S : Finset (Fin M)) (a t : Fin M → P)
    (tau : Equiv.Perm (Fin M)) (mu : P → ℝ)
    (hCopy : ∀ j ∈ S,t (tau j)=a j) :
    (∏ i : Fin M,if tau.symm i ∈ S then
      (if t i=a (tau.symm i) then (1:ℝ) else 0) else mu (t i)) =
      ∏ j ∈ Finset.univ \ S,mu (t (tau j)) := by
  let w := fun i : Fin M => if tau.symm i ∈ S then
    (if t i=a (tau.symm i) then (1:ℝ) else 0) else mu (t i)
  have he := Fintype.prod_equiv tau (fun j => w (tau j)) w (fun _ => rfl)
  have hh : (∏ i : Fin M,w i) = ∏ j : Fin M,
      if j ∈ S then (if t (tau j)=a j then (1:ℝ) else 0) else mu (t (tau j)) := by
    simpa only [w,Equiv.symm_apply_apply] using he.symm
  change (∏ i : Fin M,w i) = _
  rw [hh,Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter,Finset.filter_notMem_eq_sdiff,Finset.univ_inter]
  have hOne : (∏ j ∈ S,if t (tau j)=a j then (1:ℝ) else 0)=1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [if_pos (hCopy j hj)]
  rw [hOne,one_mul]

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- Full target integration for a fixed actual store/promotion/injection
choice. All physical legality tests remain in the left side. -/
theorem source_original_memory_BIG_fixed_choice_target_bound434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho : ℝ)
    (hV : 0<V) (hr : 0 ≤ rho)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hA : c.2.1 ⊆ orientedUnshared M shared) :
    (∑ t : Fin M → P,if OrientedBigEdgeLegal modulus M B x t shared
      sigma tau D step c then
      ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
      else 0) ≤
      (rho^(Green64PhysicalEdge.oldZeroCount x.2+
        outputZeroCount modulus M B x sigma step c) / V^c.2.1.card) *
        (∑ p : P,mu p)^(M-(shared ∪ c.2.1).card) := by
  classical
  let S := shared ∪ c.2.1
  let a := fun j : Fin M => if hj : j ∈ c.2.1 then
    (x.2.2 (c.2.2 ⟨j,hj⟩)).1 else x.1 (sigma j)
  let C := rho^(Green64PhysicalEdge.oldZeroCount x.2+
    outputZeroCount modulus M B x sigma step c) / V^c.2.1.card
  let law := fun t : Fin M → P => ∏ i : Fin M,if tau.symm i ∈ S then
    (if t i=a (tau.symm i) then (1:ℝ) else 0) else mu (t i)
  have hC : 0 ≤ C := div_nonneg (pow_nonneg hr _) (pow_nonneg hV.le _)
  have hLaw (t : Fin M → P) : 0 ≤ law t := by
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> first | positivity | exact hmu _
  have hFresh : orientedFresh M shared c.2.1=Finset.univ \ S := by
    ext i
    simp [orientedFresh,orientedUnshared,S]
  have hAbs (p : P) : |mu p|=mu p := abs_of_nonneg (hmu p)
  have hNorm (t : Fin M → P) :
      ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖ =
      C*∏ j ∈ orientedFresh M shared c.2.1,mu (t (tau j)) := by
    simp only [orientedBigBranchCoefficient,norm_mul,norm_pow,norm_div,norm_one,norm_prod,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,abs_of_pos hV,hAbs,C]
    ring
  have hEach (t : Fin M → P) :
      (if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c then
        ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
        else 0) ≤ C*law t := by
    split_ifs with ht
    · have hCopy (j : Fin M) (hj : j ∈ S) : t (tau j)=a j := by
        dsimp only [a]
        split_ifs with hja
        · exact ht.promoted_matches ⟨j,hja⟩
        · have hjs : j ∈ shared := (Finset.mem_union.mp hj).resolve_right hja
          exact (ht.shared_copy j hjs).symm
      have hl : law t=∏ j ∈ orientedFresh M shared c.2.1,mu (t (tau j)) := by
        rw [hFresh]
        exact real_fixed_target_product434 M S a t tau mu hCopy
      rw [hNorm,hl]
    · exact mul_nonneg hC (hLaw t)
  calc
    _ ≤ ∑ t : Fin M → P,C*law t := Finset.sum_le_sum (fun t _ => hEach t)
    _ = C*∑ t : Fin M → P,law t := (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [source_original_memory_oriented_fixed_target_total434]

/-- A fixed actual branch has at most d fresh integrations, giving a
constant independent of the total active slot count M. -/
theorem source_original_memory_BIG_fixed_choice_target_cap434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R : ℝ)
    (hV : 0<V) (hr : 0 ≤ rho) (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (c : BigEdgeChoice modulus M B x)
    (hA : c.2.1 ⊆ orientedUnshared M shared)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ t : Fin M → P,if OrientedBigEdgeLegal modulus M B x t shared
      sigma tau D step c then
      ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared sigma tau step c‖
      else 0) ≤
      (rho^(Green64PhysicalEdge.oldZeroCount x.2+
        outputZeroCount modulus M B x sigma step c) / V^c.2.1.card) * R^d := by
  have hsize : M-(shared ∪ c.2.1).card ≤ d := by
    have hh : (Finset.univ \ (shared ∪ c.2.1)).card ≤ (orientedUnshared M shared).card :=
      Finset.card_le_card (by intro i hi;simp only [Finset.mem_sdiff,Finset.mem_univ,
        true_and,Finset.mem_union,not_or] at hi;exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi.1⟩)
    have he : (Finset.univ \ (shared ∪ c.2.1)).card=M-(shared ∪ c.2.1).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      exact congrArg (fun n => n-(shared ∪ c.2.1).card) (Fintype.card_fin M)
    rw [he] at hh
    exact hh.trans hd
  have hpow : (∑ p : P,mu p)^(M-(shared ∪ c.2.1).card) ≤ R^d :=
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => hmu p)) hMass _).trans
      (pow_right_mono₀ hR hsize)
  exact (source_original_memory_BIG_fixed_choice_target_bound434 modulus M B mu hmu
    V rho hV hr x shared sigma tau D step c hA).trans
      (mul_le_mul_of_nonneg_left hpow (div_nonneg (pow_nonneg hr _) (pow_nonneg hV.le _)))
end Green64Analytic.CorrelationSquare

end

end

