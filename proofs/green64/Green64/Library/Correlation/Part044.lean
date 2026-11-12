module

public import Green64.Library.Correlation.MemoryPromotionTargetMass
public import Green64.Library.Correlation.Part043
public import Green64.Library.Weights.Part057
public import Green64.Library.Correlation.Part008
public import Green64.Library.Correlation.Part005
public import Green64.Library.Weights.Part054

@[expose] public section

/-!
# Correlation / Part044

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalMemoryRetrievalTargetRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- Complete fixed-store/fixed-promotion row: all ordered OLD injections
and all target tuples, with the literal input/output damping. -/
theorem source_original_memory_BIG_retrieval_target_row434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1)
    (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (S A : Finset (Fin M)) (hA : A ⊆ orientedUnshared M shared)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared
        sigma tau step (S,⟨A,f⟩)‖ else 0) ≤
      memoryPromotionDampingConstant rho d * ((V^A.card)⁻¹*R^d) := by
  classical
  let good := (Finset.univ : Finset (↥A ↪ Fin x.2.1.val)).filter
    (fun f => ∀ a,f a ∈ memoryTranslatedOldZero modulus M B x step)
  let row := fun f : ↥A ↪ Fin x.2.1.val => ∑ t : Fin M → P,
    if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
    then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared
      sigma tau step (S,⟨A,f⟩)‖ else 0
  let damp := fun f : ↥A ↪ Fin x.2.1.val =>
    rho^(Green64PhysicalEdge.oldZeroCount x.2+
      outputZeroCount modulus M B x sigma step (S,⟨A,f⟩))
  let C := (V^A.card)⁻¹*R^d
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr (pow_nonneg hV.le _))
    (pow_nonneg (le_trans zero_le_one hR) _)
  have hcut : (∑ f,row f)=∑ f ∈ good,row f := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro f hf hbad
    have hn : ¬ ∀ a,f a ∈ memoryTranslatedOldZero modulus M B x step := by
      simpa only [good,Finset.mem_filter,Finset.mem_univ,true_and] using hbad
    apply Finset.sum_eq_zero
    intro t ht
    exact if_neg (fun hlegal => hn (memory_legal_promotion_into_zero
      modulus M B x t shared sigma tau D step (S,⟨A,f⟩) hlegal))
  have hEach (f : ↥A ↪ Fin x.2.1.val) : row f ≤ damp f*C := by
    simpa only [row,damp,C,div_eq_mul_inv,mul_assoc] using
      source_original_memory_BIG_fixed_choice_target_cap434 modulus M B mu hmu
        V rho R hV hr.le hR hMass x shared sigma tau D step (S,⟨A,f⟩) hA d hd
  have hsum : (∑ f ∈ good,damp f) ≤ memoryPromotionDampingConstant rho d :=
    source_original_memory_actual_retrieval_damping_sum434 modulus M B x sigma step
      S A rho hr hr1 d ((Finset.card_le_card hA).trans hd)
  change (∑ f,row f) ≤ _
  rw [hcut]
  calc
    _ ≤ ∑ f ∈ good,damp f*C := Finset.sum_le_sum (fun f _ => hEach f)
    _ = (∑ f ∈ good,damp f)*C := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum hC

/-- A fixed store/promotion row has a constant independent of the number
of active slots and OLD memory particles. -/
theorem source_original_memory_BIG_retrieval_target_uniform434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1)
    (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (S A : Finset (Fin M)) (hA : A ⊆ orientedUnshared M shared)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared
        sigma tau step (S,⟨A,f⟩)‖ else 0) ≤
      memoryPromotionDampingConstant rho d * ((max 1 V⁻¹)^d*R^d) := by
  have ha : A.card ≤ d := (Finset.card_le_card hA).trans hd
  have hv : (V^A.card)⁻¹ ≤ (max 1 V⁻¹)^d := by
    rw [← inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hV.le) (le_max_right _ _) _).trans
      (pow_right_mono₀ (le_max_left _ _) ha)
  have hc : 0 ≤ memoryPromotionDampingConstant rho d := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    apply Finset.sum_nonneg
    intro a ha
    positivity
  exact (source_original_memory_BIG_retrieval_target_row434 modulus M B mu hmu
    V rho R hV hr hr1 hR hMass x shared sigma tau D step S A hA d hd).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hv (pow_nonneg (le_trans zero_le_one hR) _)) hc)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryCompleteBigRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)

/-- The complete literal absolute BIG row, including all targets, stores,
promotion subsets and ordered OLD injections. Its constant is independent
of the active slot count, OLD length, residue step and cutoff. -/
theorem source_original_memory_BIG_complete_absolute_row434
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1)
    (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus M B) (shared : Finset (Fin M))
    (sigma tau : Equiv.Perm (Fin M)) (D : ℕ) (step : ℤ)
    (d : ℕ) (hd : (orientedUnshared M shared).card ≤ d) :
    (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared
        sigma tau step c‖ else 0) ≤
      (4:ℝ)^d * (memoryPromotionDampingConstant rho d *
        ((max 1 V⁻¹)^d*R^d)) := by
  classical
  let U := orientedUnshared M shared
  let row := fun S A : Finset (Fin M) =>
    ∑ f : ↥A ↪ Fin x.2.1.val,∑ t : Fin M → P,
      if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step (S,⟨A,f⟩)
      then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared
        sigma tau step (S,⟨A,f⟩)‖ else 0
  let C := memoryPromotionDampingConstant rho d * ((max 1 V⁻¹)^d*R^d)
  have hC : 0 ≤ C := by
    have hmem : 0 ≤ memoryPromotionDampingConstant rho d := by
      have hh : 0<1-rho := sub_pos.mpr hr1
      unfold memoryPromotionDampingConstant
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    exact mul_nonneg hmem (mul_nonneg
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
      (pow_nonneg (le_trans zero_le_one hR) _))
  have hrow (S A : Finset (Fin M)) (hA : A ⊆ U) : row S A ≤ C :=
    source_original_memory_BIG_retrieval_target_uniform434 modulus M B mu hmu
      V rho R hV hr hr1 hR hMass x shared sigma tau D step S A hA d hd
  have hzero (S A : Finset (Fin M)) (hbad : ¬ S ⊆ U ∨ ¬ A ⊆ U) :
      row S A=0 := by
    apply Finset.sum_eq_zero
    intro f hf
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    intro hlegal
    rcases hbad with hS | hA
    · exact hS hlegal.stores_unshared
    · exact hA hlegal.promotes_unshared
  have hdecomp :
      (∑ c : BigEdgeChoice modulus M B x,∑ t : Fin M → P,
        if OrientedBigEdgeLegal modulus M B x t shared sigma tau D step c
        then ‖orientedBigBranchCoefficient modulus M B mu V rho x t shared
          sigma tau step c‖ else 0) =
      ∑ S : Finset (Fin M),∑ A : Finset (Fin M),row S A := by
    simp only [BigEdgeChoice,Fintype.sum_prod_type,Fintype.sum_sigma,row]
  rw [hdecomp]
  calc
    _ = ∑ S ∈ U.powerset,∑ A : Finset (Fin M),row S A := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S hS hnot
      apply Finset.sum_eq_zero
      intro A hA
      exact hzero S A (Or.inl (by simpa only [Finset.mem_powerset] using hnot))
    _ = ∑ S ∈ U.powerset,∑ A ∈ U.powerset,row S A := by
      apply Finset.sum_congr rfl
      intro S hS
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro A hA hnot
      exact hzero S A (Or.inr (by simpa only [Finset.mem_powerset] using hnot))
    _ ≤ ∑ S ∈ U.powerset,∑ A ∈ U.powerset,C := by
      apply Finset.sum_le_sum
      intro S hS
      exact Finset.sum_le_sum (fun A hA => hrow S A (Finset.mem_powerset.mp hA))
    _ = (4:ℝ)^U.card*C := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_powerset,
        Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _ ≤ (4:ℝ)^d*C :=
      mul_le_mul_of_nonneg_right (pow_right_mono₀ (by norm_num) hd) hC

/-- The complete original BIG frame inherits the fixed ell+m bound;
both endpoint permutations, the literal D and signed step remain free. -/
theorem source_original_memory_SOURCE_BIG_complete_absolute_row434
    {BG : Type} [Fintype BG] [DecidableEq BG] (J ell m : ℕ) (pat : SourcePattern BG J m) (g : BG)
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (V rho R : ℝ)
    (hV : 0<V) (hr : 0< rho) (hr1 : rho<1)
    (hR : 1 ≤ R) (hMass : ∑ p : P,mu p ≤ R)
    (x : BigState modulus (J+ell) B)
    (sigma tau : Equiv.Perm (Fin (J+ell))) (D : ℕ) (step : ℤ) :
    (∑ c : BigEdgeChoice modulus (J+ell) B x,∑ t : Fin (J+ell) → P,
      if OrientedBigEdgeLegal modulus (J+ell) B x t (sourceBigShared J ell m pat g)
        sigma tau D step c
      then ‖orientedBigBranchCoefficient modulus (J+ell) B mu V rho x t
        (sourceBigShared J ell m pat g) sigma tau step c‖ else 0) ≤
      (4:ℝ)^(ell+m) * (memoryPromotionDampingConstant rho (ell+m) *
        ((max 1 V⁻¹)^(ell+m)*R^(ell+m))) := by
  exact source_original_memory_BIG_complete_absolute_row434 modulus (J+ell) B mu hmu
    V rho R hV hr hr1 hR hMass x (sourceBigShared J ell m pat g) sigma tau D step
    (ell+m) (memory_source_unshared_count J ell m pat g)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryBigFrameRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
variable (M : ℕ) (cap : G → ℕ) (x : BigGroupState BP modulus M cap)

abbrev sourceOriginalMemoryBigFrameChoice434 :=
  (g : G) → (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g)

def sourceOriginalMemoryBigFrameLegal434
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) : Prop :=
  ∀ g,OrientedBigEdgeLegal (modulus g) M (cap g) (x g) (b g).1
    (shared g) (sigma g) (tau g) D step (b g).2

def sourceOriginalMemoryBigFrameNorm434
    (mu : (g : G) → BP g → ℝ) (V : G → ℝ) (rho : ℝ)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (step : ℤ) (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) : ℝ :=
  ∏ g : G,‖orientedBigBranchCoefficient (modulus g) M (cap g) (mu g) (V g) rho
    (x g) (b g).1 (shared g) (sigma g) (tau g) step (b g).2‖

def sourceOriginalMemoryBigFramePromotionHit434 (D : ℕ) (step : ℤ) : Prop :=
  ∃ j : Σ g : G,Fin (x g).2.1.val,
    ¬ modulus j.1 (((x j.1).2.2 j.2).1) ∣ D ∧
      ((x j.1).2.2 j.2).2+(step:ZMod (modulus j.1 (((x j.1).2.2 j.2).1)))=0

/-- Tensor the complete actual BIG rows, preserving each ordered target
and memory choice. No count of active/shared slots is paid. -/
theorem source_original_memory_BIG_frame_absolute_row434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (V : G → ℝ) (rho R : ℝ) (hV : ∀ g,0<V g)
    (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R)
    (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ R)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (d : ℕ)
    (hd : ∀ g,(orientedUnshared M (shared g)).card ≤ d) :
    (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0) ≤
      ∏ g : G,(4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d)) := by
  classical
  let w := fun (g : G) (z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g)) =>
    if OrientedBigEdgeLegal (modulus g) M (cap g) (x g) z.1
      (shared g) (sigma g) (tau g) D step z.2 then
      ‖orientedBigBranchCoefficient (modulus g) M (cap g) (mu g) (V g) rho
        (x g) z.1 (shared g) (sigma g) (tau g) step z.2‖ else 0
  have hprod (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) :
      (∏ g : G,w g (b g)) =
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0 := by
    simp only [w,Finset.prod_ite_zero,Finset.mem_univ,forall_const,
      sourceOriginalMemoryBigFrameLegal434,sourceOriginalMemoryBigFrameNorm434]
    congr <;> exact Subsingleton.elim _ _
  have he :
      (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
        ∏ g : G,w g (b g)) =
      ∏ g : G,∑ z : (Fin M → BP g) × BigEdgeChoice (modulus g) M (cap g) (x g),w g z := by
    convert (Fintype.prod_sum w).symm using 1 <;> congr <;> exact Subsingleton.elim _ _
  simp_rw [← hprod]
  rw [he]
  apply Finset.prod_le_prod₀
  · intro g hg
    apply Finset.sum_nonneg
    intro z hz
    dsimp only [w]
    split_ifs <;> positivity
  · intro g hg
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    exact source_original_memory_BIG_complete_absolute_row434 (modulus g) M (cap g)
      (mu g) (hmu g) (V g) rho R (hV g) hr hr1 hR (hMass g)
      (x g) (shared g) (sigma g) (tau g) D step d (hd g)

/-- A complete BIG frame with a promotion vanishes unless an actual OLD
index is promotable. On that event the full absolute row bound applies. -/
theorem source_original_memory_BIG_promoting_frame_row434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (V : G → ℝ) (rho R : ℝ) (hV : ∀ g,0<V g)
    (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R)
    (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ R)
    (shared : G → Finset (Fin M)) (sigma tau : BigGroupPerm (BG:=G) M)
    (D : ℕ) (step : ℤ) (d : ℕ)
    (hd : ∀ g,(orientedUnshared M (shared g)).card ≤ d) :
    (∑ b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x,
      if sourceOriginalMemoryBigFrameLegal434 BP modulus M cap x shared sigma tau D step b ∧
        (∃ g : G,((b g).2).2.1.Nonempty)
      then sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b else 0) ≤
      (if sourceOriginalMemoryBigFramePromotionHit434 BP modulus M cap x D step then
        (1:ℝ) else 0) *
      (∏ g : G,(4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d))) := by
  classical
  have hNorm (b : sourceOriginalMemoryBigFrameChoice434 BP modulus M cap x) :
      0 ≤ sourceOriginalMemoryBigFrameNorm434 BP modulus M cap x mu V rho
        shared sigma tau step b := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  by_cases hHit : sourceOriginalMemoryBigFramePromotionHit434 BP modulus M cap x D step
  · rw [if_pos hHit,one_mul]
    apply le_trans _ (source_original_memory_BIG_frame_absolute_row434 BP modulus M cap x
      mu hmu V rho R hV hr hr1 hR hMass shared sigma tau D step d hd)
    apply Finset.sum_le_sum
    intro b hb
    split_ifs <;> first | exact le_rfl | exact hNorm b | tauto
  · rw [if_neg hHit,zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro b hb
    apply if_neg
    rintro ⟨hlegal,g,a,ha⟩
    exact hHit ⟨⟨g,((b g).2).2.2 ⟨a,ha⟩⟩,
      (hlegal g).promoted_not_dividing ⟨a,ha⟩,(hlegal g).promoted_zero ⟨a,ha⟩⟩
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryTiltedBigRow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The actual tilted prime measure has total mass at most two once
the literal baseline is at least one half. Its normalization is the
actual harmonic mass, not a postulated probability law. -/
theorem source_original_memory_physical_tilt_mass_two434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (g : G) (hV : 0<V g)
    (hHarmonic : ∑ p : BP g,1/(modulus g p:ℝ)=V g)
    (hb : ∀ p : BP g,(1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p) :
    (∀ p : BP g,0 ≤ physicalSourceMuTilde BP modulus q N V g p) ∧
      (∑ p : BP g,physicalSourceMuTilde BP modulus q N V g p) ≤ 2 := by
  have hp (p : BP g) : 0<(modulus g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hb0 (p : BP g) : 0<physicalSourceBaseline BP modulus q N g p :=
    lt_of_lt_of_le (by norm_num) (hb p)
  have hn : (∑ p : BP g,1/(V g*(modulus g p:ℝ)))=1 := by
    calc
      _ = (V g)⁻¹*(∑ p : BP g,1/(modulus g p:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        simp [div_eq_mul_inv,mul_inv_rev,mul_comm]
      _ = 1 := by rw [hHarmonic,inv_mul_cancel₀ (ne_of_gt hV)]
  have hcap (p : BP g) :
      physicalSourceMuTilde BP modulus q N V g p ≤ 2*(1/(V g*(modulus g p:ℝ))) := by
    unfold physicalSourceMuTilde
    rw [← div_div]
    calc
      _ ≤ (1/(V g*(modulus g p:ℝ)))/((1:ℝ)/2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (hb p)
      _ = _ := by ring
  constructor
  · intro p
    exact one_div_nonneg.mpr (mul_nonneg (mul_nonneg hV.le (hp p).le) (hb0 p).le)
  · calc
      _ ≤ ∑ p : BP g,2*(1/(V g*(modulus g p:ℝ))) :=
        Finset.sum_le_sum (fun p _ => hcap p)
      _ = 2 := by rw [← Finset.mul_sum,hn,mul_one]

/-- Literal source-depth, actual tilted-law complete BIG row.
The threshold precedes every group, alphabet, J, memory sector and
physical D/step; the displayed constant contains no J or cutoff. -/
theorem eventually_source_original_memory_TILTED_SOURCE_BIG_row434
    (c : ℝ) (hc : 0<c) (q rho : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0< rho) (hr1 : rho<1) (ell m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {G : Type} [Fintype G] [DecidableEq G]
      (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
      (V : G → ℝ) (J : ℕ) (pat : SourcePattern G J m) (g : G)
      (hV : 0<V g)
      (hHarmonic : ∑ p : BP g,1/(modulus g p:ℝ)=V g)
      (hBig : ∀ p : BP g,Real.exp (L^c) ≤ (modulus g p:ℝ))
      (B : ℕ) (x : BigState (modulus g) (J+ell) B)
      (sigma tau : Equiv.Perm (Fin (J+ell))) (D : ℕ) (step : ℤ),
    let mu := physicalSourceMuTilde BP modulus q (2*Nat.ceil (L^(0.52:ℝ))) V g
    (∑ z : BigEdgeChoice (modulus g) (J+ell) B x,∑ t : Fin (J+ell) → BP g,
      if OrientedBigEdgeLegal (modulus g) (J+ell) B x t (sourceBigShared J ell m pat g)
        sigma tau D step z
      then ‖orientedBigBranchCoefficient (modulus g) (J+ell) B mu (V g) rho x t
        (sourceBigShared J ell m pat g) sigma tau step z‖ else 0) ≤
      (4:ℝ)^(ell+m) * (memoryPromotionDampingConstant rho (ell+m) *
        ((max 1 (V g)⁻¹)^(ell+m)*2^(ell+m))) := by
  filter_upwards [eventually_source_original_B26_visits_below_BIG434 c hc] with L hL
  intro G instG instDG BP instP instDP modulus instNZ V J pat g
    hV hHarmonic hBig B x sigma tau D step
  have hb (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP modulus q hq hq1 _ g p
      (hL _ (hBig p))).1
  obtain ⟨hmu,hMass⟩ := source_original_memory_physical_tilt_mass_two434 BP modulus
    q (2*Nat.ceil (L^(0.52:ℝ))) V g hV hHarmonic hb
  exact source_original_memory_SOURCE_BIG_complete_absolute_row434 (modulus g) B
    J ell m pat g _ hmu (V g) rho 2 hV hr hr1 (by norm_num) hMass x sigma tau D step
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPhysicalRarePromotionRow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

section LiteralRow
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)

def sourceOriginalMemoryPhysicalBigPromotionRow434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (smallSigma : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (mu : (g : BG) → BP g → ℝ) (V : BG → ℝ) (rho : ℝ) (o k : ℤ) : ℝ :=
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    pat aux st bigSigma smallSigma
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    pat aux st bigSigma smallSigma o k
  ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
    if sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
      (sourceBigShared J ell m pat) bigSigma bigTau D step b ∧
      (∃ g : BG,((b g).2).2.1.Nonempty)
    then sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu V rho
      (sourceBigShared J ell m pat) bigSigma bigTau step b else 0

theorem source_original_memory_PHYSICAL_BIG_promoting_row_hit434
    (pat : SourcePattern BG J m) (aux : SourceBigAux BP J m pat)
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (smallSigma : Green64SmallHaar.GroupPermFamily (G:=SG) (J+ell))
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (V : BG → ℝ) (rho R : ℝ) (hV : ∀ g,0<V g)
    (hr : 0< rho) (hr1 : rho<1) (hR : 1 ≤ R)
    (hMass : ∀ g,(∑ p : BP g,mu g p) ≤ R) (o k : ℤ) :
    sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod BP bigMod
      J ell m cap pat aux st bigSigma bigTau smallSigma mu V rho o k ≤
    (if sourceOriginalMemoryPhysicalPromotionHit434 SP smallMod BP bigMod
      J ell m cap pat aux st bigSigma smallSigma o k then (1:ℝ) else 0) *
    (∏ g : BG,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
      ((max 1 (V g)⁻¹)^(ell+m)*R^(ell+m)))) := by
  exact source_original_memory_BIG_promoting_frame_row434 BP bigMod (J+ell) cap st.2
    mu hmu V rho R hV hr hr1 hR hMass (sourceBigShared J ell m pat) bigSigma bigTau
    _ _ (ell+m) (memory_source_unshared_count J ell m pat)
end LiteralRow

/-- Applicable rare-promotion absolute row for all actual BIG groups,
at the literal original D and signed step and with the physical tilted
prime measure. The source SMALL permutation average is normalized
exactly. No row-smallness, Gram, operator or SW premise is assumed. -/
theorem eventually_source_original_memory_PHYSICAL_BIG_rare_promotion_row434
    (cfg : SourceComparisonFixed434) (ell : ℕ) (Ck q rho : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0< rho) (hr1 : rho<1) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (J m : ℕ) (cap : G → ℕ)
      (st : FullPhysicalState
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (pat : SourcePattern G J m)
      (aux : SourceBigAux (fun g => {p : ℕ // p ∈ data.Tb g}) J m pat)
      (bigSigma bigTau : BigGroupPerm (BG:=G) (J+ell))
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    (∑ smallSigma : Green64SmallHaar.GroupPermFamily (G:=ι) (J+ell),
      sourceOriginalMemoryPhysicalBigPromotionRow434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell m cap pat aux st bigSigma bigTau smallSigma mu data.Vbig rho o k) /
        (((J+ell).factorial:ℝ)^(Fintype.card ι)) ≤
      (((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ) /
        (((J+ell).choose ell:ℝ)^(Fintype.card ι))) *
      (∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
        ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m)))) := by
  have hc : 0<cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [
    eventually_source_original_memory_PHYSICAL_permutation_promotion_bound434 cfg ell Ck,
    eventually_source_original_B26_visits_below_BIG434 cfg.cexp hc] with L hCount hVisit
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    J m cap st hSmallUpper hBigLower hHarmonic pat aux bigSigma bigTau o k ho hk0 hk
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
  have hV (g : G) : 0<data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hb (g : G) (p : BP g) :
      (1:ℝ)/2 ≤ physicalSourceBaseline BP (fun _ p => p.val)
        q (2*Nat.ceil (L^(0.52:ℝ))) g p :=
    (source_original_B26_physical_baseline_half434 BP (fun _ p => p.val)
      q hq hq1 _ g p (hVisit p.val (hBigLower g p.val p.property))).1
  have hm (g : G) : (∀ p : BP g,0 ≤ mu g p) ∧ (∑ p : BP g,mu g p) ≤ 2 :=
    source_original_memory_physical_tilt_mass_two434 BP (fun _ p => p.val)
      q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig g (hV g) (hHarmonic g) (hb g)
  let C := ∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
    ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m)))
  have hmem : 0 ≤ memoryPromotionDampingConstant rho (ell+m) := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hC : 0 ≤ C := by
    apply Finset.prod_nonneg
    intro g hg
    positivity
  let hit := fun ss : Green64SmallHaar.GroupPermFamily (G:=ι) (J+ell) =>
    if sourceOriginalMemoryPhysicalPromotionHit434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap pat aux st bigSigma ss o k then (1:ℝ) else 0
  have hEach (ss : Green64SmallHaar.GroupPermFamily (G:=ι) (J+ell)) :
      sourceOriginalMemoryPhysicalBigPromotionRow434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val) BP (fun _ p => p.val)
        J ell m cap pat aux st bigSigma bigTau ss mu data.Vbig rho o k ≤ hit ss*C :=
    source_original_memory_PHYSICAL_BIG_promoting_row_hit434
      (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val) BP (fun _ p => p.val)
      J ell m cap pat aux st bigSigma bigTau ss mu (fun g => (hm g).1)
      data.Vbig rho 2 hV hr hr1 (by norm_num) (fun g => (hm g).2) o k
  have hc := hCount x Y Hprime data sep J m cap st hSmallUpper hBigLower
    pat aux bigSigma o k ho hk0 hk
  calc
    _ ≤ (∑ ss,hit ss*C)/(((J+ell).factorial:ℝ)^(Fintype.card ι)) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ss _ => hEach ss))
        (pow_nonneg (Nat.cast_nonneg _) _)
    _ = ((∑ ss,hit ss)/(((J+ell).factorial:ℝ)^(Fintype.card ι)))*C := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hC
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryRareRowBudget -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

def sourceOriginalMemoryBigRowBase434 (rho v R : ℝ) (d : ℕ) : ℝ :=
  max 1 ((4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 v⁻¹)^d*R^d)))

def sourceOriginalMemoryRareSlotChoice434 (Jmin : ℕ) (c0 C0 K A : ℝ) : ℕ :=
  max Jmin (Nat.ceil (Real.exp ((A+C0*Real.log K+3)/c0)))

/-- A fully explicit admissible fixed slot count. This choice follows
the row exponent, which is independent of J. -/
theorem source_original_memory_rare_slot_choice434
    (Jmin ell : ℕ) (hell : 1 ≤ ell) (c0 C0 K A : ℝ) (hc0 : 0<c0) :
    let J := sourceOriginalMemoryRareSlotChoice434 Jmin c0 C0 K A
    Jmin ≤ J ∧ A+C0*Real.log K+3 ≤
      c0*Real.log (((J+ell).choose ell:ℕ):ℝ) := by
  dsimp only
  let J := sourceOriginalMemoryRareSlotChoice434 Jmin c0 C0 K A
  have hj : Jmin ≤ J := le_max_left _ _
  have hchoose : J+1 ≤ (J+ell).choose ell := by
    have hh := Nat.choose_le_choose J (Nat.add_le_add_left hell J)
    rw [Nat.choose_symm_add,Nat.choose_symm_add] at hh
    simpa using hh
  have hexp : Real.exp ((A+C0*Real.log K+3)/c0) ≤
      (((J+ell).choose ell:ℕ):ℝ) := by
    calc
      _ ≤ (Nat.ceil (Real.exp ((A+C0*Real.log K+3)/c0)):ℝ) := Nat.le_ceil _
      _ ≤ (J:ℝ) := by exact_mod_cast (le_max_right Jmin _)
      _ ≤ ((J+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ J
      _ ≤ _ := by exact_mod_cast hchoose
  have hh := Real.log_le_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hc0.le
  have hcancel : c0*((A+C0*Real.log K+3)/c0)=A+C0*Real.log K+3 := by
    field_simp
  rw [hcancel] at hh'
  exact ⟨hj,hh'⟩

/-- The complete BIG row factor is a fixed logarithmic power for
growing original group families. -/
theorem source_original_memory_BIG_row_factor_polynomial434
    {G : Type} [Fintype G] (rho v R C0 L : ℝ) (d : ℕ)
    (hr : 0< rho) (hr1 : rho<1) (hv : 0<v) (hR : 1 ≤ R) (hL : 1 ≤ L)
    (V : G → ℝ) (hV : ∀ g,v ≤ V g)
    (hGroups : (Fintype.card G:ℝ) ≤ C0*Real.log L) :
    (∏ g : G,(4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d))) ≤
      L^(C0*Real.log (sourceOriginalMemoryBigRowBase434 rho v R d)) := by
  let K := sourceOriginalMemoryBigRowBase434 rho v R d
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0<K := zero_lt_one.trans_le hK1
  have hmem : 0 ≤ memoryPromotionDampingConstant rho d := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hterm (g : G) :
      0 ≤ (4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d)) :=
    mul_nonneg (by positivity) (mul_nonneg hmem
      (mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
        (pow_nonneg (le_trans zero_le_one hR) _)))
  have hEach (g : G) :
      (4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 (V g)⁻¹)^d*R^d)) ≤ K := by
    have hi : (V g)⁻¹ ≤ v⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hv (hV g)
    have hm := pow_le_pow_left₀ (le_trans zero_le_one (le_max_left 1 (V g)⁻¹))
      (max_le_max_left 1 hi) d
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm
        (pow_nonneg (le_trans zero_le_one hR) _)) hmem) (by positivity)).trans
      (le_max_right _ _)
  have hProd : (∏ g : G,(4:ℝ)^d*(memoryPromotionDampingConstant rho d*
      ((max 1 (V g)⁻¹)^d*R^d))) ≤ K^(Fintype.card G) := by
    calc
      _ ≤ ∏ _g : G,K := Finset.prod_le_prod₀ (fun g _ => hterm g) (fun g _ => hEach g)
      _ = _ := by simp
  calc
    _ ≤ K^(Fintype.card G) := hProd
    _ = Real.exp (Real.log K*(Fintype.card G:ℝ)) := by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos hK]
    _ ≤ Real.exp (Real.log K*(C0*Real.log L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hGroups (Real.log_nonneg hK1))
    _ = _ := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hL)]
      congr 1
      ring

/-- Exact exponent budget for a rare promotion row. The OLD cutoff
contributes at most L^3; no grid or conductor exponent is present. -/
theorem source_original_memory_rare_row_log_budget434
    (L c0 C0 K A T : ℝ) (N ns : ℕ)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hT0 : 0 ≤ T) (hT : T ≤ L^(3:ℝ))
    (hGroups : c0*Real.log L ≤ (ns:ℝ))
    (hBudget : A+C0*Real.log K+3 ≤ c0*Real.log (N:ℝ)) :
    (T/(N:ℝ)^ns)*L^(C0*Real.log K) ≤ L^(-A) := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hNp : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hden : L^(c0*Real.log (N:ℝ)) ≤ (N:ℝ)^ns := by
    calc
      _ = Real.exp (Real.log (N:ℝ)*(c0*Real.log L)) := by
        rw [Real.rpow_def_of_pos hLp];congr 1;ring
      _ ≤ Real.exp (Real.log (N:ℝ)*(ns:ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hGroups (Real.log_nonneg hN1))
      _ = _ := by rw [← Real.rpow_natCast,Real.rpow_def_of_pos hNp]
  have hdiv : T/(N:ℝ)^ns ≤ L^(3:ℝ)/L^(c0*Real.log (N:ℝ)) :=
    (div_le_div_of_nonneg_right hT (pow_nonneg hNp.le _)).trans
      (div_le_div_of_nonneg_left (Real.rpow_nonneg hLp.le _) (Real.rpow_pos_of_pos hLp _) hden)
  calc
    _ ≤ (L^(3:ℝ)/L^(c0*Real.log (N:ℝ)))*L^(C0*Real.log K) :=
      mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hLp.le _)
    _ = L^(3-c0*Real.log (N:ℝ)+C0*Real.log K) := by
      rw [← Real.rpow_sub hLp,← Real.rpow_add hLp]
    _ ≤ L^(-A) := Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hBudget])

theorem source_original_memory_total_cutoff_cube434
    (L : ℝ) (hL : 2 ≤ L) (n : ℕ) (hn : n ≤ Nat.ceil (L^2)) :
    (n:ℝ) ≤ L^(3:ℝ) := by
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hc := (Nat.ceil_lt_add_one (sq_nonneg L)).le
  have hn' : (n:ℝ) ≤ (Nat.ceil (L^2):ℝ) := by exact_mod_cast hn
  have hsq : 1 ≤ L^2 := one_le_pow₀ hL1
  have hm := mul_nonneg (sub_nonneg.mpr hL) (sq_nonneg L)
  have hb : L^2+1 ≤ L^3 := by nlinarith only [hm,hsq]
  have hh := hn'.trans (hc.trans hb)
  simpa only [Real.rpow_ofNat] using hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryFixedSlotRareRow -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem source_original_memory_promotion_damping_constant_mono434
    (rho : ℝ) (hr1 : rho<1) (d e : ℕ) (hde : d ≤ e) :
    memoryPromotionDampingConstant rho d ≤ memoryPromotionDampingConstant rho e := by
  have hh : 0<1-rho := sub_pos.mpr hr1
  unfold memoryPromotionDampingConstant
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right hde 1))
  intro a ha hnot
  positivity

theorem source_original_memory_complete_row_factor_mono434
    (rho V R : ℝ) (hr1 : rho<1) (hR : 1 ≤ R) (d e : ℕ) (hde : d ≤ e) :
    (4:ℝ)^d*(memoryPromotionDampingConstant rho d*((max 1 V⁻¹)^d*R^d)) ≤
    (4:ℝ)^e*(memoryPromotionDampingConstant rho e*((max 1 V⁻¹)^e*R^e)) := by
  let H : ℝ := 4*max 1 V⁻¹*R
  have h4 : 1 ≤ (4:ℝ)*max 1 V⁻¹ :=
    (by norm_num : (1:ℝ) ≤ 4).trans (le_mul_of_one_le_right (by norm_num) (le_max_left _ _))
  have hH : 1 ≤ H := h4.trans (le_mul_of_one_le_right (le_trans zero_le_one h4) hR)
  have hm0 (a : ℕ) : 0 ≤ memoryPromotionDampingConstant rho a := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have heq (a : ℕ) :
      (4:ℝ)^a*(memoryPromotionDampingConstant rho a*((max 1 V⁻¹)^a*R^a)) =
      memoryPromotionDampingConstant rho a*H^a := by
    dsimp only [H]
    simp only [mul_pow]
    ring
  rw [heq,heq]
  exact mul_le_mul
    (source_original_memory_promotion_damping_constant_mono434 rho hr1 d e hde)
    (pow_right_mono₀ hH hde) (pow_nonneg (le_trans zero_le_one hH) _) (hm0 e)

/-- Positive logarithmic saving for the literal BIG promotion row.
J is given explicitly, before L and all moving data. The original
logarithmically growing group families and total OLD cutoff are explicit.
This is a BIG-row result, not a full signed DIRTY operator assertion. -/
theorem source_original_memory_PHYSICAL_BIG_rare_promotion_log_saving434
    (cfg : SourceComparisonFixed434) (ell Jmin : ℕ) (hell : 1 ≤ ell)
    (Ck q rho c0 A : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0< rho) (hr1 : rho<1) (hc0 : 0<c0) :
    let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
    let J := sourceOriginalMemoryRareSlotChoice434 Jmin c0 cfg.C0 K A
    Jmin ≤ J ∧
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 data)
      [∀ g (p : {p : ℕ // p ∈ data.Ts g}),NeZero p.val]
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (m : ℕ) (hm : m ≤ cfg.tmax) (cap : G → ℕ)
      (st : FullPhysicalState
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val) (J+ell) cap)
      (hSmallUpper : ∀ g,∀ p ∈ data.Ts g,(p:ℝ) ≤ Real.exp (L^cfg.bexp))
      (hBigLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hHarmonic : ∀ g,∑ p : {p : ℕ // p ∈ data.Tb g},1/(p.val:ℝ)=data.Vbig g)
      (hSmallGroupsLower : c0*Real.log L ≤ (Fintype.card ι:ℝ))
      (hOldTotal : (∑ g : G,(st.2 g).2.1.val) ≤ Nat.ceil (L^2))
      (pat : SourcePattern G J m)
      (aux : SourceBigAux (fun g => {p : ℕ // p ∈ data.Tb g}) J m pat)
      (bigSigma bigTau : BigGroupPerm (BG:=G) (J+ell))
      (o k : ℤ) (ho : o=1 ∨ o= -1) (hk0 : k ≠ 0)
      (hk : (k.natAbs:ℝ) ≤ L^Ck),
    let mu := physicalSourceMuTilde (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q (2*Nat.ceil (L^(0.52:ℝ))) data.Vbig
    (∑ smallSigma : Green64SmallHaar.GroupPermFamily (G:=ι) (J+ell),
      sourceOriginalMemoryPhysicalBigPromotionRow434
        (fun g => {p : ℕ // p ∈ data.Ts g}) (fun _ p => p.val)
        (fun g => {p : ℕ // p ∈ data.Tb g}) (fun _ p => p.val)
        J ell m cap pat aux st bigSigma bigTau smallSigma mu data.Vbig rho o k) /
        (((J+ell).factorial:ℝ)^(Fintype.card ι)) ≤ L^(-A) := by
  dsimp only
  let K := sourceOriginalMemoryBigRowBase434 rho cfg.vmin 2 (ell+cfg.tmax)
  let J := sourceOriginalMemoryRareSlotChoice434 Jmin c0 cfg.C0 K A
  have hSlot := source_original_memory_rare_slot_choice434 Jmin ell hell c0 cfg.C0 K A hc0
  refine ⟨hSlot.1,?_⟩
  filter_upwards [
    eventually_source_original_memory_PHYSICAL_BIG_rare_promotion_row434
      cfg ell Ck q rho hq hq1 hr hr1,
    eventually_ge_atTop (2:ℝ)] with L hRare hL
  intro ι G instI instDI instG instDG x Y Hprime data sep instS instB
    m hm cap st hSmallUpper hBigLower hHarmonic hSmallGroupsLower
    hOldTotal pat aux bigSigma bigTau o k ho hk0 hk
  have hL1 : 1 ≤ L := le_trans (by norm_num) hL
  have hmem (d : ℕ) : 0 ≤ memoryPromotionDampingConstant rho d := by
    have hh : 0<1-rho := sub_pos.mpr hr1
    unfold memoryPromotionDampingConstant
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hfactor :
      (∏ g : G,(4:ℝ)^(ell+m)*(memoryPromotionDampingConstant rho (ell+m)*
        ((max 1 (data.Vbig g)⁻¹)^(ell+m)*2^(ell+m)))) ≤ L^(cfg.C0*Real.log K) := by
    apply le_trans _ (source_original_memory_BIG_row_factor_polynomial434
      rho cfg.vmin 2 cfg.C0 L (ell+cfg.tmax) hr hr1 cfg.hv (by norm_num) hL1
      data.Vbig data.hVbig data.hBigGroups)
    apply Finset.prod_le_prod₀
    · intro g hg
      have hmem0 := hmem (ell+m)
      positivity
    · intro g hg
      exact source_original_memory_complete_row_factor_mono434 rho (data.Vbig g) 2 hr1
        (by norm_num) (ell+m) (ell+cfg.tmax) (Nat.add_le_add_left hm ell)
  have hN : 1 ≤ (J+ell).choose ell :=
    Nat.succ_le_of_lt (Nat.choose_pos (by omega))
  have htotal : ((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ) ≤ L^(3:ℝ) :=
    source_original_memory_total_cutoff_cube434 L hL _ hOldTotal
  have hbudget := source_original_memory_rare_row_log_budget434 L c0 cfg.C0 K A
    ((∑ g : G,(st.2 g).2.1.val:ℕ):ℝ) ((J+ell).choose ell) (Fintype.card ι)
    hL1 hN (Nat.cast_nonneg _) htotal hSmallGroupsLower hSlot.2
  exact (hRare x Y Hprime data sep J m cap st hSmallUpper hBigLower hHarmonic
    pat aux bigSigma bigTau o k ho hk0 hk).trans
      ((mul_le_mul_of_nonneg_left hfactor
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))).trans hbudget)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryCompatibleRho -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

def sourceOriginalMemoryCompatibleRho434 (q : ℝ) : ℝ :=
  Real.sqrt ((1+Real.sqrt q)/2)

/-- A concrete fixed rho satisfying all numerical rho conditions of
the original MemorySourceDomain, including sqrt(q)< rho^2. This is also
admissible in the proved complete BIG and rare-promotion row bounds.
It does not assert a bound on G or smallness of the rho-invariant root. -/
theorem source_original_memory_compatible_rho434
    (q : ℝ) (hq : 0<q) (hq1 : q<1) :
    0<sourceOriginalMemoryCompatibleRho434 q ∧
    sourceOriginalMemoryCompatibleRho434 q<1 ∧
    Real.sqrt q<(sourceOriginalMemoryCompatibleRho434 q)^2 := by
  have hs0 := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q<1 := by
    nlinarith only [Real.sq_sqrt hq.le,hs0,hq1]
  have ha : 0<(1+Real.sqrt q)/2 := by linarith only [hs0]
  have hr : 0<sourceOriginalMemoryCompatibleRho434 q := Real.sqrt_pos.mpr ha
  have hsq : (sourceOriginalMemoryCompatibleRho434 q)^2=(1+Real.sqrt q)/2 :=
    Real.sq_sqrt ha.le
  refine ⟨hr,?_,?_⟩
  · nlinarith only [hr,hsq,hs1]
  · linarith only [hsq,hs1]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemorySmallGroupRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Sum every genuine SMALL target state. A joint global scalar is
charged once, with all source/target permutations retained. -/
theorem source_original_memory_SMALL_group_kernel_row434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Type) [∀ g,Fintype (P g)] [∀ g,DecidableEq (P g)]
    (modulus : (g : G) → P g → ℕ) [∀ g p,NeZero (modulus g p)]
    (M : ℕ) (q : ℝ) (V : G → ℝ)
    (hq : 0<q) (hq1 : q<1) (hV : ∀ g,0<V g)
    (shared : (g : G) → Finset (Fin M)) (step : ℤ)
    (K : GroupPermFamily (G:=G) M → GroupPermFamily (G:=G) M → ℂ)
    (sigma tau : GroupPermFamily (G:=G) M) (x : GroupState P modulus M) :
    (∑ z : GroupState P modulus M,
      ‖groupPermutedKernel P modulus M q V shared step K sigma tau x z‖) ≤
      ‖K sigma tau‖ * ∏ g : G,memorySmallRowConstant q (V g)
        (unsharedSlots M (shared g)) := by
  classical
  let w := fun (g : G) (z : SmallState (modulus g) M) =>
    if edgeAllowedPerm (modulus g) M (shared g) step (sigma g) (tau g) (x g) z
    then edgeScalar (modulus g) M q (V g) (shared g) (x g) z else 0
  have hw (g : G) (z : SmallState (modulus g) M) : 0 ≤ w g z := by
    dsimp only [w]
    split_ifs
    · exact edgeScalar_nonneg (modulus g) M q (V g) (hV g) (shared g) (x g) z
    · exact le_rfl
  have hnorm (z : GroupState P modulus M) :
      ‖groupPermutedKernel P modulus M q V shared step K sigma tau x z‖ =
      ‖K sigma tau‖ * ∏ g : G,w g (z g) := by
    by_cases h : groupEdgeAllowedPerm P modulus M shared step sigma tau x z
    · have hn : 0 ≤ groupEdgeScalar P modulus M q V shared x z :=
        Finset.prod_nonneg (fun g _ =>
          edgeScalar_nonneg (modulus g) M q (V g) (hV g) (shared g) (x g) (z g))
      rw [groupPermutedKernel,if_pos h,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hn]
      congr 1
      unfold groupEdgeScalar
      apply Finset.prod_congr rfl
      intro g hg
      exact (if_pos (h g)).symm
    · rw [groupPermutedKernel,if_neg h,norm_zero]
      have hz : (∏ g : G,w g (z g))=0 := by
        obtain ⟨g,hg⟩ := not_forall.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ g) (if_neg hg)
      rw [hz,mul_zero]
  have hs : (∑ z : GroupState P modulus M,∏ g : G,w g (z g)) =
      ∏ g : G,∑ z : SmallState (modulus g) M,w g z := by
    convert (Fintype.prod_sum w).symm using 1 <;> congr <;> exact Subsingleton.elim _ _
  simp_rw [hnorm]
  rw [← Finset.mul_sum,hs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀
  · intro g hg
    exact Finset.sum_nonneg (fun z _ => hw g z)
  · intro g hg
    have hh := memory_original_SMALL_E_absolute_row_bound (modulus g) M q (V g)
      hq hq1 (hV g) (shared g) step (sigma g) (tau g) (x g)
    simpa only [memorySmallScalarRow,memorySmallAllowed,Finset.sum_filter,w] using hh

/-- At the literal source shared set, the complete SMALL constant
depends on ell alone, not J. -/
theorem source_original_memory_SOURCE_SMALL_group_kernel_row434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Type) [∀ g,Fintype (P g)] [∀ g,DecidableEq (P g)]
    (modulus : (g : G) → P g → ℕ) [∀ g p,NeZero (modulus g p)]
    (J ell : ℕ) (q : ℝ) (V : G → ℝ)
    (hq : 0<q) (hq1 : q<1) (hV : ∀ g,0<V g) (step : ℤ)
    (K : GroupPermFamily (G:=G) (J+ell) → GroupPermFamily (G:=G) (J+ell) → ℂ)
    (sigma tau : GroupPermFamily (G:=G) (J+ell)) (x : GroupState P modulus (J+ell)) :
    (∑ z : GroupState P modulus (J+ell),
      ‖groupPermutedKernel P modulus (J+ell) q V (sourceSmallShared J ell)
        step K sigma tau x z‖) ≤
      ‖K sigma tau‖ * ∏ g : G,memorySmallRowConstant q (V g) ell := by
  simpa only [unsharedSlots,source_original_B26_small_shared_card434,Nat.add_sub_cancel_left]
    using source_original_memory_SMALL_group_kernel_row434 P modulus (J+ell)
      q V hq hq1 hV (sourceSmallShared J ell) step K sigma tau x
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryOriginalPromotionPacket -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

def sourceOriginalMemoryFixedPhysicalChoice434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2)
    (zs : GroupState SP smallMod (J+ell)) :
    FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st :=
  ⟨nu,aux,⟨bigSigma,bigTau,b,zs⟩,ss,tt⟩

/-- A literal original coefficient packet. It retains all legality
tests, auxiliary bans, the signed Fourier/Mellin scalar, stores,
ordered promotions, all target states and both permutation masses. -/
def sourceOriginalMemoryOriginalPromotingPacket434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) : ℝ :=
  ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
  ∑ zs : GroupState SP smallMod (J+ell),
    let z := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt b zs
    if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z ∧
      (∃ g : BG,((b g).2).2.1.Nonempty)
    then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
      q rho Vs Vb mu Knu zeta theta o k st z‖ else 0

/-- Exact transfer from the proved BIG promotion row to the literal
SMALL x BIG source packet. The global joint K is bounded once, after
fixing the full BIG endpoints; it is never separated into functions of
individual groups or endpoints. -/
theorem source_original_memory_ORIGINAL_promoting_packet_bound434
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (Kcap : ℝ)
    (hK : ∀ target : (g : BG) → Fin (J+ell) → BP g,
      ‖Knu nu aux (fun g i => (st.2 g).1 (bigSigma g i)) target‖ ≤ Kcap) :
    sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb mu Knu
      zeta theta o k ≤
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
    Kcap * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod BP bigMod
      J ell m cap (patterns nu) aux st bigSigma bigTau ss mu Vb rho o k := by
  classical
  let D := sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
    (patterns nu) aux st bigSigma ss
  let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
    (patterns nu) aux st bigSigma ss o k
  let W := ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
    (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
    (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let scalar := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    originalEdgeScalar (Knu nu aux
      (fun g i => (st.2 g).1 (bigSigma g i))
      (fun g i => (b g).1 (bigTau g i))) zeta theta D o k
  let bn := sourceOriginalMemoryBigFrameNorm434 BP bigMod (J+ell) cap st.2 mu Vb rho
    (sourceBigShared J ell m (patterns nu)) bigSigma bigTau step
  let good := fun b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2 =>
    sourceOriginalMemoryBigFrameLegal434 BP bigMod (J+ell) cap st.2
      (sourceBigShared J ell m (patterns nu)) bigSigma bigTau D step b ∧
      (∃ g : BG,((b g).2).2.1.Nonempty)
  let smallK := fun b zs => groupPermutedKernel SP smallMod (J+ell) q Vs
    (sourceSmallShared J ell) step (fun _ _ => scalar b) ss tt st.1 zs
  have hW : 0 ≤ W := norm_nonneg _
  have hbn (b) : 0 ≤ bn b := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hCs : 0 ≤ Cs := by
    have hsqrt : Real.sqrt q < 1 := by
      nlinarith only [Real.sq_sqrt hq.le,Real.sqrt_nonneg q,hq1]
    have hs : 0<1-Real.sqrt q := sub_pos.mpr hsqrt
    apply Finset.prod_nonneg
    intro g hg
    have hv := hVs g
    dsimp only [memorySmallRowConstant]
    positivity
  have hscalar (b) : ‖scalar b‖ ≤ Kcap := by
    dsimp only [scalar]
    rw [source_original_edge_scalar_norm434 _ _ _ _ _ _ ho]
    exact hK _
  have hsmall (b) : (∑ zs : GroupState SP smallMod (J+ell),‖smallK b zs‖) ≤
      ‖scalar b‖*Cs :=
    source_original_memory_SOURCE_SMALL_group_kernel_row434 SP smallMod J ell
      q Vs hq hq1 hVs step (fun _ _ => scalar b) ss tt st.1
  let choice := sourceOriginalMemoryFixedPhysicalChoice434 SP smallMod BP bigMod
    J ell m cap patterns nu aux st bigSigma bigTau ss tt
  have hnorm (b) (zs) :
      ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
        q rho Vs Vb mu Knu zeta theta o k st (choice b zs)‖ =
      (W*bn b)*‖smallK b zs‖ := by
    dsimp only [choice,sourceOriginalMemoryFixedPhysicalChoice434,
      sourceOrientedPhysicalCoefficient,W,bn,sourceOriginalMemoryBigFrameNorm434,
      smallK,scalar,D,step]
    simp only [norm_mul,norm_prod]
  have hrow (b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2) :
      (∑ zs : GroupState SP smallMod (J+ell),
        if sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns
          st o k (choice b zs) ∧ (∃ g : BG,((b g).2).2.1.Nonempty)
        then ‖sourceOrientedPhysicalCoefficient SP smallMod BP bigMod J ell m cap patterns
          q rho Vs Vb mu Knu zeta theta o k st (choice b zs)‖ else 0) ≤
      (W*Kcap*Cs)*(if good b then bn b else 0) := by
    by_cases hb : good b
    · rw [if_pos hb]
      calc
        _ ≤ ∑ zs : GroupState SP smallMod (J+ell),(W*bn b)*‖smallK b zs‖ := by
          apply Finset.sum_le_sum
          intro zs hzs
          split_ifs
          · rw [hnorm]
          · exact mul_nonneg (mul_nonneg hW (hbn b)) (norm_nonneg _)
        _ = (W*bn b)*(∑ zs : GroupState SP smallMod (J+ell),‖smallK b zs‖) :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ (W*bn b)*(‖scalar b‖*Cs) :=
          mul_le_mul_of_nonneg_left (hsmall b) (mul_nonneg hW (hbn b))
        _ ≤ (W*bn b)*(Kcap*Cs) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hscalar b) hCs)
            (mul_nonneg hW (hbn b))
        _ = _ := by ring
    · rw [if_neg hb,mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro zs hzs
      apply if_neg
      intro hz
      exact hb ⟨hz.1.2.2.2.1,hz.2⟩
  unfold sourceOriginalMemoryOriginalPromotingPacket434
  calc
    _ ≤ ∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        (W*Kcap*Cs)*(if good b then bn b else 0) :=
      Finset.sum_le_sum (fun b _ => hrow b)
    _ = (W*Kcap*Cs)*∑ b : sourceOriginalMemoryBigFrameChoice434 BP bigMod (J+ell) cap st.2,
        if good b then bn b else 0 := (Finset.mul_sum _ _ _).symm
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryCanonicalPromotionPacket -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Pointwise cap of the literal canonical Memory Knu, discharged by
the actual primitive GLOBAL kernels and true retained cell masses. -/
theorem source_original_memory_CANONICAL_K_norm434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (hhA : 0<hA) (hhB : 0<hB) (hxi : 0<xi)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (s t : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    ‖sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ nu Q hA hB xi aux s t‖ ≤
      (Q:ℝ)^4*(xi⁻¹)^2 := by
  exact source_original_actual_primitive_physical_Knu_bound434
    (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu) Q xi hxi
    (sourceOriginalProbeActiveCellsA434 m P V nu hA xi)
    (sourceOriginalProbeActiveCellsB434 m P V nu hB xi) hA hB hhA hhB
    (sourceOriginalProbeCellA434 m P V nu hA) (sourceOriginalProbeCellB434 m P V nu hB)
    (fun j hj => (source_original_probe_active_cell_A_mem_iff434
      m P V nu hA xi hhA hxi j).mp hj)
    (fun j hj => (source_original_probe_active_cell_B_mem_iff434
      m P V nu hB xi hhB hxi j).mp hj)
    _ _ _ _ _ _ _

/-- The literal original promoting packet with the actual two-GLOBAL
canonical Knu. Its pointwise cap is proved, rather than an assumed
operator, row, Gram or signed-residual estimate. Both signs and all
Fourier/Mellin phases are kept in the original coefficient. -/
theorem source_original_memory_CANONICAL_ORIGINAL_promoting_packet_bound434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (cap : G → ℕ)
    (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (st : FullPhysicalState SP smallMod (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=G) (J+ell))
    (ss tt : GroupPermFamily (G:=SG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : G → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
    (hhA : 0<hA nu) (hhB : 0<hB nu) (hxi : 0<xi)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) :
    let patterns := sourceOriginalProbeMemoryPattern434 J m hmJ
    let Knu := fun nu aux s t =>
      sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q
        (hA nu) (hB nu) xi aux s t
    sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb mu Knu
      zeta theta o k ≤
    ‖(sourceAuxMass (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=G) (J+ell):ℂ) *
      (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖ *
    ((Q:ℝ)^4*(xi⁻¹)^2) * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m cap (patterns nu) aux st bigSigma bigTau ss mu Vb rho o k := by
  dsimp only
  apply source_original_memory_ORIGINAL_promoting_packet_bound434 SP smallMod
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
    J ell m cap (sourceOriginalProbeMemoryPattern434 J m hmJ)
    nu aux st bigSigma bigTau ss tt q rho Vs Vb hq hq1 hVs mu
    (fun nu aux s t => sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q
      (hA nu) (hB nu) xi aux s t) zeta theta o k ho
  intro target
  exact source_original_memory_CANONICAL_K_norm434 P Vb J ell m hmJ nu Q
    (hA nu) (hB nu) xi hhA hhB hxi aux _ target
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryPacketSmallAverage -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Both actual SMALL permutation averages in the literal original
coefficient are reassembled exactly. No factorial or slot-count loss
remains; only the previously proved normalized source average survives. -/
theorem source_original_memory_ORIGINAL_packet_SMALL_average434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    {BG : Type} [Fintype BG] [DecidableEq BG]
    (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
    (J ell m : ℕ) (cap : BG → ℕ)
    {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
    (nu : Nu) (aux : SourceBigAux BP J m (patterns nu))
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=BG) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g)
    (mu : (g : BG) → BP g → ℝ) (Knu : SourcePatternK BP J ell m patterns)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
    (Kcap : ℝ)
    (hK : ∀ target : (g : BG) → Fin (J+ell) → BP g,
      ‖Knu nu aux (fun g i => (st.2 g).1 (bigSigma g i)) target‖ ≤ Kcap) :
    (∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb mu Knu
        zeta theta o k) ≤
    ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=BG) (J+ell):ℂ)‖ *
    Kcap * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    ((∑ ss : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod BP bigMod
        J ell m cap (patterns nu) aux st bigSigma bigTau ss mu Vb rho o k) /
      (((J+ell).factorial:ℝ)^(Fintype.card SG))) := by
  classical
  let F : ℝ := ((J+ell).factorial:ℝ)^(Fintype.card SG)
  let Pm := groupPermutationPairMass (G:=SG) (J+ell)
  let W := ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
    (bigEndpointPairMass (BG:=BG) (J+ell):ℂ)‖
  let Cs := ∏ g : SG,memorySmallRowConstant q (Vs g) ell
  let br := fun ss => sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod BP bigMod
    J ell m cap (patterns nu) aux st bigSigma bigTau ss mu Vb rho o k
  have hCard : (Fintype.card (GroupPermFamily (G:=SG) (J+ell)):ℝ)=F := by
    simp [GroupPermFamily,SlotPerm,Fintype.card_fun,Fintype.card_perm,F]
  have hF : F ≠ 0 := ne_of_gt (pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) _)
  have hPm : 0 ≤ Pm := (groupPermutationPairMass_positive (G:=SG) (J+ell)).le
  have hn : Pm*F^2=1 := by
    have hh : Pm*(Fintype.card (GroupPermFamily (G:=SG) (J+ell)):ℝ)^2=1 := by
      exact_mod_cast groupPermutationPairMass_normalized (G:=SG) (J+ell)
    simpa only [hCard] using hh
  have hPF : Pm*F=1/F := (eq_div_iff hF).mpr (by nlinarith only [hn])
  have hNorm :
      ‖(sourceAuxMass BP bigMod J m Vb (patterns nu) aux:ℂ) *
        (bigEndpointPairMass (BG:=BG) (J+ell):ℂ) *
        (groupPermutationPairMass (G:=SG) (J+ell):ℂ)‖=W*Pm := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hPm]
  have hEach (ss tt : GroupPermFamily (G:=SG) (J+ell)) :
      sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod BP bigMod
        J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb mu Knu
        zeta theta o k ≤ (W*Pm)*Kcap*Cs*br ss := by
    have hh := source_original_memory_ORIGINAL_promoting_packet_bound434 SP smallMod BP bigMod
      J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb hq hq1 hVs
      mu Knu zeta theta o k ho Kcap hK
    simpa only [hNorm] using hh
  calc
    _ ≤ ∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
        (W*Pm)*Kcap*Cs*br ss :=
      Finset.sum_le_sum (fun ss _ => Finset.sum_le_sum (fun tt _ => hEach ss tt))
    _ = (W*Kcap*Cs)*(Pm*F)*(∑ ss : GroupPermFamily (G:=SG) (J+ell),br ss) := by
      simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,hCard]
      simp_rw [show ∀ ss : GroupPermFamily (G:=SG) (J+ell),
        F*((W*Pm)*Kcap*Cs*br ss)=(W*Kcap*Cs)*(Pm*F)*br ss by intro ss;ring]
      rw [← Finset.mul_sum]
    _ = _ := by rw [hPF];ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryCanonicalPacketSmallAverage -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Canonical literal packet with both original SMALL averages assembled. -/
theorem source_original_memory_CANONICAL_ORIGINAL_packet_SMALL_average434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (cap : G → ℕ)
    (nu : SourceOriginalProbePattern434 G m)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu))
    (st : FullPhysicalState SP smallMod (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) cap)
    (bigSigma bigTau : BigGroupPerm (BG:=G) (J+ell))
    (q rho : ℝ) (Vs : SG → ℝ) (Vb : G → ℝ)
    (hq : 0<q) (hq1 : q<1) (hVs : ∀ g,0<Vs g)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi : ℝ)
    (hhA : 0<hA nu) (hhB : 0<hB nu) (hxi : 0<xi)
    (zeta theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) :
    let patterns := sourceOriginalProbeMemoryPattern434 J m hmJ
    let Knu := fun nu aux s t =>
      sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q
        (hA nu) (hB nu) xi aux s t
    (∑ ss : GroupPermFamily (G:=SG) (J+ell),∑ tt : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryOriginalPromotingPacket434 SP smallMod
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m cap patterns nu aux st bigSigma bigTau ss tt q rho Vs Vb mu Knu
      zeta theta o k) ≤
    ‖(sourceAuxMass (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J m Vb (patterns nu) aux:ℂ) *
      (bigEndpointPairMass (BG:=G) (J+ell):ℂ)‖ *
    ((Q:ℝ)^4*(xi⁻¹)^2) * (∏ g : SG,memorySmallRowConstant q (Vs g) ell) *
    ((∑ ss : GroupPermFamily (G:=SG) (J+ell),
      sourceOriginalMemoryPhysicalBigPromotionRow434 SP smallMod
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
      J ell m cap (patterns nu) aux st bigSigma bigTau ss mu Vb rho o k) /
        (((J+ell).factorial:ℝ)^(Fintype.card SG))) := by
  dsimp only
  apply source_original_memory_ORIGINAL_packet_SMALL_average434 SP smallMod
    (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
    J ell m cap (sourceOriginalProbeMemoryPattern434 J m hmJ)
    nu aux st bigSigma bigTau q rho Vs Vb hq hq1 hVs mu
    (fun nu aux s t => sourceOriginalProbeMemoryCanonicalK434 P Vb J ell m hmJ nu Q
      (hA nu) (hB nu) xi aux s t) zeta theta o k ho
  intro target
  exact source_original_memory_CANONICAL_K_norm434 P Vb J ell m hmJ nu Q
    (hA nu) (hB nu) xi hhA hhB hxi aux _ target
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalMemoryActualDivisorReversal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The actual ordered output state, using the literal survivor-plus-store
list and the original per-group cutoff proof. No quotient or deduplication
of repeated OLD atoms is performed. -/
def sourceOriginalMemoryActualOrderedOutput434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z) :
    FullPhysicalState SP smallMod BP bigMod (J+ell) cap :=
  (z.2.2.1.smallTarget,fun g =>
    ((z.2.2.1.bigChoice g).1,
      let step := sourceOrientedStep SP smallMod BP bigMod J ell m cap
        (patterns z.1) z.2.1 st z.2.2.1.sigmaBig z.2.2.2.1 o k
      let ls := physicalPendingOutput (bigMod g) (J+ell) (cap g) (st.2 g)
        (z.2.2.1.sigmaBig g) step (z.2.2.1.bigChoice g).2
      ⟨⟨ls.length,Nat.lt_succ_iff.mpr (hz.2.2.2.1 g).output_within_cutoff⟩,
        fun i => ls.get i⟩))

/-- The literal source divisor survives reversal at the actual ordered
output, including both SMALL/BIG endpoint permutations and the unchanged
auxiliary tuple. This removes a genuine dynamic-D obligation from the
future weighted-column construction. -/
theorem source_original_memory_actual_divisor_reverse434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z) :
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1
      (sourceOriginalMemoryActualOrderedOutput434 SP smallMod BP bigMod J ell m cap
        patterns st o k z hz) z.2.2.1.tauBig z.2.2.2.2 =
    sourceOrientedPhysicalD SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1 st z.2.2.1.sigmaBig z.2.2.2.1 := by
  unfold sourceOrientedPhysicalD
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (smallMod g) ((hz.2.2.2.2 g).2 i hi).symm
  · apply Finset.prod_congr rfl
    intro g hg
    apply congrArg (fun t : ℕ => t*∏ j : ↥((patterns z.1).free g),bigMod g (z.2.1 g j))
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (bigMod g) ((hz.2.2.2.1 g).shared_copy i hi).symm

/-- The reverse source orientation produces exactly minus the original
integer step at that literal output; the mode k is unchanged. -/
theorem source_original_memory_actual_step_reverse434
    (st : FullPhysicalState SP smallMod BP bigMod (J+ell) cap) (o k : ℤ)
    (z : FullOrientedSourceChoice SP smallMod BP bigMod J ell m cap patterns st)
    (hz : sourceOrientedPhysicalLegal SP smallMod BP bigMod J ell m cap patterns st o k z) :
    sourceOrientedStep SP smallMod BP bigMod J ell m cap
      (patterns z.1) z.2.1
      (sourceOriginalMemoryActualOrderedOutput434 SP smallMod BP bigMod J ell m cap
        patterns st o k z hz) z.2.2.1.tauBig z.2.2.2.2 (-o) k =
      -(sourceOrientedStep SP smallMod BP bigMod J ell m cap
        (patterns z.1) z.2.1 st z.2.2.1.sigmaBig z.2.2.2.1 o k) := by
  unfold sourceOrientedStep
  rw [source_original_memory_actual_divisor_reverse434]
  ring
end Green64Analytic.CorrelationSquare

end

end

