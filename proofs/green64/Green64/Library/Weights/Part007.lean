module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Green64.Library.Analysis.Estimates.Part001
public import Green64.Library.Weights.Part005
public import Mathlib.Analysis.MellinInversion

@[expose] public section

/-!
# Weights / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ReciprocalSimplex -/

section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
open scoped BigOperators Topology
namespace Green64Analytic.ReciprocalSimplex

def Expected_fixed_simplex_continuity : Prop :=
  ∀ (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsFiniteMeasure μ]
   (a : ℝ), 0 < a →
   Continuous (fun q : ℝ × ℝ =>
   (max 0 (q.2 - (n+1:ℕ)*q.1))^n / ((n+1).factorial : ℝ) *
   ∫ z, ((∏ i : Fin n, (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*z i))⁻¹) *
   (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*(1-∑ i : Fin n, z i)))⁻¹) ∂μ)

theorem fixed_simplex_continuity :
  ∀ (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsFiniteMeasure μ]
   (a : ℝ), 0 < a →
   Continuous (fun q : ℝ × ℝ =>
   (max 0 (q.2 - (n+1:ℕ)*q.1))^n / ((n+1).factorial : ℝ) *
   ∫ z, ((∏ i : Fin n, (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*z i))⁻¹) *
   (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*(1-∑ i : Fin n, z i)))⁻¹) ∂μ) :=
  by
   intro n μ _ a ha
   let s : ℝ × ℝ → ℝ := fun q => max 0 (q.2 - (n+1:ℕ)*q.1)
   let F : (ℝ × ℝ) → (Fin n → ℝ) → ℝ := fun q z =>
     (∏ i : Fin n, (max a (q.1+s q*z i))⁻¹) *
     (max a (q.1+s q*(1-∑ i : Fin n, z i)))⁻¹
   have hs : Continuous s := continuous_const.max
     (continuous_snd.sub (continuous_const.mul continuous_fst))
   have hc : ∀ q, Continuous (F q) := by
     intro q
     apply Continuous.mul
     · apply continuous_finsetProd
       intro i hi
       apply Continuous.inv₀
       · exact continuous_const.max (continuous_const.add
           (continuous_const.mul (continuous_apply i)))
       · intro z
         exact ne_of_gt (ha.trans_le (le_max_left _ _))
     · apply Continuous.inv₀
       · apply continuous_const.max
         apply continuous_const.add
         apply continuous_const.mul
         apply continuous_const.sub
         exact continuous_finsetSum _ (fun i _ => continuous_apply i)
       · intro z
         exact ne_of_gt (ha.trans_le (le_max_left _ _))
   have hp : ∀ z, Continuous (fun q => F q z) := by
     intro z
     apply Continuous.mul
     · apply continuous_finsetProd
       intro i hi
       apply Continuous.inv₀
       · exact continuous_const.max (continuous_fst.add (hs.mul continuous_const))
       · intro q
         exact ne_of_gt (ha.trans_le (le_max_left _ _))
     · apply Continuous.inv₀
       · exact continuous_const.max (continuous_fst.add (hs.mul continuous_const))
       · intro q
         exact ne_of_gt (ha.trans_le (le_max_left _ _))
   have hb : ∀ q z, ‖F q z‖ ≤ (a⁻¹)^n*a⁻¹ := by
     intro q z
     have hi (v : ℝ) : 0 ≤ (max a v)⁻¹ ∧ (max a v)⁻¹ ≤ a⁻¹ :=
       ⟨inv_nonneg.mpr (ha.le.trans (le_max_left _ _)),
        inv_anti₀ ha (le_max_left _ _)⟩
     have hprod : 0 ≤ ∏ i : Fin n, (max a (q.1+s q*z i))⁻¹ :=
       Finset.prod_nonneg (fun i _ => (hi _).1)
     have hprod' : (∏ i : Fin n, (max a (q.1+s q*z i))⁻¹) ≤ (a⁻¹)^n := by
       calc
         _ ≤ ∏ i : Fin n, a⁻¹ :=
           Finset.prod_le_prod₀ (fun i _ => (hi _).1) (fun i _ => (hi _).2)
         _ = _ := by simp
     rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (hi _).1)]
     exact mul_le_mul hprod' (hi _).2 (hi _).1 (pow_nonneg (inv_nonneg.mpr ha.le) _)
   have hcont : Continuous (fun q => ∫ z, F q z ∂μ) :=
     MeasureTheory.continuous_of_dominated
       (fun q => (hc q).aestronglyMeasurable)
       (fun q => Filter.Eventually.of_forall (hb q))
       (MeasureTheory.integrable_const _) (Filter.Eventually.of_forall hp)
   exact ((hs.pow n).div_const _).mul hcont

def Expected_simplex_volume_bound : Prop :=
  ∀ n : ℕ,
   MeasureTheory.volume {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ≤ 1

theorem simplex_volume_bound :
  ∀ n : ℕ,
   MeasureTheory.volume {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ≤ 1 :=
  by
   intro n
   have hsub : {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ⊆
     Set.Icc (fun _ : Fin n => (0:ℝ)) (fun _ => (1:ℝ)) := by
     intro z hz
     refine ⟨hz.1, ?_⟩
     intro i
     exact (Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)).trans hz.2
   calc
     _ ≤ MeasureTheory.volume (Set.Icc (fun _ : Fin n => (0:ℝ)) (fun _ => (1:ℝ))) :=
       MeasureTheory.measure_mono hsub
     _ = 1 := by simp [Real.volume_Icc_pi]

def Expected_affine_integral : Prop :=
  ∀ (n : ℕ) (s : ℝ) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ),
   0 < s → Measurable f →
   (∫ z, f z) = s^n * ∫ z, f (c + s • z)

theorem affine_integral :
  ∀ (n : ℕ) (s : ℝ) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ),
   0 < s → Measurable f →
   (∫ z, f z) = s^n * ∫ z, f (c + s • z) :=
  by
   intro n s c f hs hf
   have hg : MeasureTheory.StronglyMeasurable (fun z : Fin n → ℝ => f (c+z)) :=
     (hf.comp (continuous_const.add continuous_id).measurable).stronglyMeasurable
   have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := MeasureTheory.volume)
     (continuous_const_smul s).measurable hg
   rw [MeasureTheory.Measure.map_addHaar_smul MeasureTheory.volume (ne_of_gt hs)] at h
   simp only [Module.finrank_pi, Fintype.card_fin, MeasureTheory.integral_smul_measure, abs_of_pos (inv_pos.mpr (pow_pos hs n)), smul_eq_mul] at h
   rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hs.le n)),
     MeasureTheory.integral_add_left_eq_self f c] at h
   calc
     _ = s^n * ((s^n)⁻¹ * ∫ z, f z) := by field_simp [ne_of_gt hs]
     _ = _ := by rw [h]

def Expected_simplex_change_variables : Prop :=
  ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   (n+1:ℕ)*γ < w → Measurable f →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) =
   (w-(n+1:ℕ)*γ)^n *
   ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
   f (fun i => γ+(w-(n+1:ℕ)*γ)*z i)

theorem simplex_change_variables :
  ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   (n+1:ℕ)*γ < w → Measurable f →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) =
   (w-(n+1:ℕ)*γ)^n *
   ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
   f (fun i => γ+(w-(n+1:ℕ)*γ)*z i) :=
  by
   have affine : ∀ (n : ℕ) (s : ℝ) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ),
   0 < s → Measurable f →
   (∫ z, f z) = s^n * ∫ z, f (c + s • z) :=
    by
     intro n s c f hs hf
     have hg : MeasureTheory.StronglyMeasurable (fun z : Fin n → ℝ => f (c+z)) :=
       (hf.comp (continuous_const.add continuous_id).measurable).stronglyMeasurable
     have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := MeasureTheory.volume)
       (continuous_const_smul s).measurable hg
     rw [MeasureTheory.Measure.map_addHaar_smul MeasureTheory.volume (ne_of_gt hs)] at h
     simp only [Module.finrank_pi, Fintype.card_fin, MeasureTheory.integral_smul_measure, abs_of_pos (inv_pos.mpr (pow_pos hs n)), smul_eq_mul] at h
     rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hs.le n)),
       MeasureTheory.integral_add_left_eq_self f c] at h
     calc
       _ = s^n * ((s^n)⁻¹ * ∫ z, f z) := by field_simp [ne_of_gt hs]
       _ = _ := by rw [h]
   intro n γ w f hw hf
   classical
   let s := w-(n+1:ℕ)*γ
   have hs : 0<s := sub_pos.mpr hw
   let T := {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}
   let S := {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}
   have hT : MeasurableSet T := by dsimp [T]; measurability
   have hS : MeasurableSet S := by dsimp [S]; measurability
   have hm (z : Fin n → ℝ) :
     (fun i => γ+s*z i) ∈ T ↔ z∈S := by
     have hsum : (∑ i : Fin n, (γ+s*z i)) = (n:ℝ)*γ+s*∑ i, z i := by
       simp [Finset.sum_add_distrib, Finset.mul_sum]
     change ((∀ i, γ ≤ γ+s*z i) ∧ (∑ i : Fin n, (γ+s*z i)) ≤ w-γ) ↔ _
     rw [hsum]
     constructor
     · intro h
       refine ⟨fun i => ?_, ?_⟩
       · have := h.1 i
         nlinarith
       · have hh := h.2
         dsimp [s] at hs hh ⊢
         push_cast at hw hh hs ⊢
         nlinarith
     · intro h
       refine ⟨fun i => ?_, ?_⟩
       · have := h.1 i
         nlinarith
       · have hh := h.2
         dsimp [s]
         push_cast at hw hs ⊢
         dsimp [s] at hs
         push_cast at hs
         nlinarith
   have he := affine n s (fun _ => γ) (T.indicator f) hs (hf.indicator hT)
   rw [MeasureTheory.integral_indicator hT] at he
   rw [he]
   congr 1
   rw [← MeasureTheory.integral_indicator hS]
   apply MeasureTheory.integral_congr_ae
   apply Filter.Eventually.of_forall
   intro z
   change T.indicator f (fun i => γ+s*z i) = S.indicator (fun z => f (fun i => γ+s*z i)) z
   by_cases hz : z∈S
   · rw [Set.indicator_of_mem hz,Set.indicator_of_mem ((hm z).mpr hz)]
   · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem (mt (hm z).mp hz)]

def Expected_simplex_boundary_zero : Prop :=
  ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   0<n → w ≤ (n+1:ℕ)*γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0

theorem simplex_boundary_zero :
  ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   0<n → w ≤ (n+1:ℕ)*γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0 :=
  by
   intro n γ w f hn hw
   let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
   have hsub : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} ⊆
     {fun _ : Fin n => γ} := by
     intro t ht
     apply Set.mem_singleton_iff.mpr
     funext i
     have hle : t i-γ ≤ ∑ j : Fin n, (t j-γ) :=
       Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ht.1 j)) (Finset.mem_univ i)
     have hsum : (∑ j : Fin n, (t j-γ)) = (∑ j, t j)-(n:ℝ)*γ := by
       simp [Finset.sum_sub_distrib]
     rw [hsum] at hle
     have ht2 := ht.2
     push_cast at hw
     have := ht.1 i
     linarith
   have hz : MeasureTheory.volume {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}=0 :=
     le_antisymm ((MeasureTheory.measure_mono hsub).trans (by simp)) (by positivity)
   rw [MeasureTheory.Measure.restrict_eq_zero.mpr hz]
   simp

def Expected_literal_simplex_representation : Prop :=
  ∀ (n : ℕ) (a γ w : ℝ), 0<n → 0<a → a≤γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
     (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ) =
   (max 0 (w-(n+1:ℕ)*γ))^n / ((n+1).factorial : ℝ) *
   ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
     (∏ i : Fin n, (max a (γ+max 0 (w-(n+1:ℕ)*γ)*z i))⁻¹) *
     (max a (γ+max 0 (w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i)))⁻¹

theorem literal_simplex_representation :
  ∀ (n : ℕ) (a γ w : ℝ), 0<n → 0<a → a≤γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
     (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ) =
   (max 0 (w-(n+1:ℕ)*γ))^n / ((n+1).factorial : ℝ) *
   ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
     (∏ i : Fin n, (max a (γ+max 0 (w-(n+1:ℕ)*γ)*z i))⁻¹) *
     (max a (γ+max 0 (w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i)))⁻¹ :=
  by
   have changeVar : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   (n+1:ℕ)*γ < w → Measurable f →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) =
   (w-(n+1:ℕ)*γ)^n *
   ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
   f (fun i => γ+(w-(n+1:ℕ)*γ)*z i) :=
    by
     have affine : ∀ (n : ℕ) (s : ℝ) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ),
     0 < s → Measurable f →
     (∫ z, f z) = s^n * ∫ z, f (c + s • z) :=
      by
       intro n s c f hs hf
       have hg : MeasureTheory.StronglyMeasurable (fun z : Fin n → ℝ => f (c+z)) :=
         (hf.comp (continuous_const.add continuous_id).measurable).stronglyMeasurable
       have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := MeasureTheory.volume)
         (continuous_const_smul s).measurable hg
       rw [MeasureTheory.Measure.map_addHaar_smul MeasureTheory.volume (ne_of_gt hs)] at h
       simp only [Module.finrank_pi, Fintype.card_fin, MeasureTheory.integral_smul_measure, abs_of_pos (inv_pos.mpr (pow_pos hs n)), smul_eq_mul] at h
       rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hs.le n)),
         MeasureTheory.integral_add_left_eq_self f c] at h
       calc
         _ = s^n * ((s^n)⁻¹ * ∫ z, f z) := by field_simp [ne_of_gt hs]
         _ = _ := by rw [h]
     intro n γ w f hw hf
     classical
     let s := w-(n+1:ℕ)*γ
     have hs : 0<s := sub_pos.mpr hw
     let T := {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}
     let S := {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}
     have hT : MeasurableSet T := by dsimp [T]; measurability
     have hS : MeasurableSet S := by dsimp [S]; measurability
     have hm (z : Fin n → ℝ) :
       (fun i => γ+s*z i) ∈ T ↔ z∈S := by
       have hsum : (∑ i : Fin n, (γ+s*z i)) = (n:ℝ)*γ+s*∑ i, z i := by
         simp [Finset.sum_add_distrib, Finset.mul_sum]
       change ((∀ i, γ ≤ γ+s*z i) ∧ (∑ i : Fin n, (γ+s*z i)) ≤ w-γ) ↔ _
       rw [hsum]
       constructor
       · intro h
         refine ⟨fun i => ?_, ?_⟩
         · have := h.1 i
           nlinarith
         · have hh := h.2
           dsimp [s] at hs hh ⊢
           push_cast at hw hh hs ⊢
           nlinarith
       · intro h
         refine ⟨fun i => ?_, ?_⟩
         · have := h.1 i
           nlinarith
         · have hh := h.2
           dsimp [s]
           push_cast at hw hs ⊢
           dsimp [s] at hs
           push_cast at hs
           nlinarith
     have he := affine n s (fun _ => γ) (T.indicator f) hs (hf.indicator hT)
     rw [MeasureTheory.integral_indicator hT] at he
     rw [he]
     congr 1
     rw [← MeasureTheory.integral_indicator hS]
     apply MeasureTheory.integral_congr_ae
     apply Filter.Eventually.of_forall
     intro z
     change T.indicator f (fun i => γ+s*z i) = S.indicator (fun z => f (fun i => γ+s*z i)) z
     by_cases hz : z∈S
     · rw [Set.indicator_of_mem hz,Set.indicator_of_mem ((hm z).mpr hz)]
     · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem (mt (hm z).mp hz)]
   have vanish : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   0<n → w ≤ (n+1:ℕ)*γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0 :=
    by
     intro n γ w f hn hw
     let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
     have hsub : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} ⊆
       {fun _ : Fin n => γ} := by
       intro t ht
       apply Set.mem_singleton_iff.mpr
       funext i
       have hle : t i-γ ≤ ∑ j : Fin n, (t j-γ) :=
         Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ht.1 j)) (Finset.mem_univ i)
       have hsum : (∑ j : Fin n, (t j-γ)) = (∑ j, t j)-(n:ℝ)*γ := by
         simp [Finset.sum_sub_distrib]
       rw [hsum] at hle
       have ht2 := ht.2
       push_cast at hw
       have := ht.1 i
       linarith
     have hz : MeasureTheory.volume {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}=0 :=
       le_antisymm ((MeasureTheory.measure_mono hsub).trans (by simp)) (by positivity)
     rw [MeasureTheory.Measure.restrict_eq_zero.mpr hz]
     simp
   intro n a γ w hn ha haγ
   let f : (Fin n → ℝ) → ℝ := fun t => (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹
   by_cases hs : (n+1:ℕ)*γ < w
   · have hmax : max 0 (w-(n+1:ℕ)*γ)=w-(n+1:ℕ)*γ := max_eq_right (sub_pos.mpr hs).le
     rw [hmax]
     have hf : Measurable f := by dsimp [f]; measurability
     rw [changeVar n γ w f hs hf]
     rw [mul_div_right_comm]
     congr 1
     apply MeasureTheory.setIntegral_congr_fun
     · measurability
     intro z hz
     have hnon : 0≤w-(n+1:ℕ)*γ := (sub_pos.mpr hs).le
     have hm (i : Fin n) : max a (γ+(w-(n+1:ℕ)*γ)*z i)=γ+(w-(n+1:ℕ)*γ)*z i :=
       max_eq_right (haγ.trans (le_add_of_nonneg_right (mul_nonneg hnon (hz.1 i))))
     have hm' : max a (γ+(w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i))=
       γ+(w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i) :=
       max_eq_right (haγ.trans (le_add_of_nonneg_right (mul_nonneg hnon (sub_nonneg.mpr hz.2))))
     simp only [f,hm,hm']
     congr 2
     simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
       Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
     push_cast
     ring
   · have hw : w≤(n+1:ℕ)*γ := le_of_not_gt hs
     rw [vanish n γ w f hn hw]
     rw [max_eq_left (sub_nonpos.mpr hw),zero_pow (by omega : n≠0)]
     simp

def Expected_literal_simplex_continuity : Prop :=
  ∀ n : ℕ, 0<n →
   ContinuousOn (fun q : ℝ × ℝ =>
   (∫ t in {t : Fin n → ℝ | (∀ i, q.1 ≤ t i) ∧ ∑ i, t i ≤ q.2-q.1},
     (∏ i : Fin n, (t i)⁻¹)*(q.2-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ))
   {q | 0<q.1}

theorem literal_simplex_continuity :
  ∀ n : ℕ, 0<n →
   ContinuousOn (fun q : ℝ × ℝ =>
   (∫ t in {t : Fin n → ℝ | (∀ i, q.1 ≤ t i) ∧ ∑ i, t i ≤ q.2-q.1},
     (∏ i : Fin n, (t i)⁻¹)*(q.2-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ))
   {q | 0<q.1} :=
  by
   have representation : ∀ (n : ℕ) (a γ w : ℝ), 0<n → 0<a → a≤γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
     (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ) =
   (max 0 (w-(n+1:ℕ)*γ))^n / ((n+1).factorial : ℝ) *
   ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
     (∏ i : Fin n, (max a (γ+max 0 (w-(n+1:ℕ)*γ)*z i))⁻¹) *
     (max a (γ+max 0 (w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i)))⁻¹ :=
    by
     have changeVar : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
     (n+1:ℕ)*γ < w → Measurable f →
     (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) =
     (w-(n+1:ℕ)*γ)^n *
     ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
     f (fun i => γ+(w-(n+1:ℕ)*γ)*z i) :=
      by
       have affine : ∀ (n : ℕ) (s : ℝ) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ),
       0 < s → Measurable f →
       (∫ z, f z) = s^n * ∫ z, f (c + s • z) :=
        by
         intro n s c f hs hf
         have hg : MeasureTheory.StronglyMeasurable (fun z : Fin n → ℝ => f (c+z)) :=
           (hf.comp (continuous_const.add continuous_id).measurable).stronglyMeasurable
         have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := MeasureTheory.volume)
           (continuous_const_smul s).measurable hg
         rw [MeasureTheory.Measure.map_addHaar_smul MeasureTheory.volume (ne_of_gt hs)] at h
         simp only [Module.finrank_pi, Fintype.card_fin, MeasureTheory.integral_smul_measure, abs_of_pos (inv_pos.mpr (pow_pos hs n)), smul_eq_mul] at h
         rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hs.le n)),
           MeasureTheory.integral_add_left_eq_self f c] at h
         calc
           _ = s^n * ((s^n)⁻¹ * ∫ z, f z) := by field_simp [ne_of_gt hs]
           _ = _ := by rw [h]
       intro n γ w f hw hf
       classical
       let s := w-(n+1:ℕ)*γ
       have hs : 0<s := sub_pos.mpr hw
       let T := {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}
       let S := {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}
       have hT : MeasurableSet T := by dsimp [T]; measurability
       have hS : MeasurableSet S := by dsimp [S]; measurability
       have hm (z : Fin n → ℝ) :
         (fun i => γ+s*z i) ∈ T ↔ z∈S := by
         have hsum : (∑ i : Fin n, (γ+s*z i)) = (n:ℝ)*γ+s*∑ i, z i := by
           simp [Finset.sum_add_distrib, Finset.mul_sum]
         change ((∀ i, γ ≤ γ+s*z i) ∧ (∑ i : Fin n, (γ+s*z i)) ≤ w-γ) ↔ _
         rw [hsum]
         constructor
         · intro h
           refine ⟨fun i => ?_, ?_⟩
           · have := h.1 i
             nlinarith
           · have hh := h.2
             dsimp [s] at hs hh ⊢
             push_cast at hw hh hs ⊢
             nlinarith
         · intro h
           refine ⟨fun i => ?_, ?_⟩
           · have := h.1 i
             nlinarith
           · have hh := h.2
             dsimp [s]
             push_cast at hw hs ⊢
             dsimp [s] at hs
             push_cast at hs
             nlinarith
       have he := affine n s (fun _ => γ) (T.indicator f) hs (hf.indicator hT)
       rw [MeasureTheory.integral_indicator hT] at he
       rw [he]
       congr 1
       rw [← MeasureTheory.integral_indicator hS]
       apply MeasureTheory.integral_congr_ae
       apply Filter.Eventually.of_forall
       intro z
       change T.indicator f (fun i => γ+s*z i) = S.indicator (fun z => f (fun i => γ+s*z i)) z
       by_cases hz : z∈S
       · rw [Set.indicator_of_mem hz,Set.indicator_of_mem ((hm z).mpr hz)]
       · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem (mt (hm z).mp hz)]
     have vanish : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
     0<n → w ≤ (n+1:ℕ)*γ →
     (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0 :=
      by
       intro n γ w f hn hw
       let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
       have hsub : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} ⊆
         {fun _ : Fin n => γ} := by
         intro t ht
         apply Set.mem_singleton_iff.mpr
         funext i
         have hle : t i-γ ≤ ∑ j : Fin n, (t j-γ) :=
           Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ht.1 j)) (Finset.mem_univ i)
         have hsum : (∑ j : Fin n, (t j-γ)) = (∑ j, t j)-(n:ℝ)*γ := by
           simp [Finset.sum_sub_distrib]
         rw [hsum] at hle
         have ht2 := ht.2
         push_cast at hw
         have := ht.1 i
         linarith
       have hz : MeasureTheory.volume {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}=0 :=
         le_antisymm ((MeasureTheory.measure_mono hsub).trans (by simp)) (by positivity)
       rw [MeasureTheory.Measure.restrict_eq_zero.mpr hz]
       simp
     intro n a γ w hn ha haγ
     let f : (Fin n → ℝ) → ℝ := fun t => (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹
     by_cases hs : (n+1:ℕ)*γ < w
     · have hmax : max 0 (w-(n+1:ℕ)*γ)=w-(n+1:ℕ)*γ := max_eq_right (sub_pos.mpr hs).le
       rw [hmax]
       have hf : Measurable f := by dsimp [f]; measurability
       rw [changeVar n γ w f hs hf]
       rw [mul_div_right_comm]
       congr 1
       apply MeasureTheory.setIntegral_congr_fun
       · measurability
       intro z hz
       have hnon : 0≤w-(n+1:ℕ)*γ := (sub_pos.mpr hs).le
       have hm (i : Fin n) : max a (γ+(w-(n+1:ℕ)*γ)*z i)=γ+(w-(n+1:ℕ)*γ)*z i :=
         max_eq_right (haγ.trans (le_add_of_nonneg_right (mul_nonneg hnon (hz.1 i))))
       have hm' : max a (γ+(w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i))=
         γ+(w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i) :=
         max_eq_right (haγ.trans (le_add_of_nonneg_right (mul_nonneg hnon (sub_nonneg.mpr hz.2))))
       simp only [f,hm,hm']
       congr 2
       simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
         Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
       push_cast
       ring
     · have hw : w≤(n+1:ℕ)*γ := le_of_not_gt hs
       rw [vanish n γ w f hn hw]
       rw [max_eq_left (sub_nonpos.mpr hw),zero_pow (by omega : n≠0)]
       simp
   have fixed : ∀ (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsFiniteMeasure μ]
   (a : ℝ), 0 < a →
   Continuous (fun q : ℝ × ℝ =>
   (max 0 (q.2 - (n+1:ℕ)*q.1))^n / ((n+1).factorial : ℝ) *
   ∫ z, ((∏ i : Fin n, (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*z i))⁻¹) *
   (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*(1-∑ i : Fin n, z i)))⁻¹) ∂μ) :=
    by
     intro n μ _ a ha
     let s : ℝ × ℝ → ℝ := fun q => max 0 (q.2 - (n+1:ℕ)*q.1)
     let F : (ℝ × ℝ) → (Fin n → ℝ) → ℝ := fun q z =>
       (∏ i : Fin n, (max a (q.1+s q*z i))⁻¹) *
       (max a (q.1+s q*(1-∑ i : Fin n, z i)))⁻¹
     have hs : Continuous s := continuous_const.max
       (continuous_snd.sub (continuous_const.mul continuous_fst))
     have hc : ∀ q, Continuous (F q) := by
       intro q
       apply Continuous.mul
       · apply continuous_finsetProd
         intro i hi
         apply Continuous.inv₀
         · exact continuous_const.max (continuous_const.add
             (continuous_const.mul (continuous_apply i)))
         · intro z
           exact ne_of_gt (ha.trans_le (le_max_left _ _))
       · apply Continuous.inv₀
         · apply continuous_const.max
           apply continuous_const.add
           apply continuous_const.mul
           apply continuous_const.sub
           exact continuous_finsetSum _ (fun i _ => continuous_apply i)
         · intro z
           exact ne_of_gt (ha.trans_le (le_max_left _ _))
     have hp : ∀ z, Continuous (fun q => F q z) := by
       intro z
       apply Continuous.mul
       · apply continuous_finsetProd
         intro i hi
         apply Continuous.inv₀
         · exact continuous_const.max (continuous_fst.add (hs.mul continuous_const))
         · intro q
           exact ne_of_gt (ha.trans_le (le_max_left _ _))
       · apply Continuous.inv₀
         · exact continuous_const.max (continuous_fst.add (hs.mul continuous_const))
         · intro q
           exact ne_of_gt (ha.trans_le (le_max_left _ _))
     have hb : ∀ q z, ‖F q z‖ ≤ (a⁻¹)^n*a⁻¹ := by
       intro q z
       have hi (v : ℝ) : 0 ≤ (max a v)⁻¹ ∧ (max a v)⁻¹ ≤ a⁻¹ :=
         ⟨inv_nonneg.mpr (ha.le.trans (le_max_left _ _)),
          inv_anti₀ ha (le_max_left _ _)⟩
       have hprod : 0 ≤ ∏ i : Fin n, (max a (q.1+s q*z i))⁻¹ :=
         Finset.prod_nonneg (fun i _ => (hi _).1)
       have hprod' : (∏ i : Fin n, (max a (q.1+s q*z i))⁻¹) ≤ (a⁻¹)^n := by
         calc
           _ ≤ ∏ i : Fin n, a⁻¹ :=
             Finset.prod_le_prod₀ (fun i _ => (hi _).1) (fun i _ => (hi _).2)
           _ = _ := by simp
       rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (hi _).1)]
       exact mul_le_mul hprod' (hi _).2 (hi _).1 (pow_nonneg (inv_nonneg.mpr ha.le) _)
     have hcont : Continuous (fun q => ∫ z, F q z ∂μ) :=
       MeasureTheory.continuous_of_dominated
         (fun q => (hc q).aestronglyMeasurable)
         (fun q => Filter.Eventually.of_forall (hb q))
         (MeasureTheory.integrable_const _) (Filter.Eventually.of_forall hp)
     exact ((hs.pow n).div_const _).mul hcont
   have volume_bound : ∀ n : ℕ,
   MeasureTheory.volume {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ≤ 1 :=
    by
     intro n
     have hsub : {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ⊆
       Set.Icc (fun _ : Fin n => (0:ℝ)) (fun _ => (1:ℝ)) := by
       intro z hz
       refine ⟨hz.1, ?_⟩
       intro i
       exact (Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)).trans hz.2
     calc
       _ ≤ MeasureTheory.volume (Set.Icc (fun _ : Fin n => (0:ℝ)) (fun _ => (1:ℝ))) :=
         MeasureTheory.measure_mono hsub
       _ = 1 := by simp [Real.volume_Icc_pi]
   intro n hn q hq
   change 0<q.1 at hq
   let S := {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}
   let μ := MeasureTheory.volume.restrict S
   have : MeasureTheory.IsFiniteMeasure μ := ⟨by
     change (MeasureTheory.volume.restrict S) Set.univ < ⊤
     rw [MeasureTheory.Measure.restrict_apply_univ]
     exact (volume_bound n).trans_lt (by simp)⟩
   let a := q.1/2
   have ha : 0<a := by dsimp [a]; exact half_pos hq
   have hnear : ∀ᶠ r : ℝ×ℝ in nhds q, a< r.1 :=
     (isOpen_lt continuous_const continuous_fst).mem_nhds (by
       change q.1/2<q.1
       linarith)
   have he : (fun r : ℝ×ℝ =>
     (∫ t in {t : Fin n → ℝ | (∀ i, r.1 ≤ t i) ∧ ∑ i, t i ≤ r.2-r.1},
      (∏ i : Fin n, (t i)⁻¹)*(r.2-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ)) =ᶠ[nhds q]
     (fun r : ℝ×ℝ => (max 0 (r.2-(n+1:ℕ)*r.1))^n / ((n+1).factorial : ℝ) *
     ∫ z, ((∏ i : Fin n, (max a (r.1+max 0 (r.2-(n+1:ℕ)*r.1)*z i))⁻¹) *
     (max a (r.1+max 0 (r.2-(n+1:ℕ)*r.1)*(1-∑ i : Fin n, z i)))⁻¹) ∂μ) := by
     filter_upwards [hnear] with r hr
     exact representation n a r.1 r.2 hn ha hr.le
   exact ((fixed n μ a ha).continuousAt.congr_of_eventuallyEq he).continuousWithinAt

def Expected_density_finite_cutoff : Prop :=
  let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ∀ (N : ℕ) (γ w : ℝ), 0≤γ → w≤(N+2:ℕ)*γ →
   (∑' n : ℕ, J n γ w) = ∑ n ∈ Finset.range N, J n γ w

theorem density_finite_cutoff :
  let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ∀ (N : ℕ) (γ w : ℝ), 0≤γ → w≤(N+2:ℕ)*γ →
   (∑' n : ℕ, J n γ w) = ∑ n ∈ Finset.range N, J n γ w :=
  by
   have vanish : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
   0<n → w ≤ (n+1:ℕ)*γ →
   (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0 :=
    by
     intro n γ w f hn hw
     let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
     have hsub : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} ⊆
       {fun _ : Fin n => γ} := by
       intro t ht
       apply Set.mem_singleton_iff.mpr
       funext i
       have hle : t i-γ ≤ ∑ j : Fin n, (t j-γ) :=
         Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ht.1 j)) (Finset.mem_univ i)
       have hsum : (∑ j : Fin n, (t j-γ)) = (∑ j, t j)-(n:ℝ)*γ := by
         simp [Finset.sum_sub_distrib]
       rw [hsum] at hle
       have ht2 := ht.2
       push_cast at hw
       have := ht.1 i
       linarith
     have hz : MeasureTheory.volume {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}=0 :=
       le_antisymm ((MeasureTheory.measure_mono hsub).trans (by simp)) (by positivity)
     rw [MeasureTheory.Measure.restrict_eq_zero.mpr hz]
     simp
   intro J N γ w hγ hw
   apply tsum_eq_sum
   intro n hn
   have hNn : N≤n := by simpa using hn
   have hcast : (N+2:ℕ) ≤ (n+2:ℕ) := by omega
   have hR : ((N+2:ℕ):ℝ) ≤ ((n+2:ℕ):ℝ) := by exact_mod_cast hcast
   have hw' : w≤((n+1)+1:ℕ)*γ :=
     hw.trans (mul_le_mul_of_nonneg_right hR hγ)
   dsimp only [J]
   rw [vanish (n+1) γ w _ (by omega) hw',zero_div]

def Expected_density_continuity : Prop :=
  let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ContinuousOn (fun q : ℝ×ℝ => 1/q.2 + ∑' n : ℕ, J n q.1 q.2)
   {q | 0<q.1 ∧ q.1<q.2}

theorem density_continuity :
  let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ContinuousOn (fun q : ℝ×ℝ => 1/q.2 + ∑' n : ℕ, J n q.1 q.2)
   {q | 0<q.1 ∧ q.1<q.2} :=
  by
   have term_cont : (∀ n : ℕ, 0<n →
   ContinuousOn (fun q : ℝ × ℝ =>
   (∫ t in {t : Fin n → ℝ | (∀ i, q.1 ≤ t i) ∧ ∑ i, t i ≤ q.2-q.1},
     (∏ i : Fin n, (t i)⁻¹)*(q.2-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ))
   {q | 0<q.1}) :=
    by
     have representation : ∀ (n : ℕ) (a γ w : ℝ), 0<n → 0<a → a≤γ →
     (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
       (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ) =
     (max 0 (w-(n+1:ℕ)*γ))^n / ((n+1).factorial : ℝ) *
     ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
       (∏ i : Fin n, (max a (γ+max 0 (w-(n+1:ℕ)*γ)*z i))⁻¹) *
       (max a (γ+max 0 (w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i)))⁻¹ :=
      by
       have changeVar : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
       (n+1:ℕ)*γ < w → Measurable f →
       (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) =
       (w-(n+1:ℕ)*γ)^n *
       ∫ z in {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1},
       f (fun i => γ+(w-(n+1:ℕ)*γ)*z i) :=
        by
         have affine : ∀ (n : ℕ) (s : ℝ) (c : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ),
         0 < s → Measurable f →
         (∫ z, f z) = s^n * ∫ z, f (c + s • z) :=
          by
           intro n s c f hs hf
           have hg : MeasureTheory.StronglyMeasurable (fun z : Fin n → ℝ => f (c+z)) :=
             (hf.comp (continuous_const.add continuous_id).measurable).stronglyMeasurable
           have h := MeasureTheory.integral_map_of_stronglyMeasurable (μ := MeasureTheory.volume)
             (continuous_const_smul s).measurable hg
           rw [MeasureTheory.Measure.map_addHaar_smul MeasureTheory.volume (ne_of_gt hs)] at h
           simp only [Module.finrank_pi, Fintype.card_fin, MeasureTheory.integral_smul_measure, abs_of_pos (inv_pos.mpr (pow_pos hs n)), smul_eq_mul] at h
           rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hs.le n)),
             MeasureTheory.integral_add_left_eq_self f c] at h
           calc
             _ = s^n * ((s^n)⁻¹ * ∫ z, f z) := by field_simp [ne_of_gt hs]
             _ = _ := by rw [h]
         intro n γ w f hw hf
         classical
         let s := w-(n+1:ℕ)*γ
         have hs : 0<s := sub_pos.mpr hw
         let T := {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}
         let S := {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}
         have hT : MeasurableSet T := by dsimp [T]; measurability
         have hS : MeasurableSet S := by dsimp [S]; measurability
         have hm (z : Fin n → ℝ) :
           (fun i => γ+s*z i) ∈ T ↔ z∈S := by
           have hsum : (∑ i : Fin n, (γ+s*z i)) = (n:ℝ)*γ+s*∑ i, z i := by
             simp [Finset.sum_add_distrib, Finset.mul_sum]
           change ((∀ i, γ ≤ γ+s*z i) ∧ (∑ i : Fin n, (γ+s*z i)) ≤ w-γ) ↔ _
           rw [hsum]
           constructor
           · intro h
             refine ⟨fun i => ?_, ?_⟩
             · have := h.1 i
               nlinarith
             · have hh := h.2
               dsimp [s] at hs hh ⊢
               push_cast at hw hh hs ⊢
               nlinarith
           · intro h
             refine ⟨fun i => ?_, ?_⟩
             · have := h.1 i
               nlinarith
             · have hh := h.2
               dsimp [s]
               push_cast at hw hs ⊢
               dsimp [s] at hs
               push_cast at hs
               nlinarith
         have he := affine n s (fun _ => γ) (T.indicator f) hs (hf.indicator hT)
         rw [MeasureTheory.integral_indicator hT] at he
         rw [he]
         congr 1
         rw [← MeasureTheory.integral_indicator hS]
         apply MeasureTheory.integral_congr_ae
         apply Filter.Eventually.of_forall
         intro z
         change T.indicator f (fun i => γ+s*z i) = S.indicator (fun z => f (fun i => γ+s*z i)) z
         by_cases hz : z∈S
         · rw [Set.indicator_of_mem hz,Set.indicator_of_mem ((hm z).mpr hz)]
         · rw [Set.indicator_of_notMem hz,Set.indicator_of_notMem (mt (hm z).mp hz)]
       have vanish : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
       0<n → w ≤ (n+1:ℕ)*γ →
       (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0 :=
        by
         intro n γ w f hn hw
         let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
         have hsub : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} ⊆
           {fun _ : Fin n => γ} := by
           intro t ht
           apply Set.mem_singleton_iff.mpr
           funext i
           have hle : t i-γ ≤ ∑ j : Fin n, (t j-γ) :=
             Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ht.1 j)) (Finset.mem_univ i)
           have hsum : (∑ j : Fin n, (t j-γ)) = (∑ j, t j)-(n:ℝ)*γ := by
             simp [Finset.sum_sub_distrib]
           rw [hsum] at hle
           have ht2 := ht.2
           push_cast at hw
           have := ht.1 i
           linarith
         have hz : MeasureTheory.volume {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}=0 :=
           le_antisymm ((MeasureTheory.measure_mono hsub).trans (by simp)) (by positivity)
         rw [MeasureTheory.Measure.restrict_eq_zero.mpr hz]
         simp
       intro n a γ w hn ha haγ
       let f : (Fin n → ℝ) → ℝ := fun t => (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹
       by_cases hs : (n+1:ℕ)*γ < w
       · have hmax : max 0 (w-(n+1:ℕ)*γ)=w-(n+1:ℕ)*γ := max_eq_right (sub_pos.mpr hs).le
         rw [hmax]
         have hf : Measurable f := by dsimp [f]; measurability
         rw [changeVar n γ w f hs hf]
         rw [mul_div_right_comm]
         congr 1
         apply MeasureTheory.setIntegral_congr_fun
         · measurability
         intro z hz
         have hnon : 0≤w-(n+1:ℕ)*γ := (sub_pos.mpr hs).le
         have hm (i : Fin n) : max a (γ+(w-(n+1:ℕ)*γ)*z i)=γ+(w-(n+1:ℕ)*γ)*z i :=
           max_eq_right (haγ.trans (le_add_of_nonneg_right (mul_nonneg hnon (hz.1 i))))
         have hm' : max a (γ+(w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i))=
           γ+(w-(n+1:ℕ)*γ)*(1-∑ i : Fin n, z i) :=
           max_eq_right (haγ.trans (le_add_of_nonneg_right (mul_nonneg hnon (sub_nonneg.mpr hz.2))))
         simp only [f,hm,hm']
         congr 2
         simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
           Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
         push_cast
         ring
       · have hw : w≤(n+1:ℕ)*γ := le_of_not_gt hs
         rw [vanish n γ w f hn hw]
         rw [max_eq_left (sub_nonpos.mpr hw),zero_pow (by omega : n≠0)]
         simp
     have fixed : ∀ (n : ℕ) (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsFiniteMeasure μ]
     (a : ℝ), 0 < a →
     Continuous (fun q : ℝ × ℝ =>
     (max 0 (q.2 - (n+1:ℕ)*q.1))^n / ((n+1).factorial : ℝ) *
     ∫ z, ((∏ i : Fin n, (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*z i))⁻¹) *
     (max a (q.1 + max 0 (q.2 - (n+1:ℕ)*q.1)*(1-∑ i : Fin n, z i)))⁻¹) ∂μ) :=
      by
       intro n μ _ a ha
       let s : ℝ × ℝ → ℝ := fun q => max 0 (q.2 - (n+1:ℕ)*q.1)
       let F : (ℝ × ℝ) → (Fin n → ℝ) → ℝ := fun q z =>
         (∏ i : Fin n, (max a (q.1+s q*z i))⁻¹) *
         (max a (q.1+s q*(1-∑ i : Fin n, z i)))⁻¹
       have hs : Continuous s := continuous_const.max
         (continuous_snd.sub (continuous_const.mul continuous_fst))
       have hc : ∀ q, Continuous (F q) := by
         intro q
         apply Continuous.mul
         · apply continuous_finsetProd
           intro i hi
           apply Continuous.inv₀
           · exact continuous_const.max (continuous_const.add
               (continuous_const.mul (continuous_apply i)))
           · intro z
             exact ne_of_gt (ha.trans_le (le_max_left _ _))
         · apply Continuous.inv₀
           · apply continuous_const.max
             apply continuous_const.add
             apply continuous_const.mul
             apply continuous_const.sub
             exact continuous_finsetSum _ (fun i _ => continuous_apply i)
           · intro z
             exact ne_of_gt (ha.trans_le (le_max_left _ _))
       have hp : ∀ z, Continuous (fun q => F q z) := by
         intro z
         apply Continuous.mul
         · apply continuous_finsetProd
           intro i hi
           apply Continuous.inv₀
           · exact continuous_const.max (continuous_fst.add (hs.mul continuous_const))
           · intro q
             exact ne_of_gt (ha.trans_le (le_max_left _ _))
         · apply Continuous.inv₀
           · exact continuous_const.max (continuous_fst.add (hs.mul continuous_const))
           · intro q
             exact ne_of_gt (ha.trans_le (le_max_left _ _))
       have hb : ∀ q z, ‖F q z‖ ≤ (a⁻¹)^n*a⁻¹ := by
         intro q z
         have hi (v : ℝ) : 0 ≤ (max a v)⁻¹ ∧ (max a v)⁻¹ ≤ a⁻¹ :=
           ⟨inv_nonneg.mpr (ha.le.trans (le_max_left _ _)),
            inv_anti₀ ha (le_max_left _ _)⟩
         have hprod : 0 ≤ ∏ i : Fin n, (max a (q.1+s q*z i))⁻¹ :=
           Finset.prod_nonneg (fun i _ => (hi _).1)
         have hprod' : (∏ i : Fin n, (max a (q.1+s q*z i))⁻¹) ≤ (a⁻¹)^n := by
           calc
             _ ≤ ∏ i : Fin n, a⁻¹ :=
               Finset.prod_le_prod₀ (fun i _ => (hi _).1) (fun i _ => (hi _).2)
             _ = _ := by simp
         rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hprod (hi _).1)]
         exact mul_le_mul hprod' (hi _).2 (hi _).1 (pow_nonneg (inv_nonneg.mpr ha.le) _)
       have hcont : Continuous (fun q => ∫ z, F q z ∂μ) :=
         MeasureTheory.continuous_of_dominated
           (fun q => (hc q).aestronglyMeasurable)
           (fun q => Filter.Eventually.of_forall (hb q))
           (MeasureTheory.integrable_const _) (Filter.Eventually.of_forall hp)
       exact ((hs.pow n).div_const _).mul hcont
     have volume_bound : ∀ n : ℕ,
     MeasureTheory.volume {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ≤ 1 :=
      by
       intro n
       have hsub : {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1} ⊆
         Set.Icc (fun _ : Fin n => (0:ℝ)) (fun _ => (1:ℝ)) := by
         intro z hz
         refine ⟨hz.1, ?_⟩
         intro i
         exact (Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)).trans hz.2
       calc
         _ ≤ MeasureTheory.volume (Set.Icc (fun _ : Fin n => (0:ℝ)) (fun _ => (1:ℝ))) :=
           MeasureTheory.measure_mono hsub
         _ = 1 := by simp [Real.volume_Icc_pi]
     intro n hn q hq
     change 0<q.1 at hq
     let S := {z : Fin n → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}
     let μ := MeasureTheory.volume.restrict S
     have : MeasureTheory.IsFiniteMeasure μ := ⟨by
       change (MeasureTheory.volume.restrict S) Set.univ < ⊤
       rw [MeasureTheory.Measure.restrict_apply_univ]
       exact (volume_bound n).trans_lt (by simp)⟩
     let a := q.1/2
     have ha : 0<a := by dsimp [a]; exact half_pos hq
     have hnear : ∀ᶠ r : ℝ×ℝ in nhds q, a< r.1 :=
       (isOpen_lt continuous_const continuous_fst).mem_nhds (by
         change q.1/2<q.1
         linarith)
     have he : (fun r : ℝ×ℝ =>
       (∫ t in {t : Fin n → ℝ | (∀ i, r.1 ≤ t i) ∧ ∑ i, t i ≤ r.2-r.1},
        (∏ i : Fin n, (t i)⁻¹)*(r.2-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ)) =ᶠ[nhds q]
       (fun r : ℝ×ℝ => (max 0 (r.2-(n+1:ℕ)*r.1))^n / ((n+1).factorial : ℝ) *
       ∫ z, ((∏ i : Fin n, (max a (r.1+max 0 (r.2-(n+1:ℕ)*r.1)*z i))⁻¹) *
       (max a (r.1+max 0 (r.2-(n+1:ℕ)*r.1)*(1-∑ i : Fin n, z i)))⁻¹) ∂μ) := by
       filter_upwards [hnear] with r hr
       exact representation n a r.1 r.2 hn ha hr.le
     exact ((fixed n μ a ha).continuousAt.congr_of_eventuallyEq he).continuousWithinAt
   have cutoff : (let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ∀ (N : ℕ) (γ w : ℝ), 0≤γ → w≤(N+2:ℕ)*γ →
   (∑' n : ℕ, J n γ w) = ∑ n ∈ Finset.range N, J n γ w) :=
    by
     have vanish : ∀ (n : ℕ) (γ w : ℝ) (f : (Fin n → ℝ) → ℝ),
     0<n → w ≤ (n+1:ℕ)*γ →
     (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}, f t) = 0 :=
      by
       intro n γ w f hn hw
       let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
       have hsub : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} ⊆
         {fun _ : Fin n => γ} := by
         intro t ht
         apply Set.mem_singleton_iff.mpr
         funext i
         have hle : t i-γ ≤ ∑ j : Fin n, (t j-γ) :=
           Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ht.1 j)) (Finset.mem_univ i)
         have hsum : (∑ j : Fin n, (t j-γ)) = (∑ j, t j)-(n:ℝ)*γ := by
           simp [Finset.sum_sub_distrib]
         rw [hsum] at hle
         have ht2 := ht.2
         push_cast at hw
         have := ht.1 i
         linarith
       have hz : MeasureTheory.volume {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ}=0 :=
         le_antisymm ((MeasureTheory.measure_mono hsub).trans (by simp)) (by positivity)
       rw [MeasureTheory.Measure.restrict_eq_zero.mpr hz]
       simp
     intro J N γ w hγ hw
     apply tsum_eq_sum
     intro n hn
     have hNn : N≤n := by simpa using hn
     have hcast : (N+2:ℕ) ≤ (n+2:ℕ) := by omega
     have hR : ((N+2:ℕ):ℝ) ≤ ((n+2:ℕ):ℝ) := by exact_mod_cast hcast
     have hw' : w≤((n+1)+1:ℕ)*γ :=
       hw.trans (mul_le_mul_of_nonneg_right hR hγ)
     dsimp only [J]
     rw [vanish (n+1) γ w _ (by omega) hw',zero_div]
   intro J q hq
   change 0<q.1 ∧ q.1<q.2 at hq
   let a := q.1/2
   have ha : 0<a := by dsimp [a]; linarith [hq.1]
   obtain ⟨N,hN⟩ := exists_nat_gt (q.2/a)
   have hN' : q.2 < (N+2:ℕ)*a := by
     have h := (div_lt_iff₀ ha).mp hN
     push_cast
     nlinarith
   have hnear : ∀ᶠ r : ℝ×ℝ in nhds q, a< r.1 ∧ r.2<(N+2:ℕ)*a :=
     ((isOpen_lt continuous_const continuous_fst).inter
       (isOpen_lt continuous_snd continuous_const)).mem_nhds (by
         constructor
         · change q.1/2<q.1
           linarith [hq.1]
         · exact hN')
   have hc : ContinuousOn (fun r : ℝ×ℝ => 1/r.2 + ∑ n ∈ Finset.range N, J n r.1 r.2)
     {r | 0< r.1 ∧ r.1< r.2} := by
     apply ContinuousOn.add
     · exact continuousOn_const.div continuous_snd.continuousOn (fun r hr => ne_of_gt (hr.1.trans hr.2))
     · apply continuousOn_finsetSum
       intro n hn
       exact (term_cont (n+1) (by omega)).mono (fun r hr => hr.1)
   have he : (fun r : ℝ×ℝ => 1/r.2+∑' n : ℕ, J n r.1 r.2) =ᶠ[nhds q]
     (fun r : ℝ×ℝ => 1/r.2+∑ n ∈ Finset.range N, J n r.1 r.2) := by
     filter_upwards [hnear] with r hr
     congr 1
     apply cutoff N r.1 r.2 (ha.le.trans hr.1.le)
     exact hr.2.le.trans (mul_le_mul_of_nonneg_left hr.1.le (by positivity))
   have hopen : IsOpen {r : ℝ×ℝ | 0< r.1 ∧ r.1< r.2} :=
     (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_snd)
   exact ((hc.continuousAt (hopen.mem_nhds hq)).congr_of_eventuallyEq he).continuousWithinAt

def Expected_simplex_nonnegative : Prop :=
  ∀ (n : ℕ) (γ w : ℝ), 0<γ →
   0 ≤ (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ)

theorem simplex_nonnegative :
  ∀ (n : ℕ) (γ w : ℝ), 0<γ →
   0 ≤ (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ) :=
  by
   intro n γ w hγ
   apply div_nonneg _ (Nat.cast_nonneg _)
   apply MeasureTheory.integral_nonneg_of_ae
   have hm : MeasurableSet {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} := by
     measurability
   filter_upwards [MeasureTheory.ae_restrict_mem hm] with t ht
   apply mul_nonneg
   · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hγ.le.trans (ht.1 i)))
   · apply inv_nonneg.mpr
     have := ht.2
     linarith

def Expected_density_one_prime_lower : Prop :=
  let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ∀ γ w : ℝ, 0<γ → 1/w ≤ 1/w+∑' n : ℕ, J n γ w

theorem density_one_prime_lower :
  let J := fun (n : ℕ) (γ w : ℝ) =>
   (∫ t in {t : Fin (n+1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin (n+1), (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ);
   ∀ γ w : ℝ, 0<γ → 1/w ≤ 1/w+∑' n : ℕ, J n γ w :=
  by
   have nonneg : (∀ (n : ℕ) (γ w : ℝ), 0<γ →
   0 ≤ (∫ t in {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
   (∏ i : Fin n, (t i)⁻¹)*(w-∑ i, t i)⁻¹) / ((n+1).factorial : ℝ)) :=
    by
     intro n γ w hγ
     apply div_nonneg _ (Nat.cast_nonneg _)
     apply MeasureTheory.integral_nonneg_of_ae
     have hm : MeasurableSet {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ} := by
       measurability
     filter_upwards [MeasureTheory.ae_restrict_mem hm] with t ht
     apply mul_nonneg
     · exact Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hγ.le.trans (ht.1 i)))
     · apply inv_nonneg.mpr
       have := ht.2
       linarith
   intro J γ w hγ
   exact le_add_of_nonneg_right (tsum_nonneg (fun n => nonneg (n+1) γ w hγ))

end Green64Analytic.ReciprocalSimplex

end

/-! ## S1Base -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

noncomputable def smoothIntervalWeight (a b ε : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u-a+ε)/ε) *
    Real.smoothTransition ((b+ε-u)/ε)

theorem smoothIntervalWeight_contDiff (a b ε : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothIntervalWeight a b ε) := by
  unfold smoothIntervalWeight
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => (u-a+ε)/ε) := by fun_prop
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : ℝ => (b+ε-u)/ε) := by fun_prop
  have ht : ContDiff ℝ (↑(⊤ : ℕ∞)) Real.smoothTransition := Real.smoothTransition.contDiff
  exact (ht.comp h1).mul (ht.comp h2)
end Green64Analytic.LongPrime

end

/-! ## S1FiniteNorm -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem finite_supported_sum_norm
    (S T : Finset ℕ) (d : ℕ → ℂ) (M : ℝ)
    (hsub : T ⊆ S)
    (hzero : ∀ n ∈ S, n ∉ T → d n = 0)
    (hbound : ∀ n ∈ T, ‖d n‖ ≤ M) :
    ‖∑ n ∈ S, d n‖ ≤ (T.card:ℝ)*M := by
  rw [← Finset.sum_subset hsub hzero]
  calc
    ‖∑ n ∈ T, d n‖ ≤ ∑ n ∈ T, ‖d n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ T, M := Finset.sum_le_sum hbound
    _ = (T.card:ℝ)*M := by simp
end Green64Analytic.LongPrime

end

/-! ## S1Properties -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothIntervalWeight_range (a b ε u : ℝ) :
    0 ≤ smoothIntervalWeight a b ε u ∧ smoothIntervalWeight a b ε u ≤ 1 := by
  unfold smoothIntervalWeight
  let x : ℝ := (u-a+ε)/ε
  let y : ℝ := (b+ε-u)/ε
  have hx : 0 ≤ Real.smoothTransition x := Real.smoothTransition.nonneg x
  have hy : 0 ≤ Real.smoothTransition y := Real.smoothTransition.nonneg y
  have hxl : Real.smoothTransition x ≤ 1 := Real.smoothTransition.le_one x
  have hyl : Real.smoothTransition y ≤ 1 := Real.smoothTransition.le_one y
  constructor
  · exact mul_nonneg hx hy
  · calc
      Real.smoothTransition x * Real.smoothTransition y ≤ 1 * Real.smoothTransition y :=
        mul_le_mul_of_nonneg_right hxl hy
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hyl (by norm_num)
      _ = 1 := by ring

theorem smoothIntervalWeight_one (a b ε u : ℝ) (hε : 0 < ε)
    (hau : a ≤ u) (hub : u ≤ b) : smoothIntervalWeight a b ε u = 1 := by
  have hleft : 1 ≤ (u-a+ε)/ε :=
    (le_div_iff₀ hε).2 (by linarith)
  have hright : 1 ≤ (b+ε-u)/ε :=
    (le_div_iff₀ hε).2 (by linarith)
  simp only [smoothIntervalWeight,
    Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, one_mul]

theorem smoothIntervalWeight_zero_left (a b ε u : ℝ) (hε : 0 < ε)
    (hu : u ≤ a-ε) : smoothIntervalWeight a b ε u = 0 := by
  have harg : (u-a+ε)/ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp only [smoothIntervalWeight, Real.smoothTransition.zero_of_nonpos harg, zero_mul]

theorem smoothIntervalWeight_zero_right (a b ε u : ℝ) (hε : 0 < ε)
    (hu : b+ε ≤ u) : smoothIntervalWeight a b ε u = 0 := by
  have harg : (b+ε-u)/ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp only [smoothIntervalWeight, Real.smoothTransition.zero_of_nonpos harg, mul_zero]
end Green64Analytic.LongPrime

end

/-! ## S1Support -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothIntervalWeight_outside_collar
    (a b ε u : ℝ) (hε : 0 < ε)
    (hu : u ≤ a-ε ∨ b+ε ≤ u) :
    smoothIntervalWeight a b ε u = 0 := by
  rcases hu with hleft | hright
  · exact smoothIntervalWeight_zero_left a b ε u hε hleft
  · exact smoothIntervalWeight_zero_right a b ε u hε hright

theorem smoothIntervalWeight_support (a b ε u : ℝ)
    (ha : 1 ≤ a) (hb : b ≤ 2)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hout : u ∉ Set.Icc (1/2 : ℝ) 3) :
    smoothIntervalWeight a b ε u = 0 := by
  apply smoothIntervalWeight_outside_collar a b ε u hε
  have hcase : u < (1/2 : ℝ) ∨ 3 < u := by
    by_contra h
    push_neg at h
    exact hout (Set.mem_Icc.mpr ⟨h.1,h.2⟩)
  rcases hcase with hleft | hright
  · left
    linarith
  · right
    linarith

theorem smoothIntervalWeight_source_package (a b ε : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothIntervalWeight a b ε) ∧
    (∀ u : ℝ, 0 ≤ smoothIntervalWeight a b ε u ∧
      smoothIntervalWeight a b ε u ≤ 1) ∧
    (∀ u ∈ Set.Icc a b, smoothIntervalWeight a b ε u = 1) ∧
    (∀ u ∉ Set.Icc (1/2 : ℝ) 3, smoothIntervalWeight a b ε u = 0) := by
  refine ⟨smoothIntervalWeight_contDiff a b ε, ?_, ?_, ?_⟩
  · exact fun u => smoothIntervalWeight_range a b ε u
  · intro u hu
    exact smoothIntervalWeight_one a b ε u hε hu.1 hu.2
  · intro u hu
    exact smoothIntervalWeight_support a b ε u ha hb hε hεhalf hu
end Green64Analytic.LongPrime

end

/-! ## S1OrdinalHull -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem finite_ordinal_interval_hull
    (S : Finset ℕ) (I : Set ℝ) (hI : Set.OrdConnected I)
    (hNE : ∃ n ∈ S, (n : ℝ) ∈ I) :
    ∃ lo hi : ℕ, (lo : ℝ) ∈ I ∧ (hi : ℝ) ∈ I ∧ lo ≤ hi ∧
      ∀ n ∈ S, ((n : ℝ) ∈ I ↔ lo ≤ n ∧ n ≤ hi) := by
  classical
  let T := S.filter (fun n : ℕ => (n : ℝ) ∈ I)
  have hT : T.Nonempty := by
    obtain ⟨n,hn,hnI⟩ := hNE
    exact ⟨n,Finset.mem_filter.mpr ⟨hn,hnI⟩⟩
  let lo := T.min' hT
  let hi := T.max' hT
  have hloT : lo ∈ T := Finset.min'_mem T hT
  have hhiT : hi ∈ T := Finset.max'_mem T hT
  have hloI : (lo : ℝ) ∈ I := (Finset.mem_filter.mp hloT).2
  have hhiI : (hi : ℝ) ∈ I := (Finset.mem_filter.mp hhiT).2
  have hlohi : lo ≤ hi := Finset.min'_le_max' T hT
  refine ⟨lo,hi,hloI,hhiI,hlohi,?_⟩
  intro n hn
  constructor
  · intro hni
    have hnT : n ∈ T := Finset.mem_filter.mpr ⟨hn,hni⟩
    exact ⟨Finset.min'_le T n hnT,Finset.le_max' T n hnT⟩
  · rintro ⟨hlo, hhi⟩
    have hbetween : (n : ℝ) ∈ Set.Icc (lo:ℝ) (hi:ℝ) :=
      Set.mem_Icc.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
    exact hI.out hloI hhiI hbetween
end Green64Analytic.LongPrime

end

/-! ## S1NormalizedHull -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem finite_ordinal_interval_hull_normalized (S : Finset ℕ) (I : Set ℝ)
    (N : ℝ) (hN : 0 < N) (hI : Set.OrdConnected I)
    (hIS : I ⊆ Set.Icc N (2*N)) (hNE : ∃ n ∈ S, (n : ℝ) ∈ I) :
    ∃ a b : ℝ, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧
      ∀ n ∈ S, ((n : ℝ) ∈ I ↔ a ≤ (n : ℝ)/N ∧ (n : ℝ)/N ≤ b) := by
  obtain ⟨lo,hi,hloI,hhiI,hlohi,hExact⟩ :=
    finite_ordinal_interval_hull S I hI hNE
  have hLo := Set.mem_Icc.mp (hIS hloI)
  have hHi := Set.mem_Icc.mp (hIS hhiI)
  let a : ℝ := (lo : ℝ)/N
  let b : ℝ := (hi : ℝ)/N
  have h1 : 1 ≤ a := by
    dsimp [a]
    exact (le_div_iff₀ hN).2 (by linarith [hLo.1])
  have h2 : a ≤ b := by
    dsimp [a,b]
    apply div_le_div_of_nonneg_right (by exact_mod_cast hlohi) hN.le
  have h3 : b ≤ 2 := by
    dsimp [b]
    exact (div_le_iff₀ hN).2 (by linarith [hHi.2])
  refine ⟨a,b,h1,h2,h3,?_⟩
  intro n hn
  rw [hExact n hn]
  constructor
  · rintro ⟨hl,hr⟩
    constructor
    · dsimp [a]
      apply div_le_div_of_nonneg_right (by exact_mod_cast hl) hN.le
    · dsimp [b]
      apply div_le_div_of_nonneg_right (by exact_mod_cast hr) hN.le
  · rintro ⟨hl,hr⟩
    constructor
    · have hh : (lo : ℝ) ≤ (n : ℝ) :=
        (div_le_div_iff_of_pos_right hN).mp hl
      exact_mod_cast hh
    · have hh : (n : ℝ) ≤ (hi : ℝ) :=
        (div_le_div_iff_of_pos_right hN).mp hr
      exact_mod_cast hh
end Green64Analytic.LongPrime

end

/-! ## S1Collar -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothIntervalWeight_collar
    (a b ε u : ℝ) (hε : 0 < ε) (hab : a ≤ b)
    (hu : u ∉ Set.Icc a b)
    (hn : smoothIntervalWeight a b ε u ≠ 0) :
    (a-ε < u ∧ u < a) ∨ (b < u ∧ u < b+ε) := by
  have hl : a-ε < u := by
    by_contra h
    exact hn (smoothIntervalWeight_zero_left a b ε u hε (le_of_not_gt h))
  have hr : u < b+ε := by
    by_contra h
    exact hn (smoothIntervalWeight_zero_right a b ε u hε (le_of_not_gt h))
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · exact Or.inl ⟨hl,hu⟩
  · exact Or.inr ⟨hu,hr⟩
end Green64Analytic.LongPrime

end

/-! ## S1FiniteSource -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smooth_finite_source_interval (S : Finset ℕ) (I : Set ℝ)
    (N ε : ℝ) (hN : 0 < N) (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hI : Set.OrdConnected I) (hIS : I ⊆ Set.Icc N (2*N))
    (hNE : ∃ n ∈ S, (n : ℝ) ∈ I) :
    ∃ a b : ℝ, 1 ≤ a ∧ a ≤ b ∧ b ≤ 2 ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothIntervalWeight a b ε) ∧
      (∀ u : ℝ, 0 ≤ smoothIntervalWeight a b ε u ∧
        smoothIntervalWeight a b ε u ≤ 1) ∧
      (∀ u ∉ Set.Icc (1/2 : ℝ) 3, smoothIntervalWeight a b ε u = 0) ∧
      (∀ n ∈ S, ((n : ℝ) ∈ I ↔ a ≤ (n : ℝ)/N ∧ (n : ℝ)/N ≤ b)) ∧
      (∀ n ∈ S, (n : ℝ) ∈ I →
        smoothIntervalWeight a b ε ((n : ℝ)/N) = 1) ∧
      (∀ n ∈ S, (n : ℝ) ∉ I →
        smoothIntervalWeight a b ε ((n : ℝ)/N) ≠ 0 →
        (a-ε < (n : ℝ)/N ∧ (n : ℝ)/N < a) ∨
        (b < (n : ℝ)/N ∧ (n : ℝ)/N < b+ε)) := by
  obtain ⟨a,b,ha,hab,hb,hExact⟩ :=
    finite_ordinal_interval_hull_normalized S I N hN hI hIS hNE
  obtain ⟨hd,hrange,hone,hsupport⟩ :=
    smoothIntervalWeight_source_package a b ε ha hab hb hε hεhalf
  refine ⟨a,b,ha,hab,hb,hd,hrange,hsupport,hExact,?_,?_⟩
  · intro n hn hnI
    exact hone ((n : ℝ)/N)
      (Set.mem_Icc.mpr ((hExact n hn).mp hnI))
  · intro n hn hnI hnonzero
    have hout : (n : ℝ)/N ∉ Set.Icc a b := by
      intro hh
      exact hnI ((hExact n hn).mpr (Set.mem_Icc.mp hh))
    exact smoothIntervalWeight_collar a b ε ((n : ℝ)/N)
      hε hab hout hnonzero
end Green64Analytic.LongPrime

end

/-! ## S1CardWidth -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem finite_nat_points_card_le_width
    (S : Finset ℕ) (l r : ℝ) (hlr : l ≤ r)
    (hMem : ∀ n ∈ S, l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r) :
    (S.card : ℝ) ≤ (r-l)+1 := by
  classical
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have hab : a ≤ b := Finset.min'_le_max' S hS
    have ha := (hMem a (Finset.min'_mem S hS)).1
    have hb := (hMem b (Finset.max'_mem S hS)).2
    have hsub : S ⊆ Finset.Icc a b := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S n hn,Finset.le_max' S n hn⟩
    have hcard : S.card ≤ b+1-a := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hsub
    have hcard' : (S.card : ℝ) ≤ (b:ℝ)-(a:ℝ)+1 := by
      have hcast : (b+1-a:ℕ) = b-a+1 := by omega
      rw [hcast] at hcard
      exact_mod_cast hcard
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith
end Green64Analytic.LongPrime

end

/-! ## S1CollarCount -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem finite_left_collar_card (S : Finset ℕ) (a N ε : ℝ)
    (hN : 0 < N) (hε : 0 ≤ ε) :
    ((S.filter (fun n : ℕ => a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a)).card : ℝ)
      ≤ ε*N + 1 := by
  classical
  let T := S.filter (fun n : ℕ => a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a)
  have hle : (a-ε)*N ≤ a*N := by nlinarith
  have hrange : ∀ n ∈ T, (a-ε)*N ≤ (n:ℝ) ∧ (n:ℝ) ≤ a*N := by
    intro n hn
    obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hn
    exact ⟨((lt_div_iff₀ hN).mp hl).le,((div_lt_iff₀ hN).mp hr).le⟩
  have hh := finite_nat_points_card_le_width T ((a-ε)*N) (a*N) hle hrange
  dsimp [T] at hh ⊢
  nlinarith

theorem finite_right_collar_card (S : Finset ℕ) (b N ε : ℝ)
    (hN : 0 < N) (hε : 0 ≤ ε) :
    ((S.filter (fun n : ℕ => b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)).card : ℝ)
      ≤ ε*N + 1 := by
  classical
  let T := S.filter (fun n : ℕ => b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)
  have hle : b*N ≤ (b+ε)*N := by nlinarith
  have hrange : ∀ n ∈ T, b*N ≤ (n:ℝ) ∧ (n:ℝ) ≤ (b+ε)*N := by
    intro n hn
    obtain ⟨_,hl,hr⟩ := Finset.mem_filter.mp hn
    exact ⟨((lt_div_iff₀ hN).mp hl).le,((div_lt_iff₀ hN).mp hr).le⟩
  have hh := finite_nat_points_card_le_width T (b*N) ((b+ε)*N) hle hrange
  dsimp [T] at hh ⊢
  nlinarith

theorem finite_two_collars_card (S : Finset ℕ) (a b N ε : ℝ)
    (hN : 0 < N) (hε : 0 ≤ ε) :
    ((S.filter (fun n : ℕ =>
      (a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
      (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε))).card : ℝ)
      ≤ 2*ε*N+2 := by
  classical
  let A := S.filter (fun n : ℕ => a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a)
  let B := S.filter (fun n : ℕ => b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)
  have hunion : S.filter (fun n : ℕ =>
      (a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
      (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)) = A ∪ B := by
    ext n
    simp only [A, B, Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hunion]
  have hcard := Finset.card_union_le A B
  have ha := finite_left_collar_card S a N ε hN hε
  have hb := finite_right_collar_card S b N ε hN hε
  change (A.card : ℝ) ≤ ε*N+1 at ha
  change (B.card : ℝ) ≤ ε*N+1 at hb
  have hcardR : (((A ∪ B).card : ℕ) : ℝ) ≤
      (A.card : ℝ)+(B.card : ℝ) := by exact_mod_cast hcard
  calc
    ((A ∪ B).card : ℝ) ≤ (A.card : ℝ)+(B.card : ℝ) := hcardR
    _ ≤ (ε*N+1)+(ε*N+1) := add_le_add ha hb
    _ = 2*ε*N+2 := by ring
end Green64Analytic.LongPrime

end

/-! ## S1TransitionBounds -/

section

open Real Set Filter
open scoped Topology
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothTransition_deriv_uniform (j : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ x : ℝ, |iteratedDeriv j Real.smoothTransition x| ≤ B := by
  have hj : ContDiff ℝ (j : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hcont : Continuous (fun x : ℝ => |iteratedDeriv j Real.smoothTransition x|) :=
    ((hj.continuous_iteratedDeriv j (by norm_cast)).abs)
  obtain ⟨u, hu, hmax⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_isMaxOn
      ⟨0, by norm_num⟩ hcont.continuousOn
  refine ⟨max 1 (|iteratedDeriv j Real.smoothTransition u|),
    le_max_left _ _, ?_⟩
  intro x
  by_cases hcase : x ∈ Set.Icc (0:ℝ) 1
  · exact (hmax hcase).trans (le_max_right _ _)
  · have hout : x < 0 ∨ 1 < x := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hcase
      exact hcase
    by_cases hj0 : j = 0
    · subst j
      simp only [iteratedDeriv_zero] 
      rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
      exact (Real.smoothTransition.le_one x).trans
        (le_max_left _ _)
    · have hzero : iteratedDeriv j Real.smoothTransition x = 0 := by
        rcases hout with hx | hx
        · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
            filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
            exact Real.smoothTransition.zero_of_nonpos hy.le
          rw [(Filter.EventuallyEq.iteratedDeriv_eq j heq)]
          simp [iteratedDeriv_const, hj0]
        · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1:ℝ)) := by
            filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
            exact Real.smoothTransition.one_of_one_le hy.le
          rw [(Filter.EventuallyEq.iteratedDeriv_eq j heq)]
          simp [iteratedDeriv_const, hj0]
      rw [hzero, abs_zero]
      exact (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)

end Green64Analytic.LongPrime

end

/-! ## S1Affine -/

section

open Real Set Filter
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothTransition_affine_iteratedDeriv (n : ℕ) (c d u : ℝ) :
  iteratedDeriv n (fun v : ℝ => Real.smoothTransition (c*v+d)) u =
    c^n * iteratedDeriv n Real.smoothTransition (c*u+d) := by
  have hd : ContDiff ℝ (n : ℕ∞) (fun z : ℝ =>
      Real.smoothTransition (z+d)) := by
    have hbase : ContDiff ℝ (n : ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    fun_prop
  have hc := congrFun (iteratedDeriv_comp_const_mul hd c) u
  have ht := congrFun (iteratedDeriv_comp_add_const n Real.smoothTransition d) (c*u)
  simpa only [ht] using hc

noncomputable def transitionDerivBound (n : ℕ) : ℝ :=
  Classical.choose (smoothTransition_deriv_uniform n)

theorem transitionDerivBound_ge_one (n : ℕ) :
    1 ≤ transitionDerivBound n :=
  (Classical.choose_spec (smoothTransition_deriv_uniform n)).1

theorem transitionDerivBound_spec (n : ℕ) (u : ℝ) :
    |iteratedDeriv n Real.smoothTransition u| ≤ transitionDerivBound n :=
  (Classical.choose_spec (smoothTransition_deriv_uniform n)).2 u

theorem smoothTransition_affine_bound (n : ℕ) (c d u : ℝ) :
  |iteratedDeriv n (fun v : ℝ => Real.smoothTransition (c*v+d)) u| ≤
      |c|^n * transitionDerivBound n := by
  rw [smoothTransition_affine_iteratedDeriv]
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (transitionDerivBound_spec n (c*u+d))
     (pow_nonneg (abs_nonneg c) n)
end Green64Analytic.LongPrime

end

/-! ## S1Product -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

noncomputable def smoothIntervalLeft (a ε : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition (ε⁻¹*u + (ε-a)/ε)

noncomputable def smoothIntervalRight (b ε : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((-ε⁻¹)*u + (b+ε)/ε)

theorem smoothIntervalWeight_eq_affine (a b ε : ℝ) (hε : ε ≠ 0) :
    smoothIntervalWeight a b ε =
      fun u => smoothIntervalLeft a ε u * smoothIntervalRight b ε u := by
  funext u
  have hleft : ε⁻¹*u + (ε-a)/ε = (u-a+ε)/ε := by
    field_simp
    ring
  have hright : (-ε⁻¹)*u + (b+ε)/ε = (b+ε-u)/ε := by
    field_simp
    ring
  simp only [smoothIntervalWeight, smoothIntervalLeft, smoothIntervalRight,
    hleft, hright]

theorem smoothIntervalLeft_contDiff (a ε : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothIntervalLeft a ε) := by
  unfold smoothIntervalLeft
  have hh : ContDiff ℝ (↑(⊤ : ℕ∞)) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  fun_prop

theorem smoothIntervalRight_contDiff (b ε : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothIntervalRight b ε) := by
  unfold smoothIntervalRight
  have hh : ContDiff ℝ (↑(⊤ : ℕ∞)) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  fun_prop

theorem smoothIntervalWeight_iteratedDeriv_expansion
    (n : ℕ) (a b ε u : ℝ) (hε : ε ≠ 0) :
    iteratedDeriv n (smoothIntervalWeight a b ε) u =
      ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ) *
        iteratedDeriv i (smoothIntervalLeft a ε) u *
        iteratedDeriv (n-i) (smoothIntervalRight b ε) u := by
  rw [smoothIntervalWeight_eq_affine a b ε hε]
  exact iteratedDeriv_mul
    ((smoothIntervalLeft_contDiff a ε).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n:ℕ∞) ≤ (⊤:ℕ∞))))
    ((smoothIntervalRight_contDiff b ε).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr (le_top : (n:ℕ∞) ≤ (⊤:ℕ∞))))
end Green64Analytic.LongPrime

end

/-! ## S1ScaledDerivative -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothIntervalLeft_deriv_bound (n : ℕ) (a ε u : ℝ) :
  |iteratedDeriv n (smoothIntervalLeft a ε) u| ≤
    |ε⁻¹|^n * transitionDerivBound n := by
  exact smoothTransition_affine_bound n ε⁻¹ ((ε-a)/ε) u

theorem smoothIntervalRight_deriv_bound (n : ℕ) (b ε u : ℝ) :
  |iteratedDeriv n (smoothIntervalRight b ε) u| ≤
    |ε⁻¹|^n * transitionDerivBound n := by
  change |iteratedDeriv n (fun v : ℝ =>
      Real.smoothTransition ((-ε⁻¹)*v + (b+ε)/ε)) u| ≤ _
  simpa only [abs_neg] using
    (smoothTransition_affine_bound n (-ε⁻¹) ((b+ε)/ε) u)

noncomputable def cutoffDerivConstant (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1),
      (n.choose i : ℝ) * transitionDerivBound i *
        transitionDerivBound (n-i)

theorem cutoffDerivConstant_nonneg (n : ℕ) : 0 ≤ cutoffDerivConstant n := by
  unfold cutoffDerivConstant
  apply Finset.sum_nonneg
  intro i hi
  have h1 := transitionDerivBound_ge_one i
  have h2 := transitionDerivBound_ge_one (n-i)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith)
end Green64Analytic.LongPrime

end

/-! ## S1UniformDeriv -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothIntervalWeight_uniform_deriv (n : ℕ) (a b ε u : ℝ)
    (hε : ε ≠ 0) :
    |iteratedDeriv n (smoothIntervalWeight a b ε) u| ≤
      |ε⁻¹|^n * cutoffDerivConstant n := by
  let L (i : ℕ) := iteratedDeriv i (smoothIntervalLeft a ε) u
  let R (i : ℕ) := iteratedDeriv i (smoothIntervalRight b ε) u
  have hleft (i : ℕ) : |L i| ≤ |ε⁻¹|^i * transitionDerivBound i :=
    smoothIntervalLeft_deriv_bound i a ε u
  have hright (i : ℕ) : |R i| ≤ |ε⁻¹|^i * transitionDerivBound i :=
    smoothIntervalRight_deriv_bound i b ε u
  have heq := smoothIntervalWeight_iteratedDeriv_expansion n a b ε u hε
  change _ = ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ) * L i * R (n-i) at heq
  rw [heq]
  calc
    |∑ i ∈ Finset.range (n+1), (n.choose i:ℝ) * L i * R (n-i)| ≤
      ∑ i ∈ Finset.range (n+1), |(n.choose i:ℝ) * L i * R (n-i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n+1),
          |ε⁻¹|^n * ((n.choose i:ℝ) *
            transitionDerivBound i * transitionDerivBound (n-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hL := hleft i
      have hR := hright (n-i)
      have hB : 0 ≤ |ε⁻¹|^i * transitionDerivBound i := by
        apply mul_nonneg (pow_nonneg (abs_nonneg _) _)
        exact le_trans (by norm_num) (transitionDerivBound_ge_one i)
      have hP : |L i| * |R (n-i)| ≤
          (|ε⁻¹|^i * transitionDerivBound i) *
          (|ε⁻¹|^(n-i) * transitionDerivBound (n-i)) :=
        mul_le_mul hL hR (abs_nonneg _) hB
      calc
        |(n.choose i:ℝ) * L i * R (n-i)| =
          (n.choose i:ℝ) * (|L i| * |R (n-i)|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            ring
        _ ≤ (n.choose i:ℝ) *
              ((|ε⁻¹|^i * transitionDerivBound i) *
               (|ε⁻¹|^(n-i) * transitionDerivBound (n-i))) :=
          mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg _)
        _ = |ε⁻¹|^n * ((n.choose i:ℝ) *
             transitionDerivBound i * transitionDerivBound (n-i)) := by
          have hp : |ε⁻¹|^i * |ε⁻¹|^(n-i) = |ε⁻¹|^n := by
            rw [← pow_add, Nat.add_sub_of_le hin]
          calc
            _ = (|ε⁻¹|^i * |ε⁻¹|^(n-i)) *
                  ((n.choose i:ℝ) * transitionDerivBound i *
                    transitionDerivBound (n-i)) := by ring
            _ = _ := by rw [hp]
    _ = |ε⁻¹|^n * cutoffDerivConstant n := by
      simp only [cutoffDerivConstant, Finset.mul_sum]
end Green64Analytic.LongPrime

end

/-! ## S1FinalDerivatives -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

noncomputable def sourceCutoffDerivConst (j : ℕ) : ℝ :=
  max 1 (cutoffDerivConstant j)

theorem sourceCutoffDerivConst_ge_one (j : ℕ) :
    1 ≤ sourceCutoffDerivConst j :=
  le_max_left _ _

theorem smoothIntervalWeight_deriv_scaled (j : ℕ) (a b ε u : ℝ)
    (hε : 0 < ε) :
    |iteratedDeriv j (smoothIntervalWeight a b ε) u| ≤
      ε⁻¹ ^ j * sourceCutoffDerivConst j := by
  have hh := smoothIntervalWeight_uniform_deriv j a b ε u hε.ne'
  have hpos : 0 ≤ ε⁻¹ ^ j := pow_nonneg (inv_nonneg.mpr hε.le) _
  rw [abs_of_pos (inv_pos.mpr hε)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (le_max_right 1 _) hpos)
end Green64Analytic.LongPrime

end

/-! ## S1FlatEndpoints -/

section

open scoped Topology
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem smoothIntervalWeight_flat_endpoints
    (a b ε : ℝ)
    (ha : 1 ≤ a) (hb : b ≤ 2)
    (hε : 0 < ε) (hεquarter : ε ≤ 1/4) :
    ∀ j : ℕ,
      iteratedDeriv j (smoothIntervalWeight a b ε) (1/2 : ℝ) = 0 ∧
      iteratedDeriv j (smoothIntervalWeight a b ε) (3 : ℝ) = 0 := by
  have hleft : smoothIntervalWeight a b ε =ᶠ[nhds (1/2:ℝ)]
      (fun _ : ℝ => (0:ℝ)) := by
    have hlt : (1/2:ℝ) < a-ε := by linarith
    filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
    exact smoothIntervalWeight_zero_left a b ε u hε hu.le
  have hright : smoothIntervalWeight a b ε =ᶠ[nhds (3:ℝ)]
      (fun _ : ℝ => (0:ℝ)) := by
    have hgt : b+ε < (3:ℝ) := by linarith
    filter_upwards [isOpen_Ioi.mem_nhds hgt] with u hu
    exact smoothIntervalWeight_zero_right a b ε u hε hu.le
  intro j
  constructor
  · rw [(Filter.EventuallyEq.iteratedDeriv_eq j hleft)]
    simp
  · rw [(Filter.EventuallyEq.iteratedDeriv_eq j hright)]
    simp
end Green64Analytic.LongPrime

end

/-! ## S1WeightedCollar -/

section

set_option autoImplicit false
open scoped Classical
namespace Green64Analytic.LongPrime

theorem smooth_finite_weighted_collar_error
    (S : Finset ℕ) (I : Set ℝ) (N ε a b M : ℝ) (c : ℕ → ℂ)
    (hN : 0 < N) (hε : 0 < ε) (hab : a ≤ b)
    (hExact : ∀ n ∈ S, ((n : ℝ) ∈ I ↔
      a ≤ (n:ℝ)/N ∧ (n:ℝ)/N ≤ b))
    (hM : 0 ≤ M) (hc : ∀ n ∈ S, ‖c n‖ ≤ M) :
    ‖(∑ n ∈ S, if (n:ℝ) ∈ I then c n else 0) -
      (∑ n ∈ S, c n * (smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ))‖ ≤
      M * (2*ε*N+2) := by
  classical
  let P : ℕ → Prop := fun n =>
    (a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
    (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)
  let T := S.filter P
  let d : ℕ → ℂ := fun n =>
    (if (n:ℝ)∈I then c n else 0) -
       c n*(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hzero : ∀ n ∈ S, n ∉ T → d n = 0 := by
    intro n hn hnT
    by_cases hnI : (n:ℝ) ∈ I
    · have hmem : (n:ℝ)/N ∈ Set.Icc a b :=
        Set.mem_Icc.mpr ((hExact n hn).mp hnI)
      have hone := smoothIntervalWeight_one a b ε ((n:ℝ)/N) hε
        hmem.1 hmem.2
      simp [d, hnI, hone]
    · have hout : (n:ℝ)/N ∉ Set.Icc a b := by
        intro h
        exact hnI ((hExact n hn).mpr (Set.mem_Icc.mp h))
      have hg : smoothIntervalWeight a b ε ((n:ℝ)/N) = 0 := by
        by_contra hh
        have hhT := smoothIntervalWeight_collar a b ε ((n:ℝ)/N)
          hε hab hout hh
        exact hnT (Finset.mem_filter.mpr ⟨hn, hhT⟩)
      simp [d, hnI, hg]
  have hbound : ∀ n ∈ T, ‖d n‖ ≤ M := by
    intro n hnT
    obtain ⟨hn, hcollar⟩ := Finset.mem_filter.mp hnT
    have hout : (n:ℝ)/N ∉ Set.Icc a b := by
      intro hh
      rcases hcollar with hl | hr
      · linarith [hh.1]
      · linarith [hh.2]
    have hnI : (n:ℝ) ∉ I := by
      intro hh
      exact hout (Set.mem_Icc.mpr ((hExact n hn).mp hh))
    have hgrange := smoothIntervalWeight_range a b ε ((n:ℝ)/N)
    have hgNorm : ‖(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hgrange.1] using hgrange.2
    simp only [d, if_neg hnI, zero_sub, norm_neg, norm_mul]
    calc
      ‖c n‖ * ‖(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)‖ ≤
        ‖c n‖*1 := mul_le_mul_of_nonneg_left hgNorm (norm_nonneg _)
      _ = ‖c n‖ := mul_one _
      _ ≤ M := hc n hn
  have hcard : (T.card:ℝ) ≤ 2*ε*N+2 :=
    finite_two_collars_card S a b N ε hN hε.le
  have hsum := finite_supported_sum_norm S T d M hTsub hzero hbound
  have heq : ∑ n ∈ S, d n =
      (∑ n ∈ S, if (n:ℝ)∈I then c n else 0) -
      (∑ n ∈ S, c n*(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)) := by
    exact Finset.sum_sub_distrib _ _
  rw [← heq]
  have hh := mul_le_mul_of_nonneg_left hcard hM
  exact hsum.trans (by nlinarith [hh])
end Green64Analytic.LongPrime

end

/-! ## P1LocalizedCollar -/

section

set_option autoImplicit false
open scoped Classical
namespace Green64Analytic.LongPrime

theorem p1_localized_weighted_collar_error
    (S : Finset ℕ) (I : Set ℝ) (N ε a b M : ℝ) (c : ℕ → ℂ)
    (hN : 0 < N) (hε : 0 < ε) (hab : a ≤ b)
    (hExact : ∀ n ∈ S, ((n : ℝ) ∈ I ↔
      a ≤ (n:ℝ)/N ∧ (n:ℝ)/N ≤ b))
    (hM : 0 ≤ M)
    (hc : ∀ n ∈ S,
      ((a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
       (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)) → ‖c n‖ ≤ M) :
    ‖(∑ n ∈ S, if (n:ℝ) ∈ I then c n else 0) -
      (∑ n ∈ S, c n * (smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ))‖ ≤
      M * (2*ε*N+2) := by
  classical
  let P : ℕ → Prop := fun n =>
    (a-ε < (n:ℝ)/N ∧ (n:ℝ)/N < a) ∨
    (b < (n:ℝ)/N ∧ (n:ℝ)/N < b+ε)
  let T := S.filter P
  let d : ℕ → ℂ := fun n =>
    (if (n:ℝ)∈I then c n else 0) -
       c n*(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hzero : ∀ n ∈ S, n ∉ T → d n = 0 := by
    intro n hn hnT
    by_cases hnI : (n:ℝ) ∈ I
    · have hmem : (n:ℝ)/N ∈ Set.Icc a b :=
        Set.mem_Icc.mpr ((hExact n hn).mp hnI)
      have hone := smoothIntervalWeight_one a b ε ((n:ℝ)/N) hε
        hmem.1 hmem.2
      simp [d, hnI, hone]
    · have hout : (n:ℝ)/N ∉ Set.Icc a b := by
        intro h
        exact hnI ((hExact n hn).mpr (Set.mem_Icc.mp h))
      have hg : smoothIntervalWeight a b ε ((n:ℝ)/N) = 0 := by
        by_contra hh
        have hhT := smoothIntervalWeight_collar a b ε ((n:ℝ)/N)
          hε hab hout hh
        exact hnT (Finset.mem_filter.mpr ⟨hn, hhT⟩)
      simp [d, hnI, hg]
  have hbound : ∀ n ∈ T, ‖d n‖ ≤ M := by
    intro n hnT
    obtain ⟨hn, hcollar⟩ := Finset.mem_filter.mp hnT
    have hout : (n:ℝ)/N ∉ Set.Icc a b := by
      intro hh
      rcases hcollar with hl | hr
      · linarith [hh.1]
      · linarith [hh.2]
    have hnI : (n:ℝ) ∉ I := by
      intro hh
      exact hout (Set.mem_Icc.mpr ((hExact n hn).mp hh))
    have hgrange := smoothIntervalWeight_range a b ε ((n:ℝ)/N)
    have hgNorm : ‖(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hgrange.1] using hgrange.2
    simp only [d, if_neg hnI, zero_sub, norm_neg, norm_mul]
    calc
      ‖c n‖ * ‖(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)‖ ≤
        ‖c n‖*1 := mul_le_mul_of_nonneg_left hgNorm (norm_nonneg _)
      _ = ‖c n‖ := mul_one _
      _ ≤ M := hc n hn hcollar
  have hcard : (T.card:ℝ) ≤ 2*ε*N+2 :=
    finite_two_collars_card S a b N ε hN hε.le
  have hsum := finite_supported_sum_norm S T d M hTsub hzero hbound
  have heq : ∑ n ∈ S, d n =
      (∑ n ∈ S, if (n:ℝ)∈I then c n else 0) -
      (∑ n ∈ S, c n*(smoothIntervalWeight a b ε ((n:ℝ)/N):ℂ)) := by
    exact Finset.sum_sub_distrib _ _
  rw [← heq]
  have hh := mul_le_mul_of_nonneg_left hcard hM
  exact hsum.trans (by nlinarith [hh])
end Green64Analytic.LongPrime

end

/-! ## S2AbstractDecay -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem abstract_decay :
∀ (j : ℕ) (v : ℕ → ℝ) (B : ℝ),
  0 < B → (∀ k < j, v k ≤ v (k+1) / B) →
  v 0 ≤ v j / B^j :=
by
  intro j
  induction j with
  | zero =>
    intro v B hB hStep
    simp
  | succ j ih =>
    intro v B hB hStep
    have hPrev : ∀ k < j, v k ≤ v (k+1)/B := by
      intro k hk
      exact hStep k (Nat.lt_succ_of_lt hk)
    have hfirst := ih v B hB hPrev
    have hlast := hStep j (Nat.lt_succ_self j)
    calc
      v 0 ≤ v j / B^j := hfirst
      _ ≤ (v (j+1) / B) / B^j :=
        div_le_div_of_nonneg_right hlast (pow_nonneg hB.le _)
      _ = v (j+1) / B^(j+1) := by
        rw [pow_succ]
        field_simp
end Green64Analytic.LongPrime

end

/-! ## S2CompactPower -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem power_compact_bound :
∀ (j : ℕ) (t σ : ℝ),
  1/2 ≤ t → t ≤ 3 → -1 ≤ σ → σ ≤ 1 →
  t^(σ+(j:ℝ)-1) ≤ 8*(4:ℝ)^j :=
by
  intro j t σ htlo hthi hσlo hσhi
  have ht0 : 0 < t := by linarith
  have helo : (-2:ℝ) ≤ σ+(j:ℝ)-1 := by
    have hn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    linarith
  have hehi : σ+(j:ℝ)-1 ≤ (j:ℝ) := by linarith
  have hp : (1:ℝ) ≤ (4:ℝ)^j := one_le_pow₀ (by norm_num)
  by_cases ht : 1 ≤ t
  · have h1 := Real.rpow_le_rpow_of_exponent_le ht hehi
    have h2 := Real.rpow_le_rpow ht0.le hthi (Nat.cast_nonneg j)
    calc
      t^(σ+(j:ℝ)-1) ≤ t^(j:ℝ) := h1
      _ ≤ (3:ℝ)^(j:ℝ) := h2
      _ = (3:ℝ)^j := by simp
      _ ≤ (4:ℝ)^j := by gcongr <;> norm_num
      _ ≤ 8*(4:ℝ)^j := by nlinarith [pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) j]
  · have ht1 : t ≤ 1 := by linarith
    have h1 := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 helo
    have h2 := Real.rpow_le_rpow_of_nonpos (show 0 < (1/2:ℝ) by norm_num) htlo
      (show (-2:ℝ) ≤ 0 by norm_num)
    have hcalc : (1/2:ℝ)^(-2:ℝ) = 4 := by norm_num
    calc
      t^(σ+(j:ℝ)-1) ≤ t^(-2:ℝ) := h1
      _ ≤ (1/2:ℝ)^(-2:ℝ) := h2
      _ = 4 := hcalc
      _ ≤ 8*(4:ℝ)^j := by nlinarith
end Green64Analytic.LongPrime

end

/-! ## S2FirstIBP -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_ibp_first :
∀ (a b : ℝ) (g g' : ℝ → ℂ) (s : ℂ),
  0 < a → a ≤ b → s ≠ 0 →
  (∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t) →
  IntervalIntegrable g' MeasureTheory.volume a b →
  g a = 0 → g b = 0 →
  (∫ t in a..b, (t:ℂ)^(s-1) * g t) =
    -(∫ t in a..b, (t:ℂ)^s * g' t) / s :=
by
  intro a b g g' s ha hab hs hg hgi hga hgb
  have hv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt (fun u : ℝ => (u:ℂ)^s / s) ((t:ℂ)^(s-1)) t := by
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hder := (hasDerivAt_ofReal_cpow_const (ne_of_gt htpos) hs).div_const s
    simpa only [mul_div_cancel_left₀ _ hs] using hder
  have hvi : IntervalIntegrable
    (fun t : ℝ => (t:ℂ)^(s-1)) MeasureTheory.volume a b := by
    refine (ContinuousOn.integrableOn_Icc ?_).intervalIntegrable
    intro t ht
    have ht' : t ∈ Set.Icc a b := by
      simpa only [Set.uIcc, min_eq_left hab, max_eq_right hab] using ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht'.1
    exact (Complex.continuousAt_ofReal_cpow_const t (s-1) (Or.inr htpos.ne')).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := g) (v := fun t : ℝ => (t:ℂ)^s/s)
    (u' := g') (v' := fun t : ℝ => (t:ℂ)^(s-1))
    (fun t ht => hg t (by simpa [Set.uIcc_of_le hab] using ht))
    (fun t ht => hv t (by simpa [Set.uIcc_of_le hab] using ht))
    hgi hvi
  simp only [hga,hgb,zero_mul,sub_zero,zero_sub] at hibp
  have hcomm : (∫ t in a..b, (t:ℂ)^(s-1) * g t) =
      (∫ t in a..b, g t * (t:ℂ)^(s-1)) := by
    congr 1
    ext t
    ring
  rw [hcomm, hibp]
  simp_rw [show ∀ t : ℝ, g' t * ((t:ℂ)^s / s) = ((t:ℂ)^s * g' t) / s from
    fun t => by ring]
  rw [intervalIntegral.integral_div]
  ring
end Green64Analytic.LongPrime

end

/-! ## S2FrequencyDecay -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_first_frequency_decay :
∀ (a b : ℝ) (g g' : ℝ → ℂ) (s : ℂ),
  0 < a → a ≤ b → 0 < |s.im| →
  (∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t) →
  IntervalIntegrable g' MeasureTheory.volume a b →
  g a = 0 → g b = 0 →
  ‖∫ t in a..b, (t:ℂ)^(s-1) * g t‖ ≤
    ‖∫ t in a..b, (t:ℂ)^s * g' t‖ / |s.im| :=
by
  intro a b g g' s ha hab him hg hgi hga hgb
  have hs : s ≠ 0 := by
    intro hz
    subst s
    norm_num at him
  have h := by
    have hh : ∀ (a b : ℝ) (g g' : ℝ → ℂ) (s : ℂ),
      0 < a → a ≤ b → s ≠ 0 →
      (∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t) →
      IntervalIntegrable g' MeasureTheory.volume a b →
      g a = 0 → g b = 0 →
      (∫ t in a..b, (t:ℂ)^(s-1) * g t) =
        -(∫ t in a..b, (t:ℂ)^s * g' t) / s := by
      -- The exact preceding kernel lemma is embedded in the package rather than assumed.
      exact mellin_ibp_first
    exact hh a b g g' s ha hab hs hg hgi hga hgb
  rw [h, norm_div, norm_neg]
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    him
    (Complex.abs_im_le_norm s)
end Green64Analytic.LongPrime

end

/-! ## S2IntegralUniform -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open scoped Interval
theorem integral_uniform_bound :
∀ (j : ℕ) (a b : ℝ) (g : ℝ → ℂ) (s : ℂ) (M : ℝ),
  1/2 ≤ a → a ≤ b → b ≤ 3 →
  -1 ≤ s.re → s.re ≤ 1 → 0 ≤ M →
  (∀ t ∈ Set.Icc a b, ‖g t‖ ≤ M) →
  ‖∫ t in a..b, (t:ℂ)^(s+(j:ℂ)-1) * g t‖ ≤
    20*(4:ℝ)^j*M :=
by
  intro j a b g s M ha hab hb hσlo hσhi hM hbound
  have ha0 : 0 < a := by linarith
  have hconst : 0 ≤ (8:ℝ)*(4:ℝ)^j*M := by positivity
  have hf : ∀ t ∈ Ι a b,
      ‖(t:ℂ)^(s+(j:ℂ)-1) * g t‖ ≤ 8*(4:ℝ)^j*M := by
    intro t ht
    have ht' : t ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hab] at ht
      exact Set.Ioc_subset_Icc_self ht
    have htlo : (1/2:ℝ) ≤ t := ha.trans ht'.1
    have hthi : t ≤ 3 := ht'.2.trans hb
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hexp : (s+(j:ℂ)-1).re = s.re+(j:ℝ)-1 := by simp
    rw [hexp]
    have hp := power_compact_bound j t s.re htlo hthi hσlo hσhi
    have hg := hbound t ht'
    exact mul_le_mul hp hg (norm_nonneg _) (by positivity)
  have hwidth : |b-a| ≤ (5/2:ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith
  calc
    ‖∫ t in a..b, (t:ℂ)^(s+(j:ℂ)-1)*g t‖ ≤
        (8*(4:ℝ)^j*M)*|b-a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hf
    _ ≤ (8*(4:ℝ)^j*M)*(5/2:ℝ) :=
      mul_le_mul_of_nonneg_left hwidth hconst
    _ = 20*(4:ℝ)^j*M := by ring
end Green64Analytic.LongPrime

end

/-! ## S2MellinZero -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_zero_bound :
∀ (a b : ℝ) (g : ℝ → ℂ) (s : ℂ) (M : ℝ),
  1/2 ≤ a → a ≤ b → b ≤ 3 →
  -1 ≤ s.re → s.re ≤ 1 → 0 ≤ M →
  (∀ t : ℝ, t ≤ a ∨ b < t → g t = 0) →
  (∀ t ∈ Set.Icc a b, ‖g t‖ ≤ M) →
  ‖mellin g s‖ ≤ 20*M :=
by
  intro a b g s M ha hab hb hσlo hσhi hM hsupp hbound
  have ha0 : 0 < a := by linarith
  rw [mellin_interval a b g s ha0 hab hsupp]
  have h := integral_uniform_bound 0 a b g s M
    ha hab hb hσlo hσhi hM hbound
  simpa using h
end Green64Analytic.LongPrime

end

/-! ## S2JFold -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem jfold_integral_decay :
∀ (j : ℕ) (a b : ℝ) (g : ℕ → ℝ → ℂ) (s : ℂ),
  0 < a → a ≤ b → 0 < |s.im| →
  (∀ k < j, ∀ t ∈ Set.Icc a b, HasDerivAt (g k) (g (k+1) t) t) →
  (∀ k < j, IntervalIntegrable (g (k+1)) MeasureTheory.volume a b) →
  (∀ k < j, g k a = 0 ∧ g k b = 0) →
  ‖∫ t in a..b, (t:ℂ)^(s-1) * g 0 t‖ ≤
    ‖∫ t in a..b, (t:ℂ)^(s + (j:ℂ) - 1) * g j t‖ / |s.im|^j :=
by
  intro j a b g s ha hab hs hder hint hbd
  let I : ℕ → ℂ := fun k =>
    ∫ t in a..b, (t:ℂ)^(s+(k:ℂ)-1) * g k t
  have hstep : ∀ k < j, ‖I k‖ ≤ ‖I (k+1)‖ / |s.im| := by
    intro k hk
    have hs' : 0 < |(s+(k:ℂ)).im| := by simpa using hs
    have hf := mellin_first_frequency_decay a b (g k) (g (k+1))
      (s+(k:ℂ)) ha hab hs' (hder k hk) (hint k hk)
      (hbd k hk).1 (hbd k hk).2
    have he : (s+(↑(k+1):ℂ)-1) = s+(k:ℂ) := by
      push_cast
      ring
    have him : (s+(k:ℂ)).im = s.im := by simp
    rw [him] at hf
    change ‖I k‖ ≤ ‖I (k+1)‖ / |s.im|
    simpa only [I, he] using hf
  have hall := abstract_decay j (fun k => ‖I k‖) |s.im| hs hstep
  simpa only [I, Nat.cast_zero, add_zero, sub_zero] using hall
end Green64Analytic.LongPrime

end

/-! ## S2MellinJFold -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_jfold :
∀ (j : ℕ) (a b : ℝ) (g : ℕ → ℝ → ℂ) (s : ℂ),
  0 < a → a ≤ b → 0 < |s.im| →
  (∀ t : ℝ, t ≤ a ∨ b < t → g 0 t = 0) →
  (∀ k < j, ∀ t ∈ Set.Icc a b, HasDerivAt (g k) (g (k+1) t) t) →
  (∀ k < j, IntervalIntegrable (g (k+1)) MeasureTheory.volume a b) →
  (∀ k < j, g k a = 0 ∧ g k b = 0) →
  ‖mellin (g 0) s‖ ≤
    ‖∫ t in a..b, (t:ℂ)^(s + (j:ℂ) - 1) * g j t‖ / |s.im|^j :=
by
  intro j a b g s ha hab hs hsupport hder hint hbd
  rw [mellin_interval a b (g 0) s ha hab hsupport]
  exact jfold_integral_decay j a b g s ha hab hs hder hint hbd
end Green64Analytic.LongPrime

end

/-! ## S2MellinUniform -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_jfold_uniform :
∀ (j : ℕ) (a b : ℝ) (g : ℕ → ℝ → ℂ) (s : ℂ) (M : ℝ),
  1/2 ≤ a → a ≤ b → b ≤ 3 →
  -1 ≤ s.re → s.re ≤ 1 → 0 < |s.im| → 0 ≤ M →
  (∀ t : ℝ, t ≤ a ∨ b < t → g 0 t = 0) →
  (∀ k < j, ∀ t ∈ Set.Icc a b, HasDerivAt (g k) (g (k+1) t) t) →
  (∀ k < j, IntervalIntegrable (g (k+1)) MeasureTheory.volume a b) →
  (∀ k < j, g k a = 0 ∧ g k b = 0) →
  (∀ t ∈ Set.Icc a b, ‖g j t‖ ≤ M) →
  ‖mellin (g 0) s‖ ≤ 20*(4:ℝ)^j*M / |s.im|^j :=
by
  intro j a b g s M ha hab hb hσlo hσhi hs hM
    hsupport hder hint hbd hj
  have ha0 : 0 < a := by linarith
  have h1 := mellin_jfold j a b g s ha0 hab hs
    hsupport hder hint hbd
  have h2 := integral_uniform_bound j a b (g j) s M
    ha hab hb hσlo hσhi hM hj
  exact h1.trans (div_le_div_of_nonneg_right h2 (pow_nonneg hs.le _))
end Green64Analytic.LongPrime

end

/-! ## S2OnePlusAlgebra -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem oneplus_decay_algebra :
∀ (j : ℕ) (z M U : ℝ),
  0 ≤ z → 0 ≤ M → 0 ≤ U →
  U ≤ 20*M →
  (0 < z → U ≤ 20*(4:ℝ)^j*M/z^j) →
  U ≤ 20*(8:ℝ)^j*M/(1+z)^j :=
by
  intro j z M U hz hM hU hzero hhigh
  have hone : 0 < 1+z := by linarith
  apply (le_div_iff₀ (pow_pos hone _)).2
  by_cases hcase : z ≤ 1
  · have hpow : (1+z)^j ≤ (8:ℝ)^j := by
      calc
        (1+z)^j ≤ (2:ℝ)^j := by gcongr <;> linarith
        _ ≤ (8:ℝ)^j := by gcongr <;> norm_num
    calc
      U*(1+z)^j ≤ (20*M)*(1+z)^j :=
        mul_le_mul_of_nonneg_right hzero (pow_nonneg (by linarith) _)
      _ ≤ (20*M)*(8:ℝ)^j :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 20*(8:ℝ)^j*M := by ring
  · have hz1 : 1 ≤ z := by linarith
    have hzpos : 0 < z := by linarith
    have hbound : U*z^j ≤ 20*(4:ℝ)^j*M :=
      (le_div_iff₀ (pow_pos hzpos _)).mp (hhigh hzpos)
    have hpow : (1+z)^j ≤ (2*z)^j := by
      gcongr
      nlinarith
    calc
      U*(1+z)^j ≤ U*(2*z)^j :=
        mul_le_mul_of_nonneg_left hpow hU
      _ = (U*z^j)*(2:ℝ)^j := by rw [mul_pow]; ring
      _ ≤ (20*(4:ℝ)^j*M)*(2:ℝ)^j :=
        mul_le_mul_of_nonneg_right hbound (pow_nonneg (by norm_num) _)
      _ = 20*((4:ℝ)^j*(2:ℝ)^j)*M := by ring
      _ = 20*(8:ℝ)^j*M := by
        rw [← mul_pow]
        norm_num
end Green64Analytic.LongPrime

end

/-! ## S2MellinOnePlus -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_oneplus_decay :
∀ (j : ℕ) (a b : ℝ) (g : ℕ → ℝ → ℂ) (s : ℂ) (M : ℝ),
  1/2 ≤ a → a ≤ b → b ≤ 3 →
  -1 ≤ s.re → s.re ≤ 1 → 0 ≤ M →
  (∀ t : ℝ, t ≤ a ∨ b < t → g 0 t = 0) →
  (∀ k < j, ∀ t ∈ Set.Icc a b, HasDerivAt (g k) (g (k+1) t) t) →
  (∀ k < j, IntervalIntegrable (g (k+1)) MeasureTheory.volume a b) →
  (∀ k < j, g k a = 0 ∧ g k b = 0) →
  (∀ t ∈ Set.Icc a b, ‖g 0 t‖ ≤ M) →
  (∀ t ∈ Set.Icc a b, ‖g j t‖ ≤ M) →
  ‖mellin (g 0) s‖ ≤ 20*(8:ℝ)^j*M/(1+|s.im|)^j :=
by
  intro j a b g s M ha hab hb hσlo hσhi hM
    hsupport hder hint hbd hg0 hgj
  have h0 : ‖mellin (g 0) s‖ ≤ 20*M :=
    mellin_zero_bound a b (g 0) s M
      ha hab hb hσlo hσhi hM hsupport hg0
  have hfreq : 0 < |s.im| →
      ‖mellin (g 0) s‖ ≤ 20*(4:ℝ)^j*M / |s.im|^j := by
    intro hs
    exact mellin_jfold_uniform j a b g s M
      ha hab hb hσlo hσhi hs hM hsupport hder hint hbd hgj
  exact oneplus_decay_algebra j |s.im| M ‖mellin (g 0) s‖
    (abs_nonneg _) hM (norm_nonneg _) h0 hfreq
end Green64Analytic.LongPrime

end

/-! ## M1Vertical -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem vertical_integrable_from_s2 :
∀ (a b σ M : ℝ) (g : ℕ → ℝ → ℂ),
  1/2 ≤ a → a ≤ b → b ≤ 3 →
  -1 ≤ σ → σ ≤ 1 → 0 ≤ M →
  (∀ t : ℝ, t ≤ a ∨ b < t → g 0 t = 0) →
  (∀ k ≤ 2, Continuous (g k)) →
  (∀ k < 2, ∀ t ∈ Set.Icc a b, HasDerivAt (g k) (g (k+1) t) t) →
  (∀ k < 2, g k a = 0 ∧ g k b = 0) →
  (∀ t ∈ Set.Icc a b, ‖g 0 t‖ ≤ M) →
  (∀ t ∈ Set.Icc a b, ‖g 2 t‖ ≤ M) →
  Complex.VerticalIntegrable (mellin (g 0)) σ :=
by
  intro a b σ M g ha hab hb hσlo hσhi hM
    hsupport hcont hder hbd hg0 hg2
  have hsup : ∀ u : ℝ, u < (1/2:ℝ) ∨ (3:ℝ) < u → g 0 u = 0 := by
    intro u hu
    apply hsupport u
    rcases hu with hlow | hhigh
    · left; linarith
    · right; linarith
  have hEntire : Differentiable ℂ (mellin (g 0)) :=
    compact_mellin_entire (g 0) (hcont 0 (by norm_num)) hsup
  have hContinuous : Continuous
      (fun y : ℝ => mellin (g 0) ((σ:ℂ)+(y:ℂ)*Complex.I)) :=
    hEntire.continuous.comp (by fun_prop)
  have hmajor : MeasureTheory.Integrable
      (fun y : ℝ => (20*(8:ℝ)^2*M)/(1+|y|)^2) :=
    integrable_frequency_majorant (20*(8:ℝ)^2*M)
  change MeasureTheory.Integrable
    (fun y : ℝ => mellin (g 0) ((σ:ℂ)+(y:ℂ)*Complex.I))
  apply hmajor.mono' hContinuous.measurable.aestronglyMeasurable
  filter_upwards [] with y
  have hnorm : ‖mellin (g 0) ((σ:ℂ)+(y:ℂ)*Complex.I)‖ ≤
      (20*(8:ℝ)^2*M)/(1+|y|)^2 := by
    have hh := mellin_oneplus_decay 2 a b g ((σ:ℂ)+(y:ℂ)*Complex.I) M
      ha hab hb (by simpa using hσlo) (by simpa using hσhi)
      hM hsupport hder
      (fun k hk => (hcont (k+1) (Nat.succ_le_of_lt hk)).intervalIntegrable a b)
      hbd hg0 hg2
    simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
      Complex.natCast_re, zero_mul, mul_zero, sub_zero, add_zero,
      zero_add, mul_one, Complex.one_re] using hh
  have hnonneg : 0 ≤ (20*(8:ℝ)^2*M)/(1+|y|)^2 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm
end Green64Analytic.LongPrime

end

/-! ## M1Inversion -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime
theorem mellin_inversion_from_s2 :
∀ (a b σ M : ℝ) (g : ℕ → ℝ → ℂ),
  1/2 ≤ a → a ≤ b → b ≤ 3 →
  -1 ≤ σ → σ ≤ 1 → 0 ≤ M →
  (∀ t : ℝ, t ≤ a ∨ b < t → g 0 t = 0) →
  (∀ k ≤ 2, Continuous (g k)) →
  (∀ k < 2, ∀ t ∈ Set.Icc a b, HasDerivAt (g k) (g (k+1) t) t) →
  (∀ k < 2, g k a = 0 ∧ g k b = 0) →
  (∀ t ∈ Set.Icc a b, ‖g 0 t‖ ≤ M) →
  (∀ t ∈ Set.Icc a b, ‖g 2 t‖ ≤ M) →
  ∀ x : ℝ, 0 < x → mellinInv σ (mellin (g 0)) x = g 0 x :=
by
  intro a b σ M g ha hab hb hσlo hσhi hM hsup hcont hder hbd
    h0 h2 x hx
  have ha0 : 0 < a := by linarith
  have hf : MellinConvergent (g 0) (σ:ℂ) :=
    mellin_convergent_compact a b (g 0) (σ:ℂ) ha0 hab
      (hcont 0 (by norm_num)) hsup
  have hV : Complex.VerticalIntegrable (mellin (g 0)) σ :=
    vertical_integrable_from_s2 a b σ M g
      ha hab hb hσlo hσhi hM hsup hcont hder hbd h0 h2
  exact mellinInv_mellin_eq σ (g 0) hx hf hV
    (hcont 0 (by norm_num)).continuousAt
end Green64Analytic.LongPrime

end

/-! ## S1S2RealFamily -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

noncomputable def complexIteratedDerivFamily (h : ℝ → ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  ((iteratedDeriv k h x : ℝ) : ℂ)

theorem complexIteratedDerivFamily_zero (h : ℝ → ℝ) (x : ℝ) :
    complexIteratedDerivFamily h 0 x = (h x : ℂ) := by
  simp [complexIteratedDerivFamily]

theorem complexIteratedDerivFamily_continuous (h : ℝ → ℝ)
    (hd : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (k : ℕ) :
    Continuous (complexIteratedDerivFamily h k) := by
  have hk : Continuous (iteratedDeriv k h) :=
    hd.continuous_iteratedDeriv k
      (WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞) ≤ (⊤:ℕ∞)))
  change Continuous (fun x : ℝ => ((iteratedDeriv k h x : ℝ) : ℂ))
  exact Complex.continuous_ofReal.comp hk

theorem complexIteratedDerivFamily_hasDerivAt (h : ℝ → ℝ)
    (hd : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (k : ℕ) (x : ℝ) :
    HasDerivAt (complexIteratedDerivFamily h k)
      (complexIteratedDerivFamily h (k+1) x) x := by
  have hklt : (k : WithTop ℕ∞) < ((⊤:ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (by simp)
  have hk : Differentiable ℝ (iteratedDeriv k h) :=
    hd.differentiable_iteratedDeriv k hklt
  have hf := (hk x).hasDerivAt.ofReal_comp
  have hh : deriv (iteratedDeriv k h) x = iteratedDeriv (k+1) h x := by
    rw [iteratedDeriv_succ]
  change HasDerivAt (fun y : ℝ => ((iteratedDeriv k h y : ℝ) : ℂ))
    ((iteratedDeriv (k+1) h x : ℝ) : ℂ) x
  simpa only [hh] using hf
end Green64Analytic.LongPrime

end

/-! ## M1RealInversion -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem real_smooth_mellin_inversion
    (h : ℝ → ℝ) (σ M x : ℝ)
    (hd : ContDiff ℝ (↑(⊤:ℕ∞)) h)
    (hM : 1 ≤ M)
    (hsupp : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t → h t = 0)
    (hflat : ∀ k : ℕ, iteratedDeriv k h (1/2:ℝ) = 0 ∧
      iteratedDeriv k h (3:ℝ) = 0)
    (hrange : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |h t| ≤ 1)
    (hderiv : ∀ t ∈ Set.Icc (1/2:ℝ) 3, |iteratedDeriv 2 h t| ≤ M)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ 1) (hx : 0 < x) :
    mellinInv σ (mellin (fun t : ℝ => (h t : ℂ))) x = (h x : ℂ) := by
  let g : ℕ → ℝ → ℂ := complexIteratedDerivFamily h
  have hg0 : ∀ t ∈ Set.Icc (1/2:ℝ) 3, ‖g 0 t‖ ≤ M := by
    intro t ht
    change ‖((h t : ℝ) : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (hrange t ht).trans hM
  have hgj : ∀ t ∈ Set.Icc (1/2:ℝ) 3, ‖g 2 t‖ ≤ M := by
    intro t ht
    change ‖((iteratedDeriv 2 h t : ℝ) : ℂ)‖ ≤ M
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hderiv t ht
  have hgsupport : ∀ t : ℝ, t ≤ (1/2:ℝ) ∨ (3:ℝ) < t →
      g 0 t = 0 := by
    intro t ht
    change ((h t:ℝ):ℂ) = 0
    simp [hsupp t ht]
  have hgcont : ∀ k ≤ 2, Continuous (g k) := by
    intro k hk
    exact complexIteratedDerivFamily_continuous h hd k
  have hgderiv : ∀ k < 2, ∀ t ∈ Set.Icc (1/2:ℝ) 3,
      HasDerivAt (g k) (g (k+1) t) t := by
    intro k hk t ht
    exact complexIteratedDerivFamily_hasDerivAt h hd k t
  have hgflat : ∀ k < 2,
      g k (1/2:ℝ) = 0 ∧ g k (3:ℝ) = 0 := by
    intro k hk
    constructor
    · change ((iteratedDeriv k h (1/2:ℝ):ℝ):ℂ) = 0
      simpa using congrArg Complex.ofReal ((hflat k).1)
    · change ((iteratedDeriv k h (3:ℝ):ℝ):ℂ) = 0
      simpa using congrArg Complex.ofReal ((hflat k).2)
  have hresult := mellin_inversion_from_s2 (1/2:ℝ) 3 σ M g
    (by norm_num) (by norm_num) (by norm_num)
    hσlo hσhi (le_trans (by norm_num) hM)
    hgsupport hgcont hgderiv hgflat hg0 hgj x hx
  have hfun : g 0 = (fun t : ℝ => ((h t : ℝ) : ℂ)) := by
    funext t
    exact complexIteratedDerivFamily_zero _ t
  rw [hfun] at hresult
  exact hresult
end Green64Analytic.LongPrime

end

