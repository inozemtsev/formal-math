module

public import Green64.Library.Weights.B26NumericMarkedCleanHilbert

@[expose] public section

/-!
# Weights / NumericSeenKernelLift

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalNumericSeenKernelLift -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Counting measure in the actual finite NUMERICAL history pool,
with the same active density at both ends. -/
def sourceOriginalNumericSeenEnergy434 {X : Type} [Fintype X]
    (pool : Finset ℕ) (w : X → ℝ) (f : X → Finset ℕ → ℂ) : ℝ :=
  ∑ S ∈ pool.powerset, ∑ x : X, w x * ‖f x S‖^2

/-- A fixed physical fresh-set map. All complex row coefficients remain
inside the sum, and the future reads the actual updated history. -/
def sourceOriginalNumericSeenKernelLift434 {X : Type} [Fintype X]
    (birth : X → Finset ℕ) (gate : X → Finset ℕ → Prop)
    (row : Finset ℕ → X → X → ℂ) (f : X → Finset ℕ → ℂ)
    (x : X) (S : Finset ℕ) : ℂ :=
  if gate x S then ∑ y : X, row S x y *
    (if Disjoint S (birth y) then f y (S ∪ birth y) else 0)
  else 0

private theorem union_injective_on_fresh (F : Finset ℕ)
    (S T : Finset ℕ) (hS : Disjoint S F) (hT : Disjoint T F)
    (h : S ∪ F = T ∪ F) : S = T := by
  ext p
  constructor
  · intro hp
    have hu : p ∈ T ∪ F := by rw [←h]; exact Finset.mem_union_left F hp
    rcases Finset.mem_union.mp hu with hpT | hpF
    · exact hpT
    · exact False.elim (Finset.disjoint_left.mp hS hp hpF)
  · intro hp
    have hu : p ∈ S ∪ F := by rw [h]; exact Finset.mem_union_left F hp
    rcases Finset.mem_union.mp hu with hpS | hpF
    · exact hpS
    · exact False.elim (Finset.disjoint_left.mp hT hp hpF)

/-- Fresh numerical history update is a partial isometry in counting
measure. No independence of the future from its new labels is used. -/
theorem source_original_NUMERIC_SEEN_update_energy434
    (pool F : Finset ℕ) (hF : F ⊆ pool) (f : Finset ℕ → ℂ) :
    (∑ S ∈ pool.powerset, if Disjoint S F then ‖f (S ∪ F)‖^2 else 0) ≤
      ∑ T ∈ pool.powerset, ‖f T‖^2 := by
  let A := pool.powerset.filter (fun S => Disjoint S F)
  have hi : Set.InjOn (fun S : Finset ℕ => S ∪ F) (↑A) := by
    intro S hS T hT h
    exact union_injective_on_fresh F S T
      (Finset.mem_filter.mp hS).2 (Finset.mem_filter.mp hT).2 h
  have hs : A.image (fun S => S ∪ F) ⊆ pool.powerset := by
    intro T hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powerset.mpr (Finset.union_subset
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) hF)
  calc
    _ = ∑ S ∈ A, ‖f (S ∪ F)‖^2 := by rw [Finset.sum_filter]
    _ = ∑ T ∈ A.image (fun S => S ∪ F), ‖f T‖^2 :=
      (Finset.sum_image (f := fun T : Finset ℕ => ‖f T‖^2)
        (s := A) (g := fun S => S ∪ F) hi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)

/-- A genuine unmarked spectral estimate survives fresh numerical
history lifting with exactly the same ENERGY constant. The estimate
may vary with the past; the arbitrary joint future is never bounded
pointwise. This does not assert any unproved estimate on the row. -/
theorem source_original_NUMERIC_SEEN_spectral_lift434
    {X : Type} [Fintype X] (pool : Finset ℕ)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (birth : X → Finset ℕ) (hbirth : ∀ y, birth y ⊆ pool)
    (gate : X → Finset ℕ → Prop) (row : Finset ℕ → X → X → ℂ)
    (R : ℝ) (hR : 0 ≤ R)
    (hOp : ∀ S ∈ pool.powerset, ∀ u : X → ℂ,
      (∑ x : X, w x * ‖∑ y : X, row S x y * u y‖^2) ≤
        R * (∑ y : X, w y * ‖u y‖^2))
    (f : X → Finset ℕ → ℂ) :
    sourceOriginalNumericSeenEnergy434 pool w
      (sourceOriginalNumericSeenKernelLift434 birth gate row f) ≤
        R * sourceOriginalNumericSeenEnergy434 pool w f := by
  let u : Finset ℕ → X → ℂ := fun S y =>
    if Disjoint S (birth y) then f y (S ∪ birth y) else 0
  have hlocal (S : Finset ℕ) (hS : S ∈ pool.powerset) :
      (∑ x : X, w x *
        ‖sourceOriginalNumericSeenKernelLift434 birth gate row f x S‖^2) ≤
      R * (∑ y : X, w y * ‖u S y‖^2) := by
    apply le_trans _ (hOp S hS (u S))
    apply Finset.sum_le_sum
    intro x hx
    by_cases hg : gate x S
    · simp only [sourceOriginalNumericSeenKernelLift434,if_pos hg,u,le_refl]
    · simp only [sourceOriginalNumericSeenKernelLift434,if_neg hg,norm_zero,
        ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero]
      exact mul_nonneg (hw x) (sq_nonneg _)
  have htotal :
      (∑ S ∈ pool.powerset, ∑ y : X, w y * ‖u S y‖^2) ≤
        sourceOriginalNumericSeenEnergy434 pool w f := by
    unfold sourceOriginalNumericSeenEnergy434
    rw [Finset.sum_comm,Finset.sum_comm (s := pool.powerset)]
    apply Finset.sum_le_sum
    intro y hy
    rw [←Finset.mul_sum,←Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hw y)
    have he (S : Finset ℕ) :
        ‖u S y‖^2 =
        if Disjoint S (birth y) then ‖f y (S ∪ birth y)‖^2 else 0 := by
      dsimp only [u]
      split_ifs <;> simp
    simp_rw [he]
    exact source_original_NUMERIC_SEEN_update_energy434 pool (birth y) (hbirth y) (f y)
  calc
    _ ≤ ∑ S ∈ pool.powerset, R * (∑ y : X, w y * ‖u S y‖^2) :=
      Finset.sum_le_sum (fun S hS => hlocal S hS)
    _ = R * (∑ S ∈ pool.powerset, ∑ y : X, w y * ‖u S y‖^2) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal hR

/-- The preceding lifting theorem applies to the EXISTING literal B26
CLEAN operator, with frozen slots, all free marks, and true numeric seen.
The premise is only an unmarked spectral estimate for the SAME row;
it contains the complete joint K and is not a pointwise coefficient cap. -/
theorem source_original_B26_NUMERIC_CLEAN_spectral_lift434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : G) → BP g → ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p, 0 ≤ mu g p)
    (K : SourceOriginalB26Active434 BP J ell → Finset ℕ →
      SourceOriginalB26Active434 BP J ell → ℂ)
    (R : ℝ) (hR : 0 ≤ R)
    (hOp : ∀ S ∈ (sourceOriginalMemoryBirthPool434 BP bm).powerset,
      ∀ u : SourceOriginalB26Active434 BP J ell → ℂ,
      (∑ s : SourceOriginalB26Active434 BP J ell,
        sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu s *
        ‖∑ t : SourceOriginalB26Active434 BP J ell,
          sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
            (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
            (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) * K s S t * u t‖^2) ≤
      R * (∑ t : SourceOriginalB26Active434 BP J ell,
        sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu t * ‖u t‖^2))
    (f : SourceOriginalB26Active434 BP J ell → Finset ℕ → ℂ) :
    sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu
      (sourceOriginalB26NumericMarkedClean434 BP bm J ell m hmJ nu mu K f) ≤
      R * sourceOriginalB26NumericActiveEnergy434 BP bm J ell mu f := by
  let birth := fun t : SourceOriginalB26Active434 BP J ell =>
    (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu t).image
      (fun p : Sigma BP => bm p.1 p.2)
  have hb (t : SourceOriginalB26Active434 BP J ell) :
      birth t ⊆ sourceOriginalMemoryBirthPool434 BP bm := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨a.1,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨a.2,Finset.mem_univ _,rfl⟩⟩
  let gate := fun s : SourceOriginalB26Active434 BP J ell => fun S : Finset ℕ =>
    (sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell) s).image
      (fun p : Sigma BP => bm p.1 p.2) ⊆ S
  let row := fun S : Finset ℕ => fun s t : SourceOriginalB26Active434 BP J ell =>
    sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) * K s S t
  have hw (s : SourceOriginalB26Active434 BP J ell) :
      0 ≤ sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have he (s : SourceOriginalB26Active434 BP J ell) (S : Finset ℕ) :
      sourceOriginalNumericSeenKernelLift434 birth gate row f s S =
      sourceOriginalB26NumericMarkedClean434 BP bm J ell m hmJ nu mu K f s S := by
    unfold sourceOriginalNumericSeenKernelLift434 sourceOriginalB26NumericMarkedClean434
    dsimp only [gate,row,birth]
    split_ifs
    · apply Finset.sum_congr rfl
      intro t ht
      split_ifs <;> simp [mul_assoc]
    · rfl
  have hh := source_original_NUMERIC_SEEN_spectral_lift434
    (sourceOriginalMemoryBirthPool434 BP bm)
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) hw
    birth hb gate row R hR hOp f
  unfold sourceOriginalNumericSeenEnergy434 at hh
  simp_rw [he] at hh
  exact hh

end Green64Analytic.CorrelationSquare

end

end

