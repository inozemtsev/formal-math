module

public import Green64.Library.Weights.BigMarkedPacketHilbert

@[expose] public section

/-!
# Weights / B26MarkedCleanActiveHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26MarkedCleanActiveHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)

local notation "A" => SourceOriginalB26Active434 BP J ell
local notation "r" => sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu
abbrev MarkedFree := (g : G) → Fin (r g) → BP g
abbrev MarkedShared := (g : G) → sourceBigShared J ell m
  (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g → BP g
local notation "X" => MarkedFree BP J ell m hmJ nu
local notation "H" => MarkedShared BP J ell m hmJ nu
local notation "e" => sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ nu
local notation "birthA" => sourceOriginalBigRefreshPacket434 BP (fun _ => J+ell)
local notation "birthX" => sourceOriginalBigRefreshPacket434 BP r

def sourceOriginalB26FreeBirthSet434 (a : A) : Finset (Sigma BP) :=
  birthX (e a).2

/-- The literal original BIG CLEAN fresh law with its cumulative history.
The source gate is actual active-in-seen reachability. K may include all
additional bans, OLD factors, phases and the complete joint Knu. -/
def sourceOriginalB26MarkedCleanActive434
    (mu : (g : G) → BP g → ℝ)
    (K : A → Finset (Sigma BP) → A → ℂ)
    (f : A → Finset (Sigma BP) → ℂ) (s : A) (S : Finset (Sigma BP)) : ℂ :=
  if birthA s ⊆ S then
    ∑ t : A,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
      (if Disjoint S (sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu t) then
        K s S t*f t (S ∪ sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu t)
       else 0)
  else 0

def sourceOriginalB26MarkedActiveEnergy434
    (mu : (g : G) → BP g → ℝ) (f : A → Finset (Sigma BP) → ℂ) : ℝ :=
  sourceOriginalMarkedPacketEnergy434
    (sourceOriginalBigRefreshMass434 BP (fun _ => J+ell) mu) f

private theorem free_birth_subset (a : A) :
    sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu a ⊆ birthA a := by
  intro p hp
  obtain ⟨g,p⟩ := p
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (Finset.mem_sigma.mp hp).2
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_univ _,Finset.mem_image.mpr ?_⟩
  exact ⟨(sourceOriginalProbeMemoryFreeEquiv434 J ell m hmJ nu g j).val,
    Finset.mem_univ _,he⟩

private theorem free_birth_on_split (h : H) (x : X) :
    sourceOriginalB26FreeBirthSet434 BP J ell m hmJ nu ((e).symm (h,x)) = birthX x := by
  unfold sourceOriginalB26FreeBirthSet434
  rw [Equiv.apply_symm_apply]

private theorem clean_target_split
    (mu : (g : G) → BP g → ℝ) (h : H) (x : X) (F : A → ℂ) :
    (∑ t : A,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) ((e).symm (h,x)) t
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) * F t) =
    ∑ y : X,(sourceOriginalBigRefreshMass434 BP r mu y:ℂ)*F ((e).symm (h,y)) := by
  classical
  calc
    _ = ∑ hv : H × X,sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ nu)
        ((e).symm (h,x)) ((e).symm hv)
        (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) * F ((e).symm hv) := by
      apply Fintype.sum_equiv e
      intro t
      simp only [Equiv.symm_apply_apply]
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      simp_rw [source_original_B26_fresh_law_on_split434]
      simp [sourceOriginalBigRefreshMass434]

/-- Exact operator disintegration of the actual marked CLEAN BIG row.
The same joint future and the same post-birth seen set remain inside it. -/
theorem source_original_B26_MARKED_CLEAN_packet_exact434
    (mu : (g : G) → BP g → ℝ)
    (K : A → Finset (Sigma BP) → A → ℂ)
    (f : A → Finset (Sigma BP) → ℂ) (h : H) (x : X)
    (S : Finset (Sigma BP)) :
    sourceOriginalB26MarkedCleanActive434 BP J ell m hmJ nu mu K f ((e).symm (h,x)) S =
    sourceOriginalMarkedPacket434 (sourceOriginalBigRefreshMass434 BP r mu) birthX
      (fun u seen v => if birthA ((e).symm (h,u)) ⊆ seen then
        K ((e).symm (h,u)) seen ((e).symm (h,v)) else 0)
      (fun v seen => f ((e).symm (h,v)) seen) x S := by
  classical
  by_cases hs : birthA ((e).symm (h,x)) ⊆ S
  · have hx : birthX x ⊆ S := by
      rw [←free_birth_on_split BP J ell m hmJ nu h x]
      exact (free_birth_subset BP J ell m hmJ nu _).trans hs
    simp only [sourceOriginalB26MarkedCleanActive434,sourceOriginalMarkedPacket434,
      if_pos hs,if_pos hx]
    rw [clean_target_split]
    simp_rw [free_birth_on_split]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs <;> simp
  · simp [sourceOriginalB26MarkedCleanActive434,sourceOriginalMarkedPacket434,hs]

private theorem marked_energy_split
    (mu : (g : G) → BP g → ℝ) (f : A → Finset (Sigma BP) → ℂ) :
    sourceOriginalB26MarkedActiveEnergy434 BP J ell mu f =
    ∑ h : H,sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ nu mu h *
      sourceOriginalMarkedPacketEnergy434 (sourceOriginalBigRefreshMass434 BP r mu)
        (fun x S => f ((e).symm (h,x)) S) := by
  classical
  unfold sourceOriginalB26MarkedActiveEnergy434 sourceOriginalMarkedPacketEnergy434
  change (∑ S : Finset (Sigma BP),∑ a : A,
    (∏ g,∏ i : Fin (J+ell),mu g (a g i))*‖f a S‖^2) = _
  simp_rw [source_original_B26_active_split_weighted_sum434 BP J ell m hmJ nu mu]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [sourceOriginalBigRefreshMass434]
  ring

/-- Quantitative CLEAN BIG estimate for the original shared-copy law,
arbitrary current seen, all source/target active labels and any joint
complex continuation. The exact tilted group masses remain in the gain.
The coefficient bound is explicit; the actual Knu cap can be inserted
using the bounded version below. -/
theorem source_original_B26_MARKED_CLEAN_active_Hilbert434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (K : A → Finset (Sigma BP) → A → ℂ) (hK : ∀ s S t,‖K s S t‖ ≤ 1)
    (f : A → Finset (Sigma BP) → ℂ) :
    sourceOriginalB26MarkedActiveEnergy434 BP J ell mu
      (sourceOriginalB26MarkedCleanActive434 BP J ell m hmJ nu mu K f) ≤
    (∏ g : G,((∑ p : BP g,mu g p)^2/4)^(r g)) *
      sourceOriginalB26MarkedActiveEnergy434 BP J ell mu f := by
  classical
  let δ := ∏ g : G,((∑ p : BP g,mu g p)^2/4)^(r g)
  rw [marked_energy_split BP J ell m hmJ nu]
  simp_rw [source_original_B26_MARKED_CLEAN_packet_exact434]
  calc
    _ ≤ ∑ h : H,sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ nu mu h *
        (δ*sourceOriginalMarkedPacketEnergy434 (sourceOriginalBigRefreshMass434 BP r mu)
          (fun x S => f ((e).symm (h,x)) S)) := by
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left
      · apply source_original_BIG_MARKED_PACKET_Hilbert434 BP r mu hmu
        intro x S y
        split_ifs
        · exact hK _ _ _
        · simp
      · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g _))
    _ = δ*sourceOriginalB26MarkedActiveEnergy434 BP J ell mu f := by
      rw [marked_energy_split BP J ell m hmJ nu,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring

private theorem marked_energy_scalar
    (mu : (g : G) → BP g → ℝ) (c : ℂ) (f : A → Finset (Sigma BP) → ℂ) :
    sourceOriginalB26MarkedActiveEnergy434 BP J ell mu (fun x S => c*f x S) =
    ‖c‖^2 * sourceOriginalB26MarkedActiveEnergy434 BP J ell mu f := by
  unfold sourceOriginalB26MarkedActiveEnergy434 sourceOriginalMarkedPacketEnergy434
  simp only [norm_mul,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The true coefficient is allowed to exceed one. The full cost C^2 is
paid in the SAME original measure; no bounded-mask replacement occurs. -/
theorem source_original_B26_MARKED_CLEAN_bounded_Hilbert434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (C : ℝ) (hC : 0 ≤ C)
    (K : A → Finset (Sigma BP) → A → ℂ) (hK : ∀ s S t,‖K s S t‖ ≤ C)
    (f : A → Finset (Sigma BP) → ℂ) :
    sourceOriginalB26MarkedActiveEnergy434 BP J ell mu
      (sourceOriginalB26MarkedCleanActive434 BP J ell m hmJ nu mu K f) ≤
    C^2*(∏ g : G,((∑ p : BP g,mu g p)^2/4)^(r g)) *
      sourceOriginalB26MarkedActiveEnergy434 BP J ell mu f := by
  classical
  by_cases hz : C=0
  · have hzero (s : A) (S : Finset (Sigma BP)) (t : A) : K s S t=0 :=
      norm_eq_zero.mp (le_antisymm (by simpa only [hz] using hK s S t) (norm_nonneg _))
    simp [sourceOriginalB26MarkedCleanActive434,sourceOriginalB26MarkedActiveEnergy434,
      sourceOriginalMarkedPacketEnergy434,hzero,hz]
  · have hp : 0<C := lt_of_le_of_ne hC (Ne.symm hz)
    have hc : (C:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    let K' : A → Finset (Sigma BP) → A → ℂ := fun s S t => K s S t/(C:ℂ)
    have hk' (s : A) (S : Finset (Sigma BP)) (t : A) : ‖K' s S t‖ ≤ 1 := by
      dsimp only [K']
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
      exact (div_le_one hp).mpr (hK s S t)
    have hrow :
        sourceOriginalB26MarkedCleanActive434 BP J ell m hmJ nu mu K f =
        fun s S => (C:ℂ)*sourceOriginalB26MarkedCleanActive434 BP J ell m hmJ nu mu K' f s S := by
      funext s S
      unfold sourceOriginalB26MarkedCleanActive434
      split_ifs
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        dsimp only [K']
        split_ifs
        · field_simp [hc] <;> ring
        · simp
      · simp
    rw [hrow,marked_energy_scalar,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
    have hh := source_original_B26_MARKED_CLEAN_active_Hilbert434
      BP J ell m hmJ nu mu hmu K' hk' f
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg C)).trans_eq (by ring)

end Green64Analytic.CorrelationSquare

end

end

