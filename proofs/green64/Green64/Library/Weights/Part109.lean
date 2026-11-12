module

public import Green64.Library.Analysis.Estimates.Part015
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Green64.Library.Weights.MarkedProduct
public import Green64.Library.Weights.Part033
public import Green64.Library.Weights.Part048
public import Green64.Library.Weights.Part073
public import Green64.Library.Weights.Part099
public import Green64.Library.Weights.Part100
public import Green64.Library.Weights.Part050

@[expose] public section

/-!
# Weights / Part109

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RemovedMarkedFourthMoment -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Fixing a complete marked product D before summing positions gives
exactly the quotient prefix. This is the source of the reciprocal D
which cancels the original ordered-mark mass. -/
theorem b657_removed_marked_prefix434 (D Y : ℕ) (hD : 0 < D) :
    (∑ n ∈ Finset.Ioc 0 Y, if D∣n then ((n/D).divisors.card:ℝ)^4 else 0) =
      ∑ m ∈ Finset.Ioc 0 (Y/D), (m.divisors.card:ℝ)^4 := by
  classical
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun n _ => n/D)
  · intro n hn
    obtain ⟨hn,hdiv⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0,hnY⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn0 hdiv) hD,
      Nat.div_le_div_right hnY⟩
  · intro n hn m hm he
    have hnD := (Finset.mem_filter.mp hn).2
    have hmD := (Finset.mem_filter.mp hm).2
    calc
      n=(n/D)*D := (Nat.div_mul_cancel hnD).symm
      _=(m/D)*D := by rw [he]
      _=m := Nat.div_mul_cancel hmD
  · intro m hm
    obtain ⟨hm0,hmY⟩ := Finset.mem_Ioc.mp hm
    have hd : D∣m*D := ⟨m,by ring⟩
    refine ⟨m*D,Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨Nat.mul_pos hm0 hD,(Nat.le_div_iff_mul_le hD).mp hmY⟩,hd⟩,?_⟩
    exact mul_right_cancel₀ (ne_of_gt hD) (Nat.div_mul_cancel hd)
  · intro n hn
    rfl

/-- True fourth divisor moment AFTER removal of a fixed marked product.
The coefficient is Y/D, and the logarithmic exponent is the fixed 15,
independent of D, J, all mark counts and every source prime group. -/
theorem b657_removed_marked_fourth_moment434 (D Y : ℕ) (hD : 0 < D) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Ioc 0 Y, if D∣n then ((n/D).divisors.card:ℝ)^4 else 0) ≤
      ((Y:ℝ)/(D:ℝ))*(1+Real.log (Y:ℝ))^15 := by
  rw [b657_removed_marked_prefix434 D Y hD]
  have hYreal : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hYreal
  have hbaseY : 0 ≤ 1+Real.log (Y:ℝ) := by linarith
  by_cases hz : Y/D=0
  · simp only [hz,Finset.Ioc_self,Finset.sum_empty]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg hbaseY _)
  · have hq : 1 ≤ Y/D := Nat.one_le_iff_ne_zero.mpr hz
    have hqr : (1:ℝ) ≤ (Y/D:ℕ) := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log ((Y/D:ℕ):ℝ) := Real.log_nonneg hqr
    have hbaseq : 0 ≤ 1+Real.log ((Y/D:ℕ):ℝ) := by linarith
    have hlogle : Real.log ((Y/D:ℕ):ℝ) ≤ Real.log (Y:ℝ) :=
      Real.log_le_log (zero_lt_one.trans_le hqr) (by exact_mod_cast Nat.div_le_self Y D)
    exact (b656_tau_four_counting434 (Y/D)).trans
      (mul_le_mul Nat.cast_div_le
        (pow_le_pow_left₀ hbaseq (by linarith : 1+Real.log ((Y/D:ℕ):ℝ) ≤ 1+Real.log (Y:ℝ)) 15)
        (pow_nonneg hbaseq 15) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## FiniteMarkedNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 14000

/-- Exact finite physical L2 accounting: first fix the complete marked
product, then sum its quotient divisor moment, and only then sum ordered
marks. The final bound has fixed exponent 15 and no mark-count factor.
The injection will be supplied by the original native physical state,
and its mass inequality by the original harmonic V normalization. -/
theorem b657_finite_marked_norm_sq434
    {α S : Type*} [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
    (pos : α → ℤ) (marks : α → S)
    (hinj : Function.Injective (fun x => (pos x,marks x)))
    (D : S → ℕ) (hD : ∀ s, 0 < D s) (mu A : ℝ) (hmu : 0 ≤ mu)
    (hmass : mu*(∑ s : S,1/(D s:ℝ)) ≤ 1)
    (Y : ℕ) (hY : 1 ≤ Y) (F : EuclideanSpace ℂ α)
    (hSupport : ∀ x, F x≠0 → 0 < pos x ∧ pos x ≤ (Y:ℤ))
    (hdiv : ∀ x, F x≠0 → D (marks x) ∣ (pos x).toNat)
    (hF : ∀ x, F x≠0 → ‖F x‖ ≤ Real.sqrt mu*A*
      (((pos x).toNat/D (marks x)).divisors.card:ℝ)^2) :
    ‖F‖^2 ≤ A^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15 := by
  classical
  let active := (Finset.univ : Finset α).filter (fun x => F x≠0)
  let key : α → S × ℕ := fun x => (marks x,(pos x).toNat)
  let W : S × ℕ → ℝ := fun t => if D t.1∣t.2 then ((t.2/D t.1).divisors.card:ℝ)^4 else 0
  let B : ℝ := (1+Real.log (Y:ℝ))^15
  have hYreal : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hYreal
  have hB : 0 ≤ B := pow_nonneg (by linarith) _
  have hW (t : S × ℕ) : 0 ≤ W t := by dsimp [W]; split_ifs <;> positivity
  have hactive (x : α) (hx : x ∈ active) : F x≠0 := (Finset.mem_filter.mp hx).2
  have hkey : Set.InjOn key (active : Set α) := by
    intro x hx y hy he
    have hxpos := hSupport x (hactive x hx)
    have hypos := hSupport y (hactive y hy)
    apply hinj
    apply Prod.ext
    · have hn := congrArg Prod.snd he
      change (pos x).toNat=(pos y).toNat at hn
      calc
        pos x=((pos x).toNat:ℤ) := (Int.toNat_of_nonneg hxpos.1.le).symm
        _=((pos y).toNat:ℤ) := by rw [hn]
        _=pos y := Int.toNat_of_nonneg hypos.1.le
    · exact congrArg Prod.fst he
  have hsub : active.image key ⊆ (Finset.univ : Finset S) ×ˢ Finset.Ioc 0 Y := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
    have hp := hSupport x (hactive x hx)
    have hc := Int.toNat_of_nonneg hp.1.le
    have hp0 : (0:ℤ) < ((pos x).toNat:ℤ) := by rw [hc]; exact hp.1
    have hpY : ((pos x).toNat:ℤ) ≤ (Y:ℤ) := by rw [hc]; exact hp.2
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_Ioc.mpr
      ⟨by exact_mod_cast hp0,by exact_mod_cast hpY⟩⟩
  have hpoint (x : α) (hx : x ∈ active) : ‖F x‖^2 ≤ mu*A^2*W (key x) := by
    have hn := hactive x hx
    change _ ≤ mu*A^2*(if D (marks x)∣(pos x).toNat then _ else 0)
    rw [ite_eq_left (hdiv x hn)]
    calc
      _ ≤ (Real.sqrt mu*A*(((pos x).toNat/D (marks x)).divisors.card:ℝ)^2)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hF x hn) 2
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hmu]; ring
  have he : (∑ x : α, ‖F x‖^2) = ∑ x ∈ active, ‖F x‖^2 := by
    dsimp [active]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hz : F x=0 <;> simp [hz]
  have hsum : (∑ s : S, ((Y:ℝ)/(D s:ℝ))*B) =
      (Y:ℝ)*B*(∑ s : S,1/(D s:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [EuclideanSpace.norm_sq_eq,he]
  calc
    _ ≤ ∑ x ∈ active, mu*A^2*W (key x) := Finset.sum_le_sum (fun x hx => hpoint x hx)
    _ = mu*A^2*(∑ x ∈ active, W (key x)) := (Finset.mul_sum _ _ _).symm
    _ = mu*A^2*(∑ t ∈ active.image key, W t) := by rw [Finset.sum_image hkey]
    _ ≤ mu*A^2*(∑ t ∈ (Finset.univ : Finset S) ×ˢ Finset.Ioc 0 Y, W t) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hW t))
        (mul_nonneg hmu (sq_nonneg A))
    _ = mu*A^2*(∑ s : S, ∑ n ∈ Finset.Ioc 0 Y,
        if D s∣n then ((n/D s).divisors.card:ℝ)^4 else 0) := by rw [Finset.sum_product]
    _ ≤ mu*A^2*(∑ s : S, ((Y:ℝ)/(D s:ℝ))*B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ =>
        b657_removed_marked_fourth_moment434 (D s) Y (hD s) hY)) (mul_nonneg hmu (sq_nonneg A))
    _ = (A^2*(Y:ℝ)*B)*(mu*(∑ s : S,1/(D s:ℝ))) := by rw [hsum]; ring
    _ ≤ (A^2*(Y:ℝ)*B)*1 :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (mul_nonneg (sq_nonneg A) (Nat.cast_nonneg _)) hB)
    _ = _ := mul_one _

/-- The fixed eighth logarithmic power is a convenient genuine L2 norm
bound. Its exponent and leading constant are independent of all marks. -/
theorem b657_norm_of_marked_square434
    {α : Type*} [NormedAddCommGroup α] (F : α) (A : ℝ) (hA : 0 ≤ A)
    (Y : ℕ) (hY : 1 ≤ Y)
    (hF : ‖F‖^2 ≤ A^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15) :
    ‖F‖ ≤ A*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := by
  have hYreal : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hlog : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hYreal
  have hbase : 1 ≤ 1+Real.log (Y:ℝ) := by linarith
  have hU : 0 ≤ A*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := by positivity
  have hs : ‖F‖^2 ≤ (A*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8)^2 := by
    calc
      _ ≤ A^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15 := hF
      _ ≤ A^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^16 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by norm_num : 15≤16))
          (mul_nonneg (sq_nonneg A) (Nat.cast_nonneg _))
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg Y)]; ring
  nlinarith [norm_nonneg F]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualPhysicalNorm -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The unchanged original common physical state mass. This abbreviation
only exposes the same quantity used by B650, B654 and the B655 first vector. -/
def b657ActualStateMass434 (L : ℝ)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ) : ℝ :=
  b650IntegerStateMass434
    (SG:=SourceNativeMemorySG434 20 L hS) (BG:=sourceNativeOriginalBigType434 20 L)
    J 1 (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)

/-- The two literal actual prime reciprocal sums normalize all ordered
mark lists together. The bound is exactly one and is uniform in J. -/
theorem b657_actual_ordered_mass434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (hVs : ∀ g, 0 < SourceNativeMemorySmallMass434 20 L hS g)
    (hVb : ∀ g, 0 < sourceNativeOriginalVbig434 20 L g) :
    b657ActualStateMass434 L hS J *
      (∑ s : B657OrderedMarks434
        (SourceNativeMemorySP434 20 L hS) (SourceNativeMemoryBP434 20 L) (J+1),
        1/(b657OrderedMarkProduct434
          (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
          (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) (J+1) s:ℝ)) ≤ 1 := by
  have hHs (g) : SourceNativeMemorySmallMass434 20 L hS g =
      ∑ p : SourceNativeMemorySP434 20 L hS g, 1/(p.val:ℝ) := by
    cases g with
    | none =>
      simpa [SourceNativeMemorySmallMass434,sourceNativeOriginalVs434,
        SourceNativeMemorySP434,one_div] using
        (Finset.sum_attach (sourceNativeOriginalS434 20 L hS) (fun p => (p:ℝ)⁻¹)).symm
    | some i =>
      simpa [SourceNativeMemorySmallMass434,sourceNativeOriginalVsmall434,
        SourceNativeMemorySP434,one_div] using
        (Finset.sum_attach (sourceNativeOriginalTs434 20 L hS i) (fun p => (p:ℝ)⁻¹)).symm
  have hHb (g) : sourceNativeOriginalVbig434 20 L g =
      ∑ p : SourceNativeMemoryBP434 20 L g, 1/(p.val:ℝ) := by
    simpa [sourceNativeOriginalVbig434,SourceNativeMemoryBP434,one_div] using
      (Finset.sum_attach (sourceNativeOriginalTb434 20 L g) (fun p => (p:ℝ)⁻¹)).symm
  exact b657_full_ordered_harmonic_mass434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
    (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
    hVs hVb hHs hHb

/-- Genuine L2 transfer on the complete actual physical state carrier.
The only coefficient hypothesis is the removed-mark pointwise bound.
Numerical distinctness, full product divisibility, the physical-state
reindexing and BOTH harmonic mass normalizations are proved internally.
The second vector may depend arbitrarily on all marks. -/
theorem b657_actual_physical_norm434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (hVs : ∀ g, 0 < SourceNativeMemorySmallMass434 20 L hS g)
    (hVb : ∀ g, 0 < sourceNativeOriginalVbig434 20 L g)
    (positions : Finset ℤ) (A : ℝ) (hA : 0 ≤ A) (Y : ℕ) (hY : 1 ≤ Y)
    (F : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions))
    (hSupport : ∀ x, F x≠0 → 0 < x.val.1.val ∧ x.val.1.val ≤ (Y:ℤ))
    (hF : ∀ x, F x≠0 → ‖F x‖ ≤ Real.sqrt (b657ActualStateMass434 L hS J)*A*
      ((x.val.1.val.toNat/b657ActualMarkProduct434 L hS J positions x).divisors.card:ℝ)^2) :
    ‖F‖^2 ≤ A^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15 ∧
      ‖F‖ ≤ A*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pos : B654ActualParityState434 L hS J positions → ℤ := fun x => x.val.1.val
  let marks := b657PhysicalMarkReadout434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 positions
  let D := b657OrderedMarkProduct434 SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1)
  have hmu : 0 ≤ b657ActualStateMass434 L hS J :=
    (b650_integer_state_mass_positive434
      (SG:=SourceNativeMemorySG434 20 L hS) (BG:=sourceNativeOriginalBigType434 20 L)
      J 1 (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L) hVs hVb).le
  have hdiv (x) (hx : F x≠0) : D (marks x) ∣ (pos x).toNat :=
    b657_actual_mark_product_divides434 L hL hS J positions x (hSupport x hx).1.le
  have hb := b657_finite_marked_norm_sq434 pos marks
    (b657_physical_position_marks_injective434 SP (fun _ p => p.val) BP (fun _ p => p.val) J 1 positions)
    D (fun s => b657_ordered_mark_product_pos434 SP (fun _ p => p.val) BP (fun _ p => p.val) (J+1) s)
    (b657ActualStateMass434 L hS J) A hmu
    (b657_actual_ordered_mass434 L hS J hVs hVb) Y hY F hSupport hdiv hF
  exact ⟨hb,b657_norm_of_marked_square434 F A hA Y hY hb⟩

/-- The real moving actual prime family supplies the mass positivity;
its threshold is independent of J, the vector and the support length.
No harmonic mass or product-divisibility hypothesis remains. -/
theorem b657_eventually_actual_physical_norm434 :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
        (positions : Finset ℤ) (A : ℝ), 0 ≤ A → ∀ (Y : ℕ), 1 ≤ Y →
      ∀ (F : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions)),
        (∀ x, F x≠0 → 0 < x.val.1.val ∧ x.val.1.val ≤ (Y:ℤ)) →
        (∀ x, F x≠0 → ‖F x‖ ≤ Real.sqrt (b657ActualStateMass434 L hS J)*A*
          ((x.val.1.val.toNat/b657ActualMarkProduct434 L hS J positions x).divisors.card:ℝ)^2) →
        ‖F‖^2 ≤ A^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15 ∧
        ‖F‖ ≤ A*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := by
  filter_upwards [b654_eventually_actual_parity_masses_positive434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS J positions A hA Y hY F hSupport hF
  exact b657_actual_physical_norm434 L h.1 hS J (h.2.2 hS).1 (h.2.2 hS).2
    positions A hA Y hY F hSupport hF
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualPrimeEndpointNorm -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The genuine arithmetic endpoint in the original physical state norm:
ONE sqrt(mu0), the original n^(it) prime-slot core, the literal extra
endpoint damping, and an arbitrary unit-bounded physical multiplier.
The multiplier may depend on all marks, as the second endpoint may. -/
def b657ActualPrimeEndpointVector434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (F : PrimeSlotCore) (t : ℝ)
    (eta : B654ActualParityState434 L hS J positions → ℂ) :
    EuclideanSpace ℂ (B654ActualParityState434 L hS J positions) :=
  WithLp.toLp 2 (fun x => (Real.sqrt (b657ActualStateMass434 L hS J):ℂ)*eta x*
    b656IntegerPrimeEndpointCoefficient434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
      (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t x.val.1.val)

/-- True arithmetic L2 bound for the original physical endpoint. The
pointwise divisor bound, D|n, P-support, distinctness and harmonic mass
are all proved internally. The exponent is uniform in J and in every
source group and mark. No vector norm or pointwise tau premise remains. -/
theorem b657_actual_prime_endpoint_norm434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (hVs : ∀ g, 0 < SourceNativeMemorySmallMass434 20 L hS g)
    (hVb : ∀ g, 0 < sourceNativeOriginalVbig434 20 L g)
    (positions : Finset ℤ) (F : PrimeSlotCore) (t A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ha : ∀ m, ‖F.alpha m‖ ≤ A) (hc : ∀ r, ‖F.residual r‖ ≤ C)
    (Y : ℕ) (hY : 1 ≤ Y) (eta : B654ActualParityState434 L hS J positions → ℂ)
    (hEta : ∀ x, ‖eta x‖ ≤ 1)
    (hUpper : ∀ x, (Y:ℤ) < x.val.1.val → eta x=0) :
    ‖b657ActualPrimeEndpointVector434 L hS J positions F t eta‖^2 ≤
      (A*C)^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15 ∧
    ‖b657ActualPrimeEndpointVector434 L hS J positions F t eta‖ ≤
      (A*C)*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := by
  let v := b657ActualPrimeEndpointVector434 L hS J positions F t eta
  have hSupport (x) (hx : v x≠0) : 0 < x.val.1.val ∧ x.val.1.val ≤ (Y:ℤ) := by
    constructor
    · by_contra hn
      apply hx
      simp [v,b657ActualPrimeEndpointVector434,b656IntegerPrimeEndpointCoefficient434,hn]
    · by_contra hn
      have he := hUpper x (lt_of_not_ge hn)
      apply hx
      simp [v,b657ActualPrimeEndpointVector434,he]
  have hpoint (x) (hx : v x≠0) : ‖v x‖ ≤
      Real.sqrt (b657ActualStateMass434 L hS J)*(A*C)*
        ((x.val.1.val.toNat/b657ActualMarkProduct434 L hS J positions x).divisors.card:ℝ)^2 := by
    have hpos := (hSupport x hx).1
    have hd := b657_actual_mark_product_support434 L hL hS J positions x
    have hdiv := b657_actual_mark_product_divides434 L hL hS J positions x hpos.le
    have hb := b656_integer_prime_endpoint_removed_marks434
      (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
      (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t A C
      (by norm_num) (by norm_num) hA hC ha hc x.val.1.val hpos
      (b657ActualMarkProduct434 L hS J positions x) hd.1 hdiv hd.2
    change ‖(Real.sqrt (b657ActualStateMass434 L hS J):ℂ)*eta x*
      b656IntegerPrimeEndpointCoefficient434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
        (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t x.val.1.val‖ ≤ _
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ (Real.sqrt (b657ActualStateMass434 L hS J)*1)*
          (A*C*((x.val.1.val.toNat/b657ActualMarkProduct434 L hS J positions x).divisors.card:ℝ)^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hEta x) (Real.sqrt_nonneg _)) hb
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact b657_actual_physical_norm434 L hL hS J hVs hVb positions (A*C) (mul_nonneg hA hC)
    Y hY v hSupport hpoint

/-- Unconditional actual-family arithmetic endpoint norm, with the
native mass positivity supplied by the original reciprocal-prime theorem.
The threshold is independent of J, the core, its phases, and Y. -/
theorem b657_eventually_actual_prime_endpoint_norm434 :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
        (positions : Finset ℤ) (F : PrimeSlotCore) (t A C : ℝ),
      0 ≤ A → 0 ≤ C → (∀ m, ‖F.alpha m‖ ≤ A) → (∀ r, ‖F.residual r‖ ≤ C) →
      ∀ (Y : ℕ), 1 ≤ Y → ∀ (eta : B654ActualParityState434 L hS J positions → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) → (∀ x, (Y:ℤ) < x.val.1.val → eta x=0) →
        ‖b657ActualPrimeEndpointVector434 L hS J positions F t eta‖^2 ≤
          (A*C)^2*(Y:ℝ)*(1+Real.log (Y:ℝ))^15 ∧
        ‖b657ActualPrimeEndpointVector434 L hS J positions F t eta‖ ≤
          (A*C)*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := by
  filter_upwards [b654_eventually_actual_parity_masses_positive434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS J positions F t A C hA hC ha hc Y hY eta hEta hUpper
  exact b657_actual_prime_endpoint_norm434 L h.1 hS J (h.2.2 hS).1 (h.2.2 hS).2
    positions F t A C hA hC ha hc Y hY eta hEta hUpper
end Green64Analytic.SourceBlockSieve

end

end

/-! ## DyadicNormBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The fixed prefix enlargement Y≤3X and the true logarithmic fourth
moment cost at most one extra L power beyond L^8. This threshold is
absolute: it is independent of J, every prime band, and all marks. -/
theorem b657_eventually_dyadic_log_norm434 :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (X Y : ℕ), 1 ≤ X → 1 ≤ Y → Y ≤ 3*X → Real.log (X:ℝ) ≤ L →
        Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 ≤ Real.sqrt (X:ℝ)*L^9 := by
  let c : ℝ := 2+Real.log 3
  let K : ℝ := Real.sqrt 3*c^8
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop K] with L hL hK
  refine ⟨hL,?_⟩
  intro X Y hX hY hXY hLogX
  have hXp : (0:ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hX)
  have hYp : (0:ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hY)
  have hYr : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hXYr : (Y:ℝ) ≤ 3*(X:ℝ) := by exact_mod_cast hXY
  have hs : Real.sqrt (Y:ℝ) ≤ Real.sqrt 3*Real.sqrt (X:ℝ) := by
    calc
      _ ≤ Real.sqrt (3*(X:ℝ)) := Real.sqrt_le_sqrt hXYr
      _ = _ := Real.sqrt_mul (by norm_num) _
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hYr
  have hlog : Real.log (Y:ℝ) ≤ Real.log 3+L := by
    calc
      _ ≤ Real.log (3*(X:ℝ)) := Real.log_le_log hYp hXYr
      _ = Real.log 3+Real.log (X:ℝ) := Real.log_mul (by norm_num) (ne_of_gt hXp)
      _ ≤ _ := by linarith
  have hbase : 0 ≤ 1+Real.log (Y:ℝ) := by linarith
  have hc : 1+Real.log (Y:ℝ) ≤ c*L := by
    have h := mul_nonneg (show 0 ≤ 1+Real.log 3 by linarith) (show 0 ≤ L-1 by linarith)
    dsimp [c]
    nlinarith
  calc
    _ ≤ (Real.sqrt 3*Real.sqrt (X:ℝ))*(c*L)^8 :=
      mul_le_mul hs (pow_le_pow_left₀ hbase hc 8) (pow_nonneg hbase 8)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = Real.sqrt (X:ℝ)*K*L^8 := by dsimp [K]; rw [mul_pow]; ring
    _ ≤ Real.sqrt (X:ℝ)*L*L^8 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _))
        (pow_nonneg (zero_le_one.trans hL) 8)
    _ = _ := by ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualPolynomialNorm -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The actual S04 arithmetic endpoint has norm at most
sqrt(X)*L^(2*C+9), with this exponent fixed BEFORE J is chosen. The proof
keeps all original marks and the same sqrt(mu0), phase, prime-slot core,
extra endpoint damping and arbitrary unit multipliers. Y≤3X accounts
for the genuine enlarged dyadic carrier. In particular C=0 gives the
fixed exponent 9 for the proved canonical unit alpha/residual inputs. -/
theorem b657_eventually_actual_prime_endpoint_polynomial_norm434 (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
        (positions : Finset ℤ) (F : PrimeSlotCore) (t : ℝ),
      (∀ m, ‖F.alpha m‖ ≤ L^C) → (∀ r, ‖F.residual r‖ ≤ L^C) →
      ∀ (X Y : ℕ), 1 ≤ X → 1 ≤ Y → Y ≤ 3*X → Real.log (X:ℝ) ≤ L →
      ∀ (eta : B654ActualParityState434 L hS J positions → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) → (∀ x, (Y:ℤ) < x.val.1.val → eta x=0) →
        ‖b657ActualPrimeEndpointVector434 L hS J positions F t eta‖ ≤
          Real.sqrt (X:ℝ)*L^(2*C+9) := by
  filter_upwards [b657_eventually_actual_prime_endpoint_norm434,
    b657_eventually_dyadic_log_norm434] with L hActual hBudget
  refine ⟨hActual.1,hActual.2.1,?_⟩
  intro hS J positions F t ha hc X Y hX hY hXY hLogX eta hEta hUpper
  have hLp : 0 < L := zero_lt_one.trans hActual.1
  have hpow : 0 ≤ L^C := Real.rpow_nonneg hLp.le _
  have hn := (hActual.2.2 hS J positions F t (L^C) (L^C) hpow hpow ha hc
    Y hY eta hEta hUpper).2
  have hfac : L^C*L^C=L^(2*C) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (L^C*L^C)*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := hn
    _ = L^(2*C)*(Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8) := by rw [hfac]; ring
    _ ≤ L^(2*C)*(Real.sqrt (X:ℝ)*L^9) :=
      mul_le_mul_of_nonneg_left (hBudget.2 X Y hX hY hXY hLogX) (Real.rpow_nonneg hLp.le _)
    _ = Real.sqrt (X:ℝ)*(L^(2*C)*L^9) := by ring
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_add hLp]
      norm_num only [Nat.cast_ofNat]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualFullDyadicNorm -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 11000000

/- The original ambient L is log x; the physical dyad X can exceed x by
   the genuine subexponential D factor. This module uses log X ≤ 2L,
   without redefining L, the prime bands, or the already selected tuple.
   The earlier log X ≤ L theorem remains unchanged as an exact helper. -/

/-- The fixed prefix enlargement Y≤3X and the true logarithmic fourth
moment cost at most one extra L power beyond L^8. This threshold is
absolute: it is independent of J, every prime band, and all marks. -/
theorem b657_eventually_dyadic_twice_log_norm434 :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (X Y : ℕ), 1 ≤ X → 1 ≤ Y → Y ≤ 3*X → Real.log (X:ℝ) ≤ 2*L →
        Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 ≤ Real.sqrt (X:ℝ)*L^9 := by
  let c : ℝ := 3+Real.log 3
  let K : ℝ := Real.sqrt 3*c^8
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop K] with L hL hK
  refine ⟨hL,?_⟩
  intro X Y hX hY hXY hLogX
  have hXp : (0:ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hX)
  have hYp : (0:ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hY)
  have hYr : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hXYr : (Y:ℝ) ≤ 3*(X:ℝ) := by exact_mod_cast hXY
  have hs : Real.sqrt (Y:ℝ) ≤ Real.sqrt 3*Real.sqrt (X:ℝ) := by
    calc
      _ ≤ Real.sqrt (3*(X:ℝ)) := Real.sqrt_le_sqrt hXYr
      _ = _ := Real.sqrt_mul (by norm_num) _
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogY : 0 ≤ Real.log (Y:ℝ) := Real.log_nonneg hYr
  have hlog : Real.log (Y:ℝ) ≤ Real.log 3+2*L := by
    calc
      _ ≤ Real.log (3*(X:ℝ)) := Real.log_le_log hYp hXYr
      _ = Real.log 3+Real.log (X:ℝ) := Real.log_mul (by norm_num) (ne_of_gt hXp)
      _ ≤ _ := by linarith
  have hbase : 0 ≤ 1+Real.log (Y:ℝ) := by linarith
  have hc : 1+Real.log (Y:ℝ) ≤ c*L := by
    have h := mul_nonneg (show 0 ≤ 1+Real.log 3 by linarith) (show 0 ≤ L-1 by linarith)
    dsimp [c]
    nlinarith
  calc
    _ ≤ (Real.sqrt 3*Real.sqrt (X:ℝ))*(c*L)^8 :=
      mul_le_mul hs (pow_le_pow_left₀ hbase hc 8) (pow_nonneg hbase 8)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = Real.sqrt (X:ℝ)*K*L^8 := by dsimp [K]; rw [mul_pow]; ring
    _ ≤ Real.sqrt (X:ℝ)*L*L^8 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _))
        (pow_nonneg (zero_le_one.trans hL) 8)
    _ = _ := by ring


/-- The actual S04 arithmetic endpoint has norm at most
sqrt(X)*L^(2*C+9), with this exponent fixed BEFORE J is chosen. The proof
keeps all original marks and the same sqrt(mu0), phase, prime-slot core,
extra endpoint damping and arbitrary unit multipliers. Y≤3X accounts
for the genuine enlarged dyadic carrier. In particular C=0 gives the
fixed exponent 9 for the proved canonical unit alpha/residual inputs. -/
theorem b657_eventually_actual_full_dyadic_norm434 (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
        (positions : Finset ℤ) (F : PrimeSlotCore) (t : ℝ),
      (∀ m, ‖F.alpha m‖ ≤ L^C) → (∀ r, ‖F.residual r‖ ≤ L^C) →
      ∀ (X Y : ℕ), 1 ≤ X → 1 ≤ Y → Y ≤ 3*X → Real.log (X:ℝ) ≤ 2*L →
      ∀ (eta : B654ActualParityState434 L hS J positions → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) → (∀ x, (Y:ℤ) < x.val.1.val → eta x=0) →
        ‖b657ActualPrimeEndpointVector434 L hS J positions F t eta‖ ≤
          Real.sqrt (X:ℝ)*L^(2*C+9) := by
  filter_upwards [b657_eventually_actual_prime_endpoint_norm434,
    b657_eventually_dyadic_twice_log_norm434] with L hActual hBudget
  refine ⟨hActual.1,hActual.2.1,?_⟩
  intro hS J positions F t ha hc X Y hX hY hXY hLogX eta hEta hUpper
  have hLp : 0 < L := zero_lt_one.trans hActual.1
  have hpow : 0 ≤ L^C := Real.rpow_nonneg hLp.le _
  have hn := (hActual.2.2 hS J positions F t (L^C) (L^C) hpow hpow ha hc
    Y hY eta hEta hUpper).2
  have hfac : L^C*L^C=L^(2*C) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ (L^C*L^C)*Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8 := hn
    _ = L^(2*C)*(Real.sqrt (Y:ℝ)*(1+Real.log (Y:ℝ))^8) := by rw [hfac]; ring
    _ ≤ L^(2*C)*(Real.sqrt (X:ℝ)*L^9) :=
      mul_le_mul_of_nonneg_left (hBudget.2 X Y hX hY hXY hLogX) (Real.rpow_nonneg hLp.le _)
    _ = Real.sqrt (X:ℝ)*(L^(2*C)*L^9) := by ring
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_add hLp]
      norm_num only [Nat.cast_ofNat]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FirstVectorIdentification -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Exact identification of the S02 first vector with the arithmetic
physical lift whose norm was proved in B657. It preserves the same ONE
sqrt(mu0), actual native coefficient, and exact original seed support.
No equality of norms or replacement by a surrogate vector is assumed. -/
theorem b657_first_vector_eq_prime_endpoint434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (eta : ℤ → ℂ) :
    b655ActualParityFirstVector434 L hS J positions lo hi
      (fun n => eta n * b656IntegerPrimeEndpointCoefficient434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
        (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t n) =
    b657ActualPrimeEndpointVector434 L hS J positions F t
      (fun x => if x.val.1.val ∈ b654ParitySeedPositions434 lo hi then eta x.val.1.val else 0) := by
  let d : ℤ → ℂ := b656IntegerPrimeEndpointCoefficient434
    (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
    (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t
  let w : ℂ := Real.sqrt (b657ActualStateMass434 L hS J)
  apply (WithLp.linearEquiv 2 ℂ (B654ActualParityState434 L hS J positions → ℂ)).injective
  funext x
  change (if x.val.1.val ∈ b654ParitySeedPositions434 lo hi then
      (eta x.val.1.val*d x.val.1.val)*w else 0) =
    w*(if x.val.1.val ∈ b654ParitySeedPositions434 lo hi then eta x.val.1.val else 0)*d x.val.1.val
  by_cases hx : x.val.1.val ∈ b654ParitySeedPositions434 lo hi
  · simp only [hx,ite_true]
    ring
  · simp only [hx,ite_false,mul_zero,zero_mul]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualCutoffPairing -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.SourceBlockSieve Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- The literal full physical cutoff matrix. The ORIGINAL edge product
D and cutoff stay inside every frame and every endpoint permutation.
There is no averaging or replacement of D by a reference value. -/
def b658IntegerCutoffMatrix434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ)
    (f : 𝓢(ℝ, ℂ)) :
    Matrix (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
      (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) ℂ :=
  b658FrameMatrix434 (fun x y frame =>
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vs Vb Knu zeta 1 k x y frame *
    f (Real.log ((x.val.1.val:ℝ) /
      (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ)))))

/-- Exact genuine Fourier separation of the FULL physical pairing.
All states, all marks, all frames and their signs are retained; only
the first endpoint is assumed constant on the mark fibre. The second
endpoint is arbitrary. Integrability is proved from the actual frame
formula, not supplied as a hypothesis. -/
theorem b658_integer_cutoff_pairing_fourier434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ)
    (hZ : 0 < Z) (w : ℂ) (I : Finset ℤ) (hI : ∀ n ∈ I, 0 < n)
    (c : ℤ → ℂ) (g : EuclideanSpace ℂ
      (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions))
    (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun xi : ℝ => (𝓕 f) xi *
      inner ℂ (b652FirstPositionVector434 (fun x => x.val.1.val) w I
        (fun n => b658FourierPhase434 (-xi) (Real.log ((n:ℝ)/Z)) * c n))
        ((b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
          q Vs Vb Knu (zeta-2*Real.pi*xi) 1 k).toEuclideanLin g)) ∧
    (∫ xi : ℝ, (𝓕 f) xi *
      inner ℂ (b652FirstPositionVector434 (fun x => x.val.1.val) w I
        (fun n => b658FourierPhase434 (-xi) (Real.log ((n:ℝ)/Z)) * c n))
        ((b650IntegerPhysicalMatrix434 SP smallMod BP bigMod J ell m patterns positions
          q Vs Vb Knu (zeta-2*Real.pi*xi) 1 k).toEuclideanLin g)) =
      inner ℂ (b652FirstPositionVector434 (fun x => x.val.1.val) w I c)
        ((b658IntegerCutoffMatrix434 SP smallMod BP bigMod J ell m patterns positions
          q Vs Vb Knu zeta Z k f).toEuclideanLin g) := by
  exact b658_seed_frame_fourier_fubini434 (fun x => x.val.1.val) w I c g
    (fun n => Real.log ((n:ℝ)/Z)) (fun xi => (𝓕 f) xi)
    (fun xi x y frame => b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vs Vb Knu (zeta-2*Real.pi*xi) 1 k x y frame)
    (fun x y frame => b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vs Vb Knu zeta 1 k x y frame *
      f (Real.log ((x.val.1.val:ℝ) /
        (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ)))))
    (fun x hx y frame => b658_integer_frame_fourier_integrable434
      SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu zeta Z k x y
        (hI _ hx) hZ frame f)
    (fun x hx y frame => b658_integer_frame_cutoff_inversion434
      SP smallMod BP bigMod J ell m patterns positions q Vs Vb Knu zeta Z k x y
        (hI _ hx) hZ frame f)
end Green64FullPhysicalE

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The original actual r20 RAW-plus-comparison operator with a genuine
logarithmic source cutoff in every original physical frame. -/
def b658ActualParityCutoffMatrix434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ)
    (shift : ℤ) (positions : Finset ℤ) (f : 𝓢(ℝ, ℂ)) :
    Matrix (B654ActualParityState434 L hS J positions)
      (B654ActualParityState434 L hS J positions) ℂ := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  exact b658IntegerCutoffMatrix434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta Z shift f

/-- Actual full source identity: same B655 first vector, same B654
operator and state mass, actual shift 2k, every original mark/frame.
The integral is with respect to real Lebesgue measure and density
Fourier(f); it is not either of the separate original D61 endpoint
Fourier measures. No Fourier identity or integrability premise remains. -/
theorem b658_actual_parity_cutoff_fourier434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ)
    (k : ℤ) (positions : Finset ℤ) (lo hi : ℕ) (hlo : 0 < lo) (hZ : 0 < Z)
    (c : ℤ → ℂ) (g : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions))
    (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun v : ℝ => (𝓕 f) v *
      inner ℂ (b655ActualParityFirstVector434 L hS J positions lo hi
        (fun n => b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) * c n))
        (b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi
          (zeta-2*Real.pi*v) (2*k) positions g)) ∧
    (∫ v : ℝ, (𝓕 f) v *
      inner ℂ (b655ActualParityFirstVector434 L hS J positions lo hi
        (fun n => b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) * c n))
        (b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi
          (zeta-2*Real.pi*v) (2*k) positions g)) =
      inner ℂ (b655ActualParityFirstVector434 L hS J positions lo hi c)
        ((b658ActualParityCutoffMatrix434 L hS J m hmJ Q h xi zeta Z
          (2*k) positions f).toEuclideanLin g) := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  have hI : ∀ n ∈ b654ParitySeedPositions434 lo hi, (0:ℤ) < n := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact_mod_cast (hlo.trans_le (Finset.mem_Ico.mp ha).1)
  exact b658_integer_cutoff_pairing_fourier434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta Z (2*k) hZ
    (Real.sqrt (b650IntegerStateMass434
      (SG:=SourceNativeMemorySG434 20 L hS) (BG:=sourceNativeOriginalBigType434 20 L)
      J 1 (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)):ℂ)
    (b654ParitySeedPositions434 lo hi) hI c g f
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityUnitNorm -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Both TRUE Parity endpoint vectors have the fixed norm exponent 9.
The canonical fine alpha and full sorted-Q residual bounds are proved
internally. The original ambient L is unchanged and log X may be 2L.
The eventual threshold precedes EVERY J, all original marks, the moving
Q depth, every character/frequency, and every source allocation. Optional
unit multipliers can depend on the complete physical marked state. -/
theorem b659_actual_parity_unit_endpoint_norms434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      1<L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
          (positions : Finset ℤ) (t1 t2 : ℝ) (X Y : ℕ),
          1≤X → 1≤Y → Y≤3*X → Real.log (X:ℝ)≤2*L →
          ∀ (eta1 eta2 : B654ActualParityState434 L hFamily J positions → ℂ),
            (∀ x, ‖eta1 x‖≤1) → (∀ x, ‖eta2 x‖≤1) →
            (∀ x, (Y:ℤ)<x.val.1.val → eta1 x=0) →
            (∀ x, (Y:ℤ)<x.val.1.val → eta2 x=0) →
            ‖b657ActualPrimeEndpointVector434 L hFamily J positions E t1 eta1‖ ≤
              Real.sqrt (X:ℝ)*L^(9:ℝ) ∧
            ‖b657ActualPrimeEndpointVector434 L hFamily J positions H t2 eta2‖ ≤
              Real.sqrt (X:ℝ)*L^(9:ℝ) := by
  filter_upwards [b656_actual_fine_native_and_parity_inputs434 S beta gamma hS hbeta hgamma,
    b657_eventually_actual_full_dyadic_norm434 (0:ℝ)] with L hInputs hNorm
  refine ⟨hNorm.1,hNorm.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hFamily J positions t1 t2 X Y hX hY hXY hLog eta1 eta2 hEta1 hEta2 hUp1 hUp2
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hPair := (hInputs.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1).2 xi1 xi2 rho sigma
  have hE : B656UnitRoughPrimeCore434 L E := hPair.1
  have hH : B656UnitRoughPrimeCore434 L H := hPair.2
  have hEa : ∀ n, ‖E.alpha n‖≤L^(0:ℝ) := by simpa only [Real.rpow_zero] using hE.1
  have hEc : ∀ n, ‖E.residual n‖≤L^(0:ℝ) := by simpa only [Real.rpow_zero] using hE.2.1
  have hHa : ∀ n, ‖H.alpha n‖≤L^(0:ℝ) := by simpa only [Real.rpow_zero] using hH.1
  have hHc : ∀ n, ‖H.residual n‖≤L^(0:ℝ) := by simpa only [Real.rpow_zero] using hH.2.1
  constructor
  · simpa only [mul_zero,zero_add] using hNorm.2.2 hFamily J positions E t1 hEa hEc
      X Y hX hY hXY hLog eta1 hEta1 hUp1
  · simpa only [mul_zero,zero_add] using hNorm.2.2 hFamily J positions H t2 hHa hHc
      X Y hX hY hXY hLog eta2 hEta2 hUp2
end Green64Analytic.Parity

end

end

/-! ## ActualFirstVectorNorm -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The literal original first coefficient, before its ONE sqrt(mu0):
P-only epsilon, X/n, (n/Z)^(-iv), n^(it), the true core and the extra
S04 endpoint damping. The group family is the actual original r20 P. -/
def b659ActualParityRootCoefficient434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ) (n : ℤ) : ℂ :=
  b656SourceRootMultiplier434 (sourceOriginalPAllActualBands 20 L) tw (X:ℝ) Z v n.toNat *
    b656IntegerPrimeEndpointCoefficient434
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
      (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t n

/-- The exact E4.1 first multiplier is unit bounded on the original
dyadic seed interval. No multiplier norm hypothesis is needed. -/
theorem b659_root_multiplier_on_dyad434 {G : Type} [Fintype G]
    (P : G → Finset ℕ) (tw : Bool) (X : ℕ) (Z v : ℝ)
    (hX : 1≤X) (hZ : 0<Z) (n : ℤ) (hn : n∈b654ParitySeedPositions434 X (2*X)) :
    ‖b656SourceRootMultiplier434 P tw (X:ℝ) Z v n.toNat‖≤1 := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
  have hmX := (Finset.mem_Ico.mp hm).1
  have hmpos : 0 < m := by omega
  simpa only [Int.toNat_natCast] using b656_source_root_multiplier_norm434
    P tw (X:ℝ) Z v m (Nat.cast_nonneg _) hZ hmpos (Nat.cast_le.mpr hmX)

/-- The actual canonical Parity E-first coefficient has the ORIGINAL B655
first-vector norm bound sqrt(X)*L^9. Its literal parity/smooth/Mellin root
multiplier is discharged internally, as are alpha and native residual
norms. The threshold precedes J and keeps log X<=2L in the same L. -/
theorem b659_actual_parity_first_vector_norm434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      1<L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
          (positions : Finset ℤ) (t : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ),
          1≤X → 0<Z → Real.log (X:ℝ)≤2*L →
          ‖b655ActualParityFirstVector434 L hFamily J positions X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J E t tw X Z v)‖ ≤
              Real.sqrt (X:ℝ)*L^(9:ℝ) := by
  filter_upwards [b659_actual_parity_unit_endpoint_norms434 S beta gamma hS hbeta hgamma] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi2 rho sigma hFamily J positions t tw X Z v hX hZ hLog
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let eta : ℤ → ℂ := fun n => b656SourceRootMultiplier434
    (sourceOriginalPAllActualBands 20 L) tw (X:ℝ) Z v n.toNat
  let eta1 : B654ActualParityState434 L hFamily J positions → ℂ := fun x =>
    if x.val.1.val∈b654ParitySeedPositions434 X (2*X) then eta x.val.1.val else 0
  have hEta : ∀ x, ‖eta1 x‖≤1 := by
    intro x
    by_cases hx : x.val.1.val∈b654ParitySeedPositions434 X (2*X)
    · simpa only [eta1,hx,ite_true,eta] using b659_root_multiplier_on_dyad434
        (sourceOriginalPAllActualBands 20 L) tw X Z v hX hZ x.val.1.val hx
    · simp only [eta1,hx,ite_false,norm_zero]
      norm_num
  have hUpper : ∀ x, ((3*X:ℕ):ℤ)<x.val.1.val → eta1 x=0 := by
    intro x hx
    have hnot : x.val.1.val∉b654ParitySeedPositions434 X (2*X) := by
      intro hmem
      obtain ⟨m,hm,heq⟩ := Finset.mem_image.mp hmem
      have hmhi := (Finset.mem_Ico.mp hm).2
      omega
    simp only [eta1,hnot,ite_false]
  have hn := (h.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    0 xi2 rho sigma hFamily J positions t 0 X (3*X) hX (by omega) le_rfl hLog
    eta1 (fun _ => 0) hEta (by intro x; norm_num) hUpper (by intro x hx; rfl)).1
  change ‖b655ActualParityFirstVector434 L hFamily J positions X (2*X)
    (fun n => eta n * b656IntegerPrimeEndpointCoefficient434
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
      (sourceOriginalPAllActualBands 20 L) E (1/2:ℝ) t n)‖≤_
  rw [b657_first_vector_eq_prime_endpoint434]
  exact hn
end Green64Analytic.Parity

end

end

/-! ## ActualRootFourier -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The true complex power of a positive physical ratio factors with
Mathlib's Fourier inversion phase, including 2*pi and an arbitrary
original root frequency v0. -/
theorem b662_positive_root_mellin_fourier434 (x v0 v : ℝ) (hx : 0<x) :
    (x:ℂ)^(-Complex.I*((v0+2*Real.pi*v:ℝ):ℂ)) =
      b658FourierPhase434 (-v) (Real.log x) *
        (x:ℂ)^(-Complex.I*(v0:ℂ)) := by
  have hxC : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le]
  unfold b658FourierPhase434
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact source epsilon*(X/n)*(n/Z)^(-iv) after adding 2*pi*xi
to any baseline frequency. The original parity, real harmonic multiplier
and baseline Mellin phase remain in the coefficient on both sides. -/
theorem b662_source_root_multiplier_fourier434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (tw : Bool)
    (X Z v0 v : ℝ) (n : ℕ) (hn : 0<n) (hZ : 0<Z) :
    b656SourceRootMultiplier434 P tw X Z (v0+2*Real.pi*v) n =
      b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) *
        b656SourceRootMultiplier434 P tw X Z v0 n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  unfold b656SourceRootMultiplier434
  rw [b662_positive_root_mellin_fourier434 _ v0 v (div_pos hnR hZ)]
  ring

/-- Literal actual first coefficient: adding the true root frequency
2*pi*xi gives the B658 Fourier twist of the arbitrary baseline coefficient.
Nonpositive positions have zero endpoint coefficient on both sides by
the existing definition. -/
theorem b662_actual_parity_root_coefficient_fourier434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ)
    (Z v0 v : ℝ) (hZ : 0<Z) (n : ℤ) :
    b659ActualParityRootCoefficient434 L hFamily J F t tw X Z (v0+2*Real.pi*v) n =
      b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) *
        b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v0 n := by
  unfold b659ActualParityRootCoefficient434
  by_cases hn : 0<n
  · have hnNat : 0<n.toNat := by omega
    have hcast : (n.toNat:ℝ)=(n:ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn.le
    rw [b662_source_root_multiplier_fourier434
      (sourceOriginalPAllActualBands 20 L) tw (X:ℝ) Z v0 v n.toNat hnNat hZ, hcast]
    ring
  · simp only [b656IntegerPrimeEndpointCoefficient434, hn, ite_false, mul_zero]

/-- The exact B655 full-mark first vector with its original root Mellin
phase is the B658 Fourier-twisted baseline vector. Its one sqrt(mu0),
all marks and the unchanged seed interval are preserved. No baseline
frequency, positive-X or support strengthening is imposed. -/
theorem b662_actual_parity_first_vector_fourier434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ)
    (Z v0 v : ℝ) (hZ : 0<Z) :
    b655ActualParityFirstVector434 L hFamily J positions lo hi
      (b659ActualParityRootCoefficient434 L hFamily J F t tw X Z (v0+2*Real.pi*v)) =
    b655ActualParityFirstVector434 L hFamily J positions lo hi
      (fun n => b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) *
        b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v0 n) := by
  congr 1
  funext n
  exact b662_actual_parity_root_coefficient_fourier434 L hFamily J F t tw X Z v0 v hZ n
end Green64Analytic.Parity

end

end

/-! ## ActualFirstInputs -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Literal physical root factors preserve the norm of the true core,
including the real X/n factor and BOTH additional unit phases. -/
theorem b659_root_coefficient_norm_le_core434
    (L : ℝ) (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (F : PrimeSlotCore) (t : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ) (n : ℤ)
    (hn : 0<n) (hXn : (X:ℝ)≤n.toNat) (hZ : 0<Z) :
    ‖b659ActualParityRootCoefficient434 L hFamily J F t tw X Z v n‖ ≤
      ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F n.toNat‖ := by
  have hEta := b656_source_root_multiplier_norm434 (sourceOriginalPAllActualBands 20 L)
    tw (X:ℝ) Z v n.toNat (Nat.cast_nonneg _) hZ (by omega) hXn
  unfold b659ActualParityRootCoefficient434
  exact (b656_endpoint_unit_multiplier434 _ _ hEta).trans
    (b656_integer_prime_endpoint_norm434
      (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
      (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1
      (sourceOriginalPAllActualBands 20 L) F (1/2:ℝ) t (by norm_num) (by norm_num) n)

/-- The genuine first endpoint has BOTH original S02 inputs as proved
conclusions: norm <= sqrt(X)*L^9 and coefficient sup <= exp(5sqrt L).
The norm exponent 9 and sup exponent 5 precede every J. The source
geometric condition 2X<=exp(2L) is explicit; there are no norm, sup,
alpha, residual or signed-cancellation assumptions. -/
theorem b659_actual_parity_first_inputs434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      1<L ∧ (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
          (positions : Finset ℤ) (t : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ),
          1≤X → 0<Z → Real.log (X:ℝ)≤2*L → ((2*X:ℕ):ℝ)≤Real.exp (2*L) →
          ‖b655ActualParityFirstVector434 L hFamily J positions X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J E t tw X Z v)‖ ≤
              Real.sqrt (X:ℝ)*L^(9:ℝ) ∧
          ∀ n∈b654ParitySeedPositions434 X (2*X),
            ‖b659ActualParityRootCoefficient434 L hFamily J E t tw X Z v n‖ ≤
              Real.exp (5*Real.sqrt L) := by
  filter_upwards [b659_actual_parity_first_vector_norm434 S beta gamma hS hbeta hgamma,
    b656_actual_parity_arithmetic_bounds434 S beta gamma hS hbeta hgamma] with L hNorm hCore
  refine ⟨hNorm.1,hNorm.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi2 rho sigma hFamily J positions t tw X Z v hX hZ hLog hSize
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  refine ⟨hNorm.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi2 rho sigma hFamily J positions t tw X Z v hX hZ hLog,?_⟩
  intro n hn
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
  have hXm := (Finset.mem_Ico.mp hm).1
  have hm2 := (Finset.mem_Ico.mp hm).2
  have hmpos : 0 < m := by omega
  have hmSize : (m:ℝ)≤Real.exp (2*L) := (Nat.cast_le.mpr hm2.le).trans hSize
  have hpoint := (hCore prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    0 xi2 rho sigma (sourceOriginalPAllActualBands 20 L) m hmpos hmSize).1
  have hncore := b659_root_coefficient_norm_le_core434 L hFamily J E t tw X Z v (m:ℤ)
    (by exact_mod_cast hmpos) (by simpa only [Int.toNat_natCast] using Nat.cast_le.mpr hXm) hZ
  exact hncore.trans (by simpa only [Int.toNat_natCast] using hpoint)
end Green64Analytic.Parity

end

end

/-! ## ActualParityDyadicSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 20000

/-- Unconditional physical dyadic saving for the actual canonical fine
alpha, original native Q residual, and BOTH literal B633 Parity cores.
The first endpoint includes original P-parity, X/n and its Mellin phase;
the second endpoint permits any bounded marked-state test multiplier.
There are NO norm, sup, trace, CRT, mass, cancellation or operator
premises. The only size inputs concern the actual coefficient/dyad
configuration. The same original source tuple is chosen with Cnorm=9
BEFORE every coefficient parameter, J-dependent threshold and L. -/
theorem b660_eventually_actual_parity_dyadic_saving434
    (E Cfreq Ck gammaLong : ℝ)
    (hE : 0 < E) (hLong : 0 < gammaLong) (hCk : 0 ≤ Ck) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma Cpos : ℝ), 0 < S → 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (zeta : ℝ),
      |zeta| ≤ L^Cfreq → ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (t1 t2 : ℝ) (tw : Bool) (X : ℕ) (Z v : ℝ), 0 < Z →
        Real.exp (gammaLong*L) ≤ (X:ℝ) →
        (X:ℝ) ≤ 2*Real.exp L*L^Cpos*(b651ParityWindowSize434 J Ck L:ℝ) →
      ∀ (eta : B654ActualParityState434 L hFamily J
        (b654ParityIntervalWindow434 J Ck L X (2*X)) → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) →
        ‖inner ℂ
          (b655ActualParityFirstVector434 L hFamily J
            (b654ParityIntervalWindow434 J Ck L X (2*X)) X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v))
          (b654ActualParityPhysicalOperator434 L hFamily J m hmJ Q h xi zeta (2*k)
            (b654ParityIntervalWindow434 J Ck L X (2*X))
            (b657ActualPrimeEndpointVector434 L hFamily J
              (b654ParityIntervalWindow434 J Ck L X (2*X)) Gcore t2 eta))‖ ≤
          (X:ℝ)*L^(-E) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hEndpoint⟩ :=
    b655_eventually_actual_parity_endpoint_saving434 E Cfreq Ck gammaLong 9
      hE hLong hCk (by norm_num)
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma Cpos hS hbeta hgamma
  filter_upwards [hEndpoint 5 (by norm_num),
    b660_eventually_actual_dyadic_window434 J Ck Cpos gammaLong hCk hLong,
    b659_actual_parity_first_inputs434 S beta gamma hS hbeta hgamma,
    b659_actual_parity_unit_endpoint_norms434 S beta gamma hS hbeta hgamma]
    with L hEndpoint hGeometry hFirst hBoth
  dsimp only at hEndpoint ⊢
  obtain ⟨hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hEnd⟩ := hEndpoint
  refine ⟨hGeometry.1,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily zeta hzeta k hk hkBound prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma t1 t2 tw X Z v hZ hLower hUpper eta hEta
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L X (2*X)
  obtain ⟨hX,_,hWindow,hTriple,hLog⟩ := hGeometry.2 X hLower hUpper
  have hDouble : ((2*X:ℕ):ℝ) ≤ Real.exp (2*L) := by
    push_cast
    have hx0 : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
    linarith only [hTriple,hx0]
  have hInputs := hFirst.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi2 rho sigma hFamily J positions t1 tw X Z v hX hZ hLog hDouble
  have hEtaUpper : ∀ x : B654ActualParityState434 L hFamily J positions,
      ((3*X:ℕ):ℤ) < x.val.1.val → eta x=0 := by
    intro x hx
    have hw := (hWindow x.val.1.val x.val.1.property).2
    omega
  have hGNorm := (hBoth.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hFamily J positions t1 t2 X (3*X) hX (by omega) le_rfl hLog
    (fun _ => 0) eta (by intro x; norm_num) hEta (by intro x hx; rfl) hEtaUpper).2
  have hLength : 2*X-X=X := by omega
  have hSave := hEnd hFamily zeta hzeta k hk hkBound X (2*X)
    (by simpa only [hLength] using hLower)
    (b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v) hInputs.2
    (b657ActualPrimeEndpointVector434 L hFamily J positions Gcore t2 eta)
    (by simpa only [hLength] using hInputs.1)
    (by simpa only [hLength] using hGNorm)
  simpa only [hLength] using hSave
end Green64Analytic.Parity

end

end

/-! ## ActualCutoffSaving -/

section

open Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 24000

/-- Actual full logarithmic-cutoff physical RAW+comparison saving.
All integrability and low/global frequency bounds are proved internally.
The Fourier band Cpsi+3 precedes the ideal tuple; the Schur exponent and
arbitrary Fourier tail precision are chosen after J. The actual phase is
zeta-2*pi*v, with real Lebesgue measure and the literal log(n/(Z*D)).
The second endpoint retains its actual Parity core and an explicit unit
marked multiplier. No physical-to-stripped or comparison-arc conclusion
is inferred from this physical residual bound. -/
theorem parity_eventually_actual_log_cutoff_saving434
    (E Czeta Ck gammaLong Cpsi Bpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hE : 0 < E) (hLong : 0 < gammaLong) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hBpsi : 0 ≤ Bpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma Cpos : ℝ), 0 < S → 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (psiLog : 𝓢(ℝ,ℂ)),
      tsupport (psiLog : ℝ → ℂ) ⊆ Set.Icc (-Bpsi) Bpsi →
      sourceLogDerivativeBudget Cpsi Kpsi L psiLog →
      ∀ (zeta : ℝ), |zeta| ≤ L^Czeta → ∀ (k : ℤ), k ≠ 0 →
        (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (t1 t2 : ℝ) (tw : Bool) (X : ℕ) (Z v0 : ℝ), 0 < Z →
        Real.exp (gammaLong*L) ≤ (X:ℝ) →
        (X:ℝ) ≤ 2*Real.exp L*L^Cpos*(b651ParityWindowSize434 J Ck L:ℝ) →
      ∀ (eta : B654ActualParityState434 L hFamily J
        (b654ParityIntervalWindow434 J Ck L X (2*X)) → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) →
        ‖inner ℂ
          (b655ActualParityFirstVector434 L hFamily J
            (b654ParityIntervalWindow434 J Ck L X (2*X)) X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v0))
          ((b658ActualParityCutoffMatrix434 L hFamily J m hmJ Q h xi zeta Z (2*k)
            (b654ParityIntervalWindow434 J Ck L X (2*X)) psiLog).toEuclideanLin
            (b657ActualPrimeEndpointVector434 L hFamily J
              (b654ParityIntervalWindow434 J Ck L X (2*X)) Gcore t2 eta))‖ ≤
          (X:ℝ)*L^(-E) := by
  let Fband : ℝ := Cpsi+3
  let A : ℝ := b662CutoffSavingExponent434 E Cpsi
  have hA : 0 < A := by
    dsimp [A,b662CutoffSavingExponent434]
    have hN := Nat.cast_nonneg (Nat.ceil (3*Cpsi)) (α:=ℝ)
    linarith
  have hCF : Cpsi < Fband := by dsimp [Fband]; linarith
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hPhysical⟩ :=
    b660_eventually_actual_parity_dyadic_saving434 A (max Czeta Fband+1) Ck gammaLong
      hA hLong hCk
  obtain ⟨Cschur,hCschur,hSchur⟩ :=
    b661_eventually_actual_parity_uniform_schur434 J m Cq Cxi hmJ
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma Cpos hS hbeta hgamma
  filter_upwards [hPhysical S beta gamma Cpos hS hbeta hgamma,
    hSchur,
    b662_eventually_fourier_cutoff_saving434 E Cpsi Bpsi Fband Kpsi
      hCpsi hBpsi hKpsi hCF (Cschur+18),
    b660_eventually_actual_dyadic_window434 J Ck Cpos gammaLong hCk hLong,
    b659_actual_parity_first_vector_norm434 S beta gamma hS hbeta hgamma,
    b659_actual_parity_unit_endpoint_norms434 S beta gamma hS hbeta hgamma,
    eventually_ge_atTop (1+2*Real.pi)]
    with L hPhysical hSchur hCut hGeometry hFirst hBoth hFreq
  dsimp only at hPhysical ⊢
  obtain ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hSave⟩ := hPhysical
  refine ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily psiLog hSupp hReg zeta hzeta k hk hkBound prime l u hlow
    r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma t1 t2 tw X Z v0 hZ hLower hUpper eta hEta
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L X (2*X)
  let c := b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v0
  let g := b657ActualPrimeEndpointVector434 L hFamily J positions Gcore t2 eta
  let a : ℝ → ℂ := fun v => inner ℂ
    (b655ActualParityFirstVector434 L hFamily J positions X (2*X)
      (fun n => b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) * c n))
    (b654ActualParityPhysicalOperator434 L hFamily J m hmJ Q h xi
      (zeta-2*Real.pi*v) (2*k) positions g)
  obtain ⟨hX,_,hWindow,hTriple,hLog⟩ := hGeometry.2 X hLower hUpper
  have hLp : 0 < L := zero_lt_one.trans hL
  have hFourier := b658_actual_parity_cutoff_fourier434 L hFamily J m hmJ Q h xi
    zeta Z k positions X (2*X) (by omega) hZ c g psiLog
  have hInt : Integrable (fun v : ℝ => (𝓕 psiLog) v * a v) := hFourier.1
  have hLow (v : ℝ) (hv : |v| ≤ L^Fband) : ‖a v‖ ≤ (X:ℝ)*L^(-A) := by
    have hf := b658_actual_fourier_frequency_band434 L Czeta Fband zeta v hFreq hzeta hv
    have hs := hSave hFamily (zeta-2*Real.pi*v) hf k hk hkBound
      prime l u hlow r d hr b slot δ ξ K q chi s0 s1
      xi1 xi2 rho sigma t1 t2 tw X Z (v0+2*Real.pi*v)
      hZ hLower hUpper eta hEta
    rw [b662_actual_parity_first_vector_fourier434 L hFamily J positions X (2*X)
      Ecore t1 tw X Z v0 v hZ] at hs
    exact hs
  have hFNorm := hFirst.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi2 rho sigma hFamily J positions t1 tw X Z v0 hX hZ hLog
  have hEtaUpper : ∀ x : B654ActualParityState434 L hFamily J positions,
      ((3*X:ℕ):ℤ) < x.val.1.val → eta x=0 := by
    intro x hx
    have hw := (hWindow x.val.1.val x.val.1.property).2
    omega
  have hGNorm := (hBoth.2.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma hFamily J positions t1 t2 X (3*X) hX (by omega) le_rfl hLog
    (fun _ => 0) eta (by intro x; norm_num) hEta (by intro x hx; rfl) hEtaUpper).2
  have hAll (v : ℝ) : ‖a v‖ ≤ (X:ℝ)*L^(Cschur+18) := by
    have hs := (hSchur.2.2 hFamily Q h xi hQc hh hxi hxic
      (zeta-2*Real.pi*v) k positions).2
      (b655ActualParityFirstVector434 L hFamily J positions X (2*X)
        (fun n => b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) * c n)) g
    rw [b658_actual_parity_first_fourier_norm434] at hs
    have hn := mul_le_mul
      (mul_le_mul_of_nonneg_left hFNorm (Real.rpow_nonneg hLp.le Cschur))
      hGNorm (norm_nonneg g) (by positivity : 0 ≤ L^Cschur*(Real.sqrt (X:ℝ)*L^(9:ℝ)))
    have hcost : L^Cschur*(Real.sqrt (X:ℝ)*L^(9:ℝ)) *
        (Real.sqrt (X:ℝ)*L^(9:ℝ)) = (X:ℝ)*L^(Cschur+18) := by
      calc
        _ = (Real.sqrt (X:ℝ)*Real.sqrt (X:ℝ)) *
          (L^Cschur*(L^(9:ℝ)*L^(9:ℝ))) := by ring
        _ = _ := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg X), ←Real.rpow_add hLp,
            ←Real.rpow_add hLp]
          norm_num
    exact hs.trans (hn.trans_eq hcost)
  have hBound := hCut psiLog a (X:ℝ) (Nat.cast_nonneg X) hSupp hReg hInt hLow hAll
  rw [hFourier.2] at hBound
  exact hBound
end Green64Analytic.Parity

end

end

/-! ## OriginalCutoff -/

section

open Filter Topology MeasureTheory Green64Analytic.SpectralEndpoint
open scoped FourierTransform SchwartzMap BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Logarithmic support of the SAME original physical cutoff. -/
theorem parity_log_cutoff_support434 (psi : ℝ → ℂ)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64) :
    tsupport (fun u : ℝ => psi (Real.exp u)) ⊆
      Set.Icc (-Real.log (64:ℝ)) (Real.log (64:ℝ)) := by
  apply closure_minimal
  · intro u hu
    have hs := hSupport (Real.exp u) hu
    have hlo := Real.log_le_log (by norm_num : (0:ℝ)<1/64) hs.1
    have hhi := Real.log_le_log (Real.exp_pos u) hs.2
    have he : Real.log (1/64:ℝ) = -Real.log (64:ℝ) := by
      rw [one_div, Real.log_inv]
    constructor
    · simpa only [he,Real.log_exp] using hlo
    · simpa only [Real.log_exp] using hhi
  · exact isClosed_Icc

theorem parity_log_cutoff_compact434 (psi : ℝ → ℂ)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64) :
    HasCompactSupport (fun u : ℝ => psi (Real.exp u)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (parity_log_cutoff_support434 psi hSupport)

/-- Direct packaging, not a surrogate cutoff or extra weight. -/
def parityOriginalLogCutoff434 (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64) : 𝓢(ℝ,ℂ) :=
  (parity_log_cutoff_compact434 psi hSupport).toSchwartzMap
    (hSmooth.comp Real.contDiff_exp)

theorem parity_original_log_cutoff_apply434 (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64) (u : ℝ) :
    parityOriginalLogCutoff434 psi hSmooth hSupport u = psi (Real.exp u) := rfl

/-- Inversion is asserted only at a positive physical ratio. -/
theorem parity_original_log_cutoff_positive434 (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64)
    (x : ℝ) (hx : 0<x) :
    parityOriginalLogCutoff434 psi hSmooth hSupport (Real.log x) = psi x := by
  rw [parity_original_log_cutoff_apply434, Real.exp_log hx]
end Green64Analytic.Parity

namespace Green64FullPhysicalE
open Green64Analytic.SourceBlockSieve Green64Analytic.Parity
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell m : ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)

/-- Original psi(n/(Z*D)) in every full physical frame. -/
def parityIntegerPsiCutoffMatrix434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ)
    (psi : ℝ → ℂ) :
    Matrix (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions)
      (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) ℂ :=
  b658FrameMatrix434 (fun x y frame =>
    b650IntegerFrameScalar434 SP smallMod BP bigMod J ell m patterns positions
      q Vs Vb Knu zeta 1 k x y frame *
    psi ((x.val.1.val:ℝ) /
      (Z*(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns x.val.2 frame:ℝ))))

/-- Exact original-psi pairing identity on the positive seed. No
incorrect whole-matrix logarithm identity at nonpositive positions. -/
theorem parity_integer_original_cutoff_pairing434 (positions : Finset ℤ)
    (q : ℝ) (Vs : SG → ℝ) (Vb : BG → ℝ)
    (Knu : SourcePatternK BP J ell m patterns) (zeta Z : ℝ) (k : ℤ)
    (hZ : 0<Z) (w : ℂ) (I : Finset ℤ) (hI : ∀ n∈I, (0:ℤ)<n)
    (c : ℤ → ℂ) (g : EuclideanSpace ℂ
      (B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions))
    (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64) :
    inner ℂ (b652FirstPositionVector434 (fun x => x.val.1.val) w I c)
      ((b658IntegerCutoffMatrix434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu zeta Z k (parityOriginalLogCutoff434 psi hSmooth hSupport)).toEuclideanLin g) =
    inner ℂ (b652FirstPositionVector434 (fun x => x.val.1.val) w I c)
      ((parityIntegerPsiCutoffMatrix434 SP smallMod BP bigMod J ell m patterns positions
        q Vs Vb Knu zeta Z k psi).toEuclideanLin g) := by
  unfold b658IntegerCutoffMatrix434 parityIntegerPsiCutoffMatrix434
  rw [b658_seed_frame_pairing434,b658_seed_frame_pairing434]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro frame hf
  by_cases hi : x.val.1.val∈I
  · simp only [hi,ite_true]
    have hn : (0:ℝ)<(x.val.1.val:ℝ) := by exact_mod_cast hI _ hi
    have hD : (0:ℝ)<(b650NativeFrameD434 SP smallMod BP bigMod J ell m patterns
        x.val.2 frame:ℝ) := by
      exact_mod_cast b658_native_frame_divisor_pos434 SP smallMod BP bigMod J ell m
        patterns x.val.2 frame
    rw [parity_original_log_cutoff_positive434 psi hSmooth hSupport _
      (div_pos hn (mul_pos hZ hD))]
  · simp only [hi,ite_false]
end Green64FullPhysicalE

namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.Parity Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Literal actual Parity RAW-plus-comparison matrix with original psi. -/
def parityActualPsiCutoffMatrix434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ)
    (shift : ℤ) (positions : Finset ℤ) (psi : ℝ → ℂ) :
    Matrix (B654ActualParityState434 L hS J positions)
      (B654ActualParityState434 L hS J positions) ℂ := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  exact parityIntegerPsiCutoffMatrix434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta Z shift psi

theorem parity_actual_original_cutoff_pairing434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ)
    (k : ℤ) (positions : Finset ℤ) (lo hi : ℕ) (hlo : 0<lo) (hZ : 0<Z)
    (c : ℤ → ℂ) (g : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions))
    (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
    (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64) :
    inner ℂ (b655ActualParityFirstVector434 L hS J positions lo hi c)
      ((b658ActualParityCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) positions
        (parityOriginalLogCutoff434 psi hSmooth hSupport)).toEuclideanLin g) =
    inner ℂ (b655ActualParityFirstVector434 L hS J positions lo hi c)
      ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k) positions psi).toEuclideanLin g) := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  have hI : ∀ n∈b654ParitySeedPositions434 lo hi, (0:ℤ)<n := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    exact_mod_cast hlo.trans_le (Finset.mem_Ico.mp ha).1
  exact parity_integer_original_cutoff_pairing434 SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats positions (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta Z (2*k) hZ
    (Real.sqrt (b650IntegerStateMass434
      (SG:=SourceNativeMemorySG434 20 L hS) (BG:=sourceNativeOriginalBigType434 20 L)
      J 1 (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)):ℂ)
    (b654ParitySeedPositions434 lo hi) hI c g psi hSmooth hSupport
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option maxRecDepth 24000

/-- Unconditional original-psi physical dyadic saving. The cutoff is
literally psi(n/(Z*D)) on every full physical frame. No separate Fourier,
integrability, endpoint-norm, low-band or global-bound premise is used.
The source logarithmic derivative budget is transferred definitionally. -/
theorem parity_eventually_actual_original_cutoff_saving434
    (E Czeta Ck gammaLong Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hE : 0 < E) (hLong : 0 < gammaLong) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma Cpos : ℝ), 0 < S → 0 < beta → 0 < gamma →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64),
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
      ∀ (zeta : ℝ), |zeta| ≤ L^Czeta → ∀ (k : ℤ), k ≠ 0 →
        (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (t1 t2 : ℝ) (tw : Bool) (X : ℕ) (Z v0 : ℝ), 0 < Z →
        Real.exp (gammaLong*L) ≤ (X:ℝ) →
        (X:ℝ) ≤ 2*Real.exp L*L^Cpos*(b651ParityWindowSize434 J Ck L:ℝ) →
      ∀ (eta : B654ActualParityState434 L hFamily J
        (b654ParityIntervalWindow434 J Ck L X (2*X)) → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) →
        ‖inner ℂ
          (b655ActualParityFirstVector434 L hFamily J
            (b654ParityIntervalWindow434 J Ck L X (2*X)) X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v0))
          ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ Q h xi zeta Z (2*k)
            (b654ParityIntervalWindow434 J Ck L X (2*X)) psi).toEuclideanLin
            (b657ActualPrimeEndpointVector434 L hFamily J
              (b654ParityIntervalWindow434 J Ck L X (2*X)) Gcore t2 eta))‖ ≤
          (X:ℝ)*L^(-E) := by
  have hB : 0 ≤ Real.log (64:ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hLogSave⟩ :=
    parity_eventually_actual_log_cutoff_saving434 E Czeta Ck gammaLong Cpsi (Real.log 64)
      Kpsi hE hLong hCk hCpsi hB hKpsi
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma Cpos hS hbeta hgamma
  filter_upwards [hLogSave S beta gamma Cpos hS hbeta hgamma] with L hLogSave
  dsimp only at hLogSave ⊢
  obtain ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hSave⟩ := hLogSave
  refine ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily psi hSmooth hSupport hReg zeta hzeta k hk hkBound prime l u hlow
    r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma t1 t2 tw X Z v0 hZ hLower hUpper eta hEta
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  have hSupp : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-Real.log (64:ℝ)) (Real.log (64:ℝ)) :=
    parity_log_cutoff_support434 psi hSupport
  have hs := hSave hFamily f hSupp hReg zeta hzeta k hk hkBound
    prime l u hlow r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma t1 t2 tw X Z v0 hZ hLower hUpper eta hEta
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let positions := b654ParityIntervalWindow434 J Ck L X (2*X)
  let c := b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v0
  let g := b657ActualPrimeEndpointVector434 L hFamily J positions Gcore t2 eta
  have hXpos : 0<X := by
    have hp : (0:ℝ)<X := (Real.exp_pos _).trans_le hLower
    exact_mod_cast hp
  have he := parity_actual_original_cutoff_pairing434 L hFamily J m hmJ
    (Nat.ceil (4*L^(D+1))) (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ))
    (L^(-(Cxi:ℝ))) zeta Z k positions X (2*X) hXpos hZ c g psi hSmooth hSupport
  rw [he] at hs
  exact hs
end Green64Analytic.Parity

end

end

/-! ## OriginalMellinBudget -/

section

open Filter Topology MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Uniform mass and arbitrary tail precision for the Mellin transform of
THE ORIGINAL physical cutoff. C, F, the full derivative constants K and
the tail precision D are fixed before L and before psi or any operator
tuple. This reuses the certified uniform cutoff theorems. -/
theorem parity_eventually_original_cutoff_mellin_budget434
    (C F : ℝ) (K : ℕ → ℝ) (D : ℕ)
    (hC : 0 ≤ C) (hK : ∀ j, 0 ≤ K j) (hCF : C < F) :
    ∀ᶠ L : ℝ in atTop, ∀ (psi : ℝ → ℂ)
      (hSmooth : ContDiff ℝ ∞ psi)
      (hSupport : ∀ u : ℝ, psi u ≠ 0 → (1/64 : ℝ) ≤ u ∧ u ≤ 64),
      sourceLogDerivativeBudget C K L (fun u : ℝ => psi (Real.exp u)) →
      let f := parityOriginalLogCutoff434 psi hSmooth hSupport
      (∫ s : ℝ, ‖(𝓕 f : 𝓢(ℝ,ℂ)) s‖) ≤ L^(Nat.ceil (3*C)+1) ∧
      (∫ s : ℝ in {s : ℝ | L^F ≤ |s|}, ‖(𝓕 f : 𝓢(ℝ,ℂ)) s‖) ≤ (L^D)⁻¹ := by
  have hB : 0 ≤ Real.log (64 : ℝ) := Real.log_nonneg (by norm_num)
  have hMass := eventually_source_cutoff_family_fourier_mass_power
    C (Real.log (64 : ℝ)) K (Nat.ceil (3*C)) hC hB hK (Nat.le_ceil _)
  have hTail := eventually_source_cutoff_family_fourier_tail_saving
    C (Real.log (64 : ℝ)) F K hC hB hK hCF D
  filter_upwards [hMass,hTail] with L hM hT
  intro psi hSmooth hSupport hReg
  let f := parityOriginalLogCutoff434 psi hSmooth hSupport
  have hs : tsupport (f : ℝ → ℂ) ⊆ Set.Icc (-Real.log (64 : ℝ)) (Real.log (64 : ℝ)) :=
    parity_log_cutoff_support434 psi hSupport
  exact ⟨hM f hs hReg,hT f hs hReg⟩
end Green64Analytic.Parity

end

end

/-! ## ComparisonFixed -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Literal Parity r0=20 and sigma=1/44. The reserved fixed band j has
exact exponents tau=2^(-j)/44 and eta=3*2^(-j)/110. -/
theorem parity_r20_Q_exponent434 (j : ℕ) :
    sourceOriginalQActualExponent 20 j = 1/(44*(2:ℝ)^j) ∧
    0 < sourceOriginalQActualExponent 20 j ∧
    sourceOriginalQActualExponent 20 j < (6/5:ℝ)*sourceOriginalQActualExponent 20 j ∧
    (6/5:ℝ)*sourceOriginalQActualExponent 20 j < 1/4 := by
  have hq : 0 < (2:ℝ)^j := by positivity
  have hq1 : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have he : sourceOriginalQActualExponent 20 j = 1/(44*(2:ℝ)^j) := by
    unfold sourceOriginalQActualExponent sourceOriginalQ0Scale
    norm_num
    ring
  have ht : 0 < sourceOriginalQActualExponent 20 j := by rw [he]; positivity
  refine ⟨he, ht, ?_, ?_⟩
  · nlinarith
  · rw [he, mul_one_div]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<44*(2:ℝ)^j)).mpr
    nlinarith

/-- Genuine comparison fixed data for Parity. The complete original P
geometry and harmonic floors stay unchanged; the Q geometry is r20.
No source data, discrepancy or cancellation field is assumed. -/
def parityComparisonFixed434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi)
    (Cpsi : ℝ) (hCpsi : 0 ≤ Cpsi)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) : SourceComparisonFixed434 :=
  { sourceNativeOriginalR6Fixed434 jQ mmax cm s0 vexp Carc Cchi CZ
      hCarc hCchi hCchiPos Kpsi hKpsi with
    τ := sourceOriginalQActualExponent 20 jQ
    η := (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ
    s1base := s1
    Cpsi := Cpsi
    epsi := ⌈3*Cpsi⌉₊
    fcut := ⌈Cpsi+3⌉₊
    hCpsi := hCpsi
    hepsi := Nat.le_ceil _
    hFcut := by have hh := Nat.le_ceil (Cpsi+3); linarith
    hτ := (parity_r20_Q_exponent434 jQ).2.1
    hτη := (parity_r20_Q_exponent434 jQ).2.2.1
    hη := (parity_r20_Q_exponent434 jQ).2.2.2 }

/-- All fixed numeric arc/character gates for the same r20 record.
Every exponent precedes L. -/
theorem parity_eventually_comparison_arc_gates434
    (jQ mmax cm s0 s1 vexp : ℕ) (CZ Carc Cchi : ℝ)
    (hCarc : (cm:ℝ) ≤ Carc) (hCchi : (cm:ℝ) ≤ Cchi) (hCchiPos : 0 < Cchi)
    (Cpsi : ℝ) (hCpsi : 0 ≤ Cpsi)
    (Kpsi : ℕ → ℝ) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    let cfg := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
      hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧ L^(2*cfg.cm) ≤ Real.exp (Real.sqrt L) ∧
      L^cfg.Carc ≤ Real.exp (Real.sqrt L) ∧
      L^cfg.Carc < Real.exp (L^cfg.aexp) ∧
      L^cfg.Carc < Real.exp (cfg.τ*L) := by
  let cfg := parityComparisonFixed434 jQ mmax cm s0 s1 vexp CZ Carc Cchi
    hCarc hCchi hCchiPos Cpsi hCpsi Kpsi hKpsi
  filter_upwards [eventually_native_r6_original_comparison_arc_gates434
      jQ mmax cm s0 vexp Carc Cchi CZ hCarc hCchi hCchiPos Kpsi hKpsi,
    eventually_native_source_poly_lt_exp_scaled434 Carc 1 cfg.τ
      ((Nat.cast_nonneg cm).trans hCarc) (by norm_num) cfg.hτ] with L hOld hLong
  refine ⟨hOld.1, ?_, hOld.2.2.1, hOld.2.2.2.1, ?_⟩
  · have hh := hOld.2.1
    change L^(2*(cm:ℝ)) ≤ Real.exp (Real.sqrt L) at hh
    have he : 2*(cm:ℝ) = ((2*cm:ℕ):ℝ) := by push_cast; rfl
    rw [he, Real.rpow_natCast] at hh
    exact hh
  · change L^Carc < Real.exp (cfg.τ*L)
    simpa only [Real.rpow_one] using hLong.2

/-- The reserved original Q band has all real prime-slot fields, at
all later depths and all slot labels. Its lower endpoint is genuinely
above W=exp(sqrt L). No replacement prime set is introduced. -/
theorem parity_eventually_fixed_Q_fields434 (jQ : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      1 < L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (d : ℕ) (band : Fin (d+1)), band.val=jQ →
      let tau := sourceOriginalQActualExponent 20 jQ
      let eta := (6/5:ℝ)*tau
      let I := Set.Icc (Real.exp (tau*L)) (Real.exp (eta*L))
      let Q := sourceOriginalQActualBands 20 d L band
      Set.OrdConnected I ∧ (∀ p, p∈Q ↔ p.Prime ∧ (p:ℝ)∈I) ∧
      I ⊆ Set.Icc ((Real.exp L)^tau) ((Real.exp L)^eta) ∧
      (∀ p∈Q, Real.exp (Real.sqrt L)<(p:ℝ)) ∧
      (∀ p∈Q, Real.exp (tau*L)≤(p:ℝ)) := by
  let tau := sourceOriginalQActualExponent 20 jQ
  have ht : 0 < tau := (parity_r20_Q_exponent434 jQ).2.1
  filter_upwards [source_original_literal_depth_grows 20 jQ (by norm_num),
    eventually_gt_atTop (max (1:ℝ) ((1/tau)^2))] with L hDepth hBound
  have hL : 1 < L := (le_max_left _ _).trans_lt hBound
  have hLp : 0 < L := by linarith
  have hs := Real.sq_sqrt hLp.le
  have hs0 := Real.sqrt_nonneg L
  have hinv : 0 < 1/tau := by positivity
  have hInvSq : (1/tau)^2 < L := (le_max_right _ _).trans_lt hBound
  have hInv : 1/tau < Real.sqrt L := by nlinarith
  have hMul : 1 < Real.sqrt L*tau := (div_lt_iff₀ ht).mp hInv
  have hsPos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLp
  have hsLt : Real.sqrt L < tau*L := by nlinarith
  refine ⟨hL,hDepth,?_⟩
  intro d band hband
  dsimp only
  refine ⟨Set.ordConnected_Icc, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa only [hband] using source_actual_designated_Q_prime_interval434 20 d L band p
  · simpa only [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,mul_comm] using
      (Set.Subset.rfl : Set.Icc (Real.exp (tau*L)) (Real.exp ((6/5:ℝ)*tau*L)) ⊆
        Set.Icc (Real.exp (tau*L)) (Real.exp ((6/5:ℝ)*tau*L)))
  · intro p hp
    have hlow := ((source_actual_designated_Q_prime_interval434 20 d L band p).mp hp).2.1
    rw [hband] at hlow
    exact (Real.exp_lt_exp.mpr hsLt).trans_le hlow
  · intro p hp
    simpa only [hband] using
      ((source_actual_designated_Q_prime_interval434 20 d L band p).mp hp).2.1

/-- Every actual r20 Q prime fits the original comparison cap, including
both closed band endpoints and all moving depths. -/
theorem parity_Qslot_below_comparison_cap434
    (d : ℕ) (L : ℝ) (hL : 1 ≤ L) (band : Fin (d+1))
    (Y : ℝ) (Ncap : ℕ) (hY : Real.exp (3*L/4) ≤ Y) (hCap : 64*Y ≤ (Ncap:ℝ)) :
    ∀ p ∈ sourceOriginalQActualBands 20 d L band, p ≤ Ncap := by
  intro p hp
  have hhigh := ((source_actual_designated_Q_prime_interval434 20 d L band p).mp hp).2.2
  have he := (parity_r20_Q_exponent434 band.val).2.2.2
  have hLp : 0 ≤ L := by linarith
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hY
  have hExp : (p:ℝ) ≤ Real.exp (3*L/4) := hhigh.trans (Real.exp_le_exp.mpr (by nlinarith))
  exact_mod_cast (hExp.trans (hY.trans (by linarith : Y ≤ (Ncap:ℝ))))

/-- The true additional modulus is 2*|k|. One fixed extra log power
absorbs this factor, uniformly for every nonzero signed k. -/
theorem parity_mask_modulus_budget434
    (L Ck : ℝ) (cm : ℕ) (hL : 2 ≤ L) (hcm : Ck+1 ≤ (cm:ℝ))
    (k : ℤ) (hk : k ≠ 0) (hK : (k.natAbs:ℝ) ≤ L^Ck) :
    0 < 2*k.natAbs ∧ ((2*k.natAbs:ℕ):ℝ) ≤ L^cm := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  refine ⟨Nat.mul_pos (by norm_num) (Int.natAbs_pos.mpr hk), ?_⟩
  push_cast
  calc
    2*(k.natAbs:ℝ) ≤ 2*L^Ck := mul_le_mul_of_nonneg_left hK (by norm_num)
    _ ≤ L*L^Ck := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _)
    _ = L^(Ck+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring
    _ ≤ L^(cm:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hcm
    _ = L^cm := Real.rpow_natCast L cm
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ComparisonCellScales -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Actual r20 comparison geometry for every physical Z in the source
polynomial-log window, with no r6 bilinear chart or even-k restriction.
Both complete original A/B active-cell families and their harmonic masses
remain unchanged. All caps and strong Y bounds are proved uniformly. -/
theorem parity_eventually_full_comparison_cell_scales434
    (CZ Carc : ℝ) (m : ℕ) (hCZ : 0 ≤ CZ) (hCarc : 0 ≤ Carc) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      ∀ Z : ℝ, Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
      ∀ (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m),
        nu ∈ sourceOriginalTwoBlockProbePatterns434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m →
      ∀ (hA hB xi : ℝ), 0 < hA → 0 < hB → hA ≤ 1 → hB ≤ 1 →
      ∀ (ja jb : ℤ),
        ja ∈ sourceOriginalProbeActiveCellsA434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hA xi →
        jb ∈ sourceOriginalProbeActiveCellsB434 m (sourceNativeOriginalTb434 20 L)
          (sourceNativeOriginalVbig434 20 L) nu hB xi →
      let H := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
      let Y := Z*H
      let Ncap : ℕ := ⌈64*Y⌉₊
      0 < Z ∧ 0 < H ∧ 4 ≤ Y ∧ Real.exp (3*L/4) ≤ Y ∧
      Y ≤ Real.exp (3*L/2) ∧ 64*Y ≤ (Ncap:ℝ) ∧
      (Ncap:ℝ) ≤ (Real.exp L)^2 ∧
      2 ≤ H/L^Carc ∧ H/L^Carc ≤ Y/(8*64) := by
  let C0 : ℝ := 3+(Real.log 2)⁻¹
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  filter_upwards [eventually_source_native_cell_scalar_budget434 CZ Carc C0 m hCZ hCarc hC0,
    eventually_native_source_poly_lt_exp_scaled434 CZ 1 (1/4) hCZ (by norm_num) (by norm_num),
    eventually_ge_atTop (4*Real.log 512/3)] with L hbud hLogSmall hLZ
  rcases hbud with ⟨hLexp,hL32,hLlo,hLcap,hLarc,hupper,hlower,hshift⟩
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hCzLog : CZ*Real.log L ≤ L/4 := by
    have hh := Real.log_lt_log (Real.rpow_pos_of_pos hLp CZ) hLogSmall.2
    rw [Real.log_rpow hLp,Real.log_exp,Real.rpow_one] at hh
    linarith
  refine ⟨by linarith, ?_⟩
  intro Z hZlo hZhi nu hnu hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  let S := (ja:ℝ)*hA+(jb:ℝ)*hB
  let H := Real.exp ((ja:ℝ)*hA)*Real.exp ((jb:ℝ)*hB)
  let Y := Z*H
  let Ncap : ℕ := ⌈64*Y⌉₊
  have hZp : 0 < Z := (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hHp : 0 < H := by dsimp [H]; positivity
  have hYp : 0 < Y := mul_pos hZp hHp
  have hlogZlo : L-CZ*Real.log L ≤ Real.log Z := by
    have hh := Real.log_le_log (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))) hZlo
    rw [Real.log_mul (Real.exp_pos L).ne' (Real.rpow_pos_of_pos hLp (-CZ)).ne',
      Real.log_exp,Real.log_rpow hLp] at hh
    linarith
  have hlogZhi : Real.log Z ≤ L+CZ*Real.log L := by
    have hh := Real.log_le_log hZp hZhi
    rw [Real.log_mul (Real.exp_pos L).ne' (Real.rpow_pos_of_pos hLp CZ).ne',
      Real.log_exp,Real.log_rpow hLp] at hh
    exact hh
  have hc := source_native_original_active_cell_log_bounds434
    20 (by norm_num) L hLexp m nu hnu hA hB xi hhA hhB hA1 hB1 ja jb ha hb
  have hHexp : H=Real.exp S := by dsimp [H,S]; rw [Real.exp_add]
  have hlogY : Real.log Y=Real.log Z+S := by
    dsimp [Y]
    rw [Real.log_mul hZp.ne' hHp.ne',hHexp,Real.log_exp]
  have hp3 : 1 ≤ L^(3/10:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hp4 : 1 ≤ L^(2/5:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hp4non : 0 ≤ L^(2/5:ℝ) := Real.rpow_nonneg hLp.le _
  have hSpos : 0 < S := by dsimp [S]; linarith [hc.1]
  have hYlo : Real.exp (3*L/4) ≤ Y := by
    rw [←Real.exp_log hYp]
    apply Real.exp_le_exp.mpr
    rw [hlogY]
    linarith
  have hY4 : 4 ≤ Y := by nlinarith only [hL32,hYlo,Real.add_one_le_exp (3*L/4)]
  have hYhi : Y ≤ Real.exp (3*L/2) := by
    rw [←Real.exp_log hYp]
    apply Real.exp_le_exp.mpr
    rw [hlogY]
    have hlog144 : 0 ≤ Real.log (144:ℝ) := Real.log_nonneg (by norm_num)
    have hA0 : 0 ≤ (CZ+89)*Real.log L+Real.log 144 := by positivity
    have hAedge := mul_le_mul_of_nonneg_left hp4 hA0
    have hub := mul_le_mul_of_nonneg_right hupper hp4non
    have hrpow : L^(3/5:ℝ)*L^(2/5:ℝ)=L := by
      rw [←Real.rpow_add hLp]
      norm_num
    have hub' : ((CZ+89+(m:ℝ)*C0)*Real.log L+Real.log 144)*L^(2/5:ℝ) ≤ L/2 := by
      calc
        _ ≤ (L^(3/5:ℝ)/2)*L^(2/5:ℝ) := hub
        _ = L/2 := by rw [div_mul_eq_mul_div,hrpow]
    have hcS : S ≤ (m:ℝ)*C0*Real.log L*L^(2/5:ℝ) := hc.2
    nlinarith only [hlogZhi,hcS,hAedge,hub',hlog144,hlog0]
  have hCap : 64*Y ≤ (Ncap:ℝ) := Nat.le_ceil _
  have hNcap : (Ncap:ℝ) ≤ (Real.exp L)^2 := by
    have hceil : (Ncap:ℝ) ≤ 64*Y+1 := (Nat.ceil_lt_add_one (by positivity : 0≤64*Y)).le
    have hone : 1 ≤ Real.exp (3*L/2) := Real.one_le_exp_iff.mpr (by positivity)
    calc
      _ ≤ 65*Real.exp (3*L/2) := by nlinarith
      _ = Real.exp (Real.log 65+3*L/2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<65)]
      _ ≤ Real.exp (2*L) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp L)^2 := by rw [pow_two,←Real.exp_add]; congr 1; ring
  have hpow : 0 < L^Carc := Real.rpow_pos_of_pos hLp _
  have hHband : 2 ≤ H/L^Carc := by
    apply (le_div_iff₀ hpow).mpr
    calc
      2*L^Carc = Real.exp (Real.log 2+Carc*Real.log L) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hLp]
        congr 1; congr 1; ring
      _ ≤ Real.exp S := Real.exp_le_exp.mpr (by dsimp [S]; linarith [hc.1])
      _ = H := hHexp.symm
  have hZ512 : (512:ℝ) ≤ Z := by
    rw [←Real.exp_log hZp,←Real.exp_log (by norm_num : (0:ℝ)<512)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpow1 : 1 ≤ L^Carc := Real.one_le_rpow hL1 hCarc
  have hArc : H/L^Carc ≤ Y/(8*64) := by
    apply (div_le_div_iff₀ hpow (by norm_num : (0:ℝ)<8*64)).mpr
    have h1 : (512:ℝ) ≤ Z*L^Carc := hZ512.trans
      (by nlinarith [mul_le_mul_of_nonneg_left hpow1 hZp.le])
    have h2 := mul_le_mul_of_nonneg_right h1 hHp.le
    dsimp [Y]
    nlinarith
  exact ⟨hZp,hHp,hY4,hYlo,hYhi,hCap,hNcap,hHband,hArc⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalCutoffDyads -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.Parity
open Green64Analytic.CorrelationSquare Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The source lower Z-window dominates the fixed support loss 128.
The threshold depends only on CZ, before any frame or dyad is chosen. -/
theorem parity_eventually_source_Z_dyad_floor434 (CZ : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧ 32 ≤ L ∧
      ∀ Z : ℝ, Real.exp L*L^(-CZ) ≤ Z →
        128*Real.exp (L/2) ≤ Z := by
  filter_upwards [
    eventually_native_source_poly_lt_exp_scaled434 CZ 1 (1/4)
      hCZ (by norm_num) (by norm_num),
    eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (32:ℝ),
    eventually_ge_atTop (4*Real.log (128:ℝ))]
    with L hPoly hLexp hL32 hLlog
  have hLp : 0 < L := by linarith
  have hCzLog : CZ*Real.log L ≤ L/4 := by
    have hh := Real.log_lt_log (Real.rpow_pos_of_pos hLp CZ) hPoly.2
    rw [Real.log_rpow hLp,Real.log_exp,Real.rpow_one] at hh
    linarith
  refine ⟨hLexp,hL32,?_⟩
  intro Z hZlo
  have hZp : 0 < Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hlogZ : L-CZ*Real.log L ≤ Real.log Z := by
    have hh := Real.log_le_log
      (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))) hZlo
    rw [Real.log_mul (Real.exp_pos L).ne'
      (Real.rpow_pos_of_pos hLp (-CZ)).ne',Real.log_exp,Real.log_rpow hLp] at hh
    linarith
  calc
    128*Real.exp (L/2) = Real.exp (Real.log 128+L/2) := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<128)]
    _ ≤ Real.exp (Real.log Z) := Real.exp_le_exp.mpr (by linarith)
    _ = Z := Real.exp_log hZp

/-- Exact scalar consequences of the original support [1/64,64].
The factor 64 is absorbed by Cpos=CZ+1, not discarded. -/
theorem parity_original_cutoff_dyad_bounds434
    (L CZ Z X n H : ℝ) (D : ℕ)
    (hL : 32 ≤ L) (hZp : 0 < Z) (hD : 0 < D) (hDH : (D:ℝ) ≤ H)
    (hZlo : 128*Real.exp (L/2) ≤ Z) (hZhi : Z ≤ Real.exp L*L^CZ)
    (psi : ℝ → ℂ)
    (hSupport : ∀ u, psi u ≠ 0 → (1/64:ℝ) ≤ u ∧ u ≤ 64)
    (hpsi : psi (n/(Z*(D:ℝ))) ≠ 0)
    (hXn : X ≤ n) (hnX : n < 2*X) :
    Real.exp (L/2) ≤ X ∧ X ≤ 2*Real.exp L*L^(CZ+1)*H := by
  have hLp : 0 < L := by linarith
  have hDreal : (0:ℝ)<D := by exact_mod_cast hD
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hH0 : 0 ≤ H := (le_of_lt hDreal).trans hDH
  have hZD : 0 < Z*(D:ℝ) := mul_pos hZp hDreal
  have hs := hSupport (n/(Z*(D:ℝ))) hpsi
  have hnlo : (1/64:ℝ)*(Z*(D:ℝ)) ≤ n := (le_div_iff₀ hZD).mp hs.1
  have hnhi : n ≤ 64*(Z*(D:ℝ)) := (div_le_iff₀ hZD).mp hs.2
  have hZDlo : Z ≤ Z*(D:ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hD1 hZp.le
  constructor
  · nlinarith only [hZlo,hnlo,hZDlo,hnX]
  · have hprod : Z*(D:ℝ) ≤ (Real.exp L*L^CZ)*H :=
      mul_le_mul hZhi hDH hDreal.le
        (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hLp.le _))
    have hbase0 : 0 ≤ Real.exp L*L^CZ*H := by positivity
    calc
      X ≤ n := hXn
      _ ≤ 64*(Z*(D:ℝ)) := hnhi
      _ ≤ 64*(Real.exp L*L^CZ*H) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ (2*L)*(Real.exp L*L^CZ*H) :=
        mul_le_mul_of_nonneg_right (by linarith : (64:ℝ) ≤ 2*L) hbase0
      _ = 2*Real.exp L*L^(CZ+1)*H := by
        rw [Real.rpow_add hLp,Real.rpow_one]
        ring

/-- Every actual Parity physical frame contributing a nonzero original
cutoff lies in the admissible dyad range with gammaLong=1/2 and
Cpos=CZ+1. The source Z-window is the only scale input; positivity
and the upper frame-divisor bound are discharged from the actual
r20 arithmetic frame, for all SMALL/BIG states and all patterns. -/
theorem parity_eventually_actual_original_cutoff_dyads434
    (CZ : ℝ) (hCZ : 0 ≤ CZ) :
    ∀ᶠ L : ℝ in atTop, Real.exp 1 ≤ L ∧ 32 ≤ L ∧
    ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (J m : ℕ) (Ck : ℝ), 0 ≤ Ck →
    ∀ {Nu : Type} [Fintype Nu]
      (patterns : Nu → SourcePattern (sourceNativeOriginalBigType434 20 L) J m)
      (x : MemoryIndependentState
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1)
      (f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hFamily)
        (SourceNativeMemoryBP434 20 L) J 1 m patterns)
      (Z : ℝ), Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
    ∀ (psi : ℝ → ℂ),
      (∀ u, psi u ≠ 0 → (1/64:ℝ) ≤ u ∧ u ≤ 64) →
    ∀ (X : ℕ) (n : ℤ), (X:ℝ) ≤ (n:ℝ) → (n:ℝ) < 2*(X:ℝ) →
      psi ((n:ℝ)/(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
        J 1 m patterns x f:ℝ))) ≠ 0 →
      Real.exp ((1/2:ℝ)*L) ≤ (X:ℝ) ∧
      (X:ℝ) ≤ 2*Real.exp L*L^(CZ+1)*(b651ParityWindowSize434 J Ck L:ℝ) := by
  filter_upwards [parity_eventually_source_Z_dyad_floor434 CZ hCZ] with L hFloor
  obtain ⟨hLexp,hL32,hFloor⟩ := hFloor
  refine ⟨hLexp,hL32,?_⟩
  intro hFamily J m Ck hCk Nu instNu patterns x f Z hZlo hZhi psi hSupport X n hXn hnX hpsi
  have hLp : 0 < L := by linarith
  have hZp : 0 < Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have hD := b658_native_frame_divisor_pos434
    (SourceNativeMemorySP434 20 L hFamily) (fun _ p => p.val)
    (SourceNativeMemoryBP434 20 L) (fun _ p => p.val)
    J 1 m patterns x f
  have hDH := b660_actual_parity_frame_D_window434 L hLexp hFamily J m Ck hCk patterns x f
  have hs := parity_original_cutoff_dyad_bounds434
    L CZ Z (X:ℝ) (n:ℝ) (b651ParityWindowSize434 J Ck L:ℝ) _
    hL32 hZp hD hDH (hFloor Z hZlo) hZhi psi hSupport hpsi hXn hnX
  simpa only [one_div,mul_comm (2:ℝ)⁻¹ L,←div_eq_mul_inv] using hs
end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalCutoffAllDyads -/

section

open Filter Real Green64Analytic.SpectralEndpoint
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.Parity
open Green64Analytic.CorrelationSquare Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 24000

/-- Exact finite physical pairing vanishes when the original cutoff
vanishes on every seed frame. This is a finite sum identity. -/
theorem parity_actual_cutoff_pairing_zero_of_frame_vanishing434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta Z : ℝ)
    (k : ℤ) (positions : Finset ℤ) (X : ℕ) (c : ℤ → ℂ)
    (g : EuclideanSpace ℂ (B654ActualParityState434 L hS J positions))
    (psi : ℝ → ℂ)
    (hzero : ∀ n ∈ b654ParitySeedPositions434 X (2*X),
      ∀ x : MemoryIndependentState
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1,
      ∀ f : MemoryPrimitiveEFrame (SG:=SourceNativeMemorySG434 20 L hS)
        (SourceNativeMemoryBP434 20 L) J 1 m
        (sourceOriginalMemoryRawComparisonPattern434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
          J m hmJ),
      psi ((n:ℝ)/(Z*(b650NativeFrameD434
        (SourceNativeMemorySP434 20 L hS) (fun _ p => p.val)
        (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J 1 m
        (sourceOriginalMemoryRawComparisonPattern434
          (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
          J m hmJ) x f:ℝ))) = 0) :
    inner ℂ (b655ActualParityFirstVector434 L hS J positions X (2*X) c)
      ((parityActualPsiCutoffMatrix434 L hS J m hmJ Q h xi zeta Z (2*k)
        positions psi).toEuclideanLin g) = 0 := by
  unfold parityActualPsiCutoffMatrix434 parityIntegerPsiCutoffMatrix434
  change inner ℂ (b652FirstPositionVector434 _ _ _ _)
    ((b658FrameMatrix434 _).toEuclideanLin g) = 0
  rw [b658_seed_frame_pairing434]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finset.sum_eq_zero
  intro f hf
  by_cases hn : x.val.1.val ∈ b654ParitySeedPositions434 X (2*X)
  · simp only [hn,ite_true,hzero _ hn x.val.2 f,mul_zero,zero_mul]
  · simp only [hn,ite_false]
end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 26000

/-- Actual original-psi dyadic saving for every natural dyad scale X
in the original source Z-window. The previous admissible-scale
premises are now discharged from actual frame support; inadmissible
dyads have exactly zero pairing. All parameters m,D,HH,Q,xi,J are
selected before the Z-window exponent CZ and the fine-cell data. -/
theorem parity_eventually_actual_original_cutoff_all_dyads434
    (E Czeta Ck Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hE : 0 < E) (hCk : 0 ≤ Ck)
    (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (S beta gamma CZ : ℝ), 0 < S → 0 < beta → 0 < gamma → 0 ≤ CZ →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      1 < L ∧ 0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧
      0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (psi : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ psi)
        (hSupport : ∀ x, psi x ≠ 0 → (1/64:ℝ) ≤ x ∧ x ≤ 64),
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi (Real.exp u)) →
      ∀ (zeta : ℝ), |zeta| ≤ L^Czeta → ∀ (k : ℤ), k ≠ 0 →
        (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ), 1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
      let F := sourceNativePrimeCore r d L b slot δ ξ K
        (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
      ∀ xi1 xi2 rho sigma : ℝ,
      let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
      let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
      ∀ (t1 t2 : ℝ) (tw : Bool) (X : ℕ) (Z v0 : ℝ),
        Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
      ∀ (eta : B654ActualParityState434 L hFamily J
        (b654ParityIntervalWindow434 J Ck L X (2*X)) → ℂ),
        (∀ x, ‖eta x‖ ≤ 1) →
        ‖inner ℂ
          (b655ActualParityFirstVector434 L hFamily J
            (b654ParityIntervalWindow434 J Ck L X (2*X)) X (2*X)
            (b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v0))
          ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ Q h xi zeta Z (2*k)
            (b654ParityIntervalWindow434 J Ck L X (2*X)) psi).toEuclideanLin
            (b657ActualPrimeEndpointVector434 L hFamily J
              (b654ParityIntervalWindow434 J Ck L X (2*X)) Gcore t2 eta))‖ ≤
          (X:ℝ)*L^(-E) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hActual⟩ :=
    parity_eventually_actual_original_cutoff_saving434
      E Czeta Ck (1/2) Cpsi Kpsi hE (by norm_num) hCk hCpsi hKpsi
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro S beta gamma CZ hS hbeta hgamma hCZ
  filter_upwards [hActual S beta gamma (CZ+1) hS hbeta hgamma,
    parity_eventually_actual_original_cutoff_dyads434 CZ hCZ] with L hSave hGeom
  dsimp only at hSave ⊢
  obtain ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,hSave⟩ := hSave
  obtain ⟨hLexp,hL32,hGeom⟩ := hGeom
  refine ⟨hL,hQ,hQc,hh,hh1,hxi,hxic,hFamily0,?_⟩
  intro hFamily psi hSmooth hSupport hReg zeta hzeta k hk hkBound prime l u hlow
    r d hr b slot δ ξ K q chi s0 s1
    xi1 xi2 rho sigma t1 t2 tw X Z v0 hZlo hZhi eta hEta
  have hLp : 0<L := by linarith
  have hZp : 0<Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  by_cases hRange : Real.exp ((1/2:ℝ)*L) ≤ (X:ℝ) ∧
      (X:ℝ) ≤ 2*Real.exp L*L^(CZ+1)*(b651ParityWindowSize434 J Ck L:ℝ)
  · exact hSave hFamily psi hSmooth hSupport hReg zeta hzeta k hk hkBound
      prime l u hlow r d hr b slot δ ξ K q chi s0 s1
      xi1 xi2 rho sigma t1 t2 tw X Z v0 hZp hRange.1 hRange.2 eta hEta
  · let F := sourceNativePrimeCore r d L b slot δ ξ K
      (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
    let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
    let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
    let positions := b654ParityIntervalWindow434 J Ck L X (2*X)
    let c := b659ActualParityRootCoefficient434 L hFamily J Ecore t1 tw X Z v0
    let g := b657ActualPrimeEndpointVector434 L hFamily J positions Gcore t2 eta
    have hz := parity_actual_cutoff_pairing_zero_of_frame_vanishing434
      L hFamily J m hmJ (Nat.ceil (4*L^(D+1)))
      (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)) (L^(-(Cxi:ℝ))) zeta Z k
      positions X c g psi (by
        intro n hn x f
        by_contra hne
        have hnBounds : (X:ℝ) ≤ (n:ℝ) ∧ (n:ℝ) < 2*(X:ℝ) := by
          obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
          have ha' := Finset.mem_Ico.mp ha
          constructor
          · exact_mod_cast ha'.1
          · exact_mod_cast ha'.2
        exact hRange (hGeom hFamily J m Ck hCk
          (sourceOriginalMemoryRawComparisonPattern434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
            J m hmJ) x f Z hZlo hZhi psi hSupport X n hnBounds.1 hnBounds.2 hne))
    change ‖inner ℂ (b655ActualParityFirstVector434 L hFamily J positions X (2*X) c)
      ((parityActualPsiCutoffMatrix434 L hFamily J m hmJ (Nat.ceil (4*L^(D+1)))
        (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)) (L^(-(Cxi:ℝ))) zeta Z
        (2*k) positions psi).toEuclideanLin g)‖ ≤ (X:ℝ)*L^(-E)
    rw [hz,norm_zero]
    positivity
end Green64Analytic.Parity

end

end

