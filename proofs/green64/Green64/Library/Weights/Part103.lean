module

public import Green64.Library.Weights.Part102

@[expose] public section

/-!
# Weights / Part103

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Mass003 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics
open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourcePTiltedLocalFactors.lean; original line 11. -/
noncomputable def sourceOriginalPTiltBase
    {P : Finset ℕ} (z : {p // p ∈ P}) (k : ℕ) (δ : ℝ) : ℝ :=
  sourceOriginalPVecBaseFactor z k * ((z.val:ℝ)^δ)^k



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 23. -/
noncomputable def sourceOriginalPVecMarkFactor
    {P : Finset ℕ} (z : {p // p ∈ P}) (k : ℕ) : ℝ :=
  (if k = 0 then 0 else (1:ℝ)) * ((z.val:ℝ)⁻¹)^k



/- Exact source owner: SourcePTiltedLocalFactors.lean; original line 15. -/
noncomputable def sourceOriginalPTiltMark
    {P : Finset ℕ} (z : {p // p ∈ P}) (k : ℕ) (δ : ℝ) : ℝ :=
  sourceOriginalPVecMarkFactor z k * ((z.val:ℝ)^δ)^k

/- Each twisted local power truly has ratio p^(δ-1),
not a new prime model. -/



/- Exact source owner: SourcePFiniteMarkedEuler.lean; original line 10. -/
theorem source_original_P_finite_marked_prod_sum
    {I T : Type} [Fintype I] [DecidableEq I] [Fintype T]
    (F M : I → T → ℝ) :
    (∑ e : I → T, ∑ p : I,
        ∏ z : I, if z = p then M z (e z) else F z (e z)) =
      ∑ p : I, (∑ k : T, M p k) *
        (∏ z ∈ (Finset.univ : Finset I).erase p,
          ∑ k : T, F z k) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  let G : I → T → ℝ := fun z k =>
    if z = p then M z k else F z k
  have hProd := Finset.prod_univ_sum
    (t := fun (_ : I) => (Finset.univ : Finset T))
    (f := G)
  have hSum :
      (∑ e : I → T, ∏ z : I, G z (e z)) =
        ∏ z : I, ∑ k : T, G z k := by
    simpa only [Fintype.piFinset_univ] using hProd.symm
  calc
    (∑ e : I → T,
        ∏ z : I, if z = p then M z (e z) else F z (e z)) =
      ∑ e : I → T, ∏ z : I, G z (e z) := rfl
    _ = ∏ z : I, ∑ k : T, G z k := hSum
    _ = (∑ k : T, M p k) *
        (∏ z ∈ (Finset.univ : Finset I).erase p,
          ∑ k : T, F z k) := by
      have hErase := Finset.mul_prod_erase
        (Finset.univ : Finset I)
        (fun z => ∑ k : T, G z k)
        (Finset.mem_univ p)
      rw [← hErase]
      simp only [G, ite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro z hz
      have hne : z ≠ p := (Finset.mem_erase.mp hz).1
      simp [G, hne]



/- Exact source owner: SourcePTiltedPowerProduct.lean; original line 9. -/
theorem source_original_P_power_real_rpow_product
    (P : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (δ : ℝ) :
    ((sourceOriginalPPrimePowerProduct P e:ℝ)^δ) =
      ∏ z : {p // p ∈ P}, ((z.val:ℝ)^δ)^e z := by
  classical
  have hPrimePos (z : {p // p ∈ P}) : 0 < (z.val:ℝ) := by
    exact_mod_cast (hPrime z.val z.property).pos
  have hPowComm (z : {p // p ∈ P}) :
      (((z.val:ℝ)^e z)^δ) = ((z.val:ℝ)^δ)^e z := by
    have hnonneg : 0 ≤ (z.val:ℝ) := (hPrimePos z).le
    calc
      ((z.val:ℝ)^e z)^δ =
        (z.val:ℝ)^((e z:ℝ)*δ) := by
          rw [Real.rpow_mul hnonneg (e z:ℝ) δ,
            Real.rpow_natCast]
      _ = (z.val:ℝ)^(δ*(e z:ℝ)) := by ring
      _ = ((z.val:ℝ)^δ)^e z := by
        rw [Real.rpow_mul hnonneg δ (e z:ℝ),
          Real.rpow_natCast]
  have hGeneral (s : Finset {p // p ∈ P}) :
      ((∏ z ∈ s, ((z.val:ℝ)^e z))^δ) =
        ∏ z ∈ s, ((z.val:ℝ)^δ)^e z := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      rw [Finset.prod_insert hz, Finset.prod_insert hz]
      rw [Real.mul_rpow (pow_nonneg (hPrimePos z).le _)
        (Finset.prod_nonneg (by
          intro x hx
          exact pow_nonneg (hPrimePos x).le _))]
      rw [hPowComm z, ih]
  unfold sourceOriginalPPrimePowerProduct
  rw [Nat.cast_prod]
  simp only [Nat.cast_pow]
  exact hGeneral Finset.univ



/- Exact source owner: SourceShiftTwoWeightMajorant.lean; original line 54. -/
noncomputable def shiftTwoMarkedLocalMass (P : Finset ℕ) (u : ℕ) : ℝ :=
  ∑ p ∈ P, if p ∣ u then
      (∏ q ∈ P.erase p, if q ∣ u then (1/2:ℝ) else 1)
    else 0



/- Exact source owner: SourceShiftTwoGroupMajorant.lean; original line 8. -/
theorem shift_two_mask_distinct_count (P : Finset ℕ) (u : ℕ) :
    (∏ p ∈ P, if p ∣ u then (1/2:ℝ) else 1) =
    (1/2:ℝ) ^ shiftTwoGroupOmega P u := by
  classical
  rw [Finset.prod_ite]
  simp [shiftTwoGroupOmega]

/- Summing one marked prime divides out its Bernoulli factor.
This works even when the marked prime occurs to exponent > 1. -/



/- Exact source owner: SourceShiftTwoGroupMajorant.lean; original line 17. -/
theorem shift_two_group_mark_sum (P : Finset ℕ) (u : ℕ) :
    shiftTwoMarkedLocalMass P u =
      (shiftTwoGroupOmega P u : ℝ) *
        (2 * (1/2:ℝ)^shiftTwoGroupOmega P u) := by
  classical
  let f : ℕ → ℝ := fun p => if p ∣ u then (1/2:ℝ) else 1
  have hpoint (p : ℕ) (hp : p ∈ P) (hpu : p ∣ u) :
      (∏ q ∈ P.erase p, f q) = 2 * (∏ q ∈ P, f q) := by
    have h : f p = 1/2 := by simp [f,hpu]
    have hmul := Finset.mul_prod_erase P f hp
    rw [h] at hmul
    linarith
  unfold shiftTwoMarkedLocalMass
  calc
    (∑ p ∈ P,
        if p ∣ u then (∏ q ∈ P.erase p, f q) else 0) =
      ∑ p ∈ P, if p ∣ u then 2 * (∏ q ∈ P, f q) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        split_ifs with h
        · exact hpoint p hp h
        · rfl
    _ = (shiftTwoGroupOmega P u : ℝ) *
          (2 * ∏ q ∈ P, f q) := by
        rw [Finset.sum_ite]
        simp [shiftTwoGroupOmega]
    _ = _ := by
        dsimp [f]
        rw [shift_two_mask_distinct_count]

/- The source W1 group factor, with ω distinct and the source
q0 = 1/2. When no group prime divides u the factor is zero. -/



/- Exact source owner: SourceShiftTwoGroupMajorant.lean; original line 54. -/
theorem shift_two_group_mark_normalized (P : Finset ℕ) (u : ℕ) :
    shiftTwoMarkedLocalMass P u /
        (∑ p ∈ P, (p:ℝ)⁻¹) =
      shiftTwoOriginalGroupFactor P u := by
  rw [shift_two_group_mark_sum]
  unfold shiftTwoOriginalGroupFactor
  by_cases h : shiftTwoGroupOmega P u = 0
  · simp [h]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [hk]
    have hpow : (1/2:ℝ) ^ (k + 1 - 1) =
        2 * (1/2:ℝ) ^ (k + 1) := by
      simp only [Nat.add_sub_cancel_right, pow_succ]
      ring
    rw [hpow]

/- EXACT one-group identity: the marked-source factor is a weighted
average over all binary masks, with exactly one marked divisor. -/



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 61. -/
theorem source_original_P_mask_ne_zero (u p : ℕ) :
    (if p ∣ u then (1/2:ℝ) else 1) ≠ 0 := by
  split_ifs <;> norm_num



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 65. -/
theorem source_original_P_mask_prod_subtype_erase
    (P : Finset ℕ) (u : ℕ) (z : {p // p ∈ P}) :
    (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
       if w.val ∣ u then (1/2:ℝ) else 1) =
    (∏ q ∈ P.erase z.val,
       if q ∣ u then (1/2:ℝ) else 1) := by
  classical
  let F : ℕ → ℝ := fun q => if q ∣ u then (1/2:ℝ) else 1
  have hAll : (∏ w : {p // p ∈ P}, F w.val) =
    ∏ q ∈ P, F q := by
    simpa only [Finset.attach_eq_univ] using Finset.prod_attach P F
  have hL := Finset.mul_prod_erase
    (Finset.univ : Finset {p // p ∈ P})
    (fun w => F w.val) (Finset.mem_univ z)
  have hR := Finset.mul_prod_erase P F z.property
  have hM : F z.val ≠ 0 := source_original_P_mask_ne_zero u z.val
  have hh := hL.trans (hAll.trans hR.symm)
  have hE : (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
       F w.val) = (∏ q ∈ P.erase z.val, F q) :=
    mul_left_cancel₀ hM hh
  exact hE



/- Exact source owner: SourcePPrimePowerWeight.lean; original line 31. -/
theorem source_original_P_power_harmonic_reciprocal
    (P : Finset ℕ) (e : {p // p ∈ P} → ℕ) :
    ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹) =
      ∏ z : {p // p ∈ P}, ((z.val:ℝ)⁻¹) ^ e z := by
  unfold sourceOriginalPPrimePowerProduct
  simp only [Nat.cast_prod, Nat.cast_pow, inv_pow]
  rw [Finset.prod_inv_distrib]

/- Actual P-group omega sees positive exponents (DISTINCT primes),
unlike the original multiplicity-counted parity exponent. -/



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 7. -/
theorem source_original_P_vec_dvd_iff_pos
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (z : {p // p ∈ P}) :
    z.val ∣ sourceOriginalPPrimePowerProduct P e ↔ 0 < e z := by
  have hn := source_original_P_power_product_ne_zero P hPrime e
  rw [Nat.Prime.dvd_iff_one_le_factorization
    (hPrime z.val z.property) hn]
  rw [source_original_P_power_factorization_at
    P hPrime e z.val z.property]
  change 1 ≤ e z ↔ 0 < e z
  omega



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 27. -/
theorem source_original_P_vec_base_eq_source_mask
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (z : {p // p ∈ P}) :
    sourceOriginalPVecBaseFactor z (e z) =
      (if z.val ∣ sourceOriginalPPrimePowerProduct P e
       then (1/2:ℝ) else 1) * ((z.val:ℝ)⁻¹)^e z := by
  unfold sourceOriginalPVecBaseFactor
  by_cases h : e z = 0
  · have hd : ¬z.val ∣ sourceOriginalPPrimePowerProduct P e :=
      (source_original_P_vec_dvd_iff_pos P hPrime e z).not.mpr
        (by omega)
    simp [h,hd]
  · have hd : z.val ∣ sourceOriginalPPrimePowerProduct P e :=
      (source_original_P_vec_dvd_iff_pos P hPrime e z).mpr
        (Nat.pos_of_ne_zero h)
    simp [h,hd]



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 44. -/
theorem source_original_P_vec_mark_eq_source_mask
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (z : {p // p ∈ P}) :
    sourceOriginalPVecMarkFactor z (e z) =
      (if z.val ∣ sourceOriginalPPrimePowerProduct P e
       then (1:ℝ) else 0) * ((z.val:ℝ)⁻¹)^e z := by
  unfold sourceOriginalPVecMarkFactor
  by_cases h : e z = 0
  · have hd : ¬z.val ∣ sourceOriginalPPrimePowerProduct P e :=
      (source_original_P_vec_dvd_iff_pos P hPrime e z).not.mpr
        (by omega)
    simp [h,hd]
  · have hd : z.val ∣ sourceOriginalPPrimePowerProduct P e :=
      (source_original_P_vec_dvd_iff_pos P hPrime e z).mpr
        (Nat.pos_of_ne_zero h)
    simp [h,hd]



/- Exact source owner: SourcePVectorMarkedTerm.lean; original line 10. -/
theorem source_original_P_vec_marked_term_exact
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (z : {p // p ∈ P}) :
    (∏ w : {p // p ∈ P},
      if w = z then sourceOriginalPVecMarkFactor w (e w)
      else sourceOriginalPVecBaseFactor w (e w)) =
    (if z.val ∣ sourceOriginalPPrimePowerProduct P e then
      (∏ q ∈ P.erase z.val,
        if q ∣ sourceOriginalPPrimePowerProduct P e
        then (1/2:ℝ) else 1) else 0) *
      ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹) := by
  classical
  let n := sourceOriginalPPrimePowerProduct P e
  let A : {p // p ∈ P} → ℝ := fun w =>
    if w = z then (if w.val ∣ n then 1 else 0)
    else (if w.val ∣ n then (1/2:ℝ) else 1)
  let B : {p // p ∈ P} → ℝ := fun w => ((w.val:ℝ)⁻¹)^e w
  have hpoint (w : {p // p ∈ P}) :
      (if w = z then sourceOriginalPVecMarkFactor w (e w)
       else sourceOriginalPVecBaseFactor w (e w)) =
      A w * B w := by
    by_cases hw : w = z
    · subst w
      simpa [A,B] using
        (source_original_P_vec_mark_eq_source_mask P hPrime e z)
    · simpa [A,B,hw] using
        (source_original_P_vec_base_eq_source_mask P hPrime e w)
  have hA : (∏ w : {p // p ∈ P}, A w) =
      (if z.val ∣ n then
        (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
          if w.val ∣ n then (1/2:ℝ) else 1)
       else 0) := by
    have hsplit := Finset.mul_prod_erase
      (Finset.univ : Finset {p // p ∈ P}) A
      (Finset.mem_univ z)
    have hAt : A z = (if z.val ∣ n then (1:ℝ) else 0) := by
      simp [A]
    have hRest : (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
          A w) =
        ∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
          if w.val ∣ n then (1/2:ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro w hw
      have hne := (Finset.mem_erase.mp hw).1
      simp [A,hne]
    rw [←hsplit, hAt, hRest]
    split_ifs <;> ring
  have hB : (∏ w : {p // p ∈ P}, B w) = (n:ℝ)⁻¹ :=
    (source_original_P_power_harmonic_reciprocal P e).symm
  calc
    (∏ w : {p // p ∈ P},
      if w = z then sourceOriginalPVecMarkFactor w (e w)
      else sourceOriginalPVecBaseFactor w (e w)) =
      ∏ w : {p // p ∈ P}, A w * B w := by
        apply Finset.prod_congr rfl
        intro w hw
        exact hpoint w
    _ = (∏ w : {p // p ∈ P}, A w) *
          (∏ w : {p // p ∈ P}, B w) := Finset.prod_mul_distrib
    _ = _ := by
      rw [hA,hB]
      rw [source_original_P_mask_prod_subtype_erase P n z]

/- Reindexing the ORIGINAL marked W1 mask over actual P primes
gives exactly the sum of one-mark products over exponent vectors. -/



/- Exact source owner: SourcePVectorMarkedTerm.lean; original line 75. -/
theorem source_original_P_vec_marked_local_exact
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) :
    shiftTwoMarkedLocalMass P
      (sourceOriginalPPrimePowerProduct P e) *
      ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹) =
    ∑ z : {p // p ∈ P},
      ∏ w : {p // p ∈ P},
        if w = z then sourceOriginalPVecMarkFactor w (e w)
        else sourceOriginalPVecBaseFactor w (e w) := by
  classical
  let n := sourceOriginalPPrimePowerProduct P e
  have hAttach : shiftTwoMarkedLocalMass P n =
      ∑ z : {p // p ∈ P},
        (if z.val ∣ n then
          (∏ q ∈ P.erase z.val,
            if q ∣ n then (1/2:ℝ) else 1) else 0) := by
    unfold shiftTwoMarkedLocalMass
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach P
        (fun p => if p ∣ n then
          (∏ q ∈ P.erase p, if q ∣ n then (1/2:ℝ) else 1)
          else 0)).symm
  rw [hAttach, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  exact (source_original_P_vec_marked_term_exact
    P hPrime e z).symm

/- Pointwise identity for original source W1, with no
alternative product distribution. Every prime exponent is the
true factorization multiplicity of a positive source P integer. -/



/- Exact source owner: SourcePVectorMarkedTerm.lean; original line 107. -/
theorem source_original_P_vec_W1_marked_exact
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) :
    shiftTwoOriginalGroupFactor P
      (sourceOriginalPPrimePowerProduct P e) *
      ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹) =
    (∑ z : {p // p ∈ P},
      ∏ w : {p // p ∈ P},
        if w = z then sourceOriginalPVecMarkFactor w (e w)
        else sourceOriginalPVecBaseFactor w (e w)) /
      (∑ p ∈ P, (p:ℝ)⁻¹) := by
  let n := sourceOriginalPPrimePowerProduct P e
  have hm := shift_two_group_mark_normalized P n
  have he := source_original_P_vec_marked_local_exact P hPrime e
  calc
    shiftTwoOriginalGroupFactor P n * (n:ℝ)⁻¹ =
      (shiftTwoMarkedLocalMass P n / (∑ p ∈ P, (p:ℝ)⁻¹)) *
        (n:ℝ)⁻¹ := by rw [hm]
    _ = (shiftTwoMarkedLocalMass P n * (n:ℝ)⁻¹) /
        (∑ p ∈ P, (p:ℝ)⁻¹) := by ring
    _ = _ := by rw [he]



/- Exact source owner: SourcePTiltedMarkedVector.lean; original line 11. -/
theorem source_original_P_tilted_vector_marked_exact
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (δ : ℝ) :
    shiftTwoOriginalGroupFactor P
      (sourceOriginalPPrimePowerProduct P e) *
      ((sourceOriginalPPrimePowerProduct P e:ℝ)^(δ-1)) =
    (∑ z : {p // p ∈ P},
      ∏ w : {p // p ∈ P},
        if w = z then sourceOriginalPTiltMark w (e w) δ
        else sourceOriginalPTiltBase w (e w) δ) /
      (∑ p ∈ P, (p:ℝ)⁻¹) := by
  classical
  let n := sourceOriginalPPrimePowerProduct P e
  let T : ℝ := ∏ w : {p // p ∈ P}, ((w.val:ℝ)^δ)^e w
  let U (z : {p // p ∈ P}) : ℝ :=
    ∏ w : {p // p ∈ P},
      if w = z then sourceOriginalPVecMarkFactor w (e w)
      else sourceOriginalPVecBaseFactor w (e w)
  let R (z : {p // p ∈ P}) : ℝ :=
    ∏ w : {p // p ∈ P},
      if w = z then sourceOriginalPTiltMark w (e w) δ
      else sourceOriginalPTiltBase w (e w) δ
  have hT : (n:ℝ)^δ = T :=
    source_original_P_power_real_rpow_product P hPrime e δ
  have hTerm (z : {p // p ∈ P}) : R z = U z * T := by
    dsimp [R,U,T]
    calc
      (∏ w : {p // p ∈ P},
        if w = z then sourceOriginalPTiltMark w (e w) δ
        else sourceOriginalPTiltBase w (e w) δ) =
        (∏ w : {p // p ∈ P},
          (if w = z then sourceOriginalPVecMarkFactor w (e w)
           else sourceOriginalPVecBaseFactor w (e w)) *
          ((w.val:ℝ)^δ)^e w) := by
          apply Finset.prod_congr rfl
          intro w hw
          by_cases hh : w = z
          · simp [hh,sourceOriginalPTiltMark]
          · simp [hh,sourceOriginalPTiltBase]
      _ = (∏ w : {p // p ∈ P},
          if w = z then sourceOriginalPVecMarkFactor w (e w)
           else sourceOriginalPVecBaseFactor w (e w)) *
          (∏ w : {p // p ∈ P}, ((w.val:ℝ)^δ)^e w) :=
            Finset.prod_mul_distrib
  have hSum : (∑ z : {p // p ∈ P}, R z) =
      (∑ z : {p // p ∈ P}, U z) * T := by
    simp_rw [hTerm]
    rw [Finset.sum_mul]
  have hOriginal :
      shiftTwoOriginalGroupFactor P n * (n:ℝ)⁻¹ =
        (∑ z : {p // p ∈ P}, U z) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
    exact source_original_P_vec_W1_marked_exact P hPrime e
  have hnPos : (0:ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero
      (source_original_P_power_product_ne_zero P hPrime e)
  have hTilt : ((n:ℝ)^(δ-1)) = (n:ℝ)⁻¹ * ((n:ℝ)^δ) := by
    rw [Real.rpow_sub hnPos δ 1, Real.rpow_one]
    ring
  calc
    shiftTwoOriginalGroupFactor P n * ((n:ℝ)^(δ-1)) =
      (shiftTwoOriginalGroupFactor P n * (n:ℝ)⁻¹) * ((n:ℝ)^δ) := by
        rw [hTilt]
        ring
    _ = ((∑ z : {p // p ∈ P}, U z) /
        (∑ p ∈ P, (p:ℝ)⁻¹)) * T := by
          rw [hOriginal,hT]
    _ = (∑ z : {p // p ∈ P}, R z) /
        (∑ p ∈ P, (p:ℝ)⁻¹) := by rw [hSum]; ring



/- Exact source owner: SourcePTiltedFiniteEuler.lean; original line 7. -/
theorem source_original_P_W1_tilted_finite_euler
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (δ : ℝ) (K : ℕ) :
    (∑ e : {p // p ∈ P} → Fin (K+1),
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P (fun z => (e z).val):ℝ)^(δ-1))) =
    (∑ z : {p // p ∈ P},
      (∑ k : Fin (K+1), sourceOriginalPTiltMark z k.val δ) *
      (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
        ∑ k : Fin (K+1), sourceOriginalPTiltBase w k.val δ)) /
      (∑ p ∈ P, (p:ℝ)⁻¹) := by
  classical
  let C := {p // p ∈ P}
  let F : C → Fin (K+1) → ℝ := fun z k =>
    sourceOriginalPTiltBase z k.val δ
  let M : C → Fin (K+1) → ℝ := fun z k =>
    sourceOriginalPTiltMark z k.val δ
  have hEuler := source_original_P_finite_marked_prod_sum F M
  have hTerm (e : C → Fin (K+1)) :
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P (fun z => (e z).val):ℝ)^(δ-1)) =
        (∑ z : C, ∏ w : C,
          if w = z then M w (e w) else F w (e w)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
    simpa only [F,M] using
      (source_original_P_tilted_vector_marked_exact
        P hPrime (fun z => (e z).val) δ)
  calc
    _ = ∑ e : C → Fin (K+1),
      (∑ z : C, ∏ w : C,
        if w = z then M w (e w) else F w (e w)) /
        (∑ p ∈ P, (p:ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro e he
          exact hTerm e
    _ = (∑ e : C → Fin (K+1),
      ∑ z : C, ∏ w : C,
        if w = z then M w (e w) else F w (e w)) /
        (∑ p ∈ P, (p:ℝ)⁻¹) := by rw [Finset.sum_div]
    _ = _ := by rw [hEuler]



/- Exact source owner: SourcePTiltedBaseCap.lean; original line 9. -/
theorem source_original_P_tilted_base_finite_sum_eq
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) (δ : ℝ) :
    (∑ k : Fin (K+1), sourceOriginalPTiltBase z k.val δ) =
      1+(1/2:ℝ) *
      (∑ k : Fin (K+1), sourceOriginalPTiltMark z k.val δ) := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,
    sourceOriginalPTiltBase,sourceOriginalPTiltMark,
    sourceOriginalPVecBaseFactor,sourceOriginalPVecMarkFactor]
  simp only [Nat.succ_ne_zero, if_false, pow_zero,
    mul_one, if_pos, zero_mul]
  simp only [zero_add,one_mul,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring



/- Exact source owner: SourcePGeometricCaps.lean; original line 9. -/
theorem source_original_P_finite_geom_positive
    (r : ℝ) (K : ℕ) :
    (∑ k : Fin (K+1),
      if k.val = 0 then (0:ℝ) else r^k.val) =
      r * (∑ k : Fin K, r^k.val) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, if_pos, Fin.val_succ]
  simp only [Nat.succ_ne_zero, if_false]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  ring

/- A uniform geometric tail cap for all finite K, with no
unjustified interchange of infinite P-power sums. -/



/- Exact source owner: SourcePGeometricCaps.lean; original line 23. -/
theorem source_original_P_geom_positive_cap
    (r : ℝ) (K : ℕ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ k : Fin (K+1),
      if k.val = 0 then (0:ℝ) else r^k.val) ≤
      r/(1-r) := by
  rw [source_original_P_finite_geom_positive]
  have hSum : Summable (fun k : ℕ => r^k) :=
    summable_geometric_of_lt_one hr0 hr1
  have hUpper :
      (∑ k : Fin K, r^k.val) ≤
        ∑' k : ℕ, r^k := by
    rw [Fin.sum_univ_eq_sum_range]
    apply hSum.sum_le_tsum
    intro k hk
    exact pow_nonneg hr0 _
  have hrNorm : ‖r‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  rw [tsum_geometric_of_norm_lt_one hrNorm] at hUpper
  have hFinal := mul_le_mul_of_nonneg_left hUpper hr0
  simpa [div_eq_mul_inv] using hFinal



/- Exact source owner: SourcePTiltedLocalFactors.lean; original line 21. -/
theorem source_original_P_tilted_local_ratio
    {P : Finset ℕ} (z : {p // p ∈ P})
    (hp : 3 ≤ z.val) (k : ℕ) (δ : ℝ) :
    ((z.val:ℝ)⁻¹)^k * ((z.val:ℝ)^δ)^k =
      ((z.val:ℝ)^(δ-1))^k := by
  have hpR : (3:ℝ) ≤ z.val := by exact_mod_cast hp
  have hp0 : (0:ℝ) < z.val := by linarith
  rw [← mul_pow, Real.rpow_sub hp0 δ 1, Real.rpow_one]
  ring



/- Exact source owner: SourcePTiltedLocalFactors.lean; original line 40. -/
theorem source_original_P_tilted_mark_ratio
    {P : Finset ℕ} (z : {p // p ∈ P})
    (hp : 3 ≤ z.val) (k : ℕ) (δ : ℝ) :
    sourceOriginalPTiltMark z k δ =
      (if k = 0 then (0:ℝ) else 1) *
        ((z.val:ℝ)^(δ-1))^k := by
  unfold sourceOriginalPTiltMark sourceOriginalPVecMarkFactor
  rw [mul_assoc, source_original_P_tilted_local_ratio z hp k δ]



/- Exact source owner: SourcePTiltedGeometricCaps.lean; original line 10. -/
theorem source_original_P_tilted_mark_finite_upper
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) (δ : ℝ)
    (hp : 3 ≤ z.val)
    (hD : 1 < (z.val:ℝ)^(1-δ)) :
    (∑ k : Fin (K+1), sourceOriginalPTiltMark z k.val δ) ≤
      (((z.val:ℝ)^(1-δ))-1)⁻¹ := by
  let D : ℝ := (z.val:ℝ)^(1-δ)
  let r : ℝ := (z.val:ℝ)^(δ-1)
  have hpR : (3:ℝ) ≤ z.val := by exact_mod_cast hp
  have hp0 : (0:ℝ) < z.val := by linarith
  have hRel : r = D⁻¹ := by
    dsimp [r,D]
    have hExp : δ-1 = -(1-δ) := by ring
    rw [hExp,Real.rpow_neg hp0.le]
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hp0 _).le
  have hr1 : r < 1 := by
    rw [hRel]
    exact (inv_lt_one₀ hD0).mpr hD
  have hSum :
      (∑ k : Fin (K+1), sourceOriginalPTiltMark z k.val δ) =
      ∑ k : Fin (K+1),
        if k.val = 0 then (0:ℝ) else r^k.val := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [source_original_P_tilted_mark_ratio z hp k.val δ]
    dsimp [r]
    split_ifs <;> ring
  rw [hSum]
  have hCap := source_original_P_geom_positive_cap r K hr0 hr1
  have hId : r/(1-r) = (D-1)⁻¹ := by
    rw [hRel]
    have hDn : D ≠ 0 := ne_of_gt hD0
    have hD1 : D-1 ≠ 0 := by linarith
    have hR1 : 1-D⁻¹ ≠ 0 := by
      have := inv_lt_one₀ hD0
      have hi : D⁻¹ < 1 := (inv_lt_one₀ hD0).mpr hD
      linarith
    field_simp
    <;> ring
  exact hCap.trans_eq hId



/- Exact source owner: SourcePTiltedBaseCap.lean; original line 27. -/
theorem source_original_P_tilted_base_finite_upper
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) (δ : ℝ)
    (hp : 3 ≤ z.val) (hD : 1 < (z.val:ℝ)^(1-δ)) :
    (∑ k : Fin (K+1), sourceOriginalPTiltBase z k.val δ) ≤
      1+(1/2:ℝ) / ((z.val:ℝ)^(1-δ)-1) := by
  rw [source_original_P_tilted_base_finite_sum_eq]
  have h := source_original_P_tilted_mark_finite_upper z K δ hp hD
  have hh := mul_le_mul_of_nonneg_left h
    (by norm_num : (0:ℝ) ≤ 1/2)
  simpa [div_eq_mul_inv] using (add_le_add_left hh 1)



/- Exact source owner: SourcePTiltedFiniteUpper.lean; original line 19. -/
theorem source_original_P_tilted_finite_upper
    (P : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (δ : ℝ) (K : ℕ)
    (hD : ∀ p ∈ P, 1 < (p:ℝ)^(1-δ)) :
    (∑ e : {p // p ∈ P} → Fin (K+1),
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P (fun z => (e z).val):ℝ)^(δ-1))) ≤
      sourceOriginalPTiltedSubtypeEnvelope P
        (fun p => (p:ℝ)^(1-δ)) := by
  classical
  let C := {p // p ∈ P}
  let M : C → ℝ := fun z =>
    ∑ k : Fin (K+1), sourceOriginalPTiltMark z k.val δ
  let F : C → ℝ := fun z =>
    ∑ k : Fin (K+1), sourceOriginalPTiltBase z k.val δ
  let D : ℕ → ℝ := fun p => (p:ℝ)^(1-δ)
  have hVpos : 0 < ∑ p ∈ P, (p:ℝ)⁻¹ := by
    apply Finset.sum_pos
    · intro p hp
      exact inv_pos.mpr (by exact_mod_cast (hPrime p hp).pos)
    · exact hPn
  have hM0 (z : C) : 0 ≤ M z := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro k hk
    unfold sourceOriginalPTiltMark sourceOriginalPVecMarkFactor
    positivity
  have hF0 (z : C) : 0 ≤ F z := by
    dsimp [F]
    apply Finset.sum_nonneg
    intro k hk
    unfold sourceOriginalPTiltBase sourceOriginalPVecBaseFactor
    positivity
  have hMupper (z : C) :
      M z ≤ (D z.val-1)⁻¹ :=
    source_original_P_tilted_mark_finite_upper
      z K δ (h3 z.val z.property) (hD z.val z.property)
  have hFupper (z : C) :
      F z ≤ 1+(1/2:ℝ)/(D z.val-1) :=
    source_original_P_tilted_base_finite_upper
      z K δ (h3 z.val z.property) (hD z.val z.property)
  have hUpos (z : C) : 0 ≤ (D z.val-1)⁻¹ := by
    have hd := hD z.val z.property
    exact (inv_pos.mpr (by dsimp [D]; linarith)).le
  have hProd0 (z : C) :
      0 ≤ ∏ w ∈ (Finset.univ : Finset C).erase z, F w :=
    Finset.prod_nonneg (fun w hw => hF0 w)
  have hProdUpper (z : C) :
      (∏ w ∈ (Finset.univ : Finset C).erase z, F w) ≤
      ∏ w ∈ (Finset.univ : Finset C).erase z,
        (1+(1/2:ℝ)/(D w.val-1)) := by
    apply Finset.prod_le_prod₀
    · intro w hw
      exact hF0 w
    · intro w hw
      exact hFupper w
  have hTermUpper (z : C) :
      M z * (∏ w ∈ (Finset.univ : Finset C).erase z, F w) ≤
      (D z.val-1)⁻¹ *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          (1+(1/2:ℝ)/(D w.val-1))) :=
    mul_le_mul (hMupper z) (hProdUpper z)
      (hProd0 z) (hUpos z)
  have hSumUpper :
      (∑ z : C, M z * (∏ w ∈ (Finset.univ : Finset C).erase z, F w)) ≤
      ∑ z : C, (D z.val-1)⁻¹ *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          (1+(1/2:ℝ)/(D w.val-1))) :=
    Finset.sum_le_sum (fun z hz => hTermUpper z)
  calc
    _ = (∑ z : C, M z *
      (∏ w ∈ (Finset.univ : Finset C).erase z, F w)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) :=
      source_original_P_W1_tilted_finite_euler P hPrime δ K
    _ ≤ (∑ z : C, (D z.val-1)⁻¹ *
       (∏ w ∈ (Finset.univ : Finset C).erase z,
          (1+(1/2:ℝ)/(D w.val-1)))) /
          (∑ p ∈ P, (p:ℝ)⁻¹) :=
      div_le_div_of_nonneg_right hSumUpper hVpos.le
    _ = sourceOriginalPTiltedSubtypeEnvelope P D := rfl



/- Exact source owner: SourcePTiltedEulerMarkIdentity.lean; original line 11. -/
theorem source_original_group_tilted_Euler_mark_identity
    (P : Finset ℕ) (D : ℕ → ℝ)
    (hD : ∀ p ∈ P, 1 < D p) :
    (∑ p ∈ P, (D p-1)⁻¹ *
      (∏ q ∈ P.erase p,
        (1+(1/2:ℝ)/(D q-1)))) /
      (∑ p ∈ P, (p:ℝ)⁻¹) =
      sourceOriginalGroupTiltedEulerMass P D := by
  classical
  let F : ℕ → ℝ := fun p => 1+(1/2:ℝ)/(D p-1)
  let T : ℝ := ∏ q ∈ P, F q
  have hterm (p : ℕ) (hp : p ∈ P) :
      (D p-1)⁻¹ * (∏ q ∈ P.erase p, F q) =
        T * (D p-(1/2:ℝ))⁻¹ := by
    have hpD := hD p hp
    have hden : D p-1 ≠ 0 := by linarith
    have hden2 : D p-(1/2:ℝ) ≠ 0 := by linarith
    have hF : F p =
      (D p-(1/2:ℝ)) * ((D p-1)⁻¹) := by
      dsimp [F]
      field_simp [hden]
      <;> ring
    have halg : (D p-1)⁻¹ =
        F p * (D p-(1/2:ℝ))⁻¹ := by
      rw [hF]
      rw [mul_assoc, mul_comm ((D p-1)⁻¹) _]
      rw [← mul_assoc, mul_inv_cancel₀ hden2]
      ring
    rw [halg]
    have heq := Finset.mul_prod_erase P F hp
    dsimp [T]
    calc
      (F p * (D p-(1/2:ℝ))⁻¹) *
         (∏ q ∈ P.erase p, F q) =
        (F p * ∏ q ∈ P.erase p, F q) *
          (D p-(1/2:ℝ))⁻¹ := by ring
      _ = _ := by rw [heq]
  have hSum : (∑ p ∈ P, (D p-1)⁻¹ *
        (∏ q ∈ P.erase p, F q)) =
      T * (∑ p ∈ P, (D p-(1/2:ℝ))⁻¹) := by
    calc
      _ = ∑ p ∈ P, T * (D p-(1/2:ℝ))⁻¹ :=
        Finset.sum_congr rfl (fun p hp => hterm p hp)
      _ = _ := by rw [Finset.mul_sum]
  change (∑ p ∈ P, (D p-1)⁻¹ *
        (∏ q ∈ P.erase p, F q)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) =
      sourceOriginalGroupTiltedEulerMass P D
  rw [hSum]
  unfold sourceOriginalGroupTiltedEulerMass
  dsimp [T,F]
  ring



/- Exact source owner: SourcePTiltedEnvelopeBridge.lean; original line 10. -/
theorem source_original_P_tilted_subtype_envelope_eq
    (P : Finset ℕ) (D : ℕ → ℝ)
    (hD : ∀ p ∈ P, 1 < D p) :
    sourceOriginalPTiltedSubtypeEnvelope P D =
      sourceOriginalGroupTiltedEulerMass P D := by
  classical
  let F : ℕ → ℝ := fun p => 1+(1/2:ℝ)/(D p-1)
  have hAll :
      (∏ w : {p // p ∈ P}, F w.val) = ∏ p ∈ P, F p := by
    simpa only [Finset.attach_eq_univ] using Finset.prod_attach P F
  have hErase (z : {p // p ∈ P}) :
      (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z, F w.val) =
      (∏ q ∈ P.erase z.val, F q) := by
    have hL := Finset.mul_prod_erase
      (Finset.univ : Finset {p // p ∈ P})
      (fun w => F w.val) (Finset.mem_univ z)
    have hR := Finset.mul_prod_erase P F z.property
    have hDlocal : 0 < D z.val - 1 := by
      have := hD z.val z.property
      linarith
    have hF0 : 0 < F z.val := by
      dsimp [F]
      have hfrac : 0 ≤ (1/2:ℝ)/(D z.val-1) :=
        div_nonneg (by norm_num) hDlocal.le
      linarith
    exact mul_left_cancel₀ (ne_of_gt hF0)
      (hL.trans (hAll.trans hR.symm))
  have hPer :
      (∑ z : {p // p ∈ P},
        (D z.val-1)⁻¹ *
          (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
            F w.val)) =
      ∑ z : {p // p ∈ P},
        (D z.val-1)⁻¹ * (∏ q ∈ P.erase z.val, F q) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hErase z]
  have hAttach :
      (∑ z : {p // p ∈ P},
        (D z.val-1)⁻¹ * (∏ q ∈ P.erase z.val, F q)) =
      ∑ p ∈ P, (D p-1)⁻¹ * (∏ q ∈ P.erase p, F q) := by
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach P
        (fun p => (D p-1)⁻¹ * (∏ q ∈ P.erase p, F q)))
  unfold sourceOriginalPTiltedSubtypeEnvelope
  rw [show
      (∑ z : {p // p ∈ P},
        (D z.val-1)⁻¹ *
          (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
            (1+(1/2:ℝ)/(D w.val-1)))) =
      ∑ z : {p // p ∈ P},
        (D z.val-1)⁻¹ *
          (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
            F w.val) from rfl]
  rw [hPer,hAttach]
  exact source_original_group_tilted_Euler_mark_identity P D hD



/- Exact source owner: SourcePTiltedGroupTsum.lean; original line 11. -/
theorem source_original_P_tilted_group_vector_tsum_le
    (P : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (δ : ℝ)
    (hD : ∀ p ∈ P, 1 < (p:ℝ)^(1-δ)) :
    Summable (fun e : {p // p ∈ P} → ℕ =>
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) *
        ((sourceOriginalPPrimePowerProduct P e:ℝ)^(δ-1))) ∧
    (∑' e : {p // p ∈ P} → ℕ,
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) *
        ((sourceOriginalPPrimePowerProduct P e:ℝ)^(δ-1))) ≤
      sourceOriginalGroupTiltedEulerMass P
        (fun p => (p:ℝ)^(1-δ)) := by
  apply source_original_P_cube_summable_of_uniform_bound P
    (fun e => shiftTwoOriginalGroupFactor P
      (sourceOriginalPPrimePowerProduct P e) *
      ((sourceOriginalPPrimePowerProduct P e:ℝ)^(δ-1)))
    (sourceOriginalGroupTiltedEulerMass P
      (fun p => (p:ℝ)^(1-δ)))
  · intro e
    have hn : 0 < (sourceOriginalPPrimePowerProduct P e:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (source_original_P_power_product_ne_zero P hPrime e)
    unfold shiftTwoOriginalGroupFactor
    positivity
  · intro K
    calc
      _ ≤ sourceOriginalPTiltedSubtypeEnvelope P
          (fun p => (p:ℝ)^(1-δ)) :=
        source_original_P_tilted_finite_upper
          P hPrime h3 hPn δ K hD
      _ = sourceOriginalGroupTiltedEulerMass P
          (fun p => (p:ℝ)^(1-δ)) :=
        source_original_P_tilted_subtype_envelope_eq
          P (fun p => (p:ℝ)^(1-δ)) hD

/- The SAME tilted estimate on real original P-supported integers
by the already verified prime-power exponent bijection. -/



/- Exact source owner: SourcePTiltedGroupTsum.lean; original line 52. -/
theorem source_original_P_tilted_actual_integer_tsum_le
    (P : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (δ : ℝ)
    (hD : ∀ p ∈ P, 1 < (p:ℝ)^(1-δ)) :
    Summable (fun n : sourceOriginalPSupported P =>
      shiftTwoOriginalGroupFactor P n.val * ((n.val:ℝ)^(δ-1))) ∧
    (∑' n : sourceOriginalPSupported P,
      shiftTwoOriginalGroupFactor P n.val * ((n.val:ℝ)^(δ-1))) ≤
      sourceOriginalGroupTiltedEulerMass P
        (fun p => (p:ℝ)^(1-δ)) := by
  let E := source_original_P_power_equiv P hPrime
  let f : sourceOriginalPSupported P → ℝ :=
    fun n => shiftTwoOriginalGroupFactor P n.val * ((n.val:ℝ)^(δ-1))
  have hVec := source_original_P_tilted_group_vector_tsum_le
    P hPrime h3 hPn δ hD
  have hMatch : (f ∘ E) =
      fun e : {p // p ∈ P} → ℕ =>
        shiftTwoOriginalGroupFactor P
          (sourceOriginalPPrimePowerProduct P e) *
          ((sourceOriginalPPrimePowerProduct P e:ℝ)^(δ-1)) := by
    funext e
    rfl
  have hSumm : Summable f :=
    (E.summable_iff).mp (by rw [hMatch]; exact hVec.1)
  have hTsum : (∑' n : sourceOriginalPSupported P, f n) =
      ∑' e : {p // p ∈ P} → ℕ, (f ∘ E) e :=
    (E.tsum_eq f).symm
  have hBound : (∑' n : sourceOriginalPSupported P, f n) ≤
      sourceOriginalGroupTiltedEulerMass P
        (fun p => (p:ℝ)^(1-δ)) := by
    rw [hTsum]
    rw [hMatch]
    exact hVec.2
  exact ⟨hSumm,hBound⟩



/- Exact source owner: SourcePTiltedSourceDeltaGroup.lean; original line 12. -/
theorem source_original_P_tilted_actual_source_delta_upper
    (P : Finset ℕ) (L : ℝ) (hL : 1 < L)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h6 : ∀ p ∈ P, 6 ≤ p)
    (hPn : P.Nonempty)
    (hV4 : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ p ∈ P, Real.log (p:ℝ) ≤ L^(2/5:ℝ)) :
    Summable (fun n : sourceOriginalPSupported P =>
      shiftTwoOriginalGroupFactor P n.val *
        ((n.val:ℝ)^(L^(-(2/5:ℝ))-1))) ∧
    (∑' n : sourceOriginalPSupported P,
      shiftTwoOriginalGroupFactor P n.val *
        ((n.val:ℝ)^(L^(-(2/5:ℝ))-1))) ≤
      6*Real.exp 12 := by
  have hL0 : 0 < L := by linarith
  have hT : 1 < L^(2/5:ℝ) :=
    Real.one_lt_rpow hL (by norm_num)
  have hT0 : 0 < L^(2/5:ℝ) :=
    Real.rpow_pos_of_pos hL0 _
  have hδlt : L^(-(2/5:ℝ)) < 1 := by
    rw [Real.rpow_neg hL0.le]
    exact (inv_lt_one₀ hT0).mpr hT
  have hD (p : ℕ) (hp : p ∈ P) :
      1 < (p:ℝ)^(1-L^(-(2/5:ℝ))) := by
    have hp6 : 6 ≤ p := h6 p hp
    have hp1 : (1:ℝ) < p := by exact_mod_cast
      (by omega : 1 < p)
    exact Real.one_lt_rpow hp1 (by linarith)
  have h3 : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have h6p := h6 p hp
    omega
  have hTsum := source_original_P_tilted_actual_integer_tsum_le
    P hPrime h3 hPn (L^(-(2/5:ℝ))) hD
  have hEuler := source_group_source_delta_two_fifths_Euler_upper
    P L hL0 hPrime h6 hPn hV4 hLog
  exact ⟨hTsum.1,hTsum.2.trans hEuler⟩



/- Exact source owner: SourcePGenericPiEmpty.lean; original line 7. -/
theorem source_tsum_pi_empty
    (A : PEmpty → Type)
    (f : (i : PEmpty) → A i → ℝ) :
    Summable (fun x : (i : PEmpty) → A i =>
      ∏ i : PEmpty, f i (x i)) ∧
    (∑' x : (i : PEmpty) → A i,
      ∏ i : PEmpty, f i (x i)) =
      ∏ i : PEmpty, ∑' a : A i, f i a := by
  classical
  haveI : Unique ((i : PEmpty) → A i) := {
    default := fun i => PEmpty.elim i
    uniq := by
      intro x
      funext i
      exact PEmpty.elim i
  }
  haveI : Fintype ((i : PEmpty) → A i) := Fintype.ofFinite _
  constructor
  · exact Summable.of_finite
  · simp [tsum_fintype, Fintype.prod_empty, Fintype.card_unique]



/- Exact source owner: SourcePGenericPiEquiv.lean; original line 9. -/
theorem source_tsum_pi_of_equiv
    {G H : Type} [Fintype G] [Fintype H]
    (e : G ≃ H)
    (A : H → Type)
    (f : (h : H) → A h → ℝ)
    (hBase :
      Summable (fun x : (g : G) → A (e g) =>
        ∏ g : G, f (e g) (x g)) ∧
      (∑' x : (g : G) → A (e g),
        ∏ g : G, f (e g) (x g)) =
        ∏ g : G, ∑' a : A (e g), f (e g) a) :
    Summable (fun x : (h : H) → A h =>
      ∏ h : H, f h (x h)) ∧
    (∑' x : (h : H) → A h,
      ∏ h : H, f h (x h)) =
      ∏ h : H, ∑' a : A h, f h a := by
  classical
  let E : ((g : G) → A (e g)) ≃ ((h : H) → A h) :=
    Equiv.piCongrLeft A e
  let F : ((h : H) → A h) → ℝ :=
    fun x => ∏ h : H, f h (x h)
  have hWeight (x : (g : G) → A (e g)) :
      F (E x) = ∏ g : G, f (e g) (x g) := by
    dsimp [F]
    rw [← e.prod_comp (fun h => f h ((E x) h))]
    apply Finset.prod_congr rfl
    intro g hg
    simp [E]
  have hPi : Summable F := by
    apply (E.summable_iff).mp
    change Summable (F ∘ E)
    have heq : (F ∘ E) =
        (fun x : (g : G) → A (e g) =>
          ∏ g : G, f (e g) (x g)) := by
      funext x
      exact hWeight x
    rw [heq]
    exact hBase.1
  refine ⟨hPi, ?_⟩
  calc
    (∑' x : (h : H) → A h,
      ∏ h : H, f h (x h)) =
      (∑' x : (g : G) → A (e g), F (E x)) :=
      (E.tsum_eq F).symm
    _ = (∑' x : (g : G) → A (e g),
      ∏ g : G, f (e g) (x g)) := by
      congr 1
      funext x
      exact hWeight x
    _ = ∏ g : G, ∑' a : A (e g), f (e g) a := hBase.2
    _ = ∏ h : H, ∑' a : A h, f h a :=
      e.prod_comp (fun h => ∑' a : A h, f h a)



/- Exact source owner: SourcePGenericPiOption.lean; original line 9. -/
theorem source_tsum_pi_option
    {G : Type} [Fintype G]
    (A : Option G → Type)
    (f : (g : Option G) → A g → ℝ)
    (hf : ∀ g, Summable (f g))
    (hn : ∀ g a, 0 ≤ f g a)
    (hRest :
      Summable (fun x : (g : G) → A (some g) =>
        ∏ g : G, f (some g) (x g)) ∧
      (∑' x : (g : G) → A (some g),
        ∏ g : G, f (some g) (x g)) =
        ∏ g : G, ∑' a : A (some g), f (some g) a) :
    Summable (fun x : (g : Option G) → A g =>
      ∏ g : Option G, f g (x g)) ∧
    (∑' x : (g : Option G) → A g,
      ∏ g : Option G, f g (x g)) =
        ∏ g : Option G, ∑' a : A g, f g a := by
  classical
  let T := (g : G) → A (some g)
  let F : T → ℝ := fun x => ∏ g : G, f (some g) (x g)
  let F0 : A none → ℝ := f none
  let E : ((g : Option G) → A g) ≃ A none × T :=
    Equiv.piOptionEquivProd
  have hF0 : Summable F0 := hf none
  have hF : Summable F := hRest.1
  have hFN : ∀ x : T, 0 ≤ F x := by
    intro x
    dsimp [F]
    apply Finset.prod_nonneg
    intro g hg
    exact hn (some g) (x g)
  have hPair : Summable
      (fun z : A none × T => F0 z.1 * F z.2) :=
    Summable.mul_of_nonneg hF0 hF (hn none) hFN
  have hWeight (x : (g : Option G) → A g) :
      (∏ g : Option G, f g (x g)) = F0 (E x).1 * F (E x).2 := by
    rw [Fintype.prod_option]
    rfl
  have hPi : Summable (fun x : (g : Option G) → A g =>
      ∏ g : Option G, f g (x g)) := by
    have hPre : Summable
        ((fun z : A none × T => F0 z.1 * F z.2) ∘ E) :=
      (E.summable_iff).mpr hPair
    convert hPre using 1
    funext x
    exact hWeight x
  refine ⟨hPi, ?_⟩
  calc
    (∑' x : (g : Option G) → A g,
      ∏ g : Option G, f g (x g)) =
        ∑' x : (g : Option G) → A g,
          F0 (E x).1 * F (E x).2 := by
            congr 1
            funext x
            exact hWeight x
    _ = ∑' z : A none × T, F0 z.1 * F z.2 :=
      E.tsum_eq (fun z : A none × T => F0 z.1 * F z.2)
    _ = (∑' a : A none, F0 a) * (∑' x : T, F x) :=
      (hF0.tsum_mul_tsum hF hPair).symm
    _ = (∑' a : A none, f none a) *
        (∏ g : G, ∑' a : A (some g), f (some g) a) := by
          simpa only [F0,F,T] using
            congrArg (fun x : ℝ => (∑' a : A none, f none a)*x)
              hRest.2
    _ = ∏ g : Option G, ∑' a : A g, f g a := by
      rw [Fintype.prod_option]



/- Exact source owner: SourcePGenericPiProductTsum.lean; original line 12. -/
theorem source_tsum_pi_finite_product
    {G : Type} [Fintype G]
    (A : G → Type)
    (f : (g : G) → A g → ℝ)
    (hf : ∀ g, Summable (f g))
    (hn : ∀ g a, 0 ≤ f g a) :
    Summable (fun x : (g : G) → A g =>
      ∏ g : G, f g (x g)) ∧
    (∑' x : (g : G) → A g,
      ∏ g : G, f g (x g)) =
        ∏ g : G, ∑' a : A g, f g a := by
  classical
  let Goal (X : Type) [Fintype X] : Prop :=
    ∀ (C : X → Type) (w : (x : X) → C x → ℝ),
      (∀ x, Summable (w x)) →
      (∀ x c, 0 ≤ w x c) →
      Summable (fun s : (x : X) → C x =>
        ∏ x : X, w x (s x)) ∧
      (∑' s : (x : X) → C x,
        ∏ x : X, w x (s x)) =
          ∏ x : X, ∑' c : C x, w x c
  have hAll : Goal G := by
    apply Fintype.induction_empty_option (P := Goal)
    · intro X Y instY eq hX C w hw hnonneg
      letI : Fintype X := Fintype.ofEquiv Y eq.symm
      let Cx : X → Type := fun x => C (eq x)
      let wx : (x : X) → Cx x → ℝ :=
        fun x c => w (eq x) c
      have hSource := hX Cx wx
        (fun x => hw (eq x))
        (fun x c => hnonneg (eq x) c)
      exact source_tsum_pi_of_equiv eq C w hSource
    · intro C w hw hnonneg
      exact source_tsum_pi_empty C w
    · intro X instX hX C w hw hnonneg
      exact source_tsum_pi_option C w hw hnonneg
        (hX (fun x => C (some x))
          (fun x c => w (some x) c)
          (fun x => hw (some x))
          (fun x c => hnonneg (some x) c))
  exact hAll A f hf hn



/- Exact source owner: SourcePTiltedGlobalMoment.lean; original line 13. -/
theorem source_original_P_global_tilted_source_moment
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (L : ℝ) (hL : 1 < L)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h6 : ∀ g p, p ∈ P g → 6 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ g p, p ∈ P g →
      Real.log (p:ℝ) ≤ L^(2/5:ℝ)) :
    Summable (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
      sourceOriginalW1 P n.val *
        ((n.val:ℝ)^(L^(-(2/5:ℝ))-1))) ∧
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      sourceOriginalW1 P n.val *
        ((n.val:ℝ)^(L^(-(2/5:ℝ))-1))) ≤
      (6*Real.exp 12)^(Fintype.card G) := by
  classical
  let δ : ℝ := L^(-(2/5:ℝ))
  let A (g : G) := {p // p ∈ P g} → ℕ
  let f (g : G) (e : A g) : ℝ :=
    shiftTwoOriginalGroupFactor (P g)
      (sourceOriginalPPrimePowerProduct (P g) e) *
      ((sourceOriginalPPrimePowerProduct (P g) e:ℝ)^(δ-1))
  let Pall : Finset ℕ := Finset.univ.biUnion P
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  let E : ((g : G) → A g) ≃ sourceOriginalPSupported Pall :=
    (sourceOriginalPDisjointExponentEquiv P hDisj).trans
      (source_original_P_power_equiv Pall hAll)
  have hLocal (g : G) : Summable (f g) ∧
      (∑' e : A g, f g e) ≤ 6 * Real.exp 12 := by
    have h := source_original_P_tilted_actual_source_delta_upper
      (P g) L hL (hPrime g) (h6 g) (hPn g) (hV4 g) (hLog g)
    let Eg := source_original_P_power_equiv (P g) (hPrime g)
    have hEq : (fun n : sourceOriginalPSupported (P g) =>
        shiftTwoOriginalGroupFactor (P g) n.val *
          ((n.val:ℝ)^(L^(-(2/5:ℝ))-1))) ∘ Eg = f g := by
      funext e
      rfl
    constructor
    · rw [← hEq]
      exact (Eg.summable_iff).mpr h.1
    · calc
        (∑' e : A g, f g e) =
            ∑' n : sourceOriginalPSupported (P g),
              shiftTwoOriginalGroupFactor (P g) n.val *
                ((n.val:ℝ)^(L^(-(2/5:ℝ))-1)) := by
                  rw [← hEq]
                  exact Eg.tsum_eq (fun n : sourceOriginalPSupported (P g) =>
                    shiftTwoOriginalGroupFactor (P g) n.val *
                      ((n.val:ℝ)^(L^(-(2/5:ℝ))-1)))
        _ ≤ _ := h.2
  have hNonneg (g : G) (e : A g) : 0 ≤ f g e := by
    dsimp [f]
    unfold shiftTwoOriginalGroupFactor
    positivity
  have hProd := source_tsum_pi_finite_product A f
    (fun g => (hLocal g).1) hNonneg
  let F : sourceOriginalPSupported Pall → ℝ := fun n =>
    sourceOriginalW1 P n.val * ((n.val:ℝ)^(δ-1))
  have hPoint (e : (g : G) → A g) :
      F (E e) = ∏ g : G, f g (e g) := by
    dsimp [F, E, f]
    change sourceOriginalW1 P
      (sourceOriginalPPrimePowerProduct Pall
        (sourceOriginalPDisjointExponentEquiv P hDisj e)) *
      ((sourceOriginalPPrimePowerProduct Pall
        (sourceOriginalPDisjointExponentEquiv P hDisj e):ℝ)^(δ-1)) = _
    rw [← source_original_P_global_vector_product_eq P hPrime hDisj e]
    exact source_original_P_global_W1_tilted_pointwise P hPrime hDisj e δ
  have hMatch : (F ∘ E) = (fun e : (g : G) → A g =>
      ∏ g : G, f g (e g)) := funext hPoint
  have hSumm : Summable F :=
    (E.summable_iff).mp (by rw [hMatch]; exact hProd.1)
  have hBound : (∑' n : sourceOriginalPSupported Pall, F n) ≤
      (6*Real.exp 12)^(Fintype.card G) := by
    rw [← E.tsum_eq F]
    change (∑' e, (F ∘ E) e) ≤ _
    rw [hMatch, hProd.2]
    calc
      (∏ g : G, ∑' a : A g, f g a) ≤
          ∏ _g : G, (6 * Real.exp 12) := by
            apply Finset.prod_le_prod₀
            · intro g hg
              exact tsum_nonneg (hNonneg g)
            · intro g hg
              exact (hLocal g).2
      _ = _ := by simp
  exact ⟨hSumm, hBound⟩



/- Exact source owner: SourcePRankinRestrictedTsum.lean; original line 9. -/
theorem source_original_P_rankin_restricted_tsum
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (δ B : ℝ)
    (hWeight : ∀ n, 0 ≤ sourceOriginalW1 P n)
    (hMoment : Summable (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
       sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1))))
    (hBound : (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
       sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1))) ≤ B)
    (threshold cutoff : ℝ) (hc : 0 ≤ cutoff)
    (hPower : ∀ n : sourceOriginalPSupported (Finset.univ.biUnion P),
      threshold < (n.val : ℝ) → 1 ≤ cutoff * ((n.val : ℝ) ^ δ)) :
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if threshold < (n.val : ℝ) then
        sourceOriginalW1 P n.val / (n.val : ℝ) else 0) ≤ cutoff * B := by
  have hnonneg : ∀ n : sourceOriginalPSupported (Finset.univ.biUnion P),
      0 ≤ sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1)) := by
    intro n
    exact mul_nonneg (hWeight _) (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le n.val) _)
  have hsumm : Summable (fun n : sourceOriginalPSupported (Finset.univ.biUnion P) =>
      cutoff * (sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1)))) :=
    hMoment.mul_left cutoff
  have hlt : ∀ n : sourceOriginalPSupported (Finset.univ.biUnion P),
       (if threshold < (n.val : ℝ) then
         sourceOriginalW1 P n.val / (n.val : ℝ) else 0) ≤
       cutoff * (sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1))) := by
    intro n
    split_ifs with hn
    · have hnpos : (0:ℝ) < n.val := by exact_mod_cast Nat.pos_of_ne_zero n.property.1
      have hi : 0 ≤ sourceOriginalW1 P n.val * ((n.val : ℝ)⁻¹) :=
        mul_nonneg (hWeight _) (inv_nonneg.mpr (le_of_lt hnpos))
      calc
        sourceOriginalW1 P n.val / (n.val : ℝ) =
            (sourceOriginalW1 P n.val * (n.val:ℝ)⁻¹) * 1 := by ring
        _ ≤ (sourceOriginalW1 P n.val * (n.val:ℝ)⁻¹) *
            (cutoff * (n.val:ℝ)^δ) := mul_le_mul_of_nonneg_left (hPower n hn) hi
        _ = cutoff * (sourceOriginalW1 P n.val * ((n.val:ℝ)^(δ-1))) := by
          rw [Real.rpow_sub hnpos δ 1, Real.rpow_one]
          ring
    · exact mul_nonneg hc (hnonneg n)
  calc
    _ ≤ ∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
       cutoff * (sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1))) :=
         (Summable.tsum_le_tsum hlt (hsumm.of_nonneg_of_le
           (fun n => by
             split_ifs with hn
             · exact div_nonneg (hWeight _) (by exact_mod_cast Nat.zero_le n.val)
             · exact le_refl 0) hlt) hsumm)
    _ = cutoff * (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
       sourceOriginalW1 P n.val * ((n.val : ℝ) ^ (δ - 1))) := tsum_mul_left
    _ ≤ cutoff * B := mul_le_mul_of_nonneg_left hBound hc



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 85. -/
theorem source_original_W1_nonneg
    {G : Type} [Fintype G] (P : G → Finset ℕ) (u : ℕ) :
    0 ≤ sourceOriginalW1 P u := by
  unfold sourceOriginalW1
  apply Finset.prod_nonneg
  intro g hg
  unfold shiftTwoOriginalGroupFactor
  positivity


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Mass004 -/

section

set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
open Filter Topology Asymptotics
open scoped BigOperators Classical
noncomputable section

namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourcePGlobalRankinTail.lean; original line 10. -/
theorem source_original_P_global_rankin_tail_by_power
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (L : ℝ) (hL : 1 < L)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h6 : ∀ g p, p ∈ P g → 6 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ g p, p ∈ P g → Real.log (p:ℝ) ≤ L^(2/5:ℝ))
    (threshold cutoff : ℝ) (hc : 0 ≤ cutoff)
    (hPower : ∀ n : sourceOriginalPSupported (Finset.univ.biUnion P),
      threshold < (n.val : ℝ) →
        1 ≤ cutoff * ((n.val:ℝ)^(L^(-(2/5:ℝ))))) :
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if threshold < (n.val : ℝ) then
        sourceOriginalW1 P n.val / (n.val : ℝ) else 0) ≤
      cutoff * (6 * Real.exp 12)^(Fintype.card G) := by
  obtain ⟨hs, hb⟩ := source_original_P_global_tilted_source_moment
    P L hL hPrime h6 hPn hDisj hV4 hLog
  exact source_original_P_rankin_restricted_tsum P
    (L^(-(2/5:ℝ))) ((6 * Real.exp 12)^(Fintype.card G))
    (source_original_W1_nonneg P) hs hb threshold cutoff hc hPower



/- Exact source owner: SourcePGlobalActualTail.lean; original line 9. -/
theorem source_original_P_global_actual_rankin_tail
    {G : Type} [Fintype G]
    (P : G → Finset ℕ) (L σ : ℝ) (hL : 1 < L) (hσ : 0 < σ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h6 : ∀ g p, p ∈ P g → 6 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ g p, p ∈ P g → Real.log (p:ℝ) ≤ L^(2/5:ℝ)) :
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (Real.exp L)^σ < (n.val : ℝ) then
        sourceOriginalW1 P n.val / (n.val : ℝ) else 0) ≤
      (6 * Real.exp 12)^(Fintype.card G) *
        Real.exp (-σ * L^(3/5:ℝ)) := by
  have hLp : (0:ℝ) < L := by linarith
  let δ : ℝ := L^(-(2/5:ℝ))
  let C : ℝ := Real.exp (-σ * L^(3/5:ℝ))
  have hδ : 0 < δ := Real.rpow_pos_of_pos hLp _
  have hidentity : L * δ = L^(3/5:ℝ) := by
    dsimp [δ]
    calc
      L * L^(-(2/5:ℝ)) = L^(1:ℝ) * L^(-(2/5:ℝ)) := by rw [Real.rpow_one]
      _ = L^(1 + -(2/5:ℝ)) := (Real.rpow_add hLp _ _).symm
      _ = L^(3/5:ℝ) := by norm_num
  have hthreshold : (Real.exp L)^σ = Real.exp (σ * L) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hPow : ∀ n : sourceOriginalPSupported (Finset.univ.biUnion P),
      (Real.exp L)^σ < (n.val : ℝ) → 1 ≤ C * ((n.val:ℝ)^δ) := by
    intro n hn
    rw [hthreshold] at hn
    have hbase : (Real.exp (σ*L))^δ ≤ (n.val:ℝ)^δ :=
      Real.rpow_le_rpow (le_of_lt (Real.exp_pos _)) (le_of_lt hn) (le_of_lt hδ)
    have heq : (Real.exp (σ*L))^δ = Real.exp (σ*L^(3/5:ℝ)) := by
      rw [← Real.exp_mul]
      congr 1
      rw [← hidentity]
      ring
    have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
    calc
      1 = C * Real.exp (σ * L^(3/5:ℝ)) := by
        dsimp [C]
        rw [show -σ * L^(3/5:ℝ) = -(σ * L^(3/5:ℝ)) by ring, Real.exp_neg]
        exact (inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))).symm
      _ = C * (Real.exp (σ*L))^δ := by rw [heq]
      _ ≤ C * (n.val:ℝ)^δ := mul_le_mul_of_nonneg_left hbase hC
  have hResult := source_original_P_global_rankin_tail_by_power
    P L hL hPrime h6 hPn hDisj hV4 hLog
    ((Real.exp L)^σ) C (le_of_lt (Real.exp_pos _)) (by
      intro n hn
      exact hPow n hn)
  dsimp [C] at hResult
  simpa only [mul_comm] using hResult



/- Exact source owner: SourcePOriginalPolylogTail.lean; original line 11. -/
theorem source_original_P_actual_polylog_rankin_tail
    (r₀ : ℕ) (L σ : ℝ) (hr₀ : 1 ≤ r₀)
    (hL : Real.exp 1 ≤ L) (hσ : 0 < σ)
    (P : sourceOriginalPAllGroupType r₀ L → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (h6 : ∀ g p, p ∈ P g → 6 ≤ p)
    (hPn : ∀ g, (P g).Nonempty)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (hV4 : ∀ g, (∑ p ∈ P g, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ g p, p ∈ P g → Real.log (p:ℝ) ≤ L^(2/5:ℝ)) :
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (Real.exp L)^σ < (n.val : ℝ) then
        sourceOriginalW1 P n.val / (n.val : ℝ) else 0) ≤
      L ^ ((3 + (Real.log 2)⁻¹) * Real.log (6 * Real.exp 12)) *
        Real.exp (-σ * L^(3/5:ℝ)) := by
  have hExp : 1 < Real.exp (1:ℝ) := by
    have hh : Real.exp (0:ℝ) < Real.exp 1 :=
      Real.exp_strictMono (by norm_num)
    simpa using hh
  have hLgt : 1 < L := hExp.trans_le hL
  have hTail := source_original_P_global_actual_rankin_tail
    P L σ hLgt hσ hPrime h6 hPn hDisj hV4 hLog
  have hPoly := source_original_P_all_group_factor_polylog r₀ L hr₀ hL
  calc
    _ ≤ (6 * Real.exp 12) ^
        (Fintype.card (sourceOriginalPAllGroupType r₀ L)) *
        Real.exp (-σ * L^(3/5:ℝ)) := hTail
    _ ≤ L ^ ((3 + (Real.log 2)⁻¹) * Real.log (6 * Real.exp 12)) *
        Real.exp (-σ * L^(3/5:ℝ)) :=
          mul_le_mul_of_nonneg_right hPoly (le_of_lt (Real.exp_pos _))



/- Exact source owner: SourcePActualEvenTsum.lean; original line 8. -/
def sourceOriginalPEvenSupported (P : Finset ℕ) : Type :=
  {n : sourceOriginalPSupported P //
    Even (sourceOriginalPParityExponent P n.val)}

/- Inclusion of true products p*q, with p and q from source
subbands A and B, in the actual even-Ω P-supported integers. -/



/- Exact source owner: SourcePActualOddTsum.lean; original line 9. -/
def sourceOriginalPOddSupported (P : Finset ℕ) : Type :=
  {n : sourceOriginalPSupported P //
    Odd (sourceOriginalPParityExponent P n.val)}



/- Exact source owner: SourcePPrimePowerOrdinary.lean; original line 42. -/
noncomputable def sourceOriginalPHarmonicTsum
    {G : Type} [Fintype G] (P : G → Finset ℕ) : ℝ :=
  ∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
    sourceOriginalW1 P n.val / (n.val:ℝ)

/- GENUINE infinite weighted bijection: every P-exponent
assignment is mapped to its actual positive P-part integer.
This is a direct reindexing of the ORIGINAL W1 harmonic series,
not a postulated product sampling distribution. -/



/- Exact source owner: SourcePConditionalProductParity.lean; original line 10. -/
theorem source_conditional_two_factor_parity_tsum_floor
    {A B : Type}
    (f : A → ℝ) (g : B → ℝ)
    (p : A → Bool) (q : B → Bool) (δ : ℝ)
    (hf : Summable f) (hg : Summable g)
    (hfN : ∀ a, 0 ≤ f a) (hgN : ∀ b, 0 ≤ g b)
    (hFlags : ∀ b : Bool,
       δ * (∑' a : A, f a) ≤
         ∑' a : A, if p a ≠ b then f a else 0) :
    δ * (∑' a : A, f a) * (∑' b : B, g b) ≤
      ∑' z : A × B,
        if p z.1 ≠ q z.2 then f z.1 * g z.2 else 0 := by
  classical
  let F : B × A → ℝ :=
    fun z => if p z.2 ≠ q z.1 then g z.1 * f z.2 else 0
  have hProd : Summable (fun z : B × A => g z.1 * f z.2) :=
    Summable.mul_of_nonneg hg hf hgN hfN
  have hFN (z : B × A) : 0 ≤ F z := by
    by_cases heq : p z.2 = q z.1
    · simp [F,heq]
    · simpa [F,heq] using mul_nonneg (hgN z.1) (hfN z.2)
  have hFU (z : B × A) : F z ≤ g z.1 * f z.2 := by
    by_cases heq : p z.2 = q z.1
    · simpa [F,heq] using mul_nonneg (hgN z.1) (hfN z.2)
    · simp [F,heq]
  have hFS : Summable F :=
    Summable.of_nonneg_of_le hFN hFU hProd
  have hFibre (b : B) :
      (∑' a : A, F (b,a)) =
        g b * (∑' a : A, if p a ≠ q b then f a else 0) := by
    have hh : (fun a : A => F (b,a)) =
        (fun a : A => g b * (if p a ≠ q b then f a else 0)) := by
      funext a
      by_cases hp : p a ≠ q b
      · simp [F,hp]
      · simp [F,hp]
    rw [hh,tsum_mul_left]
  have hBound (b : B) :
      g b * (δ * (∑' a : A, f a)) ≤ ∑' a : A, F (b,a) := by
    rw [hFibre]
    exact mul_le_mul_of_nonneg_left (hFlags (q b)) (hgN b)
  have hLS : Summable
      (fun b : B => g b * (δ * (∑' a : A, f a))) :=
    hg.mul_right _
  have hRS : Summable (fun b : B => ∑' a : A, F (b,a)) :=
    hFS.prod
  have hTotal := hLS.tsum_le_tsum hBound hRS
  rw [tsum_mul_right] at hTotal
  rw [← hFS.tsum_prod] at hTotal
  calc
    δ * (∑' a : A, f a) * (∑' b : B, g b) =
      (∑' b : B, g b) * (δ * (∑' a : A, f a)) := by ring
    _ ≤ ∑' z : B × A, F z := hTotal
    _ = ∑' z : A × B,
          if p z.1 ≠ q z.2 then f z.1 * g z.2 else 0 := by
      rw [←(Equiv.prodComm A B).tsum_eq F]
      congr 1
      funext z
      dsimp [F]
      by_cases hp : p z.1 ≠ q z.2
      · simp [hp, mul_comm]
      · simp [hp]



/- Exact source owner: SourcePParityBoolLemmas.lean; original line 7. -/
theorem source_odd_add_decide_xor (a b : ℕ) :
    Odd (a+b) ↔ decide (Odd a) ≠ decide (Odd b) := by
  rw [Nat.odd_add]
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · simp [ha,hb, Nat.not_odd_iff_even.mp]
    · simp [ha,hb, Nat.not_odd_iff_even.mp hb]
  · by_cases hb : Odd b
    · simp [ha,hb]
    · simp [ha,hb,Nat.not_odd_iff_even.mp hb]



/- Exact source owner: SourcePGlobalSplitParity.lean; original line 10. -/
theorem source_pi_split_odd_iff
    {G : Type} [Fintype G] [DecidableEq G]
    (A : G → Type) (k : (g : G) → A g → ℕ)
    (i : G) (a : A i)
    (rest : (j : {j : G // j ≠ i}) → A j.val) :
    Odd (∑ g : G, k g ((Equiv.piSplitAt i A).symm (a,rest) g)) ↔
      decide (Odd (k i a)) ≠
        decide (Odd (∑ j : {j : G // j ≠ i}, k j.val (rest j))) := by
  classical
  let E := Equiv.piSplitAt i A
  have hFirst : E.symm (a,rest) i = a := by
    have hh := congrArg Prod.fst (E.apply_symm_apply (a,rest))
    simpa only [E, Equiv.piSplitAt_apply] using hh
  have hRest (j : {j : G // j ≠ i}) :
      E.symm (a,rest) j.val = rest j := by
    have hh := congrArg (fun pair => pair.2 j)
      (E.apply_symm_apply (a,rest))
    simpa only [E, Equiv.piSplitAt_apply] using hh
  have hErase :
      (∑ g ∈ (Finset.univ : Finset G).erase i,
        k g (E.symm (a,rest) g)) =
      ∑ j : {j : G // j ≠ i}, k j.val (rest j) := by
    rw [Finset.sum_subtype (p := fun g : G => g ≠ i)
      (Finset.univ.erase i)
      (by intro g; simp) (fun g => k g (E.symm (a,rest) g))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hRest j]
  have hSum :
      (∑ g : G, k g (E.symm (a,rest) g)) =
      k i a + (∑ j : {j : G // j ≠ i}, k j.val (rest j)) := by
    calc
      _ = k i (E.symm (a,rest) i) +
          (∑ g ∈ (Finset.univ : Finset G).erase i,
            k g (E.symm (a,rest) g)) :=
        (Finset.add_sum_erase Finset.univ
          (fun g => k g (E.symm (a,rest) g))
          (Finset.mem_univ i)).symm
      _ = _ := by rw [hFirst,hErase]
  rw [hSum]
  exact source_odd_add_decide_xor _ _



/- Exact source owner: SourcePGlobalSplitWeight.lean; original line 8. -/
theorem source_pi_split_weight
    {G : Type} [Fintype G] [DecidableEq G]
    (A : G → Type) (w : (g : G) → A g → ℝ)
    (i : G) (a : A i)
    (rest : (j : {j : G // j ≠ i}) → A j.val) :
    (∏ g : G,
        w g ((Equiv.piSplitAt i A).symm (a,rest) g)) =
      w i a * (∏ j : {j : G // j ≠ i}, w j.val (rest j)) := by
  classical
  let E := Equiv.piSplitAt i A
  have hFirst : E.symm (a,rest) i = a := by
    have hh := congrArg Prod.fst (E.apply_symm_apply (a,rest))
    simpa only [E, Equiv.piSplitAt_apply] using hh
  have hRest (j : {j : G // j ≠ i}) :
      E.symm (a,rest) j.val = rest j := by
    have hh := congrArg (fun pair => pair.2 j)
      (E.apply_symm_apply (a,rest))
    simpa only [E, Equiv.piSplitAt_apply] using hh
  have hErase :
      (∏ g ∈ (Finset.univ : Finset G).erase i,
        w g (E.symm (a,rest) g)) =
      ∏ j : {j : G // j ≠ i}, w j.val (rest j) := by
    rw [Finset.prod_subtype (p := fun g : G => g ≠ i)
      (Finset.univ.erase i)
      (by intro g; simp) (fun g => w g (E.symm (a,rest) g))]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hRest j]
  calc
    (∏ g : G, w g (E.symm (a,rest) g)) =
      w i (E.symm (a,rest) i) *
        (∏ g ∈ (Finset.univ : Finset G).erase i,
          w g (E.symm (a,rest) g)) :=
      (Finset.mul_prod_erase Finset.univ
        (fun g => w g (E.symm (a,rest) g))
        (Finset.mem_univ i)).symm
    _ = w i a * (∏ j : {j : G // j ≠ i}, w j.val (rest j)) := by
      rw [hFirst,hErase]



/- Exact source owner: SourcePGlobalConditionalPiParity.lean; original line 11. -/
theorem source_conditional_finite_pi_odd_tsum_floor
    {G : Type} [Fintype G] [DecidableEq G]
    (A : G → Type) (f : (g : G) → A g → ℝ)
    (k : (g : G) → A g → ℕ)
    (i : G) (δ : ℝ)
    (hf : ∀ g, Summable (f g))
    (hn : ∀ g a, 0 ≤ f g a)
    (hLocal : ∀ b : Bool,
      δ * (∑' a : A i, f i a) ≤
        ∑' a : A i,
          if decide (Odd (k i a)) ≠ b then f i a else 0) :
    δ * (∑' x : (g : G) → A g,
      ∏ g : G, f g (x g)) ≤
      ∑' x : (g : G) → A g,
        if Odd (∑ g : G, k g (x g))
        then ∏ g : G, f g (x g) else 0 := by
  classical
  let J := {g : G // g ≠ i}
  let B := (j : J) → A j.val
  let E : ((g : G) → A g) ≃ A i × B :=
    Equiv.piSplitAt i A
  let w : B → ℝ := fun r =>
    ∏ j : J, f j.val (r j)
  let kp : A i → Bool := fun a => decide (Odd (k i a))
  let kq : B → Bool :=
    fun r => decide (Odd (∑ j : J, k j.val (r j)))
  let F : ((g : G) → A g) → ℝ :=
    fun x => ∏ g : G, f g (x g)
  have hRest := source_tsum_pi_finite_product
    (fun j : J => A j.val)
    (fun j a => f j.val a)
    (fun j => hf j.val)
    (fun j a => hn j.val a)
  have hW : Summable w := hRest.1
  have hWN : ∀ r : B, 0 ≤ w r := by
    intro r
    dsimp [w]
    apply Finset.prod_nonneg
    intro j hj
    exact hn j.val (r j)
  have hPair : Summable (fun z : A i × B => f i z.1 * w z.2) :=
    Summable.mul_of_nonneg (hf i) hW (hn i) hWN
  have hSplitWeight (z : A i × B) :
      F (E.symm z) = f i z.1 * w z.2 := by
    rcases z with ⟨a,r⟩
    exact source_pi_split_weight A f i a r
  have hSplitOdd (z : A i × B) :
      Odd (∑ g : G, k g (E.symm z g)) ↔
        kp z.1 ≠ kq z.2 := by
    rcases z with ⟨a,r⟩
    exact source_pi_split_odd_iff A k i a r
  have hFull :
      (∑' x : (g : G) → A g, F x) =
        (∑' a : A i, f i a) * (∑' r : B, w r) := by
    calc
      _ = ∑' z : A i × B, F (E.symm z) :=
        (E.symm.tsum_eq F).symm
      _ = ∑' z : A i × B, f i z.1 * w z.2 := by
        apply tsum_congr
        intro z
        exact hSplitWeight z
      _ = (∑' a : A i, f i a) * (∑' r : B, w r) :=
        ((hf i).tsum_mul_tsum hW hPair).symm
  have hFlagMass :
      (∑' x : (g : G) → A g,
        if Odd (∑ g : G, k g (x g)) then F x else 0) =
      ∑' z : A i × B,
        if kp z.1 ≠ kq z.2 then f i z.1 * w z.2 else 0 := by
    calc
      _ = ∑' z : A i × B,
          if Odd (∑ g : G, k g (E.symm z g))
          then F (E.symm z) else 0 :=
        (E.symm.tsum_eq
          (fun x : (g : G) → A g =>
            if Odd (∑ g : G, k g (x g)) then F x else 0)).symm
      _ = ∑' z : A i × B,
          if kp z.1 ≠ kq z.2 then f i z.1 * w z.2 else 0 := by
        apply tsum_congr
        intro z
        rw [hSplitWeight]
        by_cases hh : Odd (∑ g : G, k g (E.symm z g))
        · simp [hh, (hSplitOdd z).mp hh]
        · simp [hh, (hSplitOdd z).not.mp hh]
  have hCond := source_conditional_two_factor_parity_tsum_floor
    (f i) w kp kq δ (hf i) hW (hn i) hWN
    (by
      intro b
      exact hLocal b)
  change δ * (∑' x : (g : G) → A g, F x) ≤
    (∑' x : (g : G) → A g,
      if Odd (∑ g : G, k g (x g)) then F x else 0)
  calc
    δ * (∑' x : (g : G) → A g, F x) =
      δ * ((∑' a : A i, f i a) * (∑' r : B, w r)) := by
        rw [hFull]
    _ ≤ ∑' z : A i × B,
        if kp z.1 ≠ kq z.2 then f i z.1 * w z.2 else 0 := by
          convert hCond using 1 <;> ring
    _ = _ := hFlagMass.symm



/- Exact source owner: SourcePGlobalSeriesReindex.lean; original line 9. -/
theorem source_original_P_global_integer_harmonic_factorization
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ) :
    sourceOriginalW1 P (sourceOriginalPGlobalVectorProduct P e) /
      ((sourceOriginalPGlobalVectorProduct P e:ℝ)) =
      ∏ g : G,
        shiftTwoOriginalGroupFactor (P g)
            (sourceOriginalPPrimePowerProduct (P g) (e g)) /
          ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)) := by
  have hW := source_original_P_global_W1_factorization
    P hPrime hDisj e
  have hD :
      ((sourceOriginalPGlobalVectorProduct P e:ℝ)⁻¹) =
        ∏ g : G,
          ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)⁻¹) := by
    unfold sourceOriginalPGlobalVectorProduct
    simp only [Nat.cast_prod]
    rw [Finset.prod_inv_distrib]
  rw [div_eq_mul_inv,hW,hD,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [div_eq_mul_inv]

/- EXACT global ORIGINAL W1 harmonic series after the verified
integer P-group bijection. This is not an assumed distribution:
the outer infinite source supported-integer sum has been reindexed
into independent group prime-power coordinates, with exact weights. -/



/- Exact source owner: SourcePGlobalWeightParity.lean; original line 73. -/
theorem source_original_P_global_parity_exponent_sum
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ) :
    sourceOriginalPParityExponent (Finset.univ.biUnion P)
      (sourceOriginalPGlobalVectorProduct P e) =
      ∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)) := by
  classical
  have hSetDisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset G)) P := by
    intro g hg h hh hne
    apply Finset.disjoint_left.mpr
    intro p hpg hph
    exact hne (hDisj g h p hpg hph)
  unfold sourceOriginalPParityExponent
  rw [Finset.sum_biUnion hSetDisj]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro p hp
  exact (source_original_P_global_factorization_at
    P hPrime hDisj e g p hp).trans
      (source_original_P_power_factorization_at
        (P g) (hPrime g) (e g) p hp).symm



/- Exact source owner: SourcePGlobalOddTsumReindex.lean; original line 13. -/
theorem source_original_P_global_actual_odd_tsum_reindex
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    (∑' n : sourceOriginalPSupported (Finset.univ.biUnion P),
      if Odd (sourceOriginalPParityExponent
        (Finset.univ.biUnion P) n.val)
      then sourceOriginalW1 P n.val / (n.val:ℝ)
      else 0) =
    ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
      if Odd (∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)))
      then ∏ g : G,
        shiftTwoOriginalGroupFactor (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)) /
        ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ)
      else 0 := by
  classical
  let Pall : Finset ℕ := Finset.univ.biUnion P
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  let E : ((g : G) → {p // p ∈ P g} → ℕ) ≃
    sourceOriginalPSupported Pall :=
    (sourceOriginalPDisjointExponentEquiv P hDisj).trans
      (source_original_P_power_equiv Pall hAll)
  let F : sourceOriginalPSupported Pall → ℝ :=
    fun n => if Odd (sourceOriginalPParityExponent Pall n.val)
      then sourceOriginalW1 P n.val / (n.val:ℝ)
      else 0
  have hPoint (e : (g : G) → {p // p ∈ P g} → ℕ) :
      F (E e) =
      (if Odd (∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)))
      then ∏ g : G,
        shiftTwoOriginalGroupFactor (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)) /
        ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ)
      else 0) := by
    have hVal : (E e).val =
        sourceOriginalPGlobalVectorProduct P e := by
      change sourceOriginalPPrimePowerProduct Pall
        (sourceOriginalPDisjointExponentEquiv P hDisj e) =
          sourceOriginalPGlobalVectorProduct P e
      exact (source_original_P_global_vector_product_eq
        P hPrime hDisj e).symm
    have hParity : Odd (sourceOriginalPParityExponent Pall
        (E e).val) ↔
      Odd (∑ g : G, sourceOriginalPParityExponent (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g))) := by
      rw [hVal, source_original_P_global_parity_exponent_sum
        P hPrime hDisj e]
    have hWeight :
        sourceOriginalW1 P (E e).val / ((E e).val:ℝ) =
          ∏ g : G,
            shiftTwoOriginalGroupFactor (P g)
              (sourceOriginalPPrimePowerProduct (P g) (e g)) /
              ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ) := by
      rw [hVal]
      exact source_original_P_global_integer_harmonic_factorization
        P hPrime hDisj e
    by_cases hh : Odd (sourceOriginalPParityExponent Pall (E e).val)
    · have hSum := hParity.mp hh
      dsimp [F]
      simp only [if_pos hh, if_pos hSum]
      exact hWeight
    · have hSum := hParity.not.mp hh
      dsimp [F]
      simp only [if_neg hh, if_neg hSum]
  calc
    (∑' n : sourceOriginalPSupported Pall, F n) =
      ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
        F (E e) := (E.tsum_eq F).symm
    _ = ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
        if Odd (∑ g : G, sourceOriginalPParityExponent (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)))
        then ∏ g : G,
          shiftTwoOriginalGroupFactor (P g)
            (sourceOriginalPPrimePowerProduct (P g) (e g)) /
          ((sourceOriginalPPrimePowerProduct (P g) (e g)):ℝ)
        else 0 := by
          apply tsum_congr
          intro e
          exact hPoint e



/- Exact source owner: SourcePPrimePowerOrdinary.lean; original line 51. -/
theorem source_original_P_harmonic_tsum_weighted_equiv
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime) :
    sourceOriginalPHarmonicTsum P =
      ∑' e : {p // p ∈ Finset.univ.biUnion P} → ℕ,
        sourceOriginalW1 P
          (sourceOriginalPPrimePowerProduct (Finset.univ.biUnion P) e) /
        ((sourceOriginalPPrimePowerProduct
          (Finset.univ.biUnion P) e):ℝ) := by
  let Pall : Finset ℕ := Finset.univ.biUnion P
  have hp : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨g,_,hpg⟩
    exact hPrime g p hpg
  let E := source_original_P_power_equiv Pall hp
  have hSwap := E.tsum_eq
    (fun n : sourceOriginalPSupported Pall =>
      sourceOriginalW1 P n.val / (n.val:ℝ))
  unfold sourceOriginalPHarmonicTsum
  change (∑' n : sourceOriginalPSupported Pall,
      sourceOriginalW1 P n.val/(n.val:ℝ)) = _
  rw [← hSwap]
  rfl



/- Exact source owner: SourcePGlobalSeriesReindex.lean; original line 39. -/
theorem source_original_P_global_weighted_tsum_group_reindex
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    sourceOriginalPHarmonicTsum P =
      ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
        ∏ g : G,
          shiftTwoOriginalGroupFactor (P g)
              (sourceOriginalPPrimePowerProduct (P g) (e g)) /
            ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)) := by
  let Pall : Finset ℕ := Finset.univ.biUnion P
  let E := sourceOriginalPDisjointExponentEquiv P hDisj
  let f : ({p // p ∈ Pall} → ℕ) → ℝ :=
    fun a => sourceOriginalW1 P
      (sourceOriginalPPrimePowerProduct Pall a) /
      ((sourceOriginalPPrimePowerProduct Pall a):ℝ)
  have hInitial := source_original_P_harmonic_tsum_weighted_equiv
    P hPrime
  calc
    sourceOriginalPHarmonicTsum P =
      ∑' a : {p // p ∈ Pall} → ℕ, f a := hInitial
    _ = ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
          f (E e) := (E.tsum_eq f).symm
    _ = ∑' e : (g : G) → {p // p ∈ P g} → ℕ,
          ∏ g : G,
            shiftTwoOriginalGroupFactor (P g)
                (sourceOriginalPPrimePowerProduct (P g) (e g)) /
              ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)) := by
      congr 1
      funext e
      dsimp [f,E,Pall]
      rw [←source_original_P_global_vector_product_eq
        P hPrime hDisj e]
      exact source_original_P_global_integer_harmonic_factorization
        P hPrime hDisj e



/- Exact source owner: SourcePFiniteW1Euler.lean; original line 7. -/
theorem source_original_P_W1_finite_harmonic_euler
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (K : ℕ) :
    (∑ e : {p // p ∈ P} → Fin (K+1),
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val):ℝ)⁻¹)) =
    (∑ z : {p // p ∈ P},
      (∑ k : Fin (K+1),
        sourceOriginalPVecMarkFactor z k.val) *
      (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
        ∑ k : Fin (K+1),
          sourceOriginalPVecBaseFactor w k.val)) /
      (∑ p ∈ P, (p:ℝ)⁻¹) := by
  classical
  let C := {p // p ∈ P}
  let F : C → Fin (K+1) → ℝ :=
    fun z k => sourceOriginalPVecBaseFactor z k.val
  let M : C → Fin (K+1) → ℝ :=
    fun z k => sourceOriginalPVecMarkFactor z k.val
  have hEuler := source_original_P_finite_marked_prod_sum F M
  have hTerm (e : C → Fin (K+1)) :
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val):ℝ)⁻¹) =
        (∑ z : C, ∏ w : C,
          if w = z then M w (e w) else F w (e w)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
    simpa only [F,M] using
      (source_original_P_vec_W1_marked_exact
        P hPrime (fun z => (e z).val))
  calc
    (∑ e : C → Fin (K+1),
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val):ℝ)⁻¹)) =
      ∑ e : C → Fin (K+1),
        (∑ z : C, ∏ w : C,
          if w = z then M w (e w) else F w (e w)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro e he
        exact hTerm e
    _ = (∑ e : C → Fin (K+1),
        ∑ z : C, ∏ w : C,
          if w = z then M w (e w) else F w (e w)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
        rw [Finset.sum_div]
    _ = (∑ z : C, (∑ k : Fin (K+1), M z k) *
          (∏ w ∈ (Finset.univ : Finset C).erase z,
            ∑ k : Fin (K+1), F w k)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
        rw [hEuler]
    _ = _ := rfl



/- Exact source owner: SourcePFiniteW1Cap.lean; original line 27. -/
theorem source_original_P_euler_subtype_erase
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p)
    (z : {p // p ∈ P}) :
    (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
       sourceGroupEulerF w.val) =
      ∏ q ∈ P.erase z.val, sourceGroupEulerF q := by
  classical
  let F : ℕ → ℝ := sourceGroupEulerF
  have hAll : (∏ w : {p // p ∈ P}, F w.val) =
      ∏ q ∈ P, F q := by
    simpa only [Finset.attach_eq_univ] using Finset.prod_attach P F
  have hL := Finset.mul_prod_erase
    (Finset.univ : Finset {p // p ∈ P})
    (fun w => F w.val) (Finset.mem_univ z)
  have hR := Finset.mul_prod_erase P F z.property
  have hNonzero : F z.val ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
      (source_group_euler_factor_one_le z.val (h3 z.val z.property)))
  exact mul_left_cancel₀ hNonzero (hL.trans (hAll.trans hR.symm))

/- Literal positive P-group finite W1 series never exceeds
the existing true F'_g(1/2)/V_g Euler factor, uniformly in the
prime-power cutoff K. -/



/- Exact source owner: SourcePGeometricCaps.lean; original line 54. -/
theorem source_original_P_vec_base_finite_sum_eq
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) :
    (∑ k : Fin (K+1), sourceOriginalPVecBaseFactor z k.val) =
      1 + (1/2:ℝ) *
        (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val) := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, sourceOriginalPVecBaseFactor,
    sourceOriginalPVecMarkFactor]
  simp only [Nat.succ_ne_zero, if_false, pow_zero, mul_one,
    if_pos, zero_mul]
  simp only [one_mul, zero_add]
  rw [← Finset.mul_sum]

/- Original prime-range cap: each positive exponent series
has total mass no larger than 1/(p-1). -/



/- Exact source owner: SourcePGeometricCaps.lean; original line 45. -/
theorem source_original_P_vec_mark_finite_sum_eq
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) :
    (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val) =
      (∑ k : Fin (K+1),
        if k.val = 0 then (0:ℝ) else ((z.val:ℝ)⁻¹)^k.val) := by
  apply Finset.sum_congr rfl
  intro k hk
  simp [sourceOriginalPVecMarkFactor]



/- Exact source owner: SourcePGeometricCaps.lean; original line 70. -/
theorem source_original_P_vec_mark_finite_upper
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ)
    (hp : 3 ≤ z.val) :
    (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val) ≤
      ((z.val:ℝ)-1)⁻¹ := by
  have hpR : (3:ℝ) ≤ z.val := by exact_mod_cast hp
  have hp0 : (0:ℝ) < z.val := by linarith
  have hR0 : 0 ≤ (z.val:ℝ)⁻¹ := (inv_pos.mpr hp0).le
  have hR1 : (z.val:ℝ)⁻¹ < 1 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ) < 3) hpR
    linarith
  rw [source_original_P_vec_mark_finite_sum_eq]
  have hCap := source_original_P_geom_positive_cap
    ((z.val:ℝ)⁻¹) K hR0 hR1
  have hId : (z.val:ℝ)⁻¹/(1-(z.val:ℝ)⁻¹) =
      ((z.val:ℝ)-1)⁻¹ := by
    have hpne : (z.val:ℝ) ≠ 0 := ne_of_gt hp0
    have hone : (z.val:ℝ)-1 ≠ 0 := by linarith
    have hden : 1-(z.val:ℝ)⁻¹ ≠ 0 := by linarith
    field_simp
    <;> ring
  exact hCap.trans_eq hId



/- Exact source owner: SourcePGeometricCaps.lean; original line 93. -/
theorem source_original_P_vec_base_finite_upper
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ)
    (hp : 3 ≤ z.val) :
    (∑ k : Fin (K+1), sourceOriginalPVecBaseFactor z k.val) ≤
      1 + (1/2:ℝ) / ((z.val:ℝ)-1) := by
  rw [source_original_P_vec_base_finite_sum_eq]
  have h := source_original_P_vec_mark_finite_upper z K hp
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 1/2)
  simpa only [div_eq_mul_inv, add_comm] using
    (add_le_add_left hh (1:ℝ))



/- Exact source owner: SourcePFiniteW1Cap.lean; original line 16. -/
theorem source_original_P_vec_base_sum_nonneg
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) :
    0 ≤ ∑ k : Fin (K+1),
      sourceOriginalPVecBaseFactor z k.val := by
  apply Finset.sum_nonneg
  intro k hk
  unfold sourceOriginalPVecBaseFactor
  split_ifs <;> positivity

/- Literal subtype/prime-index Euler erasure identity, using
strict positivity of existing sourceGroupEulerF factors. -/



/- Exact source owner: SourcePFiniteW1Cap.lean; original line 7. -/
theorem source_original_P_vec_mark_sum_nonneg
    {P : Finset ℕ} (z : {p // p ∈ P}) (K : ℕ) :
    0 ≤ ∑ k : Fin (K+1),
      sourceOriginalPVecMarkFactor z k.val := by
  apply Finset.sum_nonneg
  intro k hk
  unfold sourceOriginalPVecMarkFactor
  split_ifs <;> positivity



/- Exact source owner: SourcePGroupEulerMarkIdentity.lean; original line 10. -/
theorem source_original_group_Euler_mark_identity
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p) :
    (∑ p ∈ P, (((p:ℝ)-1)⁻¹) *
        (∏ q ∈ P.erase p, sourceGroupEulerF q)) /
        (∑ p ∈ P, (p:ℝ)⁻¹) =
      sourceOriginalGroupHarmonicMass P := by
  classical
  let F : ℕ → ℝ := sourceGroupEulerF
  let T : ℝ := ∏ q ∈ P, F q
  have hterm (p : ℕ) (hp : p ∈ P) :
      (((p:ℝ)-1)⁻¹) * (∏ q ∈ P.erase p, F q) =
        T * (((p:ℝ)-(1/2:ℝ))⁻¹) := by
    have hpR : (3:ℝ) ≤ p := by exact_mod_cast h3 p hp
    have hden : (p:ℝ)-1 ≠ 0 := by linarith
    have hden2 : (p:ℝ)-(1/2:ℝ) ≠ 0 := by linarith
    have hF : F p =
        ((p:ℝ)-(1/2:ℝ)) * (((p:ℝ)-1)⁻¹) := by
      dsimp [F,sourceGroupEulerF]
      field_simp [hden]
      <;> ring
    have halg : (((p:ℝ)-1)⁻¹) =
        F p * (((p:ℝ)-(1/2:ℝ))⁻¹) := by
      rw [hF]
      rw [mul_assoc, mul_comm (((p:ℝ)-1)⁻¹) _]
      rw [← mul_assoc, mul_inv_cancel₀ hden2]
      ring
    rw [halg]
    have heq := Finset.mul_prod_erase P F hp
    dsimp [T]
    calc
      (F p * (((p:ℝ)-(1/2:ℝ))⁻¹)) *
         (∏ q ∈ P.erase p, F q) =
        (F p * ∏ q ∈ P.erase p, F q) *
          (((p:ℝ)-(1/2:ℝ))⁻¹) := by ring
      _ = _ := by rw [heq]
  have hSum : (∑ p ∈ P, (((p:ℝ)-1)⁻¹) *
        (∏ q ∈ P.erase p, sourceGroupEulerF q)) =
      T * (∑ p ∈ P, (((p:ℝ)-(1/2:ℝ))⁻¹)) := by
    calc
      (∑ p ∈ P, (((p:ℝ)-1)⁻¹) *
          (∏ q ∈ P.erase p, sourceGroupEulerF q)) =
        ∑ p ∈ P, T * (((p:ℝ)-(1/2:ℝ))⁻¹) :=
          Finset.sum_congr rfl (fun p hp => hterm p hp)
      _ = _ := by rw [Finset.mul_sum]
  rw [hSum]
  unfold sourceOriginalGroupHarmonicMass
  dsimp [T,F]
  ring



/- Exact source owner: SourcePFiniteW1Cap.lean; original line 50. -/
theorem source_original_P_W1_finite_mass_le_Hg
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p)
    (hPn : P.Nonempty) (K : ℕ) :
    (∑ e : {p // p ∈ P} → Fin (K+1),
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val):ℝ)⁻¹)) ≤
      sourceOriginalGroupHarmonicMass P := by
  classical
  let C := {p // p ∈ P}
  let F : C → ℝ := fun z =>
    ∑ k : Fin (K+1), sourceOriginalPVecBaseFactor z k.val
  let M : C → ℝ := fun z =>
    ∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val
  have hVpos : 0 < ∑ p ∈ P, (p:ℝ)⁻¹ := by
    apply Finset.sum_pos
    · intro p hp
      exact inv_pos.mpr (by exact_mod_cast
        (hPrime p hp).pos)
    · exact hPn
  have hMnonneg (z : C) : 0 ≤ M z :=
    source_original_P_vec_mark_sum_nonneg z K
  have hFnonneg (z : C) : 0 ≤ F z :=
    source_original_P_vec_base_sum_nonneg z K
  have hMle (z : C) :
      M z ≤ ((z.val:ℝ)-1)⁻¹ :=
    source_original_P_vec_mark_finite_upper z K (h3 z.val z.property)
  have hFle (z : C) :
      F z ≤ sourceGroupEulerF z.val := by
    simpa [F,sourceGroupEulerF] using
      (source_original_P_vec_base_finite_upper
        z K (h3 z.val z.property))
  have hFprod_nonneg (z : C) :
      0 ≤ ∏ w ∈ (Finset.univ : Finset C).erase z, F w := by
    apply Finset.prod_nonneg
    intro w hw
    exact hFnonneg w
  have hFprod_le (z : C) :
      (∏ w ∈ (Finset.univ : Finset C).erase z, F w) ≤
      ∏ w ∈ (Finset.univ : Finset C).erase z,
        sourceGroupEulerF w.val := by
    apply Finset.prod_le_prod₀
    · intro w hw
      exact hFnonneg w
    · intro w hw
      exact hFle w
  have hInvPos (z : C) : 0 ≤ ((z.val:ℝ)-1)⁻¹ := by
    have hh : (3:ℝ) ≤ z.val := by exact_mod_cast h3 z.val z.property
    exact (inv_pos.mpr (by linarith)).le
  have hTermLe (z : C) :
      M z * (∏ w ∈ (Finset.univ : Finset C).erase z, F w) ≤
      (((z.val:ℝ)-1)⁻¹) *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          sourceGroupEulerF w.val) :=
    mul_le_mul (hMle z) (hFprod_le z)
      (hFprod_nonneg z) (hInvPos z)
  have hSumLe :
      (∑ z : C,
        M z * (∏ w ∈ (Finset.univ : Finset C).erase z, F w)) ≤
      ∑ z : C,
        (((z.val:ℝ)-1)⁻¹) *
          (∏ w ∈ (Finset.univ : Finset C).erase z,
            sourceGroupEulerF w.val) :=
    Finset.sum_le_sum (fun z hz => hTermLe z)
  have hAttach :
      (∑ z : C, (((z.val:ℝ)-1)⁻¹) *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          sourceGroupEulerF w.val)) =
      ∑ p ∈ P, (((p:ℝ)-1)⁻¹) *
        (∏ q ∈ P.erase p, sourceGroupEulerF q) := by
    have hPer : (∑ z : C, (((z.val:ℝ)-1)⁻¹) *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          sourceGroupEulerF w.val)) =
      ∑ z : C, (((z.val:ℝ)-1)⁻¹) *
        (∏ q ∈ P.erase z.val, sourceGroupEulerF q) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [source_original_P_euler_subtype_erase P h3 z]
    rw [hPer]
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach P
        (fun p => (((p:ℝ)-1)⁻¹) *
          (∏ q ∈ P.erase p, sourceGroupEulerF q)))
  calc
    (∑ e : C → Fin (K+1),
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val)) *
      ((sourceOriginalPPrimePowerProduct P
          (fun z => (e z).val):ℝ)⁻¹)) =
      (∑ z : C, M z *
        (∏ w ∈ (Finset.univ : Finset C).erase z, F w)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) := by
        exact source_original_P_W1_finite_harmonic_euler P hPrime K
    _ ≤ (∑ z : C, (((z.val:ℝ)-1)⁻¹) *
         (∏ w ∈ (Finset.univ : Finset C).erase z,
           sourceGroupEulerF w.val)) /
          (∑ p ∈ P, (p:ℝ)⁻¹) :=
        div_le_div_of_nonneg_right hSumLe hVpos.le
    _ = sourceOriginalGroupHarmonicMass P := by
      rw [hAttach]
      exact source_original_group_Euler_mark_identity P h3



/- Exact source owner: SourcePFiniteCubeTsum.lean; original line 31. -/
theorem source_original_P_harmonic_term_nonneg
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (hPn : P.Nonempty)
    (e : {p // p ∈ P} → ℕ) :
    0 ≤ shiftTwoOriginalGroupFactor P
       (sourceOriginalPPrimePowerProduct P e) *
       ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹) := by
  have hV : 0 < ∑ p ∈ P, (p:ℝ)⁻¹ := by
    apply Finset.sum_pos
    · intro p hp
      exact inv_pos.mpr (by exact_mod_cast (hPrime p hp).pos)
    · exact hPn
  unfold shiftTwoOriginalGroupFactor
  positivity

/- Finite exponent cubes are cofinal for all nonnegative summands.
Unlike a new probability model, this is a pure fact about the
unrestricted original prime-power indexing set. -/



/- Exact source owner: SourcePFiniteCubeTsum.lean; original line 92. -/
theorem source_original_P_group_harmonic_tsum_le_Hg
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty) :
    Summable (fun e : {p // p ∈ P} → ℕ =>
       shiftTwoOriginalGroupFactor P
         (sourceOriginalPPrimePowerProduct P e) *
         ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹)) ∧
    (∑' e : {p // p ∈ P} → ℕ,
       shiftTwoOriginalGroupFactor P
         (sourceOriginalPPrimePowerProduct P e) *
         ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹)) ≤
      sourceOriginalGroupHarmonicMass P := by
  apply source_original_P_cube_summable_of_uniform_bound P
    (fun e =>
       shiftTwoOriginalGroupFactor P
         (sourceOriginalPPrimePowerProduct P e) *
         ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹))
    (sourceOriginalGroupHarmonicMass P)
  · intro e
    exact source_original_P_harmonic_term_nonneg P hPrime hPn e
  · intro K
    exact source_original_P_W1_finite_mass_le_Hg P hPrime h3 hPn K



/- Exact source owner: SourcePCubeConvergence.lean; original line 10. -/
noncomputable def sourceOriginalPExponentCube
    (P : Finset ℕ) (K : ℕ) :
    Finset ({p // p ∈ P} → ℕ) :=
  (Finset.univ : Finset ({p // p ∈ P} → Fin (K+1))).image
    (fun e z => (e z).val)

/- These cubes are cofinal among ALL finite subsets of the
unrestricted exponent-vector space. -/



/- Exact source owner: SourcePCubeConvergence.lean; original line 51. -/
theorem source_original_P_W1_cube_sum_exact
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (K : ℕ) :
    (∑ e ∈ sourceOriginalPExponentCube P K,
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) *
        ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹)) =
    (∑ z : {p // p ∈ P},
      (∑ k : Fin (K+1),
        sourceOriginalPVecMarkFactor z k.val) *
      (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
        ∑ k : Fin (K+1),
          sourceOriginalPVecBaseFactor w k.val)) /
      (∑ p ∈ P, (p:ℝ)⁻¹) := by
  classical
  unfold sourceOriginalPExponentCube
  have hInject : Function.Injective
      (fun e : {p // p ∈ P} → Fin (K+1) =>
        (fun z => (e z).val : {p // p ∈ P} → ℕ)) := by
    intro a b hab
    funext z
    apply Fin.ext
    exact congrFun hab z
  rw [Finset.sum_image (fun a ha b hb hab => hInject hab)]
  exact source_original_P_W1_finite_harmonic_euler P hPrime K

/- **Unconditional exact original group Euler law**: the full
unrestricted harmonic series for the source's actual P-group W1
equals the pre-existing F'_g(1/2)/V_g, including every repeated
prime power. No independent law or unproved interchange is used. -/



/- Exact source owner: SourcePFiniteEulerLimit.lean; original line 10. -/
theorem source_original_P_group_Euler_subtype_formula
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p) :
    ((∑ z : {p // p ∈ P}, ((z.val:ℝ)-1)⁻¹ *
        (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
           sourceGroupEulerF w.val)) /
        (∑ p ∈ P, (p:ℝ)⁻¹)) =
      sourceOriginalGroupHarmonicMass P := by
  classical
  have hPer :
      (∑ z : {p // p ∈ P}, ((z.val:ℝ)-1)⁻¹ *
        (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
           sourceGroupEulerF w.val)) =
      ∑ z : {p // p ∈ P}, ((z.val:ℝ)-1)⁻¹ *
        (∏ q ∈ P.erase z.val, sourceGroupEulerF q) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [source_original_P_euler_subtype_erase P h3 z]
  rw [hPer]
  have hAttach :
      (∑ z : {p // p ∈ P}, ((z.val:ℝ)-1)⁻¹ *
         (∏ q ∈ P.erase z.val, sourceGroupEulerF q)) =
      ∑ p ∈ P, ((p:ℝ)-1)⁻¹ *
         (∏ q ∈ P.erase p, sourceGroupEulerF q) := by
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach P (fun p => ((p:ℝ)-1)⁻¹ *
        (∏ q ∈ P.erase p, sourceGroupEulerF q)))
  rw [hAttach]
  exact source_original_group_Euler_mark_identity P h3

/- Finite Euler expressions for the actual source W1 converge
to precisely the original (previously checked) H_g, including
all repeated prime powers. -/



/- Exact source owner: SourcePGeometricLimit.lean; original line 10. -/
theorem source_original_P_vec_mark_tendsto
    {P : Finset ℕ} (z : {p // p ∈ P})
    (hp : 3 ≤ z.val) :
    Tendsto (fun K : ℕ =>
      ∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val)
      atTop (𝓝 (((z.val:ℝ)-1)⁻¹)) := by
  let r : ℝ := (z.val:ℝ)⁻¹
  have hpR : (3:ℝ) ≤ z.val := by exact_mod_cast hp
  have hp0 : (0:ℝ) < z.val := by linarith
  have hr0 : 0 ≤ r := (inv_pos.mpr hp0).le
  have hr1 : r < 1 := by
    dsimp [r]
    have hh := inv_anti₀ (by norm_num : (0:ℝ) < 3) hpR
    linarith
  have hrNorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hSum : Tendsto
      (fun K : ℕ => ∑ k : Fin K, r^k.val)
      atTop (𝓝 ((1-r)⁻¹)) := by
    simpa only [Fin.sum_univ_eq_sum_range] using
      (hasSum_geometric_of_norm_lt_one hrNorm).tendsto_sum_nat
  have hLimit : r*(1-r)⁻¹ = ((z.val:ℝ)-1)⁻¹ := by
    dsimp [r]
    have hpne : (z.val:ℝ) ≠ 0 := ne_of_gt hp0
    have hone : (z.val:ℝ)-1 ≠ 0 := by linarith
    field_simp
    <;> ring
  have hMark (K : ℕ) :
      (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val) =
        r * (∑ k : Fin K, r^k.val) := by
    rw [source_original_P_vec_mark_finite_sum_eq]
    exact source_original_P_finite_geom_positive r K
  have ht : Tendsto
      (fun K : ℕ => r * ∑ k : Fin K, r^k.val)
      atTop (𝓝 (r * (1-r)⁻¹)) :=
    tendsto_const_nhds.mul hSum
  rw [← hLimit]
  have hEq : (fun K : ℕ =>
      ∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val) =
      (fun K : ℕ => r * ∑ k : Fin K, r^k.val) := by
    funext K
    exact hMark K
  rw [hEq]
  exact ht

/- The unmarked factor tends to the exact *pre-existing*
sourceGroupEulerF = 1+1/(2(p-1)). -/



/- Exact source owner: SourcePGeometricLimit.lean; original line 56. -/
theorem source_original_P_vec_base_tendsto
    {P : Finset ℕ} (z : {p // p ∈ P})
    (hp : 3 ≤ z.val) :
    Tendsto (fun K : ℕ =>
      ∑ k : Fin (K+1), sourceOriginalPVecBaseFactor z k.val)
      atTop (𝓝 (sourceGroupEulerF z.val)) := by
  have hMark := source_original_P_vec_mark_tendsto z hp
  have hL : Tendsto (fun K : ℕ =>
      (1:ℝ) + (1/2:ℝ) *
        (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val))
      atTop (𝓝 ((1:ℝ) + (1/2:ℝ) * (((z.val:ℝ)-1)⁻¹))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hMark)
  have hRight : (1:ℝ) + (1/2:ℝ) * (((z.val:ℝ)-1)⁻¹) =
      sourceGroupEulerF z.val := by
    unfold sourceGroupEulerF
    ring
  rw [← hRight]
  have hEq : (fun K : ℕ =>
      ∑ k : Fin (K+1), sourceOriginalPVecBaseFactor z k.val) =
      (fun K : ℕ => (1:ℝ) + (1/2:ℝ) *
        (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val)) := by
    funext K
    exact source_original_P_vec_base_finite_sum_eq z K
  rw [hEq]
  exact hL



/- Exact source owner: SourcePFiniteEulerLimit.lean; original line 42. -/
theorem source_original_P_W1_finite_Euler_tendsto_Hg
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p) :
    Tendsto (fun K : ℕ =>
      (∑ z : {p // p ∈ P},
        (∑ k : Fin (K+1),
          sourceOriginalPVecMarkFactor z k.val) *
        (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
          ∑ k : Fin (K+1),
            sourceOriginalPVecBaseFactor w k.val)) /
        (∑ p ∈ P, (p:ℝ)⁻¹))
      atTop (𝓝 (sourceOriginalGroupHarmonicMass P)) := by
  let C := {p // p ∈ P}
  let S (z : C) (K : ℕ) : ℝ :=
    (∑ k : Fin (K+1), sourceOriginalPVecMarkFactor z k.val)
  let T (z : C) (K : ℕ) : ℝ :=
    (∑ k : Fin (K+1), sourceOriginalPVecBaseFactor z k.val)
  have hS (z : C) : Tendsto (S z) atTop
      (𝓝 (((z.val:ℝ)-1)⁻¹)) :=
    source_original_P_vec_mark_tendsto z (h3 z.val z.property)
  have hT (z : C) : Tendsto (T z) atTop
      (𝓝 (sourceGroupEulerF z.val)) :=
    source_original_P_vec_base_tendsto z (h3 z.val z.property)
  have hTerm (z : C) :
      Tendsto (fun K : ℕ =>
        S z K * (∏ w ∈ (Finset.univ : Finset C).erase z,
          T w K)) atTop
      (𝓝 (((z.val:ℝ)-1)⁻¹ *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          sourceGroupEulerF w.val))) := by
    have hProd : Tendsto
        (fun K : ℕ => ∏ w ∈ (Finset.univ : Finset C).erase z, T w K)
        atTop (𝓝 (∏ w ∈ (Finset.univ : Finset C).erase z,
          sourceGroupEulerF w.val)) :=
      tendsto_finsetProd _ (fun w hw => hT w)
    exact (hS z).mul hProd
  have hSum : Tendsto (fun K : ℕ =>
      ∑ z : C, S z K * (∏ w ∈ (Finset.univ : Finset C).erase z,
          T w K)) atTop
      (𝓝 (∑ z : C, ((z.val:ℝ)-1)⁻¹ *
          (∏ w ∈ (Finset.univ : Finset C).erase z,
            sourceGroupEulerF w.val))) :=
    tendsto_finsetSum _ (fun z hz => hTerm z)
  have hDiv : Tendsto (fun K : ℕ =>
      (∑ z : C, S z K *
        (∏ w ∈ (Finset.univ : Finset C).erase z,
          T w K)) / (∑ p ∈ P, (p:ℝ)⁻¹)) atTop
      (𝓝 ((∑ z : C, ((z.val:ℝ)-1)⁻¹ *
          (∏ w ∈ (Finset.univ : Finset C).erase z,
            sourceGroupEulerF w.val)) /
          (∑ p ∈ P, (p:ℝ)⁻¹))) :=
    hSum.div_const _
  have hIdentity := source_original_P_group_Euler_subtype_formula P h3
  rw [← hIdentity]
  exact hDiv



/- Exact source owner: SourcePCubeConvergence.lean; original line 18. -/
theorem source_original_P_exponent_cubes_tendsto_atTop
    (P : Finset ℕ) :
    Tendsto (sourceOriginalPExponentCube P) atTop atTop := by
  classical
  apply Filter.tendsto_atTop.mpr
  intro s
  obtain ⟨K,hK⟩ := source_original_P_exponents_cofinal P s
  filter_upwards [eventually_ge_atTop K] with K' hKK'
  intro e he
  apply Finset.mem_image.mpr
  refine ⟨(fun z =>
    (⟨e z, Nat.lt_succ_of_le ((hK e he z).trans hKK')⟩ :
      Fin (K'+1))), Finset.mem_univ _, ?_⟩
  funext z
  rfl

/- Any summable exponent-vector series is the limit of its actual
rectangular prime-power cube partial sums. -/



/- Exact source owner: SourcePCubeConvergence.lean; original line 36. -/
theorem source_original_P_sum_cube_tendsto_tsum
    (P : Finset ℕ)
    (f : ({p // p ∈ P} → ℕ) → ℝ)
    (hf : Summable f) :
    Tendsto (fun K : ℕ =>
      ∑ e ∈ sourceOriginalPExponentCube P K, f e)
      atTop (𝓝 (∑' e, f e)) := by
  have hHas : Tendsto
      (fun s : Finset ({p // p ∈ P} → ℕ) =>
        ∑ e ∈ s, f e) atTop (𝓝 (∑' e, f e)) :=
    hf.hasSum
  exact hHas.comp (source_original_P_exponent_cubes_tendsto_atTop P)

/- Cube sums have exactly the finite Euler expression already
proved for the genuine W1 in SourcePFiniteW1Euler. -/



/- Exact source owner: SourcePCubeConvergence.lean; original line 81. -/
theorem source_original_P_group_harmonic_tsum_eq_Hg
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty) :
    (∑' e : {p // p ∈ P} → ℕ,
      shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) *
        ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹)) =
      sourceOriginalGroupHarmonicMass P := by
  let f : ({p // p ∈ P} → ℕ) → ℝ := fun e =>
    shiftTwoOriginalGroupFactor P
      (sourceOriginalPPrimePowerProduct P e) *
      ((sourceOriginalPPrimePowerProduct P e:ℝ)⁻¹)
  have hf := (source_original_P_group_harmonic_tsum_le_Hg
    P hPrime h3 hPn).1
  have hTsum := source_original_P_sum_cube_tendsto_tsum P f hf
  have hEuler := source_original_P_W1_finite_Euler_tendsto_Hg P h3
  have hSame (K : ℕ) := source_original_P_W1_cube_sum_exact P hPrime K
  have hEqFun :
      (fun K : ℕ => ∑ e ∈ sourceOriginalPExponentCube P K, f e) =
      (fun K : ℕ =>
        (∑ z : {p // p ∈ P},
          (∑ k : Fin (K+1),
            sourceOriginalPVecMarkFactor z k.val) *
          (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
            ∑ k : Fin (K+1),
              sourceOriginalPVecBaseFactor w k.val)) /
        (∑ p ∈ P, (p:ℝ)⁻¹)) := by
    funext K
    exact hSame K
  rw [hEqFun] at hTsum
  exact tendsto_nhds_unique hTsum hEuler



/- Exact source owner: SourcePGroupVectorEvenTsum.lean; original line 9. -/
theorem source_original_P_group_vector_even_tsum_eq_actual
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) :
    (∑' e : {p // p ∈ P} → ℕ,
      if Even (sourceOriginalPParityExponent P
        (sourceOriginalPPrimePowerProduct P e))
      then shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) /
        ((sourceOriginalPPrimePowerProduct P e):ℝ)
      else 0) =
    ∑' n : sourceOriginalPEvenSupported P,
      shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ) := by
  classical
  let E := source_original_P_power_equiv P hPrime
  let w : sourceOriginalPSupported P → ℝ :=
    fun n => shiftTwoOriginalGroupFactor P n.val / (n.val:ℝ)
  let F : sourceOriginalPSupported P → ℝ :=
    fun n => if Even (sourceOriginalPParityExponent P n.val)
      then w n else 0
  have hReindex := E.tsum_eq F
  have hSubset :
      (∑' n : sourceOriginalPEvenSupported P, w n.val) =
      (∑' n : sourceOriginalPSupported P, F n) := by
    let S : Set (sourceOriginalPSupported P) :=
      {n | Even (sourceOriginalPParityExponent P n.val)}
    have hh := tsum_subtype S w
    calc
      _ = ∑' n : ↑S, w n.val := rfl
      _ = ∑' n : sourceOriginalPSupported P, S.indicator w n := hh
      _ = ∑' n : sourceOriginalPSupported P, F n := by
        apply tsum_congr
        intro n
        by_cases h : Even (sourceOriginalPParityExponent P n.val)
        · simp [F,S,Set.indicator,h]
        · simp [F,S,Set.indicator,h]
  rw [← hSubset] at hReindex
  change
    (∑' e : {p // p ∈ P} → ℕ,
      if Even (sourceOriginalPParityExponent P
        (sourceOriginalPPrimePowerProduct P e))
      then shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) /
        ((sourceOriginalPPrimePowerProduct P e):ℝ)
      else 0) = _ at hReindex
  exact hReindex



/- Exact source owner: SourcePGroupVectorParityTsum.lean; original line 10. -/
theorem source_original_P_group_vector_odd_tsum_eq_actual
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) :
    (∑' e : {p // p ∈ P} → ℕ,
      if Odd (sourceOriginalPParityExponent P
        (sourceOriginalPPrimePowerProduct P e))
      then shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) /
        ((sourceOriginalPPrimePowerProduct P e):ℝ)
      else 0) =
    ∑' n : sourceOriginalPOddSupported P,
      shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ) := by
  classical
  let E := source_original_P_power_equiv P hPrime
  let w : sourceOriginalPSupported P → ℝ :=
    fun n => shiftTwoOriginalGroupFactor P n.val / (n.val:ℝ)
  let F : sourceOriginalPSupported P → ℝ :=
    fun n => if Odd (sourceOriginalPParityExponent P n.val)
      then w n else 0
  have hReindex := E.tsum_eq F
  have hSubset :
      (∑' n : sourceOriginalPOddSupported P, w n.val) =
      (∑' n : sourceOriginalPSupported P, F n) := by
    let S : Set (sourceOriginalPSupported P) :=
      {n | Odd (sourceOriginalPParityExponent P n.val)}
    have hh := tsum_subtype S w
    calc
      _ = ∑' n : ↑S, w n.val := rfl
      _ = ∑' n : sourceOriginalPSupported P, S.indicator w n := hh
      _ = ∑' n : sourceOriginalPSupported P, F n := by
        apply tsum_congr
        intro n
        by_cases h : Odd (sourceOriginalPParityExponent P n.val)
        · simp [F,S,Set.indicator,h]
        · simp [F,S,Set.indicator,h]
  rw [← hSubset] at hReindex
  change
    (∑' e : {p // p ∈ P} → ℕ,
      if Odd (sourceOriginalPParityExponent P
        (sourceOriginalPPrimePowerProduct P e))
      then shiftTwoOriginalGroupFactor P
        (sourceOriginalPPrimePowerProduct P e) /
        ((sourceOriginalPPrimePowerProduct P e):ℝ)
      else 0) = _ at hReindex
  exact hReindex



/- Exact source owner: SourcePGroupVectorFlagFloor.lean; original line 10. -/
theorem source_original_P_group_true_vector_flag_floor
    (P : Finset ℕ) (δ : ℝ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (hHg : 0 < sourceOriginalGroupHarmonicMass P)
    (hOdd : δ ≤
      (∑' n : sourceOriginalPOddSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) /
          sourceOriginalGroupHarmonicMass P)
    (hEven : δ ≤
      (∑' n : sourceOriginalPEvenSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ)) /
          sourceOriginalGroupHarmonicMass P) :
    ∀ b : Bool,
      δ * (∑' e : {p // p ∈ P} → ℕ,
        shiftTwoOriginalGroupFactor P
          (sourceOriginalPPrimePowerProduct P e) /
          ((sourceOriginalPPrimePowerProduct P e):ℝ)) ≤
      ∑' e : {p // p ∈ P} → ℕ,
        if decide (Odd (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e))) ≠ b
        then shiftTwoOriginalGroupFactor P
          (sourceOriginalPPrimePowerProduct P e) /
          ((sourceOriginalPPrimePowerProduct P e):ℝ)
        else 0 := by
  let f : ({p // p ∈ P} → ℕ) → ℝ := fun e =>
    shiftTwoOriginalGroupFactor P
      (sourceOriginalPPrimePowerProduct P e) /
      ((sourceOriginalPPrimePowerProduct P e):ℝ)
  have hTotal : (∑' e : {p // p ∈ P} → ℕ, f e) =
      sourceOriginalGroupHarmonicMass P := by
    simpa only [f, div_eq_mul_inv] using
      source_original_P_group_harmonic_tsum_eq_Hg P hPrime h3 hPn
  have hOddScaled : δ * sourceOriginalGroupHarmonicMass P ≤
      ∑' n : sourceOriginalPOddSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ) :=
    (le_div_iff₀ hHg).mp hOdd
  have hEvenScaled : δ * sourceOriginalGroupHarmonicMass P ≤
      ∑' n : sourceOriginalPEvenSupported P,
        shiftTwoOriginalGroupFactor P n.val.val / (n.val.val:ℝ) :=
    (le_div_iff₀ hHg).mp hEven
  intro b
  cases b with
  | false =>
    have hEq : (fun e : {p // p ∈ P} → ℕ =>
        if decide (Odd (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e))) ≠ false
        then f e else 0) =
        (fun e => if Odd (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e)) then f e else 0) := by
      funext e
      by_cases h : Odd (sourceOriginalPParityExponent P
        (sourceOriginalPPrimePowerProduct P e))
      · simp [h]
      · simp [h]
    change δ * (∑' e, f e) ≤
      ∑' e : {p // p ∈ P} → ℕ,
        if decide (Odd (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e))) ≠ false then f e else 0
    rw [hTotal]
    have hEqSum := congrArg
      (fun k : ({p // p ∈ P} → ℕ) → ℝ => ∑' e, k e) hEq
    rw [hEqSum]
    rw [source_original_P_group_vector_odd_tsum_eq_actual P hPrime]
    exact hOddScaled
  | true =>
    have hEq : (fun e : {p // p ∈ P} → ℕ =>
        if decide (Odd (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e))) ≠ true
        then f e else 0) =
        (fun e => if Even (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e)) then f e else 0) := by
      funext e
      by_cases h : Odd (sourceOriginalPParityExponent P
        (sourceOriginalPPrimePowerProduct P e))
      · simp [h, Nat.not_even_iff_odd.mpr h]
      · simp [h, Nat.not_odd_iff_even.mp h]
    change δ * (∑' e, f e) ≤
      ∑' e : {p // p ∈ P} → ℕ,
        if decide (Odd (sourceOriginalPParityExponent P
          (sourceOriginalPPrimePowerProduct P e))) ≠ true then f e else 0
    rw [hTotal]
    have hEqSum := congrArg
      (fun k : ({p // p ∈ P} → ℕ) → ℝ => ∑' e, k e) hEq
    rw [hEqSum]
    rw [source_original_P_group_vector_even_tsum_eq_actual P hPrime]
    exact hEvenScaled


end Green64Analytic.SourceBlockSieve

end

end

