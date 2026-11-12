module

public import Green64.Library.Weights.Part106
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part100
public import Green64.Library.Weights.Part073
public import Green64.Library.Analysis.Estimates.PrimeFineProxy
public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Green64.Library.Sieve.Foundation.Lemma9.Part001

@[expose] public section

/-!
# Sieve / Foundations / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ParityGoodSourceFloor -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- Actual midpoint Q-rest times infinite P-supported harmonic source.
The two parity branches keep the same original corridor, factorial, and
free-prime localization. No positive mass assumption is introduced. -/
noncomputable def parityOriginalParityQPActualGoodHarmonicMass434 (parityFlag : Bool)
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀) : ℝ :=
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let Good := sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i
  ∑ rest : (z : I) → {p // p ∈ Q z.val.1},
    ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (∀ z, (rest z).val ∈ Good z) ∧
          Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
        ((∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
          (((∏ z : I, (rest z).val):ℕ):ℝ)) *
          ((sourceOriginalW1 P R.val/(R.val:ℝ)) *
          ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion P) R.val)/2))
      else 0

theorem parity_original_QP_actual_good_harmonic_product_parity434 (parityFlag : Bool)
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀) :
    parityOriginalParityQPActualGoodHarmonicMass434 parityFlag r₀ jₓ k L ε b i =
      sourceOriginalQActualGoodRestHarmonicMass r₀ jₓ k L ε b i *
      (∑' R : sourceOriginalPSupported
          (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
        if Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
          (sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) R.val /
             (R.val:ℝ)) *
          ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) R.val)/2)
        else 0) := by
  classical
  unfold parityOriginalParityQPActualGoodHarmonicMass434
    sourceOriginalQActualGoodRestHarmonicMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rest hrest
  rw [← tsum_mul_left]
  apply tsum_congr
  intro R
  split_ifs <;> simp_all only [and_true, and_false, mul_zero, zero_mul]
  all_goals
    exfalso
    rename_i hn hQ hP
    exact hn (fun _ => True.intro)

theorem parity_original_XA_actual_good_pointwise_floor_eventually_parity434 (parityFlag : Bool)
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (hk : 0 < k)
    (hkPower : 288*r₀ ≤ 2^k)
    (ε α β c : ℝ) (Ψ : ℝ → ℝ)
    (hε : 0 ≤ ε)
    (hεBudget : (((k*r₀:ℕ):ℝ))*ε ≤ 1/120)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hkn : k ≤ jₓ+1) (i : Fin r₀)
      (rest : (z : {z : Fin (jₓ+1) × Fin r₀ //
        z ≠ (⟨0,Nat.succ_pos jₓ⟩,i)}) →
        {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.val.1})
      (R : sourceOriginalPSupported
        (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L))),
      (∀ z, (rest z).val ∈
        sourceOriginalQJointRestAllowed r₀ jₓ k L ε
          ⟨0,Nat.succ_pos jₓ⟩ i z) →
      Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 →
      let q : ℕ := ∏ z, (rest z).val
      let a : ℝ :=
        (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) / (q:ℝ)
      let w : ℝ :=
        (sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) R.val /
          (R.val:ℝ)) *
        ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) R.val)/2)
      sourceOriginalXAGoodPrefactor r₀ L α β c * (a*w) ≤
        parityOriginalParityQPActualFreeTerm434 parityFlag r₀
          (sourceOriginalQActualBands r₀ jₓ L)
          (sourceOriginalPAllActualBands r₀ L)
          ⟨0,Nat.succ_pos jₓ⟩ i (Real.exp L) Ψ rest R := by
  have hFree := parity_original_Q0_actual_XA_free_prime_floor_eventually_parity434 parityFlag
    r₀ hr₀ α β c Ψ hα hαβ hβ hc hΨnonneg hΨ
  filter_upwards [hFree, eventually_gt_atTop (0:ℝ)] with L hFreeL hL
  intro jₓ hkn i rest R hGood hRHi q a w
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  have hCorr := source_original_QP_actual_good_rest_corridor
    r₀ jₓ k L ε hr₀ hk hkn hkPower hL.le hε hεBudget
      i rest hGood R.val (Nat.pos_of_ne_zero R.property.1) hRHi
  have hFloor := hFreeL Q P b i
    (source_original_Q_actual_prime r₀ jₓ L)
    (by simp [Q, b, sourceOriginalQActualBands, sourceOriginalQActualExponent]) rest R hCorr.1 hCorr.2
  have hq : 0 < q := by
    dsimp [q]
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    exact (source_original_Q_actual_prime r₀ jₓ L z.val.1
      (rest z).val (rest z).property).ne_zero
  have hR : 0 < R.val := Nat.pos_of_ne_zero R.property.1
  have hRewrite :
      sourceOriginalXAGoodPrefactor r₀ L α β c * (a*w) =
      ((∏ _j : Fin (jₓ+1), (1:ℝ)/(r₀.factorial:ℝ)) *
        sourceOriginalW1 P R.val *
        ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2)) *
      ((α*Real.exp L/(q*R.val:ℕ)) *
        (c*Real.log (β/α) /
          (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
            sourceOriginalQ0Scale r₀/30)*L))) := by
    dsimp only [sourceOriginalXAGoodPrefactor, a, w, P]
    simp only [Nat.cast_mul, one_div, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hRewrite]
  change _ ≤ parityOriginalParityQPActualFreeTerm434 parityFlag r₀ Q P b i (Real.exp L) Ψ rest R
  simpa only [parityOriginalParityQPActualFreeTerm434, Q, P, b] using hFloor

theorem parity_original_XA_actual_good_harmonic_floor_eventually_parity434 (parityFlag : Bool)
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (hk : 0 < k)
    (hkPower : 288*r₀ ≤ 2^k)
    (ε α β c : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hε : 0 ≤ ε)
    (hεBudget : (((k*r₀:ℕ):ℝ))*ε ≤ 1/120)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 ≤ c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hkn : k ≤ jₓ+1) (i : Fin r₀),
      sourceOriginalXAGoodPrefactor r₀ L α β c *
        parityOriginalParityQPActualGoodHarmonicMass434 parityFlag
          r₀ jₓ k L ε ⟨0,Nat.succ_pos jₓ⟩ i ≤
      parityOriginalParityXA434 parityFlag r₀
        (sourceOriginalQActualBands r₀ jₓ L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  have hPoint := parity_original_XA_actual_good_pointwise_floor_eventually_parity434 parityFlag
    r₀ k hr₀ hk hkPower ε α β c Ψ hε hεBudget
      hα hαβ hβ hc hΨnonneg hΨ
  filter_upwards [hPoint, eventually_gt_atTop (0:ℝ)] with L hPointL hL
  intro jₓ hkn i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let Good := sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i
  let E (rest : (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) →
      {p // p ∈ Q z.val.1})
      (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : Prop :=
    (∀ z, (rest z).val ∈ Good z) ∧
      Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
  let a (rest : (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) →
      {p // p ∈ Q z.val.1}) : ℝ :=
    (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
      ((((∏ z, (rest z).val):ℕ):ℝ))
  let w (R : sourceOriginalPSupported (Finset.univ.biUnion P)) : ℝ :=
    (sourceOriginalW1 P R.val/(R.val:ℝ)) *
      ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2)
  let K := sourceOriginalXAGoodPrefactor r₀ L α β c
  have hPrune := parity_original_XA_QP_good_rest_lower_parity434 parityFlag
    r₀ Q P b i (Real.exp L) Ψ hΨzero hΨnonneg
    (source_original_Q_actual_prime r₀ jₓ L)
    (source_original_Q_actual_all_disjoint r₀ jₓ L hr₀ hL)
    (source_original_P_all_actual_band_prime r₀ L)
    (source_original_Q_actual_all_P_disjoint r₀ jₓ L hr₀ hL)
    E
  have hTerm : ∀ rest R, (if E rest R then K*(a rest*w R) else 0) ≤
      (if E rest R then
        parityOriginalParityQPActualFreeTerm434 parityFlag r₀ Q P b i (Real.exp L) Ψ rest R
       else 0) := by
    intro rest R
    by_cases hE : E rest R
    · rw [if_pos hE, if_pos hE]
      dsimp only [K, a, w, Q, P, b]
      exact hPointL jₓ hkn i rest R hE.1 hE.2
    · simp [hE]
  apply le_trans ?_ hPrune
  unfold parityOriginalParityQPActualGoodHarmonicMass434
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rest hrest
  rw [← tsum_mul_left]
  simp only [mul_ite, mul_zero]
  have hLhs : (∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
      if (∀ z, (rest z).val ∈ Good z) ∧
          Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
        sourceOriginalXAGoodPrefactor r₀ L α β c *
          (((∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
            (((∏ z, (rest z).val):ℕ):ℝ)) *
            ((sourceOriginalW1 P R.val/(R.val:ℝ)) *
              ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
                (Finset.univ.biUnion P) R.val)/2))) else 0) =
      ∑' R, if E rest R then K*(a rest*w R) else 0 := by
    apply tsum_congr
    intro R
    simp only [E, K, a, w]
    split_ifs <;> rfl
  rw [hLhs]
  have hUpper : Summable (fun R =>
      if E rest R then
        parityOriginalParityQPActualFreeTerm434 parityFlag r₀ Q P b i (Real.exp L) Ψ rest R
      else 0) := by
    have hFull := parity_original_QP_actual_free_term_summable_parity434 parityFlag
      r₀ Q P b i (Real.exp L) Ψ
        (source_original_Q_actual_prime r₀ jₓ L) rest
    have hn (R : sourceOriginalPSupported (Finset.univ.biUnion P)) :=
      parity_original_QP_actual_free_term_nonneg_parity434 parityFlag
        r₀ Q P b i (Real.exp L) Ψ hΨnonneg rest R
    exact hFull.of_nonneg_of_le
      (fun R => by split_ifs <;> [exact hn R; exact le_rfl])
      (fun R => by split_ifs <;> [exact le_rfl; exact hn R])
  have hLowerNonneg : ∀ R,
      0 ≤ (if E rest R then K*(a rest*w R) else 0) := by
    intro R
    by_cases hE : E rest R
    · rw [if_pos hE]
      have hlog : 0 < Real.log (β/α) := Real.log_pos
        ((one_lt_div (by linarith : 0 < α)).2 hαβ)
      have hs : 0 < sourceOriginalQ0Scale r₀ := by
        unfold sourceOriginalQ0Scale
        have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
        positivity
      have hd : 0 < (6/5:ℝ)*sourceOriginalQ0Scale r₀-sourceOriginalQ0Scale r₀/30 := by linarith
      have hK : 0 ≤ K := by dsimp [K, sourceOriginalXAGoodPrefactor]; positivity
      have ha : 0 ≤ a rest := by dsimp [a]; positivity
      have hp : 0 ≤ (1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)/2 := by
        rcases parity_original_parity_projection_zero_or_one434 parityFlag
          (Finset.univ.biUnion P) R.val with h | h <;> rw [h] <;> norm_num
      have hw : 0 ≤ w R := by
        exact mul_nonneg (div_nonneg (source_original_W1_nonneg P R.val)
          (by positivity)) hp
      exact mul_nonneg hK (mul_nonneg ha hw)
    · simp [hE]
  have hLower := hUpper.of_nonneg_of_le hLowerNonneg (hTerm rest)
  have hSum := Summable.tsum_le_tsum (hTerm rest) hLower hUpper
  convert hSum using 1
  apply tsum_congr
  intro R
  split_ifs <;> rfl
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityLocalizedMass -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- The actual localized source mass for each multiplicity-parity branch.
All geometry and constants come from native original Q/P source proofs.
The same fixed macro parameters and positive constant precede L. -/
noncomputable def parityOriginalParityPActualGoodHarmonicMass434 (parityFlag : Bool)
    (r₀ : ℕ) (L : ℝ) : ℝ :=
  let P := sourceOriginalPAllActualBands r₀ L
  ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
    if Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
      (sourceOriginalW1 P R.val / (R.val:ℝ)) *
      ((1 + parityOriginalParitySign434 parityFlag * (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2)
    else 0

/- Original P part has at least the verified fixed odd-small
harmonic share, not an auxiliary parity law. -/

theorem parity_original_P_good_harmonic_mass_floor_eventually_parity434
    (parityFlag : Bool) (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop,
      (sourceOriginalPGroupParityDelta/2) *
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L) ≤
      parityOriginalParityPActualGoodHarmonicMass434 parityFlag r₀ L := by
  filter_upwards [parity_original_P_actual_parity_small_full_eventually434 r₀ hr₀,
    source_original_P_all_actual_local_eventually r₀] with L hEvent hLocal
  let P := sourceOriginalPAllActualBands r₀ L
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    exact (by norm_num : 3 ≤ 6).trans (hLocal.2.1 g p hp)
  have hHP : 0 < sourceLiteralHP P :=
    (by norm_num : (0:ℝ)<1).trans_le (source_literal_HP_one_le P h3 hLocal.1)
  have hBound := (le_div_iff₀ hHP).mp (hEvent parityFlag)
  calc
    _ ≤ (∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
        if decide (Odd (sourceOriginalPParityExponent
          (Finset.univ.biUnion P) R.val)) ≠ parityFlag ∧
          Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12
        then sourceOriginalW1 P R.val / (R.val:ℝ) else 0) := hBound
    _ = parityOriginalParityPActualGoodHarmonicMass434 parityFlag r₀ L := by
      unfold parityOriginalParityPActualGoodHarmonicMass434
      apply tsum_congr
      intro R
      rw [parity_original_parity_projection_eq_indicator434]
      dsimp only [P] at *
      split_ifs <;> simp_all


theorem parity_original_QP_actual_good_mass_product_floor_eventually_parity434 (parityFlag : Bool)
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀)
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1/10) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (i : Fin r₀),
      ((sourceOriginalQUniformGamma ε)^(k*r₀) *
        (sourceOriginalPGroupParityDelta/2)) *
      ((∑ f : (z : Fin (jₓ+1) × Fin r₀) →
          {p // p ∈ sourceOriginalQActualBands r₀ jₓ L z.1},
          (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
            (((∏ z, (f z).val):ℕ):ℝ)) *
        sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)) ≤
      4 * sourceOriginalQActualGoodRestHarmonicMass
        r₀ jₓ k L ε ⟨0,Nat.succ_pos jₓ⟩ i *
        parityOriginalParityPActualGoodHarmonicMass434 parityFlag r₀ L := by
  have hQ := source_original_Q0_good_rest_full_labelled_HQ_eventually
    r₀ k hr₀ ε hε hεsmall
  have hP := parity_original_P_good_harmonic_mass_floor_eventually_parity434 parityFlag r₀ hr₀
  have hLocal := source_original_P_all_actual_local_eventually r₀
  filter_upwards [hQ,hP,hLocal] with L hQL hPL hLocalL
  intro jₓ i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let A : ℝ := ∑ f : (z : Fin (jₓ+1) × Fin r₀) →
      {p // p ∈ Q z.1},
      (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
        (((∏ z, (f z).val):ℕ):ℝ)
  let QGood := sourceOriginalQActualGoodRestHarmonicMass
    r₀ jₓ k L ε b i
  let PGood := parityOriginalParityPActualGoodHarmonicMass434 parityFlag r₀ L
  let γ : ℝ := (sourceOriginalQUniformGamma ε)^(k*r₀)
  let δ : ℝ := sourceOriginalPGroupParityDelta/2
  have hQbound : γ*A ≤ 4*QGood := hQL jₓ i
  have hPbound : δ*sourceLiteralHP P ≤ PGood := hPL
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    exact (by norm_num : 3 ≤ 6).trans (hLocalL.2.1 g p hp)
  have hHP : 1 ≤ sourceLiteralHP P :=
    source_literal_HP_one_le P h3 hLocalL.1
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos source_original_P_group_parity_delta_positive (by norm_num)
  have hδHP : 0 ≤ δ*sourceLiteralHP P :=
    mul_nonneg (le_of_lt hδpos) (by linarith)
  have hQGoodNN : 0 ≤ QGood := by
    dsimp [QGood, sourceOriginalQActualGoodRestHarmonicMass]
    apply Finset.sum_nonneg
    intro rest hrest
    split_ifs <;> positivity
  change (γ*δ)*(A*sourceLiteralHP P) ≤ 4*QGood*PGood
  calc
    (γ*δ)*(A*sourceLiteralHP P) =
        (γ*A)*(δ*sourceLiteralHP P) := by ring
    _ ≤ (4*QGood)*(δ*sourceLiteralHP P) :=
      mul_le_mul_of_nonneg_right hQbound hδHP
    _ ≤ (4*QGood)*PGood :=
      mul_le_mul_of_nonneg_left hPbound (by positivity)
    _ = 4*QGood*PGood := by ring

theorem parity_original_XA_actual_HQ_HP_floor_eventually_parity434 (parityFlag : Bool)
    (r₀ k : ℕ) (hr₀ : 1 ≤ r₀) (hk : 0 < k)
    (hkPower : 288*r₀ ≤ 2^k)
    (ε α β c : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hε : 0 < ε) (hεsmall : ε ≤ 1/10)
    (hεBudget : (((k*r₀:ℕ):ℝ))*ε ≤ 1/120)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2)
    (hc : 0 < c) (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop, ∀ (jₓ : ℕ) (hkn : k ≤ jₓ+1) (i : Fin r₀),
      let γ := (sourceOriginalQUniformGamma ε)^(k*r₀)
      let δ := sourceOriginalPGroupParityDelta/2
      let HQ := sourceOriginalQActualHQ r₀ jₓ L
      let HP := sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)
      (sourceOriginalXAGoodPrefactor r₀ L α β c*γ*δ/16)*(HQ*HP) ≤
        parityOriginalParityXA434 parityFlag r₀
          (sourceOriginalQActualBands r₀ jₓ L)
          (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  have hXA := parity_original_XA_actual_good_harmonic_floor_eventually_parity434 parityFlag
    r₀ k hr₀ hk hkPower ε α β c Ψ hΨzero hε.le hεBudget
      hα hαβ hβ hc.le hΨnonneg hΨ
  have hMass := parity_original_QP_actual_good_mass_product_floor_eventually_parity434 parityFlag
    r₀ k hr₀ ε hε hεsmall
  have hLocal := source_original_P_all_actual_local_eventually r₀
  filter_upwards [hXA, hMass, hLocal, eventually_gt_atTop (0:ℝ)]
    with L hXAL hMassL hLocalL hL
  intro jₓ hkn i
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let P := sourceOriginalPAllActualBands r₀ L
  let b : Fin (jₓ+1) := ⟨0,Nat.succ_pos jₓ⟩
  let G := parityOriginalParityQPActualGoodHarmonicMass434 parityFlag r₀ jₓ k L ε b i
  let γ := (sourceOriginalQUniformGamma ε)^(k*r₀)
  let δ := sourceOriginalPGroupParityDelta/2
  let HQ := sourceOriginalQActualHQ r₀ jₓ L
  let HP := sourceLiteralHP P
  let K := sourceOriginalXAGoodPrefactor r₀ L α β c
  let XA := parityOriginalParityXA434 parityFlag r₀ Q P (Real.exp L) Ψ
  have hGoodRaw := hMassL jₓ i
  have hGood : (γ*δ)*(HQ*HP) ≤ 4*G := by
    dsimp only [G]
    rw [parity_original_QP_actual_good_harmonic_product_parity434 parityFlag]
    rw [source_original_labelled_Q_harmonic_mass r₀
      (sourceOriginalQActualBands r₀ jₓ L)] at hGoodRaw
    simpa only [γ, δ, HQ, HP, G, Q, P, b,
      sourceOriginalQActualHQ, parityOriginalParityPActualGoodHarmonicMass434,
      mul_assoc] using hGoodRaw
  have hFloor : K*G ≤ XA := by
    dsimp [K, G, XA, Q, P, b]
    exact hXAL jₓ hkn i
  have hγ : 0 ≤ γ := by
    dsimp [γ]
    exact (pow_pos (source_original_Q_uniform_gamma_positive_le_one
      ε hε hεsmall).1 _).le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact (div_pos source_original_P_group_parity_delta_positive
      (by norm_num)).le
  have h3 : ∀ g p, p ∈ P g → 3 ≤ p := by
    intro g p hp
    exact (by norm_num : 3 ≤ 6).trans (hLocalL.2.1 g p hp)
  have hHP : 0 ≤ HP := by
    dsimp [HP]
    exact (source_literal_HP_one_le P h3 hLocalL.1).trans' (by norm_num)
  have hK : 0 ≤ K := by
    dsimp [K, sourceOriginalXAGoodPrefactor]
    have hs : 0 < sourceOriginalQ0Scale r₀ := by
      unfold sourceOriginalQ0Scale
      positivity
    have hd : 0 < (6/5:ℝ)*sourceOriginalQ0Scale r₀-
        sourceOriginalQ0Scale r₀/30 :=
      source_original_Q0_denominator_pos _ hs
    have hlog : 0 < Real.log (β/α) := Real.log_pos
      ((one_lt_div (by linarith : 0 < α)).2 hαβ)
    positivity
  have hNonneg : 0 ≤ (γ*δ)*(HQ*HP) := by
    have hHQ : 0 ≤ HQ := by
      dsimp [HQ, sourceOriginalQActualHQ]
      positivity
    positivity
  have hWeak : (γ*δ)*(HQ*HP)/16 ≤ G := by
    have hG : 0 ≤ G := by nlinarith [hGood]
    nlinarith [hGood]
  calc
    (K*γ*δ/16)*(HQ*HP) = K*((γ*δ)*(HQ*HP)/16) := by ring
    _ ≤ K*G := mul_le_mul_of_nonneg_left hWeak hK
    _ ≤ XA := hFloor

theorem parity_original_XA_fixed_parameter_lower_eventually_parity434 (parityFlag : Bool)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (α β c : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2) (hc : 0 < c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t)
    (jₓ : ℝ → ℕ)
    (hLargest : ∀ᶠ L : ℝ in atTop,
      ∀ j, sourceOriginalDepthAdmissible r₀ j L → j ≤ jₓ L) :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalXAFixedConstant r₀ α β c *
        (Real.exp L/L) *
        (sourceOriginalQActualHQ r₀ (jₓ L) L *
          sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)) ≤
      parityOriginalParityXA434 parityFlag r₀
        (sourceOriginalQActualBands r₀ (jₓ L) L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  let k := 400*r₀
  let ε := sourceOriginalFixedMacroEpsilon r₀
  have hk : 0 < k := by
    dsimp [k]
    exact source_original_fixed_macro_count_pos r₀ hr₀
  have hkPower : 288*r₀ ≤ 2^k := by
    dsimp [k]
    exact source_original_fixed_macro_count_power r₀ hr₀
  have hε : 0 < ε := by
    dsimp [ε]
    exact source_original_fixed_macro_epsilon_pos r₀ hr₀
  have hεsmall : ε ≤ 1/10 := by
    dsimp [ε]
    exact source_original_fixed_macro_epsilon_le_tenth r₀ hr₀
  have hεBudget : ((((k*r₀:ℕ):ℝ))*ε) ≤ 1/120 := by
    dsimp [k, ε]
    exact source_original_fixed_macro_epsilon_budget r₀ hr₀
  have hBase := parity_original_XA_actual_HQ_HP_floor_eventually_parity434 parityFlag
    r₀ k hr₀ hk hkPower ε α β c Ψ hΨzero hε hεsmall hεBudget
      hα hαβ hβ hc hΨnonneg hΨ
  have hDepth := source_original_fixed_depth_below_moving_eventually
    r₀ k hr₀ jₓ hLargest
  filter_upwards [hBase, hDepth, eventually_gt_atTop (0:ℝ)]
    with L hBaseL hkn hL
  have hh := hBaseL (jₓ L) hkn ⟨0,lt_of_lt_of_le (by omega : 0 < 1) hr₀⟩
  let γ := (sourceOriginalQUniformGamma ε)^(k*r₀)
  let δ := sourceOriginalPGroupParityDelta/2
  let d := (6/5:ℝ)*sourceOriginalQ0Scale r₀-sourceOriginalQ0Scale r₀/30
  let HQ := sourceOriginalQActualHQ r₀ (jₓ L) L
  let HP := sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)
  have hs : 0 < sourceOriginalQ0Scale r₀ := by
    unfold sourceOriginalQ0Scale
    have hr : (0:ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < (1:ℕ)) hr₀)
    positivity
  have hd : d ≠ 0 := ne_of_gt (source_original_Q0_denominator_pos _ hs)
  have hRewrite := source_original_XA_prefactor_extract
    α c (Real.log (β/α)) γ δ d (Real.exp L) L HQ HP hd (ne_of_gt hL)
  dsimp [sourceOriginalXAGoodPrefactor, γ, δ, d, HQ, HP] at hRewrite
  dsimp only [sourceOriginalXAGoodPrefactor] at hh
  rw [hRewrite] at hh
  simpa only [sourceOriginalXAFixedConstant, k, ε] using hh

theorem parity_original_XA_literal_depth_lower_eventually_parity434 (parityFlag : Bool)
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (α β c : ℝ) (Ψ : ℝ → ℝ) (hΨzero : Ψ 0 = 0)
    (hα : 1 < α) (hαβ : α < β) (hβ : β < 2) (hc : 0 < c)
    (hΨnonneg : ∀ t, 0 ≤ Ψ t)
    (hΨ : ∀ t, α ≤ t → t ≤ β → c ≤ Ψ t) :
    ∀ᶠ L : ℝ in atTop,
      sourceOriginalXAFixedConstant r₀ α β c *
        (Real.exp L/L) *
        (sourceOriginalQActualHQ r₀ (sourceOriginalLiteralDepth r₀ L) L *
          sourceLiteralHP (sourceOriginalPAllActualBands r₀ L)) ≤
      parityOriginalParityXA434 parityFlag r₀
        (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
        (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ := by
  exact parity_original_XA_fixed_parameter_lower_eventually_parity434 parityFlag
    r₀ hr₀ α β c Ψ hΨzero hα hαβ hβ hc hΨnonneg hΨ
    (sourceOriginalLiteralDepth r₀)
    ((source_original_literal_depth_properties_eventually r₀ hr₀).mono
      fun L h => h.2)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ParityActualRoughSupport -/

section

set_option maxHeartbeats 3000000
set_option linter.deprecated false
open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- The literal negative parity weight vanishes at zero. -/
theorem b640_original_A_zero434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) :
    sourceOriginalA r Q P 0 = 0 := by
  simp [sourceOriginalA, sourceOriginalPParityExponent]

/-- Every prime divisor of a nonzero original weight occurs in an
actual P group or an actual Q slot. All multiplicities are retained. -/
theorem b640_original_A_prime_support434
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ) (u p : ℕ)
    (hQ : ∀ b q, q ∈ Q b → q.Prime)
    (hA : sourceOriginalA r Q P u ≠ 0) (hp : p.Prime) (hpu : p ∣ u) :
    p ∈ Finset.univ.biUnion P ∨ ∃ b, p ∈ Q b := by
  classical
  by_cases hP : p ∈ Finset.univ.biUnion P
  · exact Or.inl hP
  right
  have hu : u ≠ 0 := by
    intro h
    exact hA (h ▸ b640_original_A_zero434 r Q P)
  have hc : sourceOriginalOrdinaryCoefficient r Q
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u) ≠ 0 := by
    intro h
    apply hA
    simp only [sourceOriginalA, sourceOriginalA0, h, mul_zero, zero_mul]
  have ht : ∃ f : (b : B) → Fin r → {q // q ∈ Q b},
      (∏ b : B, ∏ i : Fin r, (f b i).val) =
        sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u := by
    by_contra h
    exact hc (by simp only [sourceOriginalOrdinaryCoefficient, if_neg h])
  obtain ⟨f,hf⟩ := ht
  have hpOrd : p ∣ sourceOriginalOrdinaryPart (Finset.univ.biUnion P) u := by
    have hm : p ∈ u.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpu,hu⟩
    have he : 0 < u.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hp hu).mp hpu
    exact (dvd_pow_self p he.ne').trans
      (Finset.dvd_prod_of_mem (fun q => q^u.factorization q)
        (Finset.mem_sdiff.mpr ⟨hm,hP⟩))
  rw [← hf] at hpOrd
  obtain ⟨b,hb,hbp⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
    (fun b : B => ∏ i : Fin r, (f b i).val)).mp hpOrd
  obtain ⟨i,hi,hip⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)
    (fun i : Fin r => (f b i).val)).mp hbp
  have heq : p=(f b i).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hQ b _ (f b i).property)).mp hip
  exact ⟨b,heq ▸ (f b i).property⟩

/-- The actual largest moving Q depth gives the literal L^20 lower
prime cutoff in every Q band, including the final band. -/
theorem b640_actual_Q_prime_lower434
    (L : ℝ) (hL : 1 ≤ L)
    (hd : sourceOriginalDepthAdmissible 20 (sourceOriginalLiteralDepth 20 L) L)
    (j : Fin (sourceOriginalLiteralDepth 20 L+1)) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands 20
      (sourceOriginalLiteralDepth 20 L) L j) : L^20 ≤ (p:ℝ) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hscale := b635_admissible_all_scales434 20
    (sourceOriginalLiteralDepth 20 L) j.val L (by norm_num) hLp.le hd
    (by omega)
  have hRange := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hBand : Real.exp (sourceOriginalQActualExponent 20 j.val*L) ≤ (p:ℝ) := by
    have hcast : (⌈Real.exp (sourceOriginalQActualExponent 20 j.val*L)⌉₊:ℝ) ≤ p := by
      exact_mod_cast hRange
    exact (Nat.le_ceil _).trans hcast
  have hpow : Real.exp (20*Real.log L) = L^20 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hLp] using (Real.exp_nat_mul (Real.log L) 20)
  exact hpow ▸ (Real.exp_le_exp.mpr hscale).trans hBand

/-- On every true P group the lower logarithmic endpoint is at least
L^(1/10), hence eventually exceeds 20 log L uniformly in the group. -/
theorem b640_actual_P_prime_lower_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ g p,
      p ∈ sourceOriginalPAllActualBands 20 L g → L^20 ≤ (p:ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0:ℝ) < 1/10)).bound (by norm_num : (0:ℝ) < 1/20)
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with L hsmall hL
  intro g p hp
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hrpow : 0 ≤ L^((1:ℝ)/10) := Real.rpow_nonneg hLp.le _
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hrpow] at hsmall
  have hscale : 20*Real.log L ≤ (3/2:ℝ)*sourceOriginalPGroupScale 20 L g.val :=
    (by linarith : 20*Real.log L ≤ L^((1:ℝ)/10)).trans
      (source_original_P_all_actual_band_lower 20 L hL g)
  have hBand := (source_original_P_closed_range
    ((3/2:ℝ)*sourceOriginalPGroupScale 20 L g.val) p hp).1
  have hpow : Real.exp (20*Real.log L) = L^20 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hLp] using (Real.exp_nat_mul (Real.log L) 20)
  exact hpow ▸ (Real.exp_le_exp.mpr hscale).trans hBand

/-- Genuine L^20 roughness of every u carrying the original r=20
negative-parity weight. No rough-support hypothesis is assumed. -/
theorem b640_parity_actual_weight_prime_lower_eventually434 :
    ∀ᶠ L : ℝ in atTop, ∀ u p : ℕ,
      sourceOriginalA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) u ≠ 0 →
      p.Prime → p ∣ u → L^20 ≤ (p:ℝ) := by
  filter_upwards [source_original_literal_depth_properties_eventually 20 (by norm_num),
    b640_actual_P_prime_lower_eventually434,eventually_ge_atTop (1:ℝ)]
    with L hdepth hP hL
  intro u p hA hp hpu
  rcases b640_original_A_prime_support434 20
    (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
    (sourceOriginalPAllActualBands 20 L) u p
    (source_original_Q_actual_prime 20 (sourceOriginalLiteralDepth 20 L) L)
    hA hp hpu with hPmem | ⟨j,hj⟩
  · obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hPmem
    exact hP g p hpg
  · exact b640_actual_Q_prime_lower434 L hL hdepth.1 j p hj

end Green64Analytic.SourceBlockSieve

end

/-! ## ActualParityIndependentSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option maxRecDepth 16000

/-- Literal independent-residue root-kernel bound with the same complete
original r20 prime families, RAW/comparison patterns and canonical Knu. -/
def B642ActualParityIndependentBound434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi E zeta theta : ℝ) (shift : ℤ) : Prop := by
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  exact
    ‖memoryIndependentRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
      J 1 m pats (1/2:ℝ)
      (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)
      Knu zeta theta shift (Nat.ceil (L^(0.52:ℝ)))‖  ≤  L^(-E*(N:ℝ))

/-- The same positive original source tuple now controls OLD, Memory AND
its exact independent-residue root. No physical-integer transference or
endpoint pairing is silently inferred from this kernel identity. -/
theorem b642_eventually_actual_parity_independent_saving434
    (E Cfreq Ck : ℝ) (hE : 0 < E) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧ 0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (zeta theta : ℝ), |zeta| ≤ L^Cfreq →
      ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
        B636ActualParityMemoryBounds434 L hS J m hmJ Q h xi E zeta theta (2*k) ∧
        B642ActualParityIndependentBound434 L hS J m hmJ Q h xi E zeta theta (2*k) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hRoot⟩ :=
    b636_eventually_actual_parity_memory_saving434 E Cfreq Ck hE
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hRoot,b642_eventually_actual_parity_memory_identity434 Ck] with L hRoot hId
  dsimp only at hRoot ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,hRoot⟩ := hRoot
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,?_⟩
  intro hS zeta theta hzeta k hk hkcap
  have hb := hRoot hS zeta theta hzeta k hk hkcap
  have hid := hId.2 hS k hk hkcap J m hmJ (Nat.ceil (4*L^(D+1)))
    (Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)) (L^(-(Cxi:ℝ))) zeta theta
  refine ⟨hb,?_⟩
  dsimp only [B642ActualParityIndependentBound434]
  dsimp only [B642ActualParityRootIdentity434] at hid
  rw [hid]
  exact hb.2
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityPhysicalSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

/-- Unconditional signed cancellation for the complete original Parity
physical marked path sum, on every long integer interval. The source
tuple is fixed before L. The CRT accuracy is chosen only after the true
all-path mass exponent C is known, so no circular choice of J is used.
All initial masses, actual P primes, physical Knu, phases and shift 2k
are retained. This is not yet a spectral endpoint or Type II estimate. -/
theorem b645_eventually_actual_parity_physical_saving434
    (E Cfreq Ck gamma : ℝ) (hE : 0<E) (hgamma : 0<gamma) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      let N := 2*Nat.ceil (L^(13/25:ℝ))
      0<Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0<h ∧ h+h ≤ 1 ∧ 0<xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (zeta theta : ℝ), |zeta| ≤ L^Cfreq →
      ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (lo hi : ℕ), Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
        ‖b645ActualParityPhysicalPathSum434 L hS J m hmJ Q h xi zeta theta (2*k) N lo hi‖  ≤ 
        ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ)) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hRoot⟩ :=
    b642_eventually_actual_parity_independent_saving434 (E+1) Cfreq Ck (by linarith)
  obtain ⟨C,hC,hMass⟩ := b644_eventually_actual_parity_absolute_path_mass434 J m Cq Cxi hmJ
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hRoot,hMass,
    b645_eventually_actual_parity_physical_root_transfer434 (E+C+1) gamma (by linarith) hgamma J m hmJ,
    eventually_ge_atTop (2:ℝ)] with L hRoot hMass hTransfer hL2
  dsimp only at hRoot ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,hRoot⟩ := hRoot
  obtain ⟨hL0,hSMass,hMass⟩ := hMass
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,?_⟩
  intro hS zeta theta hzeta k hk hkcap lo hi hH
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let R := Nat.ceil (L^(13/25:ℝ))
  let N := 2*R
  let H : ℝ := ((hi-lo:ℕ):ℝ)
  let P := b645ActualParityPhysicalPathSum434 L hS J m hmJ Q h xi zeta theta (2*k) N lo hi
  let SP := SourceNativeMemorySP434 20 L hS
  let BP := SourceNativeMemoryBP434 20 L
  let pats := sourceOriginalMemoryRawComparisonPattern434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) J m hmJ
  let Knu := sourceOriginalMemoryRawComparisonK434
    (sourceNativeOriginalTb434 20 L) (sourceNativeOriginalVbig434 20 L)
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L)
    J 1 m hmJ Q (fun _ => h) (fun _ => h) xi
  let I := memoryIndependentRoot SP (fun _ p => p.val) BP (fun _ p => p.val)
    J 1 m pats (1/2:ℝ) (SourceNativeMemorySmallMass434 20 L hS)
    (sourceNativeOriginalVbig434 20 L) Knu zeta theta (2*k) R
  let mass := b644ActualParityAbsoluteArrayMass434 L hS J m hmJ Q h xi zeta theta (2*k) N
  have hI : ‖I‖ ≤ L^(-(E+1)*(N:ℝ)) := by
    have hi := (hRoot hS zeta theta hzeta k hk hkcap).2
    have hp : (0.52:ℝ)=(13/25:ℝ) := by norm_num
    simpa only [B642ActualParityIndependentBound434,hp] using hi
  have hM : mass ≤ L^(C*(N:ℝ)) := hMass hS Q h xi zeta theta (2*k) N hQcap hh hxi hxicap
  have hT : ‖P-(H:ℂ)*I‖ ≤ H*L^(-(E+C+1)*(N:ℝ))*mass :=
    hTransfer.2 hS Q h xi zeta theta (2*k) lo hi hH
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hEpow : 0 ≤ L^(-(E+C+1)*(N:ℝ)) := Real.rpow_nonneg hL0.le _
  have hErr : ‖P-(H:ℂ)*I‖ ≤ H*L^(-(E+1)*(N:ℝ)) := by
    calc
      _  ≤  H*L^(-(E+C+1)*(N:ℝ))*L^(C*(N:ℝ)) :=
        hT.trans (mul_le_mul_of_nonneg_left hM (mul_nonneg hH0 hEpow))
      _ = _ := by
        rw [mul_assoc,← Real.rpow_add hL0]
        congr 2
        ring
  have hMain : ‖(H:ℂ)*I‖ ≤ H*L^(-(E+1)*(N:ℝ)) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hH0]
    exact mul_le_mul_of_nonneg_left hI hH0
  have hR : 0<R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hL0 _)
  have hN : 1 ≤ (N:ℝ) := by
    have hn : 1 ≤ N := by dsimp [N]; omega
    exact_mod_cast hn
  have hfactor : 2 ≤ L^(N:ℝ) :=
    hL2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (show 1 ≤ L by linarith) hN)
  have hAbsorb : 2*L^(-(E+1)*(N:ℝ)) ≤ L^(-E*(N:ℝ)) := by
    calc
      _  ≤  L^(N:ℝ)*L^(-(E+1)*(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hL0.le _)
      _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring
  change ‖P‖ ≤ H*L^(-E*(N:ℝ))
  calc
    _ = ‖(P-(H:ℂ)*I)+(H:ℂ)*I‖ := by rw [sub_add_cancel]
    _  ≤  ‖P-(H:ℂ)*I‖+‖(H:ℂ)*I‖ := norm_add_le _ _
    _  ≤  H*L^(-(E+1)*(N:ℝ))+H*L^(-(E+1)*(N:ℝ)) := add_le_add hErr hMain
    _ = H*(2*L^(-(E+1)*(N:ℝ))) := by ring
    _  ≤  _ := mul_le_mul_of_nonneg_left hAbsorb hH0
end Green64Analytic.SourceBlockSieve

end

end

/-! ## Conductor001 -/

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
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoDeletedCoefficientPolylog.lean; original line 87. -/
noncomputable def sourceDeletedCoefficientExponent : ℝ :=
  (3 + (Real.log 2)⁻¹) * Real.log (max (2/(Real.log (12/11:ℝ)/4)) 2)

/- The actual source06 residual integer coefficient obeys the required
uniform polylog pointwise bound. PNT supplies band nonemptiness and floors;
neither is an added assumption. -/



/- Exact source owner: SourceShiftTwoDeletedSlotConvolution.lean; original line 9. -/
noncomputable def sourceDeletedQCoefficient
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r) (v : ℕ) : ℝ :=
  ∑ rest : (k : {k : B × Fin r // k ≠ (b,i)}) → {p // p ∈ Q k.1.1},
    if (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val) = v
    then ∏ _b : B, (1:ℝ)/(r.factorial:ℝ) else 0



/- Exact source owner: SourceShiftTwoDeletedWeightConvolution.lean; original line 41. -/
noncomputable def sourceDeletedWeight
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (R : ℕ) : ℝ :=
  sourceOriginalW1 P R *
    sourceDeletedQCoefficient r Q b i
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) R) *
    ((1-(-1:ℝ)^sourceOriginalPParityExponent (Finset.univ.biUnion P) R)/2)

/- Source A itself is the long-prime convolution. Every P group, its
normalization, all Q bands, all factorials, repeats, and parity survive. -/



/- Exact source owner: SourceShiftTwoActualDeletedConvolution.lean; original line 11. -/
noncomputable def sourceOriginalDeletedMovingCoefficient
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (L : ℝ) (R : ℕ) : ℝ :=
  sourceDeletedWeight r₀
    (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
    (sourceOriginalPAllActualBands r₀ L)
    ⟨0, by omega⟩ ⟨0, by omega⟩ R

/- The actual moving source weight, with its exact natural cutoff and
all original prime bands, has the source06 long Q0 prime convolution. -/



/- Exact source owner: SourceShiftTwoFourierBox.lean; original line 56. -/
noncomputable def sourceDeletedSmoothBoxCharacter
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ)
    (h M₁ N₁ M₂ N₂ d : ℕ) (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ p ∈ Finset.Ioc M₁ (M₁+N₁), ∑ R ∈ Finset.Ioc M₂ (M₂+N₂),
    if (p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ∧ p.Coprime h) ∧ R.Coprime h
    then (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
      (Ψ (((p*R : ℕ) : ℝ)/Real.exp L) : ℂ) * χ p * χ R else 0

/- Original smooth Ψ and true residual coefficient, retaining both masks.
Only ordinary Mellin inversion is a premise; no character estimate is assumed. -/



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 10. -/
def sourceEchiDyadLower (j : ℕ) : ℕ := 2^j-1



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 11. -/
def sourceEchiDyad (j : ℕ) : Finset ℕ :=
  Finset.Ioc (sourceEchiDyadLower j) (sourceEchiDyadLower j+2^j)



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 11. -/
noncomputable def sourceLogProfile (Ψ : ℝ → ℝ) (v : ℝ) : ℂ :=
  (Ψ (Real.exp (2 * Real.pi * v)) : ℂ)



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 17. -/
noncomputable def sourceLogMellinMass (Ψ : ℝ → ℝ) : ℝ :=
  ∫ t, ‖(𝓕 (sourceLogProfile Ψ)) t‖



/- Exact source owner: SourceShiftTwoGlobalConductorBudget.lean; original line 28. -/
noncomputable def sourceEchiLargeBoxBudget (Ψ : ℝ → ℝ) (L : ℝ)
    (s : ℕ) (a : ℕ×ℕ) : ℝ :=
  (Real.sqrt (((((2*2^s:ℕ):ℝ)^2 + Real.pi*(2^a.1:ℕ))/(2^s:ℕ))*(2^a.1:ℕ)) *
    Real.sqrt (((((2*2^s:ℕ):ℝ)^2 + Real.pi*(2^a.2:ℕ))/(2^s:ℕ))*
      ((2^a.2:ℕ)*(L^sourceDeletedCoefficientExponent)^2))) *
        sourceLogMellinMass Ψ

/- The literal primitive source-box large-sieve theorem, now in global
conductor dyads. Its bound is independent of h; both h masks remain. -/



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 35. -/
def sourceEchiCompatible (L : ℝ) (j k : ℕ) : Prop :=
  Real.exp L < 4*(2:ℝ)^j*(2:ℝ)^k ∧
    (2:ℝ)^j*(2:ℝ)^k ≤ 2*Real.exp L



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 39. -/
noncomputable def sourceEchiSourceBoxes (r₀ : ℕ) (L : ℝ) (J : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range J) ×ˢ (Finset.range J)).filter (fun a =>
    ((sourceEchiDyad a.1).filter (fun p =>
      p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)))).Nonempty ∧
      sourceEchiCompatible L a.1 a.2)



/- Exact source owner: SourceShiftTwoSmallConductorAbel.lean; original line 45. -/
noncomputable def sourcePsiDiscreteVariation (Ψ : ℝ → ℝ) (L : ℝ)
    (M N R : ℕ) : ℝ :=
  ‖(Ψ (((M+(N-1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ)‖ +
    ∑ i ∈ Finset.range (N-1),
      ‖(Ψ (((M+(i+1)+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ) -
        (Ψ (((M+i+1:ℕ):ℝ)*(R:ℝ)/Real.exp L) : ℂ)‖

/- Raw source prime partial sums to the true Ψ-smoothed Q0 sum by Abel.
The only cancellation premise is a literal unweighted prime prefix bound. -/



/- Exact source owner: SourceOriginalShiftTwoExtractionContract.lean; original line 7. -/
noncomputable def sourceOriginalMovingWeight
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (u : ℕ) : ℝ :=
  sourceOriginalA r₀
    (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
    (sourceOriginalPAllActualBands r₀ L) u * Ψ ((u:ℝ)/Real.exp L)



/- Exact source owner: SourceShiftTwoGenuineRemainder.lean; original line 24. -/
noncomputable def sourceShiftTwoCharacterL1
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (d : ℕ) : ℝ :=
  if hd : d = 0 then 0 else
    letI : NeZero d := ⟨hd⟩
    letI : DecidableEq (DirichletCharacter ℂ d) := fun a b => Classical.propDecidable (a = b)
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
      ‖∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        (sourceOriginalMovingWeight r₀ Ψ L u : ℂ) * χ (u : ZMod d)‖

/- Exact principal correction, retaining source weights on nonunits. -/



/- Exact source owner: SourceShiftTwoLogMellin.lean; original line 73. -/
theorem source_log_mellin_mass_nonneg (Ψ : ℝ → ℝ) :
    0 ≤ sourceLogMellinMass Ψ := integral_nonneg (fun t => norm_nonneg _)

/- Genuine original Ψ inversion, no assumed Mellin equation. Both arguments
must be positive; every Ioc source box used downstream meets this obligation. -/



/- Exact source owner: SourceShiftTwoGlobalSourceBoxMajorant.lean; original line 8. -/
noncomputable def sourceOriginalPrimitiveBoxMass
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ)
    (f h : ℕ) (a : ℕ×ℕ) : ℝ :=
  if hf0 : f = 0 then 0 else
    letI : NeZero f := ⟨hf0⟩
    if f = 1 then 0 else
      (f.totient:ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ f, if χ.IsPrimitive then
          ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
            (sourceEchiDyadLower a.1) (2^a.1)
            (sourceEchiDyadLower a.2) (2^a.2) f χ‖ else 0



/- Exact source owner: SourceShiftTwoTotientHarmonic.lean; original line 12. -/
noncomputable def sourceSquarefreeTotientSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, if Squarefree d then (d.totient : ℝ)⁻¹ else 0



/- Exact source owner: SourceShiftTwoGlobalConductorBudget.lean; original line 7. -/
theorem source_conductor_dyadic_sum {V : Type} [AddCommMonoid V]
    (S : ℕ) (g : ℕ → V) :
    (∑ f ∈ Finset.Ioc 1 (2^S), g f) =
      ∑ s ∈ Finset.range S, ∑ f ∈ Finset.Ioc (2^s) (2*2^s), g f := by
  induction S with
  | zero => simp
  | succ S ih =>
    have hpow : 2^S ≤ 2^(S+1) := by
      rw [pow_succ]
      omega
    have hlow : 1 ≤ 2^S := Nat.one_le_two_pow
    have hd : Disjoint (Finset.Ioc 1 (2^S)) (Finset.Ioc (2^S) (2^(S+1))) := by
      apply Finset.disjoint_left.mpr
      intro f hf hg
      have := Finset.mem_Ioc.mp hf
      have := Finset.mem_Ioc.mp hg
      omega
    rw [← Finset.Ioc_union_Ioc_eq_Ioc hlow hpow,Finset.sum_union hd,
      ih,Finset.sum_range_succ,pow_succ]
    rw [mul_comm (2^S) 2]



/- Exact source owner: SourceShiftTwoConductorEchi.lean; original line 9. -/
noncomputable def sourceOriginalConductorConvolution
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (f h : ℕ)
    (ψ : DirichletCharacter ℂ f) : ℂ :=
  ∑ p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)),
    ∑ R ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      if p*R < ⌊2*Real.exp L⌋₊+1 ∧ p.Coprime h ∧ R.Coprime h then
        (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
          (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ) * ψ p * ψ R
      else 0

/- Exact per-modulus Echi conductor identity, principal f=1 omitted. -/



/- Exact source owner: SourceShiftTwoGlobalConductorSum.lean; original line 7. -/
noncomputable def sourceOriginalPrimitiveConductorMass
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (f h : ℕ) : ℝ :=
  if hf0 : f = 0 then 0 else
    letI : NeZero f := ⟨hf0⟩
    if f = 1 then 0 else
      (f.totient : ℝ)⁻¹ * (h.totient : ℝ)⁻¹ *
        ∑ ψ : DirichletCharacter ℂ f, if ψ.IsPrimitive then
          ‖sourceOriginalConductorConvolution r₀ hr₀ Ψ L f h ψ‖ else 0



/- Exact source owner: SourceShiftTwoGlobalConductorSum.lean; original line 54. -/
theorem source_odd_squarefree_divisor_factor_reindex
    (Q : ℕ) (G : ℕ → ℕ → ℝ) :
    (∑ d ∈ (Finset.range (Q+1)).filter (fun d => Odd d ∧ Squarefree d),
      ∑ f ∈ d.divisors, G f (d/f)) =
      ∑ a ∈ ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter
        (fun a => a.1*a.2 ≤ Q ∧ Odd (a.1*a.2) ∧ Squarefree (a.1*a.2)), G a.1 a.2 := by
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun a _ => (a.2, a.1/a.2))
  · intro a ha
    have hs := Finset.mem_sigma.mp ha
    have hd := Finset.mem_filter.mp hs.1
    have hf := Nat.mem_divisors.mp hs.2
    have hdpos : 0 < a.1 := hd.2.1.pos
    have hfpos : 0 < a.2 := by
      by_contra h
      have hz : a.2 = 0 := by omega
      rw [hz] at hf
      exact hf.2 (Nat.eq_zero_of_zero_dvd hf.1)
    have hfle : a.2 ≤ a.1 := Nat.le_of_dvd hdpos hf.1
    have he : a.2 * (a.1/a.2) = a.1 := Nat.mul_div_cancel' hf.1
    have hq : a.1 ≤ Q := by have := Finset.mem_range.mp hd.1; omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hfpos,hfle.trans hq⟩,
      Finset.mem_Icc.mpr ⟨Nat.div_pos hfle hfpos, (Nat.div_le_self _ _).trans hq⟩⟩, ?_⟩
    simpa only [he] using And.intro hq hd.2
  · intro a ha b hb he
    have hfa := (Nat.mem_divisors.mp (Finset.mem_sigma.mp ha).2).1
    have hfb := (Nat.mem_divisors.mp (Finset.mem_sigma.mp hb).2).1
    have hf : a.2 = b.2 := congrArg Prod.fst he
    have hh : a.1/a.2 = b.1/b.2 := congrArg Prod.snd he
    have hd : a.1 = b.1 := by
      calc
        a.1 = a.2*(a.1/a.2) := (Nat.mul_div_cancel' hfa).symm
        _ = b.2*(b.1/b.2) := by rw [hh,hf]
        _ = b.1 := Nat.mul_div_cancel' hfb
    exact Sigma.ext hd (by cases a; cases b; dsimp at *; subst hd; simpa using hf)
  · intro a ha
    have hs := Finset.mem_filter.mp ha
    have hfr := (Finset.mem_product.mp hs.1).1
    have hhr := (Finset.mem_product.mp hs.1).2
    have hfpos := (Finset.mem_Icc.mp hfr).1
    refine ⟨⟨a.1*a.2,a.1⟩, ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp only; omega), hs.2.2⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, hs.2.2.2.ne_zero⟩⟩
    · simp only
      rw [Nat.mul_div_cancel_left _ hfpos]
  · intro a ha
    rfl

/- Global actual Echi = the sum over d=f*h, with no lost masks or repeated
primitive character. This finite identity leaves cancellation as the sole
analytic use of these terms; it does not assert the missing SW theorem. -/



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 8. -/
abbrev SourcePrimitiveFibres (d : ℕ) :=
  Σ f : ↥d.divisors, {ψ : DirichletCharacter ℂ f.val // ψ.IsPrimitive}



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 54. -/
theorem source_change_level_complement_mask (d f : ℕ) (hf : f ∣ d)
    (ψ : DirichletCharacter ℂ f) (n : ℕ) :
    (DirichletCharacter.changeLevel hf ψ) (n : ZMod d) =
      if n.Coprime (d/f) then ψ (n : ZMod f) else 0 := by
  have hprod : f * (d/f) = d := Nat.mul_div_cancel' hf
  by_cases hn : n.Coprime (d/f)
  · rw [if_pos hn]
    by_cases hnf : n.Coprime f
    · have hnd : n.Coprime d := by
        rw [← hprod, Nat.coprime_mul_iff_right]
        exact ⟨hnf, hn⟩
      have hi : IsCoprime (n : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.mpr hnd
      simpa only [Int.cast_natCast] using
        DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hf hi
    · have hnd : ¬ n.Coprime d := by
        rw [← hprod, Nat.coprime_mul_iff_right]
        tauto
      rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]),
        MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
  · rw [if_neg hn]
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime, ← hprod, Nat.coprime_mul_iff_right]
    tauto



/- Exact source owner: SourceShiftTwoActualCharacterConvolution.lean; original line 8. -/
theorem source_finite_prime_multiple_reindex
    {V : Type} [AddCommMonoid V] (p N : ℕ) (hp : 0 < p) (F : ℕ → V) :
    (∑ u ∈ Finset.range N, if p ∣ u then F u else 0) =
      ∑ R ∈ Finset.range N, if p*R < N then F (p*R) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u/p)
  · intro u hu
    have h := Finset.mem_filter.mp hu
    have huN := Finset.mem_range.mp h.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ((Nat.div_le_self u p).trans_lt huN), ?_⟩
    rw [Nat.mul_div_cancel_left' h.2]
    exact huN
  · intro u hu v hv he
    have hdu := (Finset.mem_filter.mp hu).2
    have hdv := (Finset.mem_filter.mp hv).2
    calc
      u = p*(u/p) := (Nat.mul_div_cancel_left' hdu).symm
      _ = p*(v/p) := by rw [he]
      _ = v := Nat.mul_div_cancel_left' hdv
  · intro R hR
    have hRN := (Finset.mem_filter.mp hR).2
    refine ⟨p*R, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hRN, dvd_mul_right p R⟩, ?_⟩
    exact Nat.mul_div_cancel_left R hp
  · intro u hu
    rw [Nat.mul_div_cancel_left' (Finset.mem_filter.mp hu).2]

/- Exact original weighted character sum as a prime × residual-integer
convolution. This applies to EVERY character, including imprimitive ones;
it is the physical sum whose nonprincipal L1 saving is still required. -/



/- Exact source owner: SourceShiftTwoOriginalWeights.lean; original line 14. -/
theorem source_ordinary_part_dvd_of_not_mem
    (Pall : Finset ℕ) (u p : ℕ) (hu : u ≠ 0)
    (hp : p.Prime) (hpu : p ∣ u) (hnot : p ∉ Pall) :
    p ∣ sourceOriginalOrdinaryPart Pall u := by
  classical
  have hm : p ∈ u.primeFactors :=
    (Nat.mem_primeFactors).mpr ⟨hp, hpu, hu⟩
  have hf : 0 < u.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hu).mp hpu
  exact (dvd_pow_self p hf.ne').trans
    (Finset.dvd_prod_of_mem (fun q => q ^ u.factorization q)
      (Finset.mem_sdiff.mpr ⟨hm, hnot⟩))

/- The exact multiplicity-preserving n_* always divides n. -/



/- Exact source owner: SourceShiftTwoDeletedWeightConvolution.lean; original line 9. -/
theorem source_ordinary_part_nonP_prime_mul
    (Pall : Finset ℕ) (p R : ℕ) (hp : p.Prime) (hR : R ≠ 0)
    (hP : ∀ q ∈ Pall, q.Prime) (hnot : p ∉ Pall) :
    sourceOriginalOrdinaryPart Pall (p*R) = p * sourceOriginalOrdinaryPart Pall R := by
  have hNo : ∀ q ∈ Pall, ¬ q ∣ p := by
    intro q hq hdiv
    have he := (Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hdiv
    exact hnot (he ▸ hq)
  have hExpo : sourceOriginalPExponentVector Pall (p*R) =
      sourceOriginalPExponentVector Pall R := by
    funext z
    dsimp [sourceOriginalPExponentVector]
    rw [Nat.factorization_mul hp.ne_zero hR]
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_eq_zero_of_not_dvd (hNo z.val z.property), zero_add]
  have hPart : sourceOriginalPPrimePart Pall (p*R) =
      sourceOriginalPPrimePart Pall R := by
    rw [source_original_P_prime_part_eq_vector_product Pall hP (p*R)
        (mul_ne_zero hp.ne_zero hR),
      source_original_P_prime_part_eq_vector_product Pall hP R hR, hExpo]
  have hs := source_original_ordinary_times_P_part Pall R hR
  have ht := source_original_ordinary_times_P_part Pall (p*R) (mul_ne_zero hp.ne_zero hR)
  rw [hPart] at ht
  have hPP : sourceOriginalPPrimePart Pall R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hs
    exact hR hs.symm
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hPP)
  rw [ht, mul_assoc, hs]

/- Actual residual coefficient b of source06, with the unchanged P marks
and multiplicity-counted odd projection. -/



/- Exact source owner: SourceShiftTwoDeletedSlotConvolution.lean; original line 26. -/
theorem source_original_Q_coefficient_all_assignments
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (v : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    sourceOriginalOrdinaryCoefficient r Q v =
      ∑ f : (b : B) → Fin r → {p // p ∈ Q b},
        if (∏ b : B, ∏ j : Fin r, (f b j).val) = v
        then ∏ _b : B, (1:ℝ)/(r.factorial:ℝ) else 0 := by
  rw [source_original_full_Q_coefficient_finite_sampling r Q v hPrime hDisjoint]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext f
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      source_original_full_Q_canonical_orbit_iff_product r Q v f hPrime hDisjoint
  · intro f hf
    rfl

/- Exact prime convolution with the genuine deleted coefficient. Repeated
Q0 primes are counted correctly: no squarefree hypothesis on v. -/



/- Exact source owner: SourceShiftTwoDeletedSlotConvolution.lean; original line 46. -/
theorem source_original_Q_deleted_slot_convolution
    {B : Type} [Fintype B] [DecidableEq B]
    (r : ℕ) (Q : B → Finset ℕ) (b : B) (i : Fin r) (v : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    sourceOriginalOrdinaryCoefficient r Q v =
      ∑ p ∈ Q b, if p ∣ v then sourceDeletedQCoefficient r Q b i (v/p) else 0 := by
  classical
  let C : ℝ := ∏ _b : B, (1:ℝ)/(r.factorial:ℝ)
  let F (f : (j : B) → Fin r → {p // p ∈ Q j}) : ℝ :=
    if (∏ j : B, ∏ m : Fin r, (f j m).val) = v then C else 0
  let e := sourceOriginalQSlotsCurryEquiv r Q
  rw [source_original_Q_coefficient_all_assignments r Q v hPrime hDisjoint]
  change (∑ f, F f) = _
  rw [← Equiv.sum_comp e F]
  rw [source_full_Q_one_free_slot_sum r Q b i (fun f => F (e f))]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : {p // p ∈ Q b},
        if p.val ∣ v then sourceDeletedQCoefficient r Q b i (v/p.val) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold sourceDeletedQCoefficient
      by_cases hd : p.val ∣ v
      · rw [if_pos hd]
        apply Finset.sum_congr rfl
        intro rest hrest
        dsimp only [F, e]
        rw [source_original_Q_free_slot_product_exact r Q b i p rest]
        have hp0 := (hPrime b p.val p.property).pos
        have hiff : p.val * (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val) = v ↔
            (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val) = v/p.val := by
          constructor
          · intro he
            rw [← he, Nat.mul_div_cancel_left _ hp0]
          · intro he
            rw [he, Nat.mul_div_cancel_left' hd]
        simp only [hiff]
        rfl
      · rw [if_neg hd]
        apply Finset.sum_eq_zero
        intro rest hrest
        dsimp only [F, e]
        rw [source_original_Q_free_slot_product_exact r Q b i p rest]
        have hn : p.val * (∏ k : {k : B × Fin r // k ≠ (b,i)}, (rest k).val) ≠ v := by
          intro he
          exact hd (he ▸ dvd_mul_right p.val _)
        simp [hn]
    _ = _ := Finset.sum_coe_sort (Q b) (fun p : ℕ =>
      if p ∣ v then sourceDeletedQCoefficient r Q b i (v/p) else 0)



/- Exact source owner: SourceShiftTwoDeletedWeightConvolution.lean; original line 52. -/
theorem source_original_A_deleted_prime_convolution
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (b : B) (i : Fin r) (u : ℕ) (hu : u ≠ 0)
    (hQ : ∀ b p, p ∈ Q b → p.Prime)
    (hDisj : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (hP : ∀ g p, p ∈ P g → p.Prime)
    (hQP : ∀ b g p, p ∈ Q b → p ∈ P g → False) :
    sourceOriginalA r Q P u =
      ∑ p ∈ Q b, if p ∣ u then sourceDeletedWeight r Q P b i (u/p) else 0 := by
  classical
  let Pall := Finset.univ.biUnion P
  have hPall : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    exact hP g p hpg
  unfold sourceOriginalA sourceOriginalA0
  rw [source_original_Q_deleted_slot_convolution r Q b i _ hQ hDisj,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hprime := hQ b p hp
  have hnot : p ∉ Pall := by
    intro h
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp h
    exact hQP b g p hp hpg
  have hiff : p ∣ sourceOriginalOrdinaryPart Pall u ↔ p ∣ u :=
    ⟨fun h => h.trans (source_ordinary_part_dvd Pall u hu),
      fun h => source_ordinary_part_dvd_of_not_mem Pall u p hu hprime h hnot⟩
  by_cases hd : p ∣ u
  · rw [if_pos (hiff.mpr hd), if_pos hd]
    have he : p*(u/p) = u := Nat.mul_div_cancel_left' hd
    have hr : u/p ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at he
      exact hu he.symm
    have hOrd : sourceOriginalOrdinaryPart Pall u / p =
        sourceOriginalOrdinaryPart Pall (u/p) := by
      conv_lhs => rw [← he]
      rw [source_ordinary_part_nonP_prime_mul Pall p (u/p)
        hprime hr hPall hnot, Nat.mul_div_cancel_left _ hprime.pos]
    have hNo : ∀ g q, q ∈ P g → ¬ q ∣ p := by
      intro g q hq hdiv
      have hEq := (Nat.prime_dvd_prime_iff_eq (hP g q hq) hprime).mp hdiv
      exact hQP b g p hp (hEq ▸ hq)
    have hW : sourceOriginalW1 P u = sourceOriginalW1 P (u/p) := by
      conv_lhs => rw [← he]
      exact source_original_W1_nonP_mul P p (u/p) hP hNo
    have hParity : sourceOriginalPParityExponent Pall u =
        sourceOriginalPParityExponent Pall (u/p) := by
      conv_lhs => rw [← he]
      apply source_original_P_multiplicity_nonP_mul Pall p (u/p) hprime.ne_zero hr
      intro q hq hdiv
      have hEq := (Nat.prime_dvd_prime_iff_eq (hPall q hq) hprime).mp hdiv
      exact hnot (hEq ▸ hq)
    change _ = sourceDeletedWeight r Q P b i (u/p)
    unfold sourceDeletedWeight
    rw [hW, hOrd, hParity]
  · rw [if_neg (hiff.not.mpr hd), if_neg hd]
    ring


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Conductor002 -/

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
open Filter Topology Asymptotics MeasureTheory
open scoped BigOperators Classical FourierTransform ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve


/- Exact source owner: SourceShiftTwoActualDeletedConvolution.lean; original line 20. -/
theorem source_original_moving_deleted_prime_convolution
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (u : ℕ) :
    sourceOriginalMovingWeight r₀ Ψ L u =
      (∑ p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
          (⟨0, by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)),
        if p ∣ u then sourceOriginalDeletedMovingCoefficient r₀ hr₀ L (u/p) else 0) *
      Ψ ((u:ℝ)/Real.exp L) := by
  by_cases hu : u = 0
  · subst u
    simp [sourceOriginalMovingWeight, sourceOriginalA, sourceOriginalA0,
      sourceOriginalPParityExponent, sourceOriginalDeletedMovingCoefficient,
      sourceDeletedWeight]
  · unfold sourceOriginalMovingWeight sourceOriginalDeletedMovingCoefficient
    congr 1
    exact source_original_A_deleted_prime_convolution r₀ _ _ _ _ u hu
      (fun j p hp => source_original_Q_actual_prime r₀ _ L j p hp)
      (source_original_Q_actual_all_disjoint r₀ _ L hr₀ hL)
      (source_original_P_all_actual_band_prime r₀ L)
      (source_original_Q_actual_all_P_disjoint r₀ _ L hr₀ hL)



/- Exact source owner: SourceShiftTwoActualCharacterConvolution.lean; original line 38. -/
theorem source_original_actual_character_prime_convolution
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (d : ℕ) (χ : DirichletCharacter ℂ d) :
    (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      (sourceOriginalMovingWeight r₀ Ψ L u : ℂ) * χ (u : ZMod d)) =
      ∑ p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)),
        ∑ R ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
          if p*R < ⌊2*Real.exp L⌋₊+1 then
            (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
              (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ) *
              χ (p : ZMod d) * χ (R : ZMod d)
          else 0 := by
  let Q := sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
    (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
  let N : ℕ := ⌊2*Real.exp L⌋₊+1
  let b := sourceOriginalDeletedMovingCoefficient r₀ hr₀ L
  calc
    _ = ∑ u ∈ Finset.range N, ∑ p ∈ Q,
        if p ∣ u then (b (u/p) : ℂ)*(Ψ ((u:ℝ)/Real.exp L):ℂ)*χ (u : ZMod d) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [source_original_moving_deleted_prime_convolution r₀ hr₀ Ψ L hL u]
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp [b]
    _ = ∑ p ∈ Q, ∑ u ∈ Finset.range N,
        if p ∣ u then (b (u/p):ℂ)*(Ψ ((u:ℝ)/Real.exp L):ℂ)*χ (u : ZMod d) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpPos : 0 < p := (source_original_Q_actual_prime r₀ _ L _ p hp).pos
      have h := source_finite_prime_multiple_reindex p N hpPos
        (fun u => (b (u/p):ℂ)*(Ψ ((u:ℝ)/Real.exp L):ℂ)*χ (u : ZMod d))
      rw [h]
      apply Finset.sum_congr rfl
      intro R hR
      split_ifs
      · rw [Nat.mul_div_cancel_left _ hpPos]
        simp only [Nat.cast_mul, map_mul]
        ring
      · rfl



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 91. -/
theorem source_original_conductor_masked_convolution
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (d f : ℕ) (hf : f ∣ d) (ψ : DirichletCharacter ℂ f) :
    (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      (sourceOriginalMovingWeight r₀ Ψ L u : ℂ) *
        (DirichletCharacter.changeLevel hf ψ) (u : ZMod d)) =
      ∑ p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
        (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)),
        ∑ R ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
          if p*R < ⌊2*Real.exp L⌋₊+1 ∧ p.Coprime (d/f) ∧ R.Coprime (d/f) then
            (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
              (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ) * ψ (p : ZMod f) * ψ (R : ZMod f)
          else 0 := by
  rw [source_original_actual_character_prime_convolution r₀ hr₀ Ψ L hL]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro R hR
  rw [source_change_level_complement_mask d f hf ψ p,
    source_change_level_complement_mask d f hf ψ R]
  split_ifs <;> simp_all



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 11. -/
noncomputable def sourcePrimitiveLift (d : ℕ) (a : SourcePrimitiveFibres d) :
    DirichletCharacter ℂ d :=
  DirichletCharacter.changeLevel (Nat.mem_divisors.mp a.1.property).1 a.2.val



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 15. -/
theorem source_primitive_lift_bijective (d : ℕ) [NeZero d] :
    Function.Bijective (sourcePrimitiveLift d) := by
  constructor
  · rintro ⟨f, ψ⟩ ⟨g, η⟩ he
    have hc := congrArg DirichletCharacter.conductor he
    dsimp [sourcePrimitiveLift] at hc
    rw [DirichletCharacter.conductor_changeLevel,
      DirichletCharacter.conductor_changeLevel, ψ.property, η.property] at hc
    have hfg : f = g := Subtype.ext hc
    subst g
    have hψη : ψ = η := Subtype.ext
      (DirichletCharacter.changeLevel_injective (Nat.mem_divisors.mp f.property).1 he)
    subst η
    rfl
  · intro χ
    refine ⟨⟨⟨χ.conductor, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne d⟩⟩,
      ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩⟩, ?_⟩
    exact χ.changeLevel_primitiveCharacter



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 34. -/
noncomputable def sourcePrimitiveFibreEquiv (d : ℕ) [NeZero d] :
    SourcePrimitiveFibres d ≃ DirichletCharacter ℂ d :=
  Equiv.ofBijective (sourcePrimitiveLift d) (source_primitive_lift_bijective d)

/- Exact finite conductor reindex. No extra character multiplicity occurs. -/



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 39. -/
theorem source_primitive_fibre_sum (d : ℕ) [NeZero d]
    (G : DirichletCharacter ℂ d → ℝ) :
    (∑ χ : DirichletCharacter ℂ d, G χ) =
      ∑ a : SourcePrimitiveFibres d, G (sourcePrimitiveLift d a) :=
  ((sourcePrimitiveFibreEquiv d).sum_comp G).symm

/- Conductor one is exactly principal; this removes the f=1 fibre. -/



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 46. -/
theorem source_primitive_lift_ne_one_iff (d : ℕ) [NeZero d]
    (a : SourcePrimitiveFibres d) : sourcePrimitiveLift d a ≠ 1 ↔ a.1.val ≠ 1 := by
  rw [ne_eq, DirichletCharacter.eq_one_iff_conductor_eq_one]
  unfold sourcePrimitiveLift
  rw [DirichletCharacter.conductor_changeLevel, a.2.property]

/- Lifting a primitive character retains the exact complementary nonunit
mask. This equality even holds for a nonsquarefree modulus. -/



/- Exact source owner: SourceShiftTwoConductorEchi.lean; original line 21. -/
theorem source_original_characterL1_conductor_identity
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (d : ℕ) [NeZero d] :
    sourceShiftTwoCharacterL1 r₀ Ψ L d =
      ∑ a : SourcePrimitiveFibres d, if a.1.val ≠ 1 then
        ‖sourceOriginalConductorConvolution r₀ hr₀ Ψ L a.1.val (d/a.1.val) a.2.val‖ else 0 := by
  have hc := source_primitive_fibre_sum d (fun χ => if χ ≠ 1 then
    ‖∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      (sourceOriginalMovingWeight r₀ Ψ L u : ℂ) * χ (u : ZMod d)‖ else 0)
  have hleft : sourceShiftTwoCharacterL1 r₀ Ψ L d =
      ∑ χ : DirichletCharacter ℂ d, if χ ≠ 1 then
        ‖∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
          (sourceOriginalMovingWeight r₀ Ψ L u : ℂ) * χ (u : ZMod d)‖ else 0 := by
    simp only [sourceShiftTwoCharacterL1, dif_neg (NeZero.ne d)]
    rw [← Finset.sum_filter]
    congr 1
    ext χ
    simp
  rw [hleft, hc]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [source_primitive_lift_ne_one_iff]
  split_ifs
  · congr 1
    exact source_original_conductor_masked_convolution r₀ hr₀ Ψ L hL d a.1.val
      (Nat.mem_divisors.mp a.1.property).1 a.2.val
  · rfl

/- Exact Echi denominator factorization on a squarefree source modulus. -/



/- Exact source owner: SourceShiftTwoConductorFibres.lean; original line 78. -/
theorem source_squarefree_conductor_totient (d f : ℕ) [NeZero d]
    (hd : Squarefree d) (hf : f ∣ d) :
    f.Coprime (d/f) ∧ (d.totient : ℝ) = (f.totient : ℝ) * ((d/f).totient : ℝ) := by
  have hf0 : f ≠ 0 := by intro h; subst f; exact NeZero.ne d (Nat.eq_zero_of_zero_dvd hf)
  have hc : (d/f).Coprime f := by
    simpa only [Nat.gcd_eq_right hf] using Nat.coprime_div_gcd_of_squarefree hd hf0
  refine ⟨hc.symm, ?_⟩
  have he := Nat.totient_mul hc.symm
  rw [Nat.mul_div_cancel' hf] at he
  exact_mod_cast he

/- The exact ORIGINAL weighted sum rewritten along an actual primitive fibre.
Both p and R complementary masks are retained, as is the literal cutoff. -/



/- Exact source owner: SourceShiftTwoConductorEchi.lean; original line 50. -/
theorem source_original_Echi_conductor_identity
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (d : ℕ) [NeZero d] (hd : Squarefree d) :
    sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient : ℝ) =
      ∑ a : SourcePrimitiveFibres d, if a.1.val ≠ 1 then
        (a.1.val.totient : ℝ)⁻¹ * ((d/a.1.val).totient : ℝ)⁻¹ *
          ‖sourceOriginalConductorConvolution r₀ hr₀ Ψ L a.1.val (d/a.1.val) a.2.val‖ else 0 := by
  rw [source_original_characterL1_conductor_identity r₀ hr₀ Ψ L hL,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(source_squarefree_conductor_totient d a.1.val hd
    (Nat.mem_divisors.mp a.1.property).1).2]
  split_ifs <;> simp [div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm]

/- The exact original growing-range terminal sum, now in genuine primitive
conductor fibres. This is an identity, not an unproved cancellation estimate. -/



/- Exact source owner: SourceShiftTwoGlobalConductorSum.lean; original line 22. -/
theorem source_original_Echi_divisor_sum
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (d : ℕ) [NeZero d] (hd : Squarefree d) :
    sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient : ℝ) =
      ∑ f ∈ d.divisors, sourceOriginalPrimitiveConductorMass r₀ hr₀ Ψ L f (d/f) := by
  rw [source_original_Echi_conductor_identity r₀ hr₀ Ψ L hL d hd,
    Fintype.sum_sigma]
  rw [Finset.sum_subtype d.divisors (fun f => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro f hf
  have hf0 : f.val ≠ 0 := by
    intro hz
    have hv := (Nat.mem_divisors.mp f.property).1
    rw [hz] at hv
    exact NeZero.ne d (Nat.eq_zero_of_zero_dvd hv)
  letI : NeZero f.val := ⟨hf0⟩
  dsimp only [sourceOriginalPrimitiveConductorMass]
  rw [dif_neg hf0]
  by_cases hf1 : f.val = 1
  · simp [hf1]
  · simp only [hf1, ne_eq, not_false_eq_true, ite_true, ite_false]
    rw [← Finset.mul_sum]
    congr 1
    have hsub := Finset.sum_subtype (p := fun ψ : DirichletCharacter ℂ f.val => ψ.IsPrimitive) (F := inferInstance)
      ((Finset.univ : Finset (DirichletCharacter ℂ f.val)).filter (fun ψ => ψ.IsPrimitive))
      (fun ψ => by simp)
      (fun ψ => ‖sourceOriginalConductorConvolution r₀ hr₀ Ψ L f.val (d/f.val) ψ‖)
    rw [Finset.sum_filter] at hsub
    exact hsub.symm

/- Exact positive divisor-to-factor-pair reindex for odd squarefree moduli.
The finite domain records the original conductor product cutoff. -/



/- Exact source owner: SourceShiftTwoGlobalConductorSum.lean; original line 107. -/
theorem source_original_Echi_factor_pair_identity
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (Q : ℕ) :
    (∑ d ∈ (Finset.range (Q+1)).filter (fun d => Odd d ∧ Squarefree d),
      sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient : ℝ)) =
    ∑ a ∈ ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter
      (fun a => a.1*a.2 ≤ Q ∧ Odd (a.1*a.2) ∧ Squarefree (a.1*a.2)),
      sourceOriginalPrimitiveConductorMass r₀ hr₀ Ψ L a.1 a.2 := by
  rw [← source_odd_squarefree_divisor_factor_reindex]
  apply Finset.sum_congr rfl
  intro d hd
  have hs := (Finset.mem_filter.mp hd).2
  letI : NeZero d := ⟨hs.2.ne_zero⟩
  exact source_original_Echi_divisor_sum r₀ hr₀ Ψ L hL d hs.2



/- Exact source owner: SourceActualQ0PDisjoint.lean; original line 9. -/
theorem source_original_P_scale_zero_eq_Q0
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) :
    sourceOriginalPGroupScale r₀ L 0 = sourceOriginalQ0Scale r₀ * L := by
  have hr : (r₀:ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀)
  unfold sourceOriginalPGroupScale sourceOriginalQ0Scale
  simp only [pow_zero, mul_one]
  field_simp

/- Even at boundary primes, the original closed Q₀ band is disjoint
from EVERY source P_j closed dyadic band. Handles j=0 separately
and all j≥1 using true dyadic scale separation. -/



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 7. -/
theorem source_original_Q0_upper_cutoff (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (L : ℝ) (hL : 0 < L) (p : ℕ)
    (hp : p ∈ sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))) :
    p ≤ ⌊2*Real.exp L⌋₊ := by
  have hb := (source_original_Q_actual_prime_range r₀ _ L hr₀ _ p hp).2
  rw [source_original_P_scale_zero_eq_Q0 r₀ L hr₀] at hb
  have hr : (1:ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hα : (6/5:ℝ)*sourceOriginalQ0Scale r₀ ≤ 1 := by
    unfold sourceOriginalQ0Scale
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<11*(r₀:ℝ))).mpr
    nlinarith
  have he : (6/5:ℝ)*(sourceOriginalQ0Scale r₀*L) ≤ L := by nlinarith
  apply Nat.le_floor
  exact hb.trans ((Real.exp_le_exp.mpr he).trans (by nlinarith [Real.exp_pos L]))

/- Source Q0 is inside the finite half-open dyadic cover once the original
natural product cutoff is covered. No extra geometry assumption remains. -/



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 26. -/
theorem source_original_Q0_dyadic_subset (r₀ : ℕ) (hr₀ : 1 ≤ r₀)
    (L : ℝ) (hL : 0 < L) (J : ℕ) (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1) :
    sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ⊆
        Finset.Ioc 0 (2^J-1) := by
  intro p hp
  exact Finset.mem_Ioc.mpr ⟨(source_original_Q_actual_prime r₀ _ L _ p hp).pos,
    (source_original_Q0_upper_cutoff r₀ hr₀ L hL p hp).trans hN⟩



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 14. -/
theorem source_echi_dyad_end (j : ℕ) :
    sourceEchiDyadLower j+2^j = 2^(j+1)-1 := by
  have h := Nat.two_pow_pos j
  simp only [sourceEchiDyadLower, pow_succ]
  omega



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 20. -/
theorem source_echi_dyad_mem (j n : ℕ) :
    n ∈ sourceEchiDyad j ↔ 2^j ≤ n ∧ n < 2^(j+1) := by
  rw [sourceEchiDyad, source_echi_dyad_end]
  have h := Nat.two_pow_pos j
  have h' := Nat.two_pow_pos (j+1)
  simp only [Finset.mem_Ioc, sourceEchiDyadLower]
  omega

/- Every positive integer below 2^J is counted exactly once.
No closed dyadic endpoint is counted twice. -/



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 46. -/
theorem source_psi_nonzero_dyad_compatible (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (L : ℝ) (j k p R : ℕ) (hp : p ∈ sourceEchiDyad j) (hR : R ∈ sourceEchiDyad k)
    (hn : Ψ (((p*R:ℕ):ℝ)/Real.exp L) ≠ 0) :
    sourceEchiCompatible L j k := by
  have hm := hs (show ((p*R:ℕ):ℝ)/Real.exp L ∈ Function.support Ψ from hn)
  have hlow : Real.exp L ≤ (p:ℝ)*(R:ℝ) := by
    simpa only [Nat.cast_mul, one_mul] using (le_div_iff₀ (Real.exp_pos L)).mp hm.1
  have hhigh : (p:ℝ)*(R:ℝ) ≤ 2*Real.exp L := by
    simpa only [Nat.cast_mul] using (div_le_iff₀ (Real.exp_pos L)).mp hm.2
  have hp' := (source_echi_dyad_mem j p).mp hp
  have hR' := (source_echi_dyad_mem k R).mp hR
  have hpl : (2:ℝ)^j ≤ p := by exact_mod_cast hp'.1
  have hRl : (2:ℝ)^k ≤ R := by exact_mod_cast hR'.1
  have hpu : (p:ℝ) < 2*(2:ℝ)^j := by
    have h : (p:ℝ) < (2:ℝ)^(j+1) := by exact_mod_cast hp'.2
    simpa only [pow_succ,mul_comm] using h
  have hRu : (R:ℝ) < 2*(2:ℝ)^k := by
    have h : (R:ℝ) < (2:ℝ)^(k+1) := by exact_mod_cast hR'.2
    simpa only [pow_succ,mul_comm] using h
  have hRp : (0:ℝ) < R := (by positivity : (0:ℝ)<(2:ℝ)^k).trans_le hRl
  have hpr := mul_lt_mul hpu hRu.le hRp (by positivity)
  have hl := mul_le_mul hpl hRl (by positivity : (0:ℝ)≤(2:ℝ)^k) (by positivity)
  constructor
  · nlinarith [hpr]
  · exact hl.trans hhigh

/- Every omitted box is identically zero for every conductor and h mask.
The source box family has no surrogate residual support. -/



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 75. -/
theorem source_original_box_zero_off_source_boxes
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) (L : ℝ)
    (J j k h f : ℕ) (hj : j < J) (hk : k < J) (χ : DirichletCharacter ℂ f)
    (hnot : (j,k) ∉ sourceEchiSourceBoxes r₀ L J) :
    sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
      (sourceEchiDyadLower j) (2^j) (sourceEchiDyadLower k) (2^k) f χ = 0 := by
  unfold sourceDeletedSmoothBoxCharacter
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro R hR
  split_ifs with hmask
  · have hz : Ψ (((p*R:ℕ):ℝ)/Real.exp L) = 0 := by
      by_contra hn
      have hc := source_psi_nonzero_dyad_compatible Ψ hs L j k p R hp hR hn
      apply hnot
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,Finset.mem_range.mpr hk⟩, ?_⟩
      exact ⟨⟨p,Finset.mem_filter.mpr ⟨hp,hmask.1.1⟩⟩,hc⟩
    rw [hz]
    simp
  · rfl

/- Literal complete conductor convolution restricted to genuine source boxes. -/



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 30. -/
theorem source_echi_dyadic_sum {V : Type} [AddCommMonoid V]
    (J : ℕ) (g : ℕ → V) :
    (∑ n ∈ Finset.Ioc 0 (2^J-1), g n) =
      ∑ j ∈ Finset.range J, ∑ n ∈ sourceEchiDyad j, g n := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hpow : 2^J-1 ≤ 2^(J+1)-1 := by
      have h := Nat.two_pow_pos J
      rw [pow_succ]
      omega
    have he : Finset.Ioc 0 (2^(J+1)-1) =
        Finset.Ioc 0 (2^J-1) ∪ sourceEchiDyad J := by
      ext n
      rw [Finset.mem_union, sourceEchiDyad, source_echi_dyad_end]
      simp only [Finset.mem_Ioc, sourceEchiDyadLower]
      omega
    have hd : Disjoint (Finset.Ioc 0 (2^J-1)) (sourceEchiDyad J) := by
      apply Finset.disjoint_left.mpr
      intro n hn hm
      have hn' := Finset.mem_Ioc.mp hn
      have hm' := Finset.mem_Ioc.mp hm
      change 2^J-1 < n ∧ n ≤ sourceEchiDyadLower J+2^J at hm'
      omega
    rw [he, Finset.sum_union hd, ih, Finset.sum_range_succ]

/- Exact closed-Q0/half-open-dyad intersection, including a prime
equal to the original lower boundary. -/



/- Exact source owner: SourceShiftTwoConductorDyadicIdentity.lean; original line 9. -/
theorem source_positive_cutoff_sum {V : Type} [AddCommMonoid V]
    (N B : ℕ) (hN : N ≤ B+1) (g : ℕ → V) (hg0 : g 0 = 0)
    (hg : ∀ R, N ≤ R → g R = 0) :
    (∑ R ∈ Finset.range N, g R) = ∑ R ∈ Finset.Ioc 0 B, g R := by
  have h1 : (∑ R ∈ Finset.range N, g R) =
      ∑ R ∈ Finset.range (B+1), g R := by
    apply Finset.sum_subset
    · intro R hR
      exact Finset.mem_range.mpr ((Finset.mem_range.mp hR).trans_le hN)
    · intro R hR hnot
      exact hg R (by simpa only [Finset.mem_range, not_lt] using hnot)
  have h2 : (∑ R ∈ Finset.Ioc 0 B, g R) =
      ∑ R ∈ Finset.range (B+1), g R := by
    apply Finset.sum_subset
    · intro R hR
      exact Finset.mem_range.mpr (by have := Finset.mem_Ioc.mp hR; omega)
    · intro R hR hnot
      have hR0 : R = 0 := by
        have := Finset.mem_range.mp hR
        simp only [Finset.mem_Ioc, not_and, not_le] at hnot
        omega
      simpa only [hR0] using hg0
  exact h1.trans h2.symm

/- Exact original conductor convolution as a complete smooth box.
Both complementary coprimality masks remain in the integrand. -/



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 80. -/
theorem source_psi_at_zero (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) : Ψ 0 = 0 := by
  by_contra h
  have := (hs (show (0:ℝ) ∈ Function.support Ψ from h)).1
  norm_num at this



/- Exact source owner: SourceShiftTwoDyadicCover.lean; original line 71. -/
theorem source_psi_product_cutoff (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (L : ℝ) (p R : ℕ) (hΨ : Ψ (((p*R:ℕ):ℝ)/Real.exp L) ≠ 0) :
    p*R < ⌊2*Real.exp L⌋₊+1 := by
  have hmem := hs (show ((p*R:ℕ):ℝ)/Real.exp L ∈ Function.support Ψ from hΨ)
  have he := (div_le_iff₀ (Real.exp_pos L)).mp hmem.2
  have hn : p*R ≤ ⌊2*Real.exp L⌋₊ := Nat.le_floor he
  omega



/- Exact source owner: SourceShiftTwoConductorDyadicIdentity.lean; original line 35. -/
theorem source_original_conductor_complete_box
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (L : ℝ) (f h B : ℕ) (χ : DirichletCharacter ℂ f)
    (hN : ⌊2*Real.exp L⌋₊ ≤ B)
    (hQ : sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ⊆ Finset.Ioc 0 B) :
    sourceOriginalConductorConvolution r₀ hr₀ Ψ L f h χ =
      sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h 0 B 0 B f χ := by
  let Q := sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
    (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1))
  let g : ℕ → ℕ → ℂ := fun p R =>
    if p.Coprime h ∧ R.Coprime h then
      (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
        (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ) * χ p * χ R else 0
  have hg0 (p : ℕ) : g p 0 = 0 := by
    simp [g, source_psi_at_zero Ψ hs]
  have hcut (p R : ℕ) : (if p*R < ⌊2*Real.exp L⌋₊+1 ∧
      p.Coprime h ∧ R.Coprime h then
      (sourceOriginalDeletedMovingCoefficient r₀ hr₀ L R : ℂ) *
        (Ψ (((p*R:ℕ):ℝ)/Real.exp L) : ℂ) * χ p * χ R else 0) = g p R := by
    by_cases hpR : p*R < ⌊2*Real.exp L⌋₊+1
    · simp [g,hpR]
    · have hz : Ψ (((p*R:ℕ):ℝ)/Real.exp L) = 0 := by
        by_contra hn
        exact hpR (source_psi_product_cutoff Ψ hs L p R hn)
      simp only [g, hpR, false_and, if_false]
      split_ifs <;> simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]
  have hg (p : ℕ) (hp : p ∈ Q) (R : ℕ) (hR : ⌊2*Real.exp L⌋₊+1 ≤ R) :
      g p R = 0 := by
    have hp1 : 1 ≤ p := (source_original_Q_actual_prime r₀ _ L _ p hp).one_le
    have hproduct : ⌊2*Real.exp L⌋₊+1 ≤ p*R := by
      exact hR.trans (by nlinarith)
    have hz : Ψ (((p*R:ℕ):ℝ)/Real.exp L) = 0 := by
      by_contra hn
      have := source_psi_product_cutoff Ψ hs L p R hn
      omega
    dsimp only [g]
    split_ifs <;> simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]
  unfold sourceOriginalConductorConvolution
  change (∑ p ∈ Q, _) = _
  simp_rw [hcut]
  have hinner (p : ℕ) (hp : p ∈ Q) :
      (∑ R ∈ Finset.range (⌊2*Real.exp L⌋₊+1), g p R) =
        ∑ R ∈ Finset.Ioc 0 B, g p R :=
    source_positive_cutoff_sum _ B (by omega) (g p) (hg0 p) (hg p hp)
  calc
    _ = ∑ p ∈ Q, ∑ R ∈ Finset.Ioc 0 B, g p R := Finset.sum_congr rfl hinner
    _ = ∑ p ∈ Finset.Ioc 0 B, ∑ R ∈ Finset.Ioc 0 B,
        if p ∈ Q then g p R else 0 := by
      have hf (p : ℕ) : (∑ R ∈ Finset.Ioc 0 B, if p ∈ Q then g p R else 0) =
          if p ∈ Q then (∑ R ∈ Finset.Ioc 0 B, g p R) else 0 := by
        by_cases hp : p ∈ Q <;> simp [hp]
      simp_rw [hf]
      rw [← Finset.sum_filter]
      have he : (Finset.Ioc 0 B).filter (fun p => p ∈ Q) = Q := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun hp => hp.2,fun hp => ⟨hQ hp,hp⟩⟩
      rw [he]
    _ = _ := by
      unfold sourceDeletedSmoothBoxCharacter
      simp only [zero_add]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro R hR
      dsimp [g,Q]
      split_ifs <;> simp_all

/- Complete finite dyadic decomposition of the actual original conductor
sum. Ψ and all source factorial/parity coefficients are unchanged. -/



/- Exact source owner: SourceShiftTwoConductorDyadicIdentity.lean; original line 107. -/
theorem source_original_conductor_dyadic_identity
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (L : ℝ) (f h J : ℕ) (χ : DirichletCharacter ℂ f)
    (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1)
    (hQ : sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L
      (⟨0,by omega⟩ : Fin (sourceOriginalLiteralDepth r₀ L+1)) ⊆ Finset.Ioc 0 (2^J-1)) :
    sourceOriginalConductorConvolution r₀ hr₀ Ψ L f h χ =
      ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
        sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
          (sourceEchiDyadLower j) (2^j) (sourceEchiDyadLower k) (2^k) f χ := by
  rw [source_original_conductor_complete_box r₀ hr₀ Ψ hs L f h _ χ hN hQ]
  unfold sourceDeletedSmoothBoxCharacter
  simp only [zero_add]
  rw [source_echi_dyadic_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [source_echi_dyadic_sum J]
  rw [Finset.sum_comm]
  rfl



/- Exact source owner: SourceShiftTwoDyadicSourceGeometry.lean; original line 100. -/
theorem source_original_conductor_source_box_identity
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2)
    (L : ℝ) (hL : 0 < L) (f h J : ℕ) (χ : DirichletCharacter ℂ f)
    (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1) :
    sourceOriginalConductorConvolution r₀ hr₀ Ψ L f h χ =
      ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
        sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
          (sourceEchiDyadLower a.1) (2^a.1) (sourceEchiDyadLower a.2) (2^a.2) f χ := by
  rw [source_original_conductor_dyadic_identity r₀ hr₀ Ψ hs L f h J χ hN
    (source_original_Q0_dyadic_subset r₀ hr₀ L hL J hN)]
  rw [← Finset.sum_product (Finset.range J) (Finset.range J)
    (fun a : ℕ×ℕ => sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
      (sourceEchiDyadLower a.1) (2^a.1) (sourceEchiDyadLower a.2) (2^a.2) f χ)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hn
  have hh := Finset.mem_product.mp ha
  exact source_original_box_zero_off_source_boxes r₀ hr₀ Ψ hs L J a.1 a.2 h f
    (Finset.mem_range.mp hh.1) (Finset.mem_range.mp hh.2) χ hn



/- Exact source owner: SourceShiftTwoGlobalSourceBoxMajorant.lean; original line 26. -/
theorem source_original_primitive_conductor_box_majorant
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) (L : ℝ) (hL : 0 < L)
    (f h J : ℕ) (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1) :
    sourceOriginalPrimitiveConductorMass r₀ hr₀ Ψ L f h ≤
      (h.totient:ℝ)⁻¹ * ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
        sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L f h a := by
  by_cases hf0 : f = 0
  · simp [sourceOriginalPrimitiveConductorMass,sourceOriginalPrimitiveBoxMass,hf0]
  letI : NeZero f := ⟨hf0⟩
  by_cases hf1 : f = 1
  · simp [sourceOriginalPrimitiveConductorMass,sourceOriginalPrimitiveBoxMass,hf0,hf1]
  simp only [sourceOriginalPrimitiveConductorMass,sourceOriginalPrimitiveBoxMass,
    dif_neg hf0,if_neg hf1]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (f.totient:ℝ)⁻¹ * (h.totient:ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ f, ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
          if χ.IsPrimitive then
            ‖sourceDeletedSmoothBoxCharacter r₀ hr₀ Ψ L h
              (sourceEchiDyadLower a.1) (2^a.1)
              (sourceEchiDyadLower a.2) (2^a.2) f χ‖ else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      split_ifs with hp
      · rw [source_original_conductor_source_box_identity r₀ hr₀ Ψ hs L hL f h J χ hN]
        exact norm_sum_le _ _
      · simp
    _ = _ := by rw [Finset.sum_comm]; ring

/- Global actual Echi reduced to source dyadic boxes and genuine f,h sums.
The squarefree h restriction survives, allowing the checked harmonic budget. -/



/- Exact source owner: SourceShiftTwoGlobalConductorSum.lean; original line 16. -/
theorem source_original_primitive_mass_nonneg
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ) (L : ℝ) (f h : ℕ) :
    0 ≤ sourceOriginalPrimitiveConductorMass r₀ hr₀ Ψ L f h := by
  unfold sourceOriginalPrimitiveConductorMass
  split_ifs <;> positivity



/- Exact source owner: SourceShiftTwoGlobalSourceBoxMajorant.lean; original line 59. -/
theorem source_original_Echi_source_box_majorant
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (Ψ : ℝ → ℝ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) (L : ℝ) (hL : 0 < L)
    (Q J : ℕ) (hN : ⌊2*Real.exp L⌋₊ ≤ 2^J-1) :
    (∑ d ∈ (Finset.range (Q+1)).filter (fun d => Odd d ∧ Squarefree d),
      sourceShiftTwoCharacterL1 r₀ Ψ L d / (d.totient:ℝ)) ≤
      ∑ h ∈ (Finset.Icc 1 Q).filter Squarefree,
        (h.totient:ℝ)⁻¹ * ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
          ∑ f ∈ Finset.Icc 1 Q, sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L f h a := by
  rw [source_original_Echi_factor_pair_identity r₀ hr₀ Ψ L hL Q]
  have hsub : ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).filter
      (fun a => a.1*a.2 ≤ Q ∧ Odd (a.1*a.2) ∧ Squarefree (a.1*a.2)) ⊆
      (Finset.Icc 1 Q) ×ˢ ((Finset.Icc 1 Q).filter Squarefree) := by
    intro a ha
    have hm := Finset.mem_filter.mp ha
    have hp := Finset.mem_product.mp hm.1
    exact Finset.mem_product.mpr ⟨hp.1,Finset.mem_filter.mpr ⟨hp.2,
      Squarefree.squarefree_of_dvd (dvd_mul_left a.2 a.1) hm.2.2.2⟩⟩
  calc
    _ ≤ ∑ b ∈ (Finset.Icc 1 Q) ×ˢ ((Finset.Icc 1 Q).filter Squarefree),
        sourceOriginalPrimitiveConductorMass r₀ hr₀ Ψ L b.1 b.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun b hb hn => source_original_primitive_mass_nonneg r₀ hr₀ Ψ L b.1 b.2)
    _ ≤ ∑ b ∈ (Finset.Icc 1 Q) ×ˢ ((Finset.Icc 1 Q).filter Squarefree),
        (b.2.totient:ℝ)⁻¹ * ∑ a ∈ sourceEchiSourceBoxes r₀ L J,
          sourceOriginalPrimitiveBoxMass r₀ hr₀ Ψ L b.1 b.2 a :=
      Finset.sum_le_sum (fun b hb =>
        source_original_primitive_conductor_box_majorant r₀ hr₀ Ψ hs L hL b.1 b.2 J hN)
    _ = _ := by
      rw [Finset.sum_product,Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      simp_rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

/- Per-character small-conductor saving loses no totient factor. -/


end Green64Analytic.SourceBlockSieve

end

end

