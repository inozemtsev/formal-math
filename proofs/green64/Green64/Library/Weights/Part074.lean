module

public import Green64.Library.Weights.Part071
public import Green64.Library.Weights.Part073
public import Green64.Library.Correlation.PhysicalReturnGSchur

@[expose] public section

/-!
# Weights / Part074

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalActualSourceDIRTYKSmallJointLattice -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- EXACT JOINT lattice of TWO true chronological source03 path
frequencies, for matched real start/end SMALL tori:
the spectral gap is divisible by LCM(full SMALL prime modulus,
absolute moving k). Joint K and FIRST-DIRTY interference survive. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_k_LCM_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0) :
    Nat.lcm (sourceOriginalActualSourceALLSmallModulus434 u) k.natAbs ∣
      (d-e).natAbs := by
  have hQ := source_original_ACTUAL_SOURCE_DIRTY_ALL_SMALL_endpoint_gap434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    p q d e hstarts hends hnp hnq
  have hk1 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d hnp
  have hk2 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e hnq
  have hk : k.natAbs ∣ (d-e).natAbs :=
    (Int.natAbs_dvd_natAbs).mpr (dvd_sub hk1 hk2)
  exact Nat.lcm_dvd hQ hk

/-- Under the ORIGINAL source small-prime band and moving frequency
restriction |k| ≤ L^Carc, every distinguished S prime exceeds |k|,
so their WHOLE product is coprime to |k|.
No analogous bound is guessed for arbitrary Ts from SourceComparisonData. -/
theorem source_original_ACTUAL_SOURCE_distinguished_S_coprime_k434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (k : ℤ) (hk : k ≠ 0)
    (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc) :
    Nat.Coprime (u.S.prod id) k.natAbs := by
  apply (Nat.coprime_prod_left_iff).2
  intro p hp
  apply ((u.hSPrime p hp).coprime_iff_not_dvd).2
  intro hdiv
  have hpositive : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hle : p ≤ k.natAbs := Nat.le_of_dvd hpositive hdiv
  have hleReal : (p:ℝ) ≤ (k.natAbs:ℝ) := by exact_mod_cast hle
  have hlarge : L^cfg.Carc < (p:ℝ) :=
    u.hOrigSmall.trans_le (u.hSmall p hp).1
  exact (not_lt_of_ge hleReal) (hkBound.trans_lt hlarge)

/-- For the TRUE moving source k ≠ 0, on the original |k|
arc range, matched-SMALL-endpoint physical paths have spectral
gap divisible by |k| TIMES the entire genuine S prime product.
This is strictly stronger than either frequency lattice alone. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_S_times_k_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : k ≠ 0) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0) :
    (u.S.prod id) * k.natAbs ∣ (d-e).natAbs := by
  have hsource := source_original_ACTUAL_SOURCE_DIRTY_equal_small_endpoints_gap_product434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T
    none p q d e (hstarts none) (hends none) hnp hnq
  have hS : u.S.prod id ∣ (d-e).natAbs := by
    simpa [sourceOriginalActualSmallPrimeSets434,
      sourceOriginalFullGroupPrimeSets434] using hsource
  have hk1 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d hnp
  have hk2 := source_original_ACTUAL_SOURCE_DIRTY_each_path_k_dvd434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e hnq
  have hkd : k.natAbs ∣ (d-e).natAbs :=
    (Int.natAbs_dvd_natAbs).mpr (dvd_sub hk1 hk2)
  exact (source_original_ACTUAL_SOURCE_distinguished_S_coprime_k434
    u k hk hkBound).mul_dvd_of_dvd_of_dvd hS hkd
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYKCancelledNoReturn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- A sharper true first-DIRTY no-frequency-return criterion that
CANCELS the moving Fourier multiplier |k|. The ACTUAL physical
local divisor bound is compared ONLY to the distinguished ORIGINAL
source S prime product. The old k-lattice and genuine S-prime
coprimality justify cancellation; k need not equal 1.
Every original chronological Fock×seen state and joint K survives.
No asymptotic bound on R or signed Gram is asserted here. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_S_k_cancelled_no_return434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : k ≠ 0) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (hwindow :
      2*(2*R)*sourceOriginalActualSourceGEDualDivisorCap434
        u blockA blockB J ell m hmJ k < u.S.prod id)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q e ≠ 0) : d = e := by
  let M := sourceOriginalActualSourceGEDualDivisorCap434
    u blockA blockB J ell m hmJ k
  let B := (2*R)*(k.natAbs*M)
  have hkp : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hd : d.natAbs ≤ B :=
    source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T p d hnp
  have he : e.natAbs ≤ B :=
    source_original_ACTUAL_SOURCE_DIRTY_true_path_radius434
      u blockA blockB J ell m hmJ Q hA hB
      xi rho zeta k R T q e hnq
  have hsmall : (d-e).natAbs ≤ (2*(2*R)*M)*k.natAbs := by
    calc
      (d-e).natAbs ≤ d.natAbs + e.natAbs := Int.natAbs_sub_le d e
      _ ≤ B+B := Nat.add_le_add hd he
      _ = (2*(2*R)*M)*k.natAbs := by
        dsimp [B]
        ring
  have hstrict :
      (2*(2*R)*M)*k.natAbs < (u.S.prod id)*k.natAbs :=
    Nat.mul_lt_mul_of_pos_right hwindow hkp
  by_contra hneq
  have hdiv := source_original_ACTUAL_SOURCE_DIRTY_S_times_k_gap434
    u blockA blockB J ell m hmJ Q hA hB
    xi rho zeta k R T hk hkBound
    p q d e hstarts hends hnp hnq
  have hpos : 0 < (d-e).natAbs :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hneq)
  have hlower : (u.S.prod id)*k.natAbs ≤ (d-e).natAbs :=
    Nat.le_of_dvd hpos hdiv
  omega
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSourceDIRTYShiftAmplifiedGap -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Real
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The REAL original distinguished source03 S prime product,
without replacing it by an abstract modulus, has exponential
magnitude at least (exp(L^a))^(number of genuine S primes). -/
theorem source_original_ACTUAL_SOURCE_S_product_exp_lower434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) :
    (Real.exp (L^cfg.aexp))^(u.S.card) ≤
      ((u.S.prod id : ℕ):ℝ) := by
  calc
    _ = ∏ p ∈ u.S, Real.exp (L^cfg.aexp) := by
      simp only [Finset.prod_const]
    _ ≤ ∏ p ∈ u.S, (p:ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact (Real.exp_pos _).le
      · intro p hp
        exact (u.hSmall p hp).1
    _ = ((u.S.prod id:ℕ):ℝ) := by
      simp only [Nat.cast_prod]
      rfl

/-- The genuinely moving original-k source03 spectral gap gains
the ENTIRE factor |k|, not merely a symbolic LCM. Whenever two
true signed first-DIRTY chronological path amplitudes have the
SAME SMALL initial and terminal tori and distinct total modes,
their absolute frequency separation is ≥ |k|*exp(L^a)^|S|.
All real source03 Fock/seen transitions and RAW/comparison joint
coefficients remain inside the theorem; no frequency-window
upper bound or signed saving is assumed. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_SHIFT_amplified_gap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : k ≠ 0) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0)
    (hneq : d ≠ e) :
    (k.natAbs:ℝ) * (Real.exp (L^cfg.aexp))^(u.S.card) ≤
      ((d-e).natAbs:ℝ) := by
  have hdiv := source_original_ACTUAL_SOURCE_DIRTY_S_times_k_gap434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T hk hkBound
    p q d e hstarts hends hnp hnq
  have hpos : 0 < (d-e).natAbs := by
    exact Int.natAbs_pos.mpr (sub_ne_zero.mpr hneq)
  have hle : u.S.prod id * k.natAbs ≤ (d-e).natAbs :=
    Nat.le_of_dvd hpos hdiv
  calc
    _ ≤ (k.natAbs:ℝ) * ((u.S.prod id : ℕ):ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (source_original_ACTUAL_SOURCE_S_product_exp_lower434 u)
        (Nat.cast_nonneg k.natAbs)
    _ = ((u.S.prod id * k.natAbs : ℕ):ℝ) := by
      push_cast
      ring
    _ ≤ ((d-e).natAbs:ℝ) := by exact_mod_cast hle

/-- In a window shorter than the actual shift-amplified source03
S prime product, every matched-SMALL-endpoint first-DIRTY
frequency collision is an EXACT diagonal-frequency collision.
This does NOT eliminate coherent off-path Gram terms at the
same frequency. -/
theorem source_original_ACTUAL_SOURCE_DIRTY_SHIFT_short_window_unique434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (blockA blockB : Finset β) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (hA hB : SourceOriginalProbePattern434 β m → ℝ)
    (xi rho zeta : ℝ) (k : ℤ) (R T : ℕ)
    (hk : k ≠ 0) (hkBound : (k.natAbs:ℝ) ≤ L^cfg.Carc)
    (p q : (sourceOriginalActualSourceDIRTYPathState434 u J ell) ×
      (Fin (2*R) → sourceOriginalActualSourceDIRTYPathState434 u J ell))
    (d e : ℤ)
    (hstarts : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYStartTorus434 u J ell R g q)
    (hends : ∀ g : Option ι,
      sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g p =
        sourceOriginalActualSourceDIRTYTerminalTorus434 u J ell R g q)
    (hnp : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T p d ≠ 0)
    (hnq : sourceOriginalActualSourceDIRTYPathAmplitude434
      u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T q e ≠ 0)
    (hwidth : ((d-e).natAbs:ℝ) <
      (k.natAbs:ℝ) * (Real.exp (L^cfg.aexp))^(u.S.card)) :
    d = e := by
  by_contra hn
  have hLower := source_original_ACTUAL_SOURCE_DIRTY_SHIFT_amplified_gap434
    u blockA blockB J ell m hmJ Q hA hB xi rho zeta k R T hk hkBound
    p q d e hstarts hends hnp hnq hn
  exact (not_lt_of_ge hLower) hwidth
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalBaselineGlobalG -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- One original baseline cancels the first-order growth of ALL visit
Schur factors. The remaining cost is quadratic in the total visit mass. -/
theorem source_original_BASELINE_visit_product434
    (I : Finset ℕ) (eta : ℕ → ℝ) (he : ∀ i,0 ≤ eta i)
    (p : ℝ) (hp : 0 < p) (hs : (∑ i ∈ I,eta i)/p ≤ 1/2) :
    (1-(∑ i ∈ I,eta i)/p) *
      (∏ i ∈ I,(1+eta i/(p*(1-(∑ i ∈ I,eta i)/p)))) ≤
      Real.exp (2*((∑ i ∈ I,eta i)/p)^2) := by
  let x := (∑ i ∈ I,eta i)/p
  have hx : 0 ≤ x := div_nonneg (Finset.sum_nonneg (fun i _ => he i)) hp.le
  have hx1 : x ≤ 1/2 := hs
  have hb : 0 < 1-x := by linarith
  have hbhalf : 1/2 ≤ 1-x := by linarith
  have hprod : (∏ i ∈ I,(1+eta i/(p*(1-x)))) ≤ Real.exp (x/(1-x)) := by
    calc
      _ ≤ ∏ i ∈ I,Real.exp (eta i/(p*(1-x))) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact add_nonneg zero_le_one (div_nonneg (he i) (mul_pos hp hb).le)
        · intro i hi
          simpa only [add_comm] using Real.add_one_le_exp (eta i/(p*(1-x)))
      _ = Real.exp (x/(1-x)) := by
        rw [←Real.exp_sum,←Finset.sum_div]
        congr 1
        dsimp only [x]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
  have hbexp : 1-x ≤ Real.exp (-x) := by
    simpa only [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-x)
  have hquad : -x+x/(1-x) ≤ 2*x^2 := by
    have hid : -x+x/(1-x)=x^2/(1-x) := by
      field_simp [hb.ne']
      <;> ring
    rw [hid]
    apply (div_le_iff₀ hb).mpr
    nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hbhalf)]
  change (1-x)*(∏ i ∈ I,(1+eta i/(p*(1-x)))) ≤ Real.exp (2*x^2)
  calc
    _ ≤ (1-x)*Real.exp (x/(1-x)) := mul_le_mul_of_nonneg_left hprod hb.le
    _ ≤ Real.exp (-x)*Real.exp (x/(1-x)) :=
      mul_le_mul_of_nonneg_right hbexp (Real.exp_pos _).le
    _ = Real.exp (-x+x/(1-x)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hquad

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- The full ORIGINAL source baseline and the product of exact rho=1
physical G Schur budgets, including both endpoint visits. -/
def sourceOriginalBaselineGlobalGBudget434
    (q : ℝ) (N : ℕ) (V : BG → ℝ) : ℝ :=
  physicalSourceBaselineProduct BP bm q N *
    ∏ i ∈ Finset.range (N+1),sourceOriginalFullReturnSchurBudget434 BP
      (sourceVisitEta q N i) V (physicalSourceMuTilde BP bm q N V)

/-- Global normalized G cost on the unchanged physical density.
This budget controls arbitrary complex joint futures via the checked
actual G matrix estimate; it is not a bounded-mask background bound. -/
theorem source_original_BASELINE_GLOBAL_G_quadratic434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hSize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ)) :
    sourceOriginalBaselineGlobalGBudget434 BP bm q N V ≤
      Real.exp (2*(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)^2 *
        (∑ g,∑ p : BP g,(1/(bm g p:ℝ))^2)) := by
  let A := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
  have hp (g : BG) (p : BP g) : 0 < (bm g p:ℝ) :=
    Nat.cast_pos.mpr (NeZero.pos _)
  have hb (g : BG) (p : BP g) :
      1/2 ≤ physicalSourceBaseline BP bm q N g p :=
    (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p (hSize g p)).1
  have hb0 (g : BG) (p : BP g) : 0 < physicalSourceBaseline BP bm q N g p :=
    lt_of_lt_of_le (by norm_num) (hb g p)
  have hi (g : BG) (p : BP g) :
      V g*physicalSourceMuTilde BP bm q N V g p =
        1/((bm g p:ℝ)*physicalSourceBaseline BP bm q N g p) := by
    unfold physicalSourceMuTilde
    field_simp [(hV g).ne',(hp g p).ne',(hb0 g p).ne']
  have he (i : ℕ) : 0 ≤ sourceVisitEta q N i :=
    (source_original_B26_visit_eta_unit434 q hq hq1 N i).1
  have hprime (g : BG) (p : BP g) :
      physicalSourceBaseline BP bm q N g p *
        (∏ i ∈ Finset.range (N+1),
          (1+sourceVisitEta q N i*(V g*physicalSourceMuTilde BP bm q N V g p))) ≤
      Real.exp (2*A^2*(1/(bm g p:ℝ))^2) := by
    have hs : A/(bm g p:ℝ) ≤ 1/2 := by
      have hb' := hb g p
      change 1/2 ≤ 1-A/(bm g p:ℝ) at hb'
      linarith only [hb']
    have h := source_original_BASELINE_visit_product434
      (Finset.range (N+1)) (sourceVisitEta q N) he (bm g p:ℝ) (hp g p) hs
    rw [hi]
    convert h using 1 <;>
      simp only [physicalSourceBaseline,A,div_eq_mul_inv,one_mul,mul_pow] <;> ring
  have hflat :
      sourceOriginalBaselineGlobalGBudget434 BP bm q N V =
      ∏ g,∏ p : BP g,physicalSourceBaseline BP bm q N g p *
        (∏ i ∈ Finset.range (N+1),
          (1+sourceVisitEta q N i*(V g*physicalSourceMuTilde BP bm q N V g p))) := by
    unfold sourceOriginalBaselineGlobalGBudget434 physicalSourceBaselineProduct
      sourceOriginalFullReturnSchurBudget434
    rw [Finset.prod_comm]
    simp_rw [Finset.prod_comm (s := Finset.range (N+1))]
    simp only [Finset.prod_mul_distrib]
  rw [hflat]
  calc
    _ ≤ ∏ g,∏ p : BP g,Real.exp (2*A^2*(1/(bm g p:ℝ))^2) := by
      apply Finset.prod_le_prod₀
      · intro g hg
        apply Finset.prod_nonneg
        intro p hp'
        apply mul_nonneg (hb0 g p).le
        apply Finset.prod_nonneg
        intro i hi'
        rw [hi]
        exact add_nonneg zero_le_one
          (mul_nonneg (he i) (one_div_pos.mpr (mul_pos (hp g p) (hb0 g p))).le)
      · intro g hg
        apply Finset.prod_le_prod₀
        · intro p hp'
          apply mul_nonneg (hb0 g p).le
          apply Finset.prod_nonneg
          intro i hi'
          rw [hi]
          exact add_nonneg zero_le_one
            (mul_nonneg (he i) (one_div_pos.mpr (mul_pos (hp g p) (hb0 g p))).le)
        · intro p hp'
          exact hprime g p
    _ = _ := by simp only [Real.exp_sum,Finset.mul_sum,A]

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalBaselineGlobalGDecay -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

theorem source_original_BASELINE_GLOBAL_G_nonneg434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hSize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ)) :
    0 ≤ sourceOriginalBaselineGlobalGBudget434 BP bm q N V := by
  have hb (g : BG) (p : BP g) : 0 < physicalSourceBaseline BP bm q N g p :=
    lt_of_lt_of_le (by norm_num)
      (source_original_B26_physical_baseline_half434 BP bm q hq hq1 N g p (hSize g p)).1
  have hm (g : BG) (p : BP g) : 0 ≤ physicalSourceMuTilde BP bm q N V g p := by
    unfold physicalSourceMuTilde
    exact (one_div_pos.mpr (mul_pos (mul_pos (hV g)
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb g p))).le
  unfold sourceOriginalBaselineGlobalGBudget434 physicalSourceBaselineProduct
    sourceOriginalFullReturnSchurBudget434
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun p _ => (hb g p).le))
  · apply Finset.prod_nonneg
    intro i hi
    exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun p _ =>
      add_nonneg zero_le_one (mul_nonneg
        (source_original_B26_visit_eta_unit434 q hq hq1 N i).1
        (mul_nonneg (hV g).le (hm g p)))))

/-- The true minimum prime and true total harmonic mass pay the complete
normalized G energy cost. Only N squared remains, not a product L^(C*N). -/
theorem source_original_BASELINE_GLOBAL_G_squared_harmonic434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : BG → ℝ) (hV : ∀ g,0 < V g)
    (hSize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ))
    (Pmin : ℝ) (hP : 0 < Pmin) (hmin : ∀ g p,Pmin ≤ (bm g p:ℝ)) :
    (sourceOriginalBaselineGlobalGBudget434 BP bm q N V)^2 ≤
      Real.exp (4*((N+1:ℕ):ℝ)^2 *
        ((∑ g,∑ p : BP g,1/(bm g p:ℝ))/Pmin)) := by
  let H := ∑ g,∑ p : BP g,1/(bm g p:ℝ)
  let S := ∑ g,∑ p : BP g,(1/(bm g p:ℝ))^2
  let A := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
  have hH : 0 ≤ H := Finset.sum_nonneg (fun g _ =>
    Finset.sum_nonneg (fun p _ => (one_div_pos.mpr
      (Nat.cast_pos.mpr (NeZero.pos _))).le))
  have hS : S ≤ H/Pmin := by
    calc
      _ ≤ ∑ g,∑ p : BP g,(1/(bm g p:ℝ))*(1/Pmin) := by
        apply Finset.sum_le_sum
        intro g hg
        apply Finset.sum_le_sum
        intro p hp
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hP (hmin g p))
          (one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos _))).le
      _ = H/Pmin := by simp only [H,div_eq_mul_inv,one_mul,Finset.sum_mul]
  have hA := source_original_B26_visit_sum_unit434 q hq hq1 N
  have hc := source_original_BASELINE_GLOBAL_G_quadratic434 BP bm q hq hq1 N V hV hSize
  have hn := source_original_BASELINE_GLOBAL_G_nonneg434 BP bm q hq hq1 N V hV hSize
  have he : 4*A^2*S ≤ 4*((N+1:ℕ):ℝ)^2*(H/Pmin) := by
    calc
      _ ≤ 4*A^2*(H/Pmin) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA.1 hA.2 2) (by norm_num))
        (div_nonneg hH hP.le)
  calc
    _ ≤ (Real.exp (2*A^2*S))^2 := pow_le_pow_left₀ hn hc 2
    _ = Real.exp (4*A^2*S) := by rw [pow_two,←Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr he

/-- Arbitrarily small global excess at the ORIGINAL growing depth.
The threshold precedes the moving prime alphabet, physical state space,
the number of histories and all complex observables. -/
theorem eventually_source_original_BASELINE_GLOBAL_G_near_one434
    (c A B : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {BG : Type} [Fintype BG] [DecidableEq BG]
      (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
      (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
      (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
      (V : BG → ℝ) (hV : ∀ g,0 < V g)
      (hmin : ∀ g p,Real.exp (L^c) ≤ (bm g p:ℝ))
      (hMass : (∑ g,∑ p : BP g,1/(bm g p:ℝ)) ≤ A*Real.log L),
      (sourceOriginalBaselineGlobalGBudget434 BP bm q
        (2*Nat.ceil (L^(0.52:ℝ))) V)^2 ≤ Real.exp (L^(-B)) := by
  obtain ⟨L0,hLarge⟩ := source_original_circle_eventual_exp_dominance434
    c (B+4) 0 hc (by linarith) (by norm_num)
  filter_upwards [eventually_ge_atTop L0,eventually_ge_atTop (100*A),
    eventually_source_original_B26_visits_below_BIG434 c hc] with L hL0 hConst hVisit
  obtain ⟨hL4,hExp'⟩ := hLarge L hL0
  have hL : 1 ≤ L := by linarith
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hExp : 4*L^(B+4) ≤ Real.exp (L^c) := by
    simpa using hExp' 1 (by norm_num) (by simp)
  intro BG _ _ BP _ _ bm _ q hq hq1 V hV hmin hMass
  let N := 2*Nat.ceil (L^(0.52:ℝ))
  let H := ∑ g,∑ p : BP g,1/(bm g p:ℝ)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun g _ =>
    Finset.sum_nonneg (fun p _ => (one_div_pos.mpr
      (Nat.cast_pos.mpr (NeZero.pos _))).le))
  have hSize (g : BG) (p : BP g) : 2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ) :=
    hVisit (bm g p) (hmin g p)
  have hN : ((N+1:ℕ):ℝ) ≤ 5*L := by
    have hpow : L^(0.52:ℝ) ≤ L := by
      simpa using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0.52:ℝ) ≤ 1)
    have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hLp.le (0.52:ℝ))).le
    dsimp only [N]
    push_cast
    linarith
  have hHL : H ≤ A*L :=
    hMass.trans (mul_le_mul_of_nonneg_left
      ((Real.log_le_sub_one_of_pos hLp).trans (sub_le_self L zero_le_one)) hA)
  have hnum : 4*((N+1:ℕ):ℝ)^2*H ≤ 100*A*L^3 := by
    calc
      _ ≤ 4*((5*L)^2*(A*L)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) hHL hH (by positivity))
          (by norm_num)
      _ = _ := by ring
  have hcoef : 100*A*L^3 ≤ L^4 := by
    have h := mul_le_mul_of_nonneg_right hConst (pow_nonneg hLp.le 3)
    nlinarith only [h]
  have hdiv : L^4/Real.exp (L^c) ≤ L^(-B) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hid : L^(-B)*(4*L^(B+4))=4*L^4 := by
      rw [←mul_assoc,mul_comm (L^(-B)) (4:ℝ),mul_assoc,←Real.rpow_add hLp]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hExp (Real.rpow_nonneg hLp.le (-B))
    rw [hid] at hh
    exact (by nlinarith only [pow_nonneg hLp.le 4] : L^4 ≤ 4*L^4).trans hh
  have herror : 4*((N+1:ℕ):ℝ)^2*(H/Real.exp (L^c)) ≤ L^(-B) := by
    calc
      _ = (4*((N+1:ℕ):ℝ)^2*H)/Real.exp (L^c) := by ring
      _ ≤ L^4/Real.exp (L^c) :=
        div_le_div_of_nonneg_right (hnum.trans hcoef) (Real.exp_pos _).le
      _ ≤ _ := hdiv
  exact (source_original_BASELINE_GLOBAL_G_squared_harmonic434
    BP bm q hq hq1 N V hV hSize (Real.exp (L^c)) (Real.exp_pos _) hmin).trans
    (Real.exp_le_exp.mpr herror)

end Green64Analytic.CorrelationSquare

end

end

