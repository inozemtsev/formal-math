module

public import Green64.Library.Analysis.Estimates.Part014

@[expose] public section

/-!
# Weights / Part102

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ParityActualCorrelation -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The literal separated physical pair before Parity (4.16) is contracted.
Both endpoint rough cofactors, both genuine prime-slot remainders, actual
P weights and the SAME P-only sign remain inside the complete finite sum. -/
def b633ParityPhysicalPair434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (q0 : ℝ) (ell : ℕ) (tw : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi1 xi2 xi3 rho sigma : ℝ) (z t : ℕ) : ℂ :=
  ∑ mp ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
    ∑ m ∈ (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) t).divisors,
      alpha m * star (alpha mp) * chi mp * star (chi m) *
      imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
      imaginaryPower (z/mp) rho * imaginaryPower (t/m) (-rho) *
      b633PrimeRest434 lo hi sigma residual
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (z/mp)) *
      star (b633PrimeRest434 lo hi sigma residual
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (t/m))) *
      (sourceMarkedWeight q0 ell P (z/mp)*sourceMarkedWeight q0 ell P (t/m) : ℝ) *
      (groupSign P tw (z/mp)*groupSign P tw (t/m) : ℝ)

/-- Exact Parity (4.16)--(4.17) at two positive physical positions. Every
cofactor term is retained; the alpha=0 terms vanish, and rough support
supplies all ordinary-part, P-weight and P-sign identifications. -/
theorem b633_parity_full_physical_pair434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (W q0 : ℝ) (ell : ℕ) (tw : Bool)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi1 xi2 xi3 rho sigma : ℝ) (z t : ℕ)
    (hz : 0 < z) (ht : 0 < t)
    (hp : ∀g p, p ∈ P g → p.Prime) (hW : ∀g p, p ∈ P g → (p:ℝ) ≤ W)
    (hs : ∀m, alpha m ≠ 0 → sourceD20Rough W m) :
    b633ParityPhysicalPair434 P q0 ell tw alpha residual q chi lo hi xi1 xi2 xi3 rho sigma z t =
      imaginaryPower z (rho+xi3)*imaginaryPower t (-rho)*
      primeSlotCoreValue P (b633ParityFirstCore434 alpha residual q chi lo hi xi2 rho sigma) z *
      primeSlotCoreValue P (b633ParitySecondCore434 alpha residual q chi lo hi xi1 rho sigma) t *
      (sourceMarkedWeight q0 ell P z*sourceMarkedWeight q0 ell P t : ℝ) *
      (groupSign P tw z*groupSign P tw t : ℝ) := by
  rw [b633_prime_core_full_rest_expansion434,b633_prime_core_full_rest_expansion434]
  simp only [b633ParityFirstCore434,b633ParitySecondCore434,
    b633_prime_rest_conjugate434]
  simp only [b633ParityPhysicalPair434,Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mp hmp
  apply Finset.sum_congr rfl
  intro m hm
  change _ = imaginaryPower z (rho+xi3)*imaginaryPower t (-rho)*
    (star (alpha mp)*chi mp*imaginaryPower mp (xi2-rho)*
      b633PrimeRest434 lo hi sigma residual
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z/mp))*
    (alpha m*star (chi m)*imaginaryPower m (xi1+rho)*
      star (b633PrimeRest434 lo hi sigma residual
        (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) t/m)))*
    (sourceMarkedWeight q0 ell P z*sourceMarkedWeight q0 ell P t : ℝ)*
    (groupSign P tw z*groupSign P tw t : ℝ)
  by_cases ham : alpha m = 0
  · simp only [ham,zero_mul,mul_zero]
  by_cases hamp : alpha mp = 0
  · simp only [hamp,star_zero,zero_mul,mul_zero]
  have dmp := b633_parity_rough_physical_divisor434 P W q0 ell tw z mp hz hp hW hmp (hs mp hamp)
  have dm := b633_parity_rough_physical_divisor434 P W q0 ell tw t m ht hp hW hm (hs m ham)
  rw [dmp.2.2.1,dm.2.2.1,←dmp.2.2.2.1,←dm.2.2.2.1,←dmp.2.2.2.2,←dm.2.2.2.2]
  have hzf : mp*(z/mp)=z := by rw [mul_comm];exact Nat.div_mul_cancel dmp.1
  have htf : m*(t/m)=t := by rw [mul_comm];exact Nat.div_mul_cancel dm.1
  have hphase :
      imaginaryPower m xi1 * imaginaryPower mp xi2 * imaginaryPower z xi3 *
        imaginaryPower (z/mp) rho * imaginaryPower (t/m) (-rho) =
      imaginaryPower z (rho+xi3)*imaginaryPower t (-rho)*
        imaginaryPower mp (xi2-rho)*imaginaryPower m (xi1+rho) := by
    simpa only [hzf,htf] using b633_parity_physical_phase434
      m mp (z/mp) (t/m) (Nat.pos_of_mem_divisors hm)
      (Nat.pos_of_mem_divisors hmp) dmp.2.1 xi1 xi2 xi3 rho
  let C : ℂ := alpha m*star (alpha mp)*chi mp*star (chi m)*
    b633PrimeRest434 lo hi sigma residual
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (z/mp))*
    star (b633PrimeRest434 lo hi sigma residual
      (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (t/m)))*
    (sourceMarkedWeight q0 ell P z*sourceMarkedWeight q0 ell P t : ℝ)*
    (groupSign P tw z*groupSign P tw t : ℝ)
  calc
    _ = C*(imaginaryPower m xi1*imaginaryPower mp xi2*imaginaryPower z xi3*
      imaginaryPower (z/mp) rho*imaginaryPower (t/m) (-rho)) := by dsimp [C];ring
    _ = C*(imaginaryPower z (rho+xi3)*imaginaryPower t (-rho)*
      imaginaryPower mp (xi2-rho)*imaginaryPower m (xi1+rho)) := by rw [hphase]
    _ = _ := by dsimp [C];ring

/-- The whole unharmonized Parity separated sum, retaining the true signed
shift 2k and both physical positivity conditions. -/
def b633ParitySeparatedCorrelation434
    (cfg : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (tw : Bool) (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi1 xi2 xi3 rho sigma Z bPsi : ℝ)
    (k : ℤ) (psi : ℝ → ℂ) : ℂ :=
  ∑ z ∈ Finset.Icc 1 ⌊bPsi*Z⌋₊,
    if 0 < (z:ℤ)+2*k then
      psi ((z:ℝ)/Z)*b633ParityPhysicalPair434 P cfg.q₀ cfg.ell tw
        alpha residual q chi lo hi xi1 xi2 xi3 rho sigma z (((z:ℤ)+2*k).toNat)
    else 0

/-- Exact normalization into E's existing native correlation: one exterior
Z, SAME twist at both ends, first core F_E=conjugate F, actual shift 2k.
This is an equality, not a claim that the correlation estimate is proved. -/
theorem b633_parity_actual_harmonic_correlation434
    (cfg : CorrelationGroupConstants) (g : ℕ) (P : Fin g → Finset ℕ)
    (W : ℝ) (tw : Bool) (alpha residual : ℕ → ℂ) (q : ℕ)
    (chi : DirichletCharacter ℂ q) (lo hi : ℕ)
    (xi1 xi2 xi3 rho sigma Z bPsi : ℝ) (k : ℤ) (psi : ℝ → ℂ)
    (hZ : Z ≠ 0)
    (hp : ∀g p, p ∈ P g → p.Prime) (hW : ∀g p, p ∈ P g → (p:ℝ) ≤ W)
    (hs : ∀m, alpha m ≠ 0 → sourceD20Rough W m) :
    b633ParitySeparatedCorrelation434 cfg g P tw alpha residual q chi lo hi
      xi1 xi2 xi3 rho sigma Z bPsi k psi =
    (Z:ℂ)*sourceCorrelationTwoTwists cfg g P
      (b633ParityEFirstCore434 alpha residual q chi lo hi xi2 rho sigma)
      (b633ParitySecondCore434 alpha residual q chi lo hi xi1 rho sigma)
      tw tw Z (rho+xi3) (-rho) bPsi (2*k) (fun t => (t:ℂ)*psi t) := by
  unfold b633ParitySeparatedCorrelation434 sourceCorrelationTwoTwists
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hzmem
  have hz : 0 < z := (Finset.mem_Icc.mp hzmem).1
  have hzc : (z:ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hZc : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ
  by_cases ht : 0 < (z:ℤ)+2*k
  · have htNat : 0 < ((z:ℤ)+2*k).toNat := by omega
    rw [ite_eq_left ht,b633_parity_full_physical_pair434 P W cfg.q₀ cfg.ell tw
      alpha residual q chi lo hi xi1 xi2 xi3 rho sigma z
        (((z:ℤ)+2*k).toNat) hz htNat hp hW hs]
    unfold sourceCorrelationBaseKernel
    rw [ite_eq_left ht,b633_parity_E_first_literal_conjugate434,star_star]
    push_cast
    field_simp
  · simp only [sourceCorrelationBaseKernel,ite_eq_right ht,mul_zero,zero_mul]
end Green64Analytic.Parity

end

end

/-! ## ParityActualHarmonicFloor -/

section

set_option maxHeartbeats 3000000
open Filter Topology
open scoped BigOperators Classical
namespace Green64Analytic.SourceBlockSieve

/-- Literal all-band harmonic normalization, with every repeated labelled
slot represented through the original factorial denominator. -/
noncomputable def sourceOriginalQActualHQ
    (r₀ jₓ : ℕ) (L : ℝ) : ℝ :=
  ∏ j : Fin (jₓ+1),
    ((∑ p ∈ sourceOriginalQActualBands r₀ jₓ L j,
      (p:ℝ)⁻¹)^r₀ / (r₀.factorial:ℝ))

/-- The half-open PNT cell lies in the literal closed Q band. -/
theorem b635_prime_log_band_subset_closed434
    (L u v : ℝ) :
    sourcePrimeLogBand L u v ⊆ sourceClosedPrimeLogBand L u v := by
  intro p hp
  have hPrime := (Finset.mem_filter.mp hp).2
  have hRange := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
  have hf := Nat.lt_floor_add_one (Real.exp (u*L))
  have hNat : ((⌊Real.exp (u*L)⌋₊:ℕ):ℝ)+1 ≤ (p:ℝ) := by
    exact_mod_cast hRange.1
  have hLower : Real.exp (u*L) ≤ (p:ℝ) := by linarith
  have hCeil : ⌈Real.exp (u*L)⌉₊ ≤ p := (Nat.ceil_le).2 hLower
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hCeil, hRange.2⟩, hPrime⟩

/-- A numeric positive reciprocal mass on the true closed 6/5 band,
proved from the independently checked native PNT. -/
theorem b635_closed_Q_band_twelfth_floor434 :
    ∀ᶠ t : ℝ in atTop,
      (1/12:ℝ) ≤ ∑ p ∈ sourceClosedPrimeLogBand t 1 (6/5), (p:ℝ)⁻¹ := by
  have hlog : (1/6:ℝ) ≤ Real.log (6/5:ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 6/5)
    norm_num at h
    exact h
  filter_upwards [source_prime_log_band_floor_unconditional
    1 (6/5) 1 (6/5) (by norm_num) le_rfl (by norm_num) le_rfl
    (by norm_num)] with t ht
  have hsub := b635_prime_log_band_subset_closed434 t 1 (6/5)
  have hsum : (∑ p ∈ sourcePrimeLogBand t 1 (6/5), (p:ℝ)⁻¹) ≤
      ∑ p ∈ sourceClosedPrimeLogBand t 1 (6/5), (p:ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp hnot => inv_nonneg.mpr (Nat.cast_nonneg p))
  exact (by linarith : (1/12:ℝ) ≤ Real.log (6/5:ℝ)/2).trans
    (ht.trans hsum)

/-- Actual admissibility gives the same diverging lower scale in ALL
Q bands, including the moving final band. -/
theorem b635_admissible_all_scales434
    (r₀ d j : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) (hL : 0 ≤ L)
    (hd : sourceOriginalDepthAdmissible r₀ d L) (hj : j ≤ d) :
    20*Real.log L ≤ sourceOriginalQActualExponent r₀ j * L := by
  have hr : (0:ℝ) < r₀ := by exact_mod_cast (by omega : 0 < r₀)
  have hs : 0 ≤ sourceOriginalQ0Scale r₀ := by
    unfold sourceOriginalQ0Scale
    positivity
  have hp : (2:ℝ)^j ≤ (2:ℝ)^d :=
    pow_le_pow_right₀ (by norm_num) hj
  have hdiv : sourceOriginalQ0Scale r₀/(2:ℝ)^d ≤
      sourceOriginalQ0Scale r₀/(2:ℝ)^j :=
    div_le_div_of_nonneg_left hs (by positivity) hp
  have hh := mul_le_mul_of_nonneg_right hdiv hL
  exact hd.trans hh

/-- Uniform positive floor over the genuine moving all-band family;
no fixed-index replacement is used. -/
theorem b635_actual_moving_Q_twelfth_floor434
    (r₀ : ℕ) (hr₀ : 1 ≤ r₀) :
    ∀ᶠ L : ℝ in atTop, ∀ d,
      sourceOriginalDepthAdmissible r₀ d L → ∀ j, j ≤ d →
      (1/12:ℝ) ≤ ∑ p ∈ sourceClosedPrimeLogBand L
        (sourceOriginalQActualExponent r₀ j)
        ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j), (p:ℝ)⁻¹ := by
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1 b635_closed_Q_band_twelfth_floor434
  have hScale : ∀ᶠ L : ℝ in atTop, t₀ ≤ 20*Real.log L := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (t₀/20)]
      with L h
    linarith
  filter_upwards [hScale, eventually_ge_atTop (0:ℝ)]
    with L hScaleL hL
  intro d hd j hj
  let t := sourceOriginalQActualExponent r₀ j * L
  have ht : t₀ ≤ t := hScaleL.trans
    (b635_admissible_all_scales434 r₀ d j L hr₀ hL hd hj)
  have hh := ht₀ t ht
  have hBand : sourceClosedPrimeLogBand t 1 (6/5) =
      sourceClosedPrimeLogBand L (sourceOriginalQActualExponent r₀ j)
        ((6/5:ℝ)*sourceOriginalQActualExponent r₀ j) := by
    unfold sourceClosedPrimeLogBand
    dsimp [t]
    congr 4 <;> ring
  simpa only [hBand] using hh

/-- Exact Parity parameters, with no rescaled slot multiplicity. -/
theorem b635_parity_r20_scale434 :
    sourceOriginalQ0Scale 20 = (1/44:ℝ) := by
  norm_num [sourceOriginalQ0Scale]

/-- Parity's 2 log L upper count is derived from actual admissibility. -/
theorem b635_parity_admissible_band_count434
    (d : ℕ) (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hd : sourceOriginalDepthAdmissible 20 d L) :
    ((d+1:ℕ):ℝ) ≤ 2*Real.log L := by
  have hLp : 0 < L := (Real.exp_pos 2).trans_le hL
  have hlog : 2 ≤ Real.log L := by
    simpa using Real.log_le_log (Real.exp_pos 2) hL
  have hp : 0 < (2:ℝ)^d := by positivity
  have hcross : 20*Real.log L * (2:ℝ)^d ≤ (1/44:ℝ)*L := by
    dsimp [sourceOriginalDepthAdmissible] at hd
    norm_num at hd
    rw [div_mul_eq_mul_div] at hd
    exact (le_div_iff₀ hp).1 hd
  have hpow : (2:ℝ)^d ≤ L := by nlinarith [hcross]
  have hlogpow := Real.log_le_log hp hpow
  rw [Real.log_pow] at hlogpow
  have h2 : (2/3:ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hprod := mul_le_mul_of_nonneg_left h2 hd0
  push_cast
  nlinarith

/-- Numerical constants are proved in Lean, using the exponential
series bound; no decimal evaluation or oracle is involved. -/
theorem b635_parity_band_factor_numeric434 :
    (1/(200:ℝ)^20 ≤ (1/12:ℝ)^20/(Nat.factorial 20:ℝ)) ∧
      Real.log (200:ℝ) ≤ (11/2:ℝ) := by
  constructor
  · norm_num [Nat.factorial]
  · have he := Real.sum_le_exp_of_nonneg
      (by norm_num : (0:ℝ) ≤ 11/2) 12
    norm_num [Finset.sum_range_succ, Nat.factorial] at he
    have hE : (200:ℝ) < Real.exp (11/2:ℝ) := by linarith
    exact ((Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 200)).2 hE).le

/-- Actual Parity lower harmonic mass. Every original Q_j remains present,
with all twenty slots and the exact 20! denominator. This proves a
positive estimate, independently of Type II precision or a final witness. -/
theorem b635_parity_actual_HQ_lower_220434 :
    ∀ᶠ L : ℝ in atTop,
      L ^ (-220:ℝ) ≤
        sourceOriginalQActualHQ 20 (sourceOriginalLiteralDepth 20 L) L := by
  filter_upwards [source_original_literal_depth_properties_eventually 20
      (by norm_num),
    b635_actual_moving_Q_twelfth_floor434 20 (by norm_num),
    eventually_ge_atTop (Real.exp 2)] with L hdepth hbands hL
  let d := sourceOriginalLiteralDepth 20 L
  let b : ℝ := 1/(200:ℝ)^20
  have hbp : 0 < b := by dsimp [b]; positivity
  have hlog200 : 0 < Real.log (200:ℝ) := Real.log_pos (by norm_num)
  have hlogb : Real.log b = -20*Real.log (200:ℝ) := by
    dsimp [b]
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_pow]
    ring
  have hbl : Real.log b ≤ 0 := by rw [hlogb]; linarith
  have hLp : 0 < L := (Real.exp_pos 2).trans_le hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg
    ((Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2)).trans hL)
  have hcount := b635_parity_admissible_band_count434 d L hL hdepth.1
  have hprod : b^(d+1) ≤ sourceOriginalQActualHQ 20 d L := by
    unfold sourceOriginalQActualHQ
    calc
      b^(d+1) = ∏ j : Fin (d+1), b := by simp
      _ ≤ ∏ j : Fin (d+1),
          ((∑ p ∈ sourceOriginalQActualBands 20 d L j, (p:ℝ)⁻¹)^20 /
            (Nat.factorial 20:ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact hbp.le
        · intro j hj
          have hband := hbands d hdepth.1 j.val (by omega)
          have hfactor : (1/12:ℝ)^20/(Nat.factorial 20:ℝ) ≤
              (∑ p ∈ sourceOriginalQActualBands 20 d L j, (p:ℝ)⁻¹)^20 /
                (Nat.factorial 20:ℝ) := by
            dsimp only [sourceOriginalQActualBands]
            gcongr
          exact b635_parity_band_factor_numeric434.1.trans hfactor
  have hexp : Real.log L * (-220:ℝ) ≤
      Real.log b * ((d+1:ℕ):ℝ) := by
    have hcount' := mul_le_mul_of_nonpos_left hcount hbl
    have hnum := mul_le_mul_of_nonneg_right
      b635_parity_band_factor_numeric434.2 hlogL
    rw [hlogb] at hcount'
    nlinarith
  calc
    L ^ (-220:ℝ) = Real.exp (Real.log L * (-220:ℝ)) :=
      Real.rpow_def_of_pos hLp _
    _ ≤ Real.exp (Real.log b * ((d+1:ℕ):ℝ)) := Real.exp_le_exp.mpr hexp
    _ = b^(d+1) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_def_of_pos hbp _).symm
    _ ≤ sourceOriginalQActualHQ 20 d L := hprod

end Green64Analytic.SourceBlockSieve

end

/-! ## Mass001 -/

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


/- Exact source owner: SourceH2GroupHP.lean; original line 8. -/
noncomputable def sourceGroupEulerF (p : ℕ) : ℝ :=
  1 + ((1/2 : ℝ) / ((p:ℝ)-1))

/- The source H_P group mass, expressed using the full distinct
group-prime union. For disjoint groups this is the formula F'_g(q₀)/V_g. -/



/- Exact source owner: SourceH2GroupHP.lean; original line 13. -/
noncomputable def sourceLiteralHP {G : Type} [Fintype G]
    (P : G → Finset ℕ) : ℝ :=
  (∏ p ∈ Finset.univ.biUnion P, sourceGroupEulerF p) *
  ∏ g : G,
    ((∑ p ∈ P g, (((p:ℝ)-(1/2:ℝ))⁻¹)) /
      (∑ p ∈ P g, (p:ℝ)⁻¹))



/- Exact source owner: SourceShiftTwoHarmonicNormalization.lean; original line 74. -/
noncomputable def sourceOriginalXA
    {B G : Type} [Fintype B] [DecidableEq B] [Fintype G]
    (r : ℕ) (Q : B → Finset ℕ) (P : G → Finset ℕ)
    (x : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*x⌋₊+1),
    sourceOriginalA r Q P u * Ψ ((u:ℝ)/x)



/- Exact source owner: SourceOriginalFixedMacroParameters.lean; original line 22. -/
noncomputable def sourceOriginalFixedMacroEpsilon (r₀ : ℕ) : ℝ :=
  1 / (48000*(r₀:ℝ)^2)



/- Exact source owner: SourceShiftTwoPGroupParityConditioning.lean; original line 8. -/
noncomputable def sourceOriginalPGroupParityDelta : ℝ :=
  min (1/((6/5:ℝ)*Real.exp 4))
    (((Real.log (12/11:ℝ)/4)^2) /
      (4*((6/5:ℝ)*Real.exp 4)))



/- Exact source owner: SourceOriginalQUniformMacroFactor.lean; original line 9. -/
noncomputable def sourceOriginalQUniformGamma (ε : ℝ) : ℝ :=
  Real.log ((11/10+ε)/(11/10-ε))/16



/- Exact source owner: SourceOriginalXAMassCompositionCore.lean; original line 32. -/
noncomputable def sourceOriginalXAMassConstant
    (α c logRatio γ δ d : ℝ) : ℝ :=
  α*c*logRatio*γ*δ/(64*d)



/- Exact source owner: SourceOriginalXAFixedParameterLower.lean; original line 11. -/
noncomputable def sourceOriginalXAFixedConstant
    (r₀ : ℕ) (α β c : ℝ) : ℝ :=
  let k := 400*r₀
  let ε := sourceOriginalFixedMacroEpsilon r₀
  sourceOriginalXAMassConstant α c (Real.log (β/α))
    ((sourceOriginalQUniformGamma ε)^(k*r₀))
    (sourceOriginalPGroupParityDelta/2)
    ((6/5:ℝ)*sourceOriginalQ0Scale r₀-sourceOriginalQ0Scale r₀/30)



/- Exact source owner: SourceOriginalXAPointwiseNative.lean; original line 14. -/
noncomputable def sourceOriginalXAGoodPrefactor
    (r₀ : ℕ) (L α β c : ℝ) : ℝ :=
  α*Real.exp L *
    (c*Real.log (β/α) /
      (4*((6/5:ℝ)*sourceOriginalQ0Scale r₀-
        sourceOriginalQ0Scale r₀/30)*L))

/- Pointwise form of the lower bound: after the full actual rest corridor
has been verified, the free-Q0 sum dominates the exact harmonic
rest-times-P weight times the explicit positive prefactor. -/



/- Exact source owner: SourceOriginalXAMassCompositionCore.lean; original line 56. -/
theorem source_original_Q0_denominator_eq
    (s : ℝ) : (6/5:ℝ)*s-s/30 = (7/6)*s := by ring



/- Exact source owner: SourceOriginalXAMassCompositionCore.lean; original line 59. -/
theorem source_original_Q0_denominator_pos
    (s : ℝ) (hs : 0 < s) : 0 < (6/5:ℝ)*s-s/30 := by
  rw [source_original_Q0_denominator_eq]
  positivity



/- Exact source owner: SourcePActualOddSmallEvent.lean; original line 11. -/
noncomputable def sourceOriginalPDelta (r₀ : ℕ) (L : ℝ) : ℝ :=
  L/(11*(r₀:ℝ))



/- Exact source owner: SourcePPrimePowerEquiv.lean; original line 9. -/
def sourceOriginalPSupported (P : Finset ℕ) : Type :=
  {n : ℕ // n ≠ 0 ∧ n.primeFactors ⊆ P}

/- EXPLICIT exact bijection, not a newly assumed distribution:
P-prime-power exponent vectors <-> positive integers supported on P.
Injectivity, both inverse identities, and all powers are checked. -/



/- Exact source owner: SourceOriginalQPGoodMassBound.lean; original line 13. -/
noncomputable def sourceOriginalPActualGoodHarmonicMass
    (r₀ : ℕ) (L : ℝ) : ℝ :=
  let P := sourceOriginalPAllActualBands r₀ L
  ∑' R : sourceOriginalPSupported (Finset.univ.biUnion P),
    if Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
      (sourceOriginalW1 P R.val / (R.val:ℝ)) *
      ((1 - (-1:ℝ)^sourceOriginalPParityExponent
        (Finset.univ.biUnion P) R.val)/2)
    else 0

/- Original P part has at least the verified fixed odd-small
harmonic share, not an auxiliary parity law. -/



/- Exact source owner: SourceOriginalQRestrictedMidpointPNT.lean; original line 9. -/
noncomputable def sourceOriginalQRestrictedMidpoint
    (r₀ j : ℕ) (ε L : ℝ) : Finset ℕ :=
  let s := sourceOriginalQActualExponent r₀ j
  sourcePrimeLogBand L ((11/10-ε)*s) ((11/10+ε)*s)

/- All primes selected for a fixed midpoint lie in the ORIGINAL closed Q_j. -/



/- Exact source owner: SourceOriginalQJointMidpoint.lean; original line 12. -/
noncomputable def sourceOriginalQJointRestAllowed
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀)
    (z : {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}) : Finset ℕ :=
  if z.val.1.val < k then
    sourceOriginalQRestrictedMidpoint r₀ z.val.1.val ε L
  else sourceOriginalQActualBands r₀ jₓ L z.val.1

/- Exact local positive fraction for each restricted macro slot.
The micro fractions equal one. The number of macro indices is fixed. -/



/- Exact source owner: SourceQPActualGoodHarmonicProduct.lean; original line 28. -/
noncomputable def sourceOriginalQPActualGoodHarmonicMass
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
          ((1-(-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion P) R.val)/2))
      else 0



/- Exact source owner: SourceH2GroupHP.lean; original line 27. -/
theorem source_group_euler_factor_one_le
    (p : ℕ) (hp : 3 ≤ p) :
    1 ≤ sourceGroupEulerF p := by
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  unfold sourceGroupEulerF
  have : 0 ≤ (1/2:ℝ) / ((p:ℝ)-1) :=
    div_nonneg (by norm_num) (by linarith)
  linarith



/- Exact source owner: SourceH2GroupHP.lean; original line 20. -/
theorem source_group_inverse_ge
    (p : ℕ) (hp : 3 ≤ p) :
    (p:ℝ)⁻¹ ≤ ((p:ℝ)-(1/2:ℝ))⁻¹ := by
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0:ℝ) < (p:ℝ)-(1/2:ℝ) := by linarith
  have hle : (p:ℝ)-(1/2:ℝ) ≤ (p:ℝ) := by linarith
  exact (inv_anti₀ hden hle)



/- Exact source owner: SourceH2GroupHP.lean; original line 36. -/
theorem source_literal_hp_ge_base
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hP : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty) :
    (∏ p ∈ Finset.univ.biUnion P, sourceGroupEulerF p) ≤
      sourceLiteralHP P := by
  classical
  have hV (g : G) : 0 < (∑ p ∈ P g, (p:ℝ)⁻¹) := by
    apply Finset.sum_pos
    · intro p hp
      have h3 := hP g p hp
      exact inv_pos.mpr (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) h3))
    · exact hPn g
  have hAlt (g : G) :
      (∑ p ∈ P g, (p:ℝ)⁻¹) ≤
      ∑ p ∈ P g, ((p:ℝ)-(1/2:ℝ))⁻¹ :=
    Finset.sum_le_sum (fun p hp => source_group_inverse_ge p (hP g p hp))
  have hRatios : 1 ≤
      ∏ g : G, ((∑ p ∈ P g, ((p:ℝ)-(1/2:ℝ))⁻¹) /
          (∑ p ∈ P g, (p:ℝ)⁻¹)) := by
    apply Finset.one_le_prod₀
    intro g hg
    apply (le_div_iff₀ (hV g)).2
    simpa using hAlt g
  have hprod : 0 ≤
       ∏ p ∈ Finset.univ.biUnion P, sourceGroupEulerF p := by
    apply Finset.prod_nonneg
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨g,_,hpg⟩
    exact (source_group_euler_factor_one_le p (hP g p hpg)).trans' (by norm_num)
  unfold sourceLiteralHP
  calc
    _ = (∏ p ∈ Finset.univ.biUnion P, sourceGroupEulerF p) * 1 := by ring
    _ ≤ (∏ p ∈ Finset.univ.biUnion P, sourceGroupEulerF p) *
        ∏ g : G, ((∑ p ∈ P g, ((p:ℝ)-(1/2:ℝ))⁻¹) /
          (∑ p ∈ P g, (p:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hRatios hprod



/- Exact source owner: SourceShiftTwoHarmonicNormalization.lean; original line 59. -/
theorem source_literal_HP_one_le
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (hP : ∀ g p, p ∈ P g → 3 ≤ p)
    (hPn : ∀ g, (P g).Nonempty) :
    1 ≤ sourceLiteralHP P := by
  have hProd : (1:ℝ) ≤
    ∏ p ∈ Finset.univ.biUnion P, sourceGroupEulerF p := by
    apply Finset.one_le_prod₀
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨g,_,hgp⟩
    exact source_group_euler_factor_one_le p (hP g p hgp)
  exact hProd.trans (source_literal_hp_ge_base P hP hPn)

/- Literal source total mass with the original positive cutoff.
For Psi supported on [1,2], this is the full sum X_A. -/



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 11. -/
noncomputable def sourceOriginalGroupHarmonicMass (P : Finset ℕ) : ℝ :=
  (∏ p ∈ P, sourceGroupEulerF p) *
    ((∑ p ∈ P, ((p:ℝ)-(1/2:ℝ))⁻¹) /
      (∑ p ∈ P, (p:ℝ)⁻¹))



/- Exact source owner: SourceShiftTwoXAGroupEvenPairs.lean; original line 49. -/
noncomputable def sourceOriginalGroupCrossEvenImages
    (A B : Finset ℕ) : Finset ℕ :=
  (A.product B).image (fun z => z.1*z.2)

/- These are genuine, distinct source P-part integers with even
multiplicity-counted Omega, not an auxiliary parity definition. -/



/- Exact source owner: SourceShiftTwoPGroupHalfPNT.lean; original line 10. -/
theorem pgroup_error_tends_zero (a M C : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ =>
      C*(2+(M-a)*t)/(a*t)^2+(a*t)⁻¹) atTop (𝓝 0) := by
  have hInv : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have h1 : Tendsto (fun t : ℝ =>
      (2*C/a^2)*(t⁻¹)^2) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul (hInv.pow 2) using 1 <;> simp
  have h2 : Tendsto (fun t : ℝ =>
      (C*(M-a)/a^2 + 1/a)*t⁻¹) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hInv using 1 <;> simp
  have hPoly : Tendsto (fun t : ℝ =>
      (2*C/a^2)*(t⁻¹)^2 +
        (C*(M-a)/a^2 + 1/a)*t⁻¹) atTop (𝓝 0) := by
    convert h1.add h2 using 1 <;> simp
  apply hPoly.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp
  <;> ring

/- The SAME actual PNT2 arithmetic controls a fixed ratio smaller
than 6/5, with a positive chosen floor below half the log ratio. -/



/- Exact source owner: SourceShiftTwoPGroupHalfPNT.lean; original line 34. -/
theorem source_prime_log_band_short_fixed_floor
    (a M u v ν : ℝ) (ha : 0 < a)
    (hau : a ≤ u) (huv : u ≤ v) (hvM : v ≤ M)
    (hν : 0 < ν) (hlog : 2*ν ≤ Real.log (v/u)) :
    ∀ᶠ t : ℝ in atTop,
      ν ≤ ∑ p ∈ sourcePrimeLogBand t u v, (p:ℝ)⁻¹ := by
  obtain ⟨C,hC,hPNT⟩ :=
    Green64Analytic.SourcePNT2.source_pnt2_unconditional a ha
  have hErr := pgroup_error_tends_zero a M C ha
  have hSmall : ∀ᶠ t : ℝ in atTop,
      C*(2+(M-a)*t)/(a*t)^2+(a*t)⁻¹ < ν :=
    hErr.eventually (eventually_lt_nhds hν)
  have hReady : ∀ᶠ t : ℝ in atTop, 1 ≤ a*t := by
    filter_upwards [eventually_ge_atTop (1/a)] with t ht
    have hh := mul_le_mul_of_nonneg_left ht ha.le
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp at hh
    nlinarith
  filter_upwards [hPNT,hSmall,hReady] with t hp hs hr
  have hMass := Green64Analytic.ReciprocalPrimeGrid.uniform_prime_reciprocal_log_error
    a M t C ha hr hC hp u v hau huv hvM
  have hMass' :
      |(∑ p ∈ sourcePrimeLogBand t u v, (p:ℝ)⁻¹) -
        Real.log (v/u)| ≤
          C*(2+(M-a)*t)/(a*t)^2+(a*t)⁻¹ := by
    simpa only [sourcePrimeLogBand, Finset.sum_filter] using hMass
  have hLeft := (abs_le.mp hMass').1
  linarith

/- Uniform positive reciprocal mass in both disjoint prime subbands
of the original source [c3 s_j,c4 s_j], since c4/c3=6/5. -/



/- Exact source owner: SourceShiftTwoPGroupHalfPNT.lean; original line 65. -/
theorem source_P_group_two_half_prime_mass :
    ∀ᶠ t : ℝ in atTop,
      (Real.log (12/11:ℝ)/4 ≤
        ∑ p ∈ sourcePrimeLogBand t 1 (11/10), (p:ℝ)⁻¹) ∧
      (Real.log (12/11:ℝ)/4 ≤
        ∑ p ∈ sourcePrimeLogBand t (11/10) (6/5), (p:ℝ)⁻¹) := by
  have hlogpos : 0 < Real.log (12/11:ℝ)/4 := by
    have h : (1:ℝ) < 12/11 := by norm_num
    have hh := Real.log_pos h
    linarith
  have hcompare :
      Real.log (12/11:ℝ) ≤ Real.log (11/10:ℝ) := by
    apply Real.log_le_log (by norm_num)
    norm_num
  have hfirst := source_prime_log_band_short_fixed_floor
    1 (6/5) 1 (11/10) (Real.log (12/11:ℝ)/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlogpos (by linarith)
  have hsecond := source_prime_log_band_short_fixed_floor
    1 (6/5) (11/10) (6/5) (Real.log (12/11:ℝ)/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlogpos (by
      have he : (6/5:ℝ)/(11/10) = 12/11 := by norm_num
      rw [he]
      linarith [Real.log_pos (by norm_num : (1:ℝ) < 12/11)])
  filter_upwards [hfirst,hsecond] with t ha hb
  exact ⟨ha,hb⟩



/- Exact source owner: SourceShiftTwoXAGroupEvenPairs.lean; original line 21. -/
theorem source_group_cross_products_injective
    (P A B : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) (hB : B ⊆ P) (hAB : Disjoint A B) :
    Set.InjOn (fun z : ℕ × ℕ => z.1*z.2) (↑(A.product B)) := by
  intro u hu v hv huv
  rcases u with ⟨p,q⟩
  rcases v with ⟨p',q'⟩
  have ⟨hpA,hqB⟩ := Finset.mem_product.mp hu
  have ⟨hpA',hqB'⟩ := Finset.mem_product.mp hv
  change p*q = p'*q' at huv
  have hp := hPrime p (hA hpA)
  have hp' := hPrime p' (hA hpA')
  have hq' := hPrime q' (hB hqB')
  have hdiv : p ∣ p'*q' := by
    rw [← huv]
    exact dvd_mul_right p q
  have hpp : p = p' := by
    rcases (Nat.Prime.dvd_mul hp).mp hdiv with hh | hh
    · exact (Nat.prime_dvd_prime_iff_eq hp hp').mp hh
    · have hpq' : p = q' :=
        (Nat.prime_dvd_prime_iff_eq hp hq').mp hh
      have hpB : p ∈ B := by simpa [hpq'] using hqB'
      exact False.elim ((Finset.disjoint_left.mp hAB) hpA hpB)
  subst p'
  have hqq : q = q' := Nat.eq_of_mul_eq_mul_left hp.pos huv
  simp [hqq]



/- Exact source owner: SourceShiftTwoXAGroupParityAtoms.lean; original line 49. -/
theorem source_group_omega_two_primes
    (P : Finset ℕ) (p q : ℕ)
    (hPrime : ∀ z ∈ P, z.Prime)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    shiftTwoGroupOmega P (p*q) = 2 := by
  have hpPrime := hPrime p hp
  have hqPrime := hPrime q hq
  have hFilt : P.filter (fun z => z ∣ p*q) = {p,q} := by
    ext z
    constructor
    · intro hz
      have hP := (Finset.mem_filter.mp hz).1
      have hdvd := (Finset.mem_filter.mp hz).2
      rcases (Nat.Prime.dvd_mul (hPrime z hP)).mp hdvd with hzp | hzq
      · exact Finset.mem_insert.mpr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq (hPrime z hP) hpPrime).mp hzp))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          ((Nat.prime_dvd_prime_iff_eq (hPrime z hP) hqPrime).mp hzq)))
    · intro hz
      rcases Finset.mem_insert.mp hz with hzp | hqz
      · subst z
        exact Finset.mem_filter.mpr ⟨hp, dvd_mul_right p q⟩
      · have : z = q := Finset.mem_singleton.mp hqz
        subst z
        exact Finset.mem_filter.mpr ⟨hq, dvd_mul_left q p⟩
  unfold shiftTwoGroupOmega
  rw [hFilt]
  simp [hpq]



/- Exact source owner: SourceShiftTwoXAGroupParityAtoms.lean; original line 77. -/
theorem source_group_factor_two_distinct_primes
    (P : Finset ℕ) (p q : ℕ)
    (hPrime : ∀ z ∈ P, z.Prime)
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    shiftTwoOriginalGroupFactor P (p*q) =
      (∑ z ∈ P, (z:ℝ)⁻¹)⁻¹ := by
  simp [shiftTwoOriginalGroupFactor,
    source_group_omega_two_primes P p q hPrime hp hq hpq]



/- Exact source owner: SourceShiftTwoXAGroupEvenMass.lean; original line 10. -/
theorem source_group_actual_even_cross_harmonic_mass
    (P A B : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (hA : A ⊆ P) (hB : B ⊆ P) (hAB : Disjoint A B) :
    (∑ n ∈ sourceOriginalGroupCrossEvenImages A B,
      (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n) =
      ((∑ p ∈ A, (p:ℝ)⁻¹) * (∑ q ∈ B, (q:ℝ)⁻¹)) /
        (∑ r ∈ P, (r:ℝ)⁻¹) := by
  classical
  have hInject := source_group_cross_products_injective P A B
    hPrime hA hB hAB
  unfold sourceOriginalGroupCrossEvenImages
  rw [Finset.sum_image hInject]
  rw [show A.product B = A ×ˢ B from rfl]
  rw [Finset.sum_product]
  let V : ℝ := ∑ r ∈ P, (r:ℝ)⁻¹
  have hTerms :
      (∑ p ∈ A, ∑ q ∈ B,
          ((p*q:ℕ):ℝ)⁻¹ * shiftTwoOriginalGroupFactor P (p*q)) =
      ∑ p ∈ A, ∑ q ∈ B,
          ((p:ℝ)⁻¹ * (q:ℝ)⁻¹) * V⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    have hpq : p ≠ q := by
      intro h
      exact (Finset.disjoint_left.mp hAB) hp
        (by simpa [h] using hq)
    rw [source_group_factor_two_distinct_primes P p q
      hPrime (hA hp) (hB hq) hpq]
    simp only [Nat.cast_mul, mul_inv_rev]
    dsimp [V]
    ring
  rw [hTerms]
  dsimp [V]
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 16. -/
theorem source_original_group_euler_local_exp_upper
    (p : ℕ) (hp : 3 ≤ p) :
    sourceGroupEulerF p ≤ Real.exp ((p:ℝ)⁻¹) := by
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hd : (0:ℝ) < (p:ℝ)-1 := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have hdiv : (1/2:ℝ) / ((p:ℝ)-1) ≤ 1/(p:ℝ) :=
    (div_le_div_iff₀ hd hp0).2 (by nlinarith)
  have he := Real.add_one_le_exp ((p:ℝ)⁻¹)
  unfold sourceGroupEulerF
  simp only [one_div] at hdiv
  linarith



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 41. -/
theorem source_original_group_euler_prod_upper
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p) :
    (∏ p ∈ P, sourceGroupEulerF p) ≤
      Real.exp (∑ p ∈ P, (p:ℝ)⁻¹) := by
  have hp0 (p : ℕ) (hp : p ∈ P) :
      0 ≤ sourceGroupEulerF p :=
    le_trans (by norm_num) (source_group_euler_factor_one_le p (h3 p hp))
  calc
    _ ≤ ∏ p ∈ P, Real.exp ((p:ℝ)⁻¹) :=
      Finset.prod_le_prod₀ hp0
        (fun p hp => source_original_group_euler_local_exp_upper p (h3 p hp))
    _ = Real.exp (∑ p ∈ P, (p:ℝ)⁻¹) := by
      rw [Real.exp_sum]



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 29. -/
theorem source_original_group_inverse_local_upper
    (p : ℕ) (hp : 3 ≤ p) :
    ((p:ℝ)-(1/2:ℝ))⁻¹ ≤
      (6/5:ℝ) * (p:ℝ)⁻¹ := by
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hd : (0:ℝ) < (p:ℝ)-(1/2:ℝ) := by linarith
  have hp0 : (0:ℝ) < p := by linarith
  have h := (div_le_div_iff₀ hd hp0).2
    (show (1:ℝ)*(p:ℝ) ≤ (6/5:ℝ)*((p:ℝ)-(1/2:ℝ)) by
      nlinarith)
  simpa only [one_div, div_eq_mul_inv, one_mul] using h



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 55. -/
theorem source_original_group_harmonic_mass_bounds
    (P : Finset ℕ) (h3 : ∀ p ∈ P, 3 ≤ p)
    (hPn : P.Nonempty)
    (hVupper : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4) :
    1 ≤ sourceOriginalGroupHarmonicMass P ∧
    sourceOriginalGroupHarmonicMass P ≤
      (6/5:ℝ) * Real.exp 4 := by
  let V : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
  let D : ℝ := ∑ p ∈ P, ((p:ℝ)-(1/2:ℝ))⁻¹
  let F : ℝ := ∏ p ∈ P, sourceGroupEulerF p
  have hV : 0 < V := by
    dsimp [V]
    apply Finset.sum_pos
    · intro p hp
      exact inv_pos.mpr (by exact_mod_cast
        (lt_of_lt_of_le (by norm_num : 0 < 3) (h3 p hp)))
    · exact hPn
  have hDlower : V ≤ D := Finset.sum_le_sum
    (fun p hp => source_group_inverse_ge p (h3 p hp))
  have hDupper : D ≤ (6/5:ℝ)*V := by
    calc
      D ≤ ∑ p ∈ P, (6/5:ℝ) * (p:ℝ)⁻¹ :=
        Finset.sum_le_sum (fun p hp =>
          source_original_group_inverse_local_upper p (h3 p hp))
      _ = (6/5:ℝ)*V := by rw [Finset.mul_sum]
  have hRlower : 1 ≤ D/V := (le_div_iff₀ hV).2 (by simpa using hDlower)
  have hRupper : D/V ≤ (6/5:ℝ) := (div_le_iff₀ hV).2 (by simpa using hDupper)
  have hFlower : 1 ≤ F := Finset.one_le_prod₀
    (fun p hp => source_group_euler_factor_one_le p (h3 p hp))
  have hFupper : F ≤ Real.exp 4 :=
    (source_original_group_euler_prod_upper P h3).trans
      (Real.exp_le_exp.mpr hVupper)
  have hRnonneg : 0 ≤ D/V := le_trans (by norm_num) hRlower
  have hFnonneg : 0 ≤ F := le_trans (by norm_num) hFlower
  change 1 ≤ F * (D/V) ∧ F * (D/V) ≤
    (6/5:ℝ) * Real.exp 4
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hFlower)
      (sub_nonneg.mpr hRlower)]
  · have h1 := mul_le_mul_of_nonneg_right hFupper hRnonneg
    have h2 := mul_le_mul_of_nonneg_left hRupper (Real.exp_nonneg 4)
    nlinarith

/- The same original group factors multiply to sourceLiteralHP. -/



/- Exact source owner: SourceShiftTwoXAGroupEvenFloor.lean; original line 11. -/
theorem source_group_actual_even_cross_normalized_floor
    (P A B : Finset ℕ) (ν : ℝ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (hA : A ⊆ P) (hB : B ⊆ P) (hAB : Disjoint A B)
    (hVupper : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4)
    (hν : 0 < ν)
    (hVA : ν ≤ ∑ p ∈ A, (p:ℝ)⁻¹)
    (hVB : ν ≤ ∑ p ∈ B, (p:ℝ)⁻¹) :
    (ν^2) / (4 * ((6/5:ℝ)*Real.exp 4)) ≤
      (∑ n ∈ sourceOriginalGroupCrossEvenImages A B,
          (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n) /
        sourceOriginalGroupHarmonicMass P := by
  let V : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
  let VA : ℝ := ∑ p ∈ A, (p:ℝ)⁻¹
  let VB : ℝ := ∑ p ∈ B, (p:ℝ)⁻¹
  let H : ℝ := sourceOriginalGroupHarmonicMass P
  let C : ℝ := (6/5:ℝ)*Real.exp 4
  have hVpos : 0 < V := by
    dsimp [V]
    apply Finset.sum_pos
    · intro p hp
      exact inv_pos.mpr (by exact_mod_cast
        (lt_of_lt_of_le (by norm_num : 0 < 3) (h3 p hp)))
    · exact hPn
  have hVA0 : 0 ≤ VA := hν.le.trans hVA
  have hVB0 : 0 ≤ VB := hν.le.trans hVB
  have hProd : ν^2 ≤ VA * VB := by
    have hh := mul_le_mul hVA hVB hν.le hVA0
    nlinarith
  have hV4 : V ≤ 4 := hVupper
  have hPair : ν^2 / 4 ≤ (VA * VB)/V := by
    apply (le_div_iff₀ hVpos).2
    have hbound : ν^2*V ≤ ν^2*4 :=
      mul_le_mul_of_nonneg_left hV4 (sq_nonneg ν)
    nlinarith
  have hHbounds := source_original_group_harmonic_mass_bounds
    P h3 hPn hVupper
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hHbounds.1
  have hHC : H ≤ C := hHbounds.2
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hMass := source_group_actual_even_cross_harmonic_mass
    P A B hPrime hA hB hAB
  rw [hMass]
  change ν^2 / (4*C) ≤ (VA*VB/V)/H
  apply (div_le_div_iff₀ (by positivity : 0 < 4*C) hHpos).2
  have ha : ν^2 * H ≤ ν^2 * C :=
    mul_le_mul_of_nonneg_left hHC (sq_nonneg ν)
  have hb : (ν^2 / 4)*(4*C) ≤ (VA*VB/V)*(4*C) :=
    mul_le_mul_of_nonneg_right hPair (by positivity)
  nlinarith



/- Exact source owner: SourceShiftTwoXAGroupParityAtoms.lean; original line 8. -/
theorem source_group_omega_one_prime
    (P : Finset ℕ) (p : ℕ)
    (hPrime : ∀ q ∈ P, q.Prime) (hp : p ∈ P) :
    shiftTwoGroupOmega P p = 1 := by
  have hpPrime := hPrime p hp
  have hFilt : P.filter (fun q => q ∣ p) = {p} := by
    ext q
    constructor
    · intro hq
      have hqP := (Finset.mem_filter.mp hq).1
      have hqD := (Finset.mem_filter.mp hq).2
      exact Finset.mem_singleton.mpr
        ((Nat.prime_dvd_prime_iff_eq (hPrime q hqP) hpPrime).mp hqD)
    · intro hq
      have : q = p := Finset.mem_singleton.mp hq
      subst q
      simp [hp]
  unfold shiftTwoGroupOmega
  rw [hFilt]
  simp

/- Exact source W1 local factor on a single, odd-multiplicity atom. -/



/- Exact source owner: SourceShiftTwoXAGroupParityAtoms.lean; original line 30. -/
theorem source_group_factor_single_prime
    (P : Finset ℕ) (p : ℕ)
    (hPrime : ∀ q ∈ P, q.Prime) (hp : p ∈ P) :
    shiftTwoOriginalGroupFactor P p =
      (∑ q ∈ P, (q:ℝ)⁻¹)⁻¹ := by
  simp [shiftTwoOriginalGroupFactor,
    source_group_omega_one_prime P p hPrime hp]
/- Here the parity exponent counts valuations, not omega. -/



/- Exact source owner: SourceShiftTwoXAGroupOddSingleMass.lean; original line 9. -/
theorem source_group_actual_odd_single_harmonic_mass
    (P : Finset ℕ)
    (hPrime : ∀ p ∈ P, p.Prime) (hNonempty : P.Nonempty) :
    (∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p) = 1 := by
  let V : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
  have hV : 0 < V := by
    dsimp [V]
    apply Finset.sum_pos
    · intro p hp
      exact inv_pos.mpr (by exact_mod_cast (hPrime p hp).pos)
    · exact hNonempty
  calc
    (∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p) =
        ∑ p ∈ P, (p:ℝ)⁻¹ * V⁻¹ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [source_group_factor_single_prime P p hPrime hp]
    _ = V * V⁻¹ := by rw [Finset.sum_mul]
    _ = 1 := mul_inv_cancel₀ hV.ne'



/- Exact source owner: SourceShiftTwoXAGroupMassUpper.lean; original line 109. -/
theorem source_original_group_odd_single_normalized_lower
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (h3 : ∀ p ∈ P, 3 ≤ p) (hPn : P.Nonempty)
    (hVupper : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4) :
    ((∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p) /
       sourceOriginalGroupHarmonicMass P) ≥
      1 / ((6/5:ℝ)*Real.exp 4) := by
  have hmass := source_group_actual_odd_single_harmonic_mass P hPrime hPn
  obtain ⟨hLower,hUpper⟩ :=
    source_original_group_harmonic_mass_bounds P h3 hPn hVupper
  have hpos : 0 < sourceOriginalGroupHarmonicMass P :=
    lt_of_lt_of_le (by norm_num) hLower
  have hC : 0 < (6/5:ℝ)*Real.exp 4 := by positivity
  rw [hmass]
  exact (div_le_div_iff₀ hC hpos).2 (by simpa using hUpper)



/- Exact source owner: SourceShiftTwoPGroupUniformParity.lean; original line 13. -/
theorem source_original_closed_P_group_uniform_parity_floor :
    ∀ᶠ t : ℝ in atTop,
      let P := sourceOriginalClosedPGroup t
      let A := sourcePrimeLogBand t 1 (11/10)
      let B := sourcePrimeLogBand t (11/10) (6/5)
      1 ≤ sourceOriginalGroupHarmonicMass P ∧
      sourceOriginalGroupHarmonicMass P ≤
        (6/5:ℝ)*Real.exp 4 ∧
      1/((6/5:ℝ)*Real.exp 4) ≤
        (∑ p ∈ P, (p:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P p) /
          sourceOriginalGroupHarmonicMass P ∧
      ((Real.log (12/11:ℝ)/4)^2) /
          (4*((6/5:ℝ)*Real.exp 4)) ≤
        (∑ n ∈ sourceOriginalGroupCrossEvenImages A B,
          (n:ℝ)⁻¹ * shiftTwoOriginalGroupFactor P n) /
          sourceOriginalGroupHarmonicMass P := by
  have hFloors := source_P_group_two_half_prime_mass
  filter_upwards [hFloors, eventually_ge_atTop (2:ℝ)]
    with t hFloors ht
  let P := sourceOriginalClosedPGroup t
  let A := sourcePrimeLogBand t 1 (11/10)
  let B := sourcePrimeLogBand t (11/10) (6/5)
  let ν : ℝ := Real.log (12/11:ℝ)/4
  have hν : 0 < ν := by
    dsimp [ν]
    exact div_pos (Real.log_pos (by norm_num : (1:ℝ) < 12/11))
      (by norm_num)
  have hVA : ν ≤ ∑ p ∈ A, (p:ℝ)⁻¹ := hFloors.1
  have hVB : ν ≤ ∑ p ∈ B, (p:ℝ)⁻¹ := hFloors.2
  have hA : A ⊆ P := source_original_P_short_band_subset
    t 1 (11/10) (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
  have hB : B ⊆ P := source_original_P_short_band_subset
    t (11/10) (6/5) (by linarith) (by norm_num)
    (by norm_num) (by norm_num)
  have hAB : Disjoint A B :=
    source_original_P_two_halves_disjoint t
  have hPn : P.Nonempty := by
    by_contra h
    have hPempty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hAempty : A = ∅ := Finset.subset_empty.mp
      (by simpa [hPempty] using hA)
    simp [hAempty] at hVA
    linarith
  have hPrime : ∀ p ∈ P, p.Prime :=
    fun p hp => source_original_P_closed_prime t p hp
  have h3 : ∀ p ∈ P, 3 ≤ p :=
    fun p hp => source_original_P_closed_prime_ge_three t ht p hp
  let w : ℝ := Real.exp ((3/4:ℝ)*t)
  have hw : 1 < w := by
    dsimp [w]
    have he := Real.add_one_le_exp ((3/4:ℝ)*t)
    linarith
  have hBand : ∀ p ∈ P,
      w < (p:ℝ) ∧ (p:ℝ) ≤ w^2 :=
    fun p hp => source_original_P_closed_quadratic_range t ht p hp
  have hV4 : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4 :=
    source_quadratic_prime_reciprocal_le_four
      w P hw (fun p hp =>
        ⟨hPrime p hp,(hBand p hp).1,(hBand p hp).2⟩)
  have hBounds := source_original_group_harmonic_mass_bounds
    P h3 hPn hV4
  have hOdd := source_original_group_odd_single_normalized_lower
    P hPrime h3 hPn hV4
  have hEven := source_group_actual_even_cross_normalized_floor
    P A B ν hPrime h3 hPn hA hB hAB hV4 hν hVA hVB
  dsimp only
  exact ⟨hBounds.1,hBounds.2,hOdd,hEven⟩


end Green64Analytic.SourceBlockSieve

end

end

/-! ## Mass002 -/

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


/- Exact source owner: SourcePActualAllLocal.lean; original line 10. -/
theorem source_original_P_all_actual_local_eventually
    (r₀ : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (∀ g : sourceOriginalPAllGroupType r₀ L,
        (sourceOriginalPAllActualBands r₀ L g).Nonempty) ∧
      (∀ g : sourceOriginalPAllGroupType r₀ L,
        ∀ p ∈ sourceOriginalPAllActualBands r₀ L g, 6 ≤ p) ∧
      (∀ g : sourceOriginalPAllGroupType r₀ L,
        (∑ p ∈ sourceOriginalPAllActualBands r₀ L g,
            (p:ℝ)⁻¹) ≤ 4) := by
  obtain ⟨T, hParityFrom⟩ :=
    Filter.eventually_atTop.1 source_original_closed_P_group_uniform_parity_floor
  have hPow : Tendsto (fun L : ℝ => L^(1/10:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hLarge : ∀ᶠ L : ℝ in atTop,
      max T 5 ≤ L^(1/10:ℝ) :=
    hPow.eventually (eventually_ge_atTop (max T 5))
  filter_upwards [eventually_ge_atTop (1:ℝ), hLarge] with L hL hLargeL
  have hT (g : sourceOriginalPAllGroupType r₀ L) :
      max T 5 ≤ (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val :=
    hLargeL.trans (source_original_P_all_actual_band_lower r₀ L hL g)
  have h5 (g : sourceOriginalPAllGroupType r₀ L) :
      5 ≤ (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val :=
    (le_max_right T 5).trans (hT g)
  have hMass (g : sourceOriginalPAllGroupType r₀ L) :
      1 ≤ sourceOriginalGroupHarmonicMass
        (sourceOriginalPAllActualBands r₀ L g) := by
    exact (hParityFrom _ ((le_max_left T 5).trans (hT g))).1
  constructor
  · intro g
    by_contra hEmpty
    have hEq : sourceOriginalPAllActualBands r₀ L g = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have h := hMass g
    simp [sourceOriginalGroupHarmonicMass, hEq] at h
    linarith
  constructor
  · intro g p hp
    let t : ℝ := (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val
    have hLower := (source_original_P_closed_range t p hp).1
    have hExp := Real.add_one_le_exp t
    have hSix : (6:ℝ) ≤ p := by
      have ht5 := h5 g
      dsimp [t] at *
      linarith
    exact_mod_cast hSix
  · intro g
    let t : ℝ := (3/2:ℝ)*sourceOriginalPGroupScale r₀ L g.val
    let w : ℝ := Real.exp ((3/4:ℝ)*t)
    have ht5 : 5 ≤ t := h5 g
    have ht2 : 2 ≤ t := by linarith
    have hw : 1 < w := by
      dsimp [w]
      have he := Real.add_one_le_exp ((3/4:ℝ)*t)
      nlinarith
    have hPrime : ∀ p ∈ sourceOriginalClosedPGroup t, p.Prime :=
      fun p hp => source_original_P_closed_prime t p hp
    have hBand : ∀ p ∈ sourceOriginalClosedPGroup t,
        w < (p:ℝ) ∧ (p:ℝ) ≤ w^2 :=
      fun p hp => source_original_P_closed_quadratic_range t ht2 p hp
    change (∑ p ∈ sourceOriginalClosedPGroup t, (p:ℝ)⁻¹) ≤ 4
    exact source_quadratic_prime_reciprocal_le_four w
      (sourceOriginalClosedPGroup t) hw
      (fun p hp => ⟨hPrime p hp, (hBand p hp).1, (hBand p hp).2⟩)



/- Exact source owner: SourceShiftTwoPGroupParityConditioning.lean; original line 13. -/
theorem source_original_P_group_parity_delta_positive :
    0 < sourceOriginalPGroupParityDelta := by
  unfold sourceOriginalPGroupParityDelta
  have hν : 0 < Real.log (12/11:ℝ)/4 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hC : 0 < (6/5:ℝ)*Real.exp 4 := by positivity
  apply lt_min
  · exact div_pos (by norm_num) hC
  · exact div_pos (sq_pos_of_pos hν) (by positivity)

/- Pure conditioning algebra: background masses need only be nonnegative
and sum to one. No auxiliary integer sampling law is introduced. -/



/- Exact source owner: SourceOriginalQJointPositiveRest.lean; original line 21. -/
noncomputable def sourceOriginalQActualGoodRestHarmonicMass
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀) : ℝ :=
  let Q := sourceOriginalQActualBands r₀ jₓ L
  let I := {z : Fin (jₓ+1) × Fin r₀ // z ≠ (b,i)}
  let Good := sourceOriginalQJointRestAllowed r₀ jₓ k L ε b i
  ∑ rest : (z : I) → {p // p ∈ Q z.val.1},
    if (∀ z, (rest z).val ∈ Good z) then
      (∏ _j : Fin (jₓ+1), (r₀.factorial:ℝ)⁻¹) /
        (((∏ z : I, (rest z).val):ℕ):ℝ)
    else 0

/- A fixed positive FRACTION of full original Q-rest harmonic mass
survives all macro midpoint constraints simultaneously. It depends
only on fixed r₀, k and relative epsilon, not on L or moving j_x. -/



/- Exact source owner: SourceQPActualGoodHarmonicProduct.lean; original line 50. -/
theorem source_original_QP_actual_good_harmonic_product
    (r₀ jₓ k : ℕ) (L ε : ℝ)
    (b : Fin (jₓ+1)) (i : Fin r₀) :
    sourceOriginalQPActualGoodHarmonicMass r₀ jₓ k L ε b i =
      sourceOriginalQActualGoodRestHarmonicMass r₀ jₓ k L ε b i *
      (∑' R : sourceOriginalPSupported
          (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)),
        if Real.log (R.val:ℝ) ≤ sourceOriginalPDelta r₀ L/12 then
          (sourceOriginalW1 (sourceOriginalPAllActualBands r₀ L) R.val /
             (R.val:ℝ)) *
          ((1-(-1:ℝ)^sourceOriginalPParityExponent
            (Finset.univ.biUnion (sourceOriginalPAllActualBands r₀ L)) R.val)/2)
        else 0) := by
  classical
  unfold sourceOriginalQPActualGoodHarmonicMass
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



/- Exact source owner: SourcePActualOddSmallEvent.lean; original line 14. -/
theorem source_original_P_actual_cutoff_exact
    (r₀ : ℕ) (L : ℝ) (hr₀ : 1 ≤ r₀) :
    (Real.exp L)^(1/(132*(r₀:ℝ))) =
      Real.exp (sourceOriginalPDelta r₀ L/12) := by
  have hr : (r₀:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < (1:ℕ)) hr₀))
  rw [← Real.exp_mul]
  congr 1
  dsimp [sourceOriginalPDelta]
  field_simp
  ring

/- For the actual original P_g sets, all local geometry assumptions
needed by the global tilted moment and odd parity theorem are
discharged from source dyadic bands and PNT; no hypothetical small G. -/



/- Exact source owner: SourcePGlobalIndexEquiv.lean; original line 9. -/
noncomputable def sourceOriginalPDisjointSigmaEquiv
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    (Σ g : G, {p // p ∈ P g}) ≃
      {p // p ∈ Finset.univ.biUnion P} := by
  classical
  let toP : (Σ g : G, {p // p ∈ P g}) →
      {p // p ∈ Finset.univ.biUnion P} :=
    fun x => ⟨x.2.val,
      Finset.mem_biUnion.mpr ⟨x.1,Finset.mem_univ _,x.2.property⟩⟩
  have hinj : Function.Injective toP := by
    intro x y h
    obtain ⟨g,p⟩ := x
    obtain ⟨j,q⟩ := y
    have hpq : p.val = q.val := congrArg Subtype.val h
    have hgj : g = j := hDisj g j p.val p.property (by
      simpa [←hpq] using q.property)
    cases hgj
    have hp : p = q := Subtype.ext hpq
    cases hp
    rfl
  have hsurj : Function.Surjective toP := by
    intro q
    obtain ⟨g,hg,hp⟩ := Finset.mem_biUnion.mp q.property
    refine ⟨⟨g,⟨q.val,hp⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact Equiv.ofBijective toP ⟨hinj,hsurj⟩

/- Unrestricted P-prime exponent vectors form an exact disjoint
groupwise product, with repeated powers preserved. -/



/- Exact source owner: SourcePGlobalIndexEquiv.lean; original line 41. -/
noncomputable def sourceOriginalPDisjointExponentEquiv
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h) :
    ((g : G) → {p // p ∈ P g} → ℕ) ≃
      ({p // p ∈ Finset.univ.biUnion P} → ℕ) :=
  (Equiv.piCurry (fun (g : G) (_ : {p // p ∈ P g}) => ℕ)).symm |>.trans
    (Equiv.piCongrLeft'
      (fun (_ : Σ g : G, {p // p ∈ P g}) => ℕ)
      (sourceOriginalPDisjointSigmaEquiv P hDisj))



/- Exact source owner: SourcePPrimePowerFibres.lean; original line 9. -/
noncomputable def sourceOriginalPPrimePowerProduct
    (P : Finset ℕ) (e : {p // p ∈ P} → ℕ) : ℕ :=
  ∏ z : {p // p ∈ P}, z.val ^ e z

/- A P-prime exponent in the true product is exactly its chosen
valuation, including arbitrarily repeated prime powers. -/



/- Exact source owner: SourcePGlobalVectorProduct.lean; original line 10. -/
noncomputable def sourceOriginalPGlobalVectorProduct
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (e : (g : G) → {p // p ∈ P g} → ℕ) : ℕ :=
  ∏ g : G, sourceOriginalPPrimePowerProduct (P g) (e g)



/- Exact source owner: SourcePPrimePowerFibres.lean; original line 15. -/
theorem source_original_P_power_factorization_at
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (q : ℕ) (hq : q ∈ P) :
    (sourceOriginalPPrimePowerProduct P e).factorization q =
      e ⟨q,hq⟩ := by
  classical
  have hn : ∀ z ∈ (Finset.univ : Finset {p // p ∈ P}),
      z.val ^ e z ≠ 0 := by
    intro z hz
    exact pow_ne_zero _ (hPrime z.val z.property).ne_zero
  unfold sourceOriginalPPrimePowerProduct
  rw [Nat.factorization_prod hn]
  simp only [Finsupp.finsetSum_apply]
  have hterms (z : {p // p ∈ P}) :
      ((z.val ^ e z).factorization q) =
        if z.val = q then e z else 0 := by
    rw [Nat.factorization_pow, Nat.Prime.factorization
      (hPrime z.val z.property)]
    simp [Finsupp.single_apply]
  simp_rw [hterms]
  have hsum : (∑ z : {p // p ∈ P}, if z.val = q then e z else 0) =
      (if (⟨q,hq⟩ : {p // p ∈ P}).val = q then e ⟨q,hq⟩ else 0) := by
    change (∑ z ∈ (Finset.univ : Finset {p // p ∈ P}),
      if z.val = q then e z else 0) = _
    apply Finset.sum_eq_single (⟨q,hq⟩ : {p // p ∈ P})
    · intro z hz hne
      have hv : z.val ≠ q := by
        intro hh
        exact hne (Subtype.ext hh)
      simp [hv]
    · intro hh
      exact False.elim (hh (Finset.mem_univ _))
  simpa using hsum

/- Distinct primes outside the group have valuation zero in
every product of its indexed prime-power exponent vector. -/



/- Exact source owner: SourcePPrimePowerFibres.lean; original line 51. -/
theorem source_original_P_power_factorization_out
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) (q : ℕ) (hq : q ∉ P) :
    (sourceOriginalPPrimePowerProduct P e).factorization q = 0 := by
  classical
  have hn : ∀ z ∈ (Finset.univ : Finset {p // p ∈ P}),
      z.val ^ e z ≠ 0 := by
    intro z hz
    exact pow_ne_zero _ (hPrime z.val z.property).ne_zero
  unfold sourceOriginalPPrimePowerProduct
  rw [Nat.factorization_prod hn]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro z hz
  rw [Nat.factorization_pow, Nat.Prime.factorization
    (hPrime z.val z.property)]
  have hne : z.val ≠ q := by
    intro h
    exact hq (h ▸ z.property)
  simp [Finsupp.single_apply, hne]

/- Full product is positive, including all-zero exponent vectors. -/



/- Exact source owner: SourcePPrimePowerFibres.lean; original line 73. -/
theorem source_original_P_power_product_ne_zero
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) :
    sourceOriginalPPrimePowerProduct P e ≠ 0 := by
  unfold sourceOriginalPPrimePowerProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (hPrime z.val z.property).ne_zero

/- No two different P prime-power assignments can represent the
same positive integer; the original prime multiplicities are retained. -/



/- Exact source owner: SourcePGlobalVectorProduct.lean; original line 30. -/
theorem source_original_P_global_factorization_at
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ)
    (g : G) (p : ℕ) (hp : p ∈ P g) :
    (sourceOriginalPGlobalVectorProduct P e).factorization p =
      e g ⟨p,hp⟩ := by
  classical
  have hFac :
      (sourceOriginalPGlobalVectorProduct P e).factorization p =
      ∑ h : G,
        (sourceOriginalPPrimePowerProduct (P h) (e h)).factorization p := by
    unfold sourceOriginalPGlobalVectorProduct
    rw [Nat.factorization_prod (by
      intro h hh
      exact source_original_P_power_product_ne_zero
        (P h) (hPrime h) (e h))]
    simp only [Finsupp.finsetSum_apply]
  calc
    _ = ∑ h : G,
        (sourceOriginalPPrimePowerProduct (P h) (e h)).factorization p := hFac
    _ = (sourceOriginalPPrimePowerProduct (P g) (e g)).factorization p := by
      apply Finset.sum_eq_single g
      · intro h hh hne
        have hpOut : p ∉ P h := by
          intro hpH
          exact hne (hDisj h g p hpH hp)
        exact source_original_P_power_factorization_out
          (P h) (hPrime h) (e h) p hpOut
      · intro hg
        exact False.elim (hg (Finset.mem_univ _))
    _ = e g ⟨p,hp⟩ := source_original_P_power_factorization_at
          (P g) (hPrime g) (e g) p hp



/- Exact source owner: SourcePGlobalVectorProduct.lean; original line 16. -/
theorem source_original_P_global_product_ne_zero
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (e : (g : G) → {p // p ∈ P g} → ℕ) :
    sourceOriginalPGlobalVectorProduct P e ≠ 0 := by
  unfold sourceOriginalPGlobalVectorProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro g hg
  exact source_original_P_power_product_ne_zero
    (P g) (hPrime g) (e g)

/- Exact valuations in each P-group under the true disjoint
integer product, retaining EVERY repeated exponent. -/



/- Exact source owner: SourcePGlobalWeightParity.lean; original line 9. -/
theorem source_original_P_global_group_dvd_iff
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ)
    (g : G) (p : ℕ) (hp : p ∈ P g) :
    (p ∣ sourceOriginalPGlobalVectorProduct P e) ↔
      p ∣ sourceOriginalPPrimePowerProduct (P g) (e g) := by
  have hRne := source_original_P_global_product_ne_zero
    P hPrime e
  have hNne := source_original_P_power_product_ne_zero
    (P g) (hPrime g) (e g)
  rw [Nat.Prime.dvd_iff_one_le_factorization
      (hPrime g p hp) hRne]
  rw [Nat.Prime.dvd_iff_one_le_factorization
      (hPrime g p hp) hNne]
  rw [source_original_P_global_factorization_at
    P hPrime hDisj e g p hp,
    source_original_P_power_factorization_at
      (P g) (hPrime g) (e g) p hp]

/- Distinct omega_g counts are independent of prime powers in
other disjoint groups; this is NOT the multiplicity Ω parity. -/



/- Exact source owner: SourcePGlobalWeightParity.lean; original line 33. -/
theorem source_original_P_global_omega_at
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ)
    (g : G) :
    shiftTwoGroupOmega (P g) (sourceOriginalPGlobalVectorProduct P e) =
      shiftTwoGroupOmega (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)) := by
  unfold shiftTwoGroupOmega
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro hp
    exact ⟨hp.1, (source_original_P_global_group_dvd_iff
      P hPrime hDisj e g p hp.1).mp hp.2⟩
  · intro hp
    exact ⟨hp.1, (source_original_P_global_group_dvd_iff
      P hPrime hDisj e g p hp.1).mpr hp.2⟩
/- Pointwise exact W1 multiplicativity over disjoint original
P groups for true P-powered source products. -/



/- Exact source owner: SourcePGlobalWeightParity.lean; original line 56. -/
theorem source_original_P_global_W1_factorization
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ) :
    sourceOriginalW1 P (sourceOriginalPGlobalVectorProduct P e) =
      ∏ g : G, shiftTwoOriginalGroupFactor (P g)
        (sourceOriginalPPrimePowerProduct (P g) (e g)) := by
  unfold sourceOriginalW1
  apply Finset.prod_congr rfl
  intro g hg
  unfold shiftTwoOriginalGroupFactor
  rw [source_original_P_global_omega_at P hPrime hDisj e g]

/- The actual total multiplicity Ω parity is additive across
source P groups, unlike the distinct prime count omega_g. -/



/- Exact source owner: SourcePTiltedGlobalProduct.lean; original line 10. -/
theorem source_original_P_global_real_rpow_product
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (e : (g : G) → {p // p ∈ P g} → ℕ) (δ : ℝ) :
    ((sourceOriginalPGlobalVectorProduct P e:ℝ)^δ) =
      ∏ g : G,
        ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)^δ) := by
  classical
  have hFactor (g : G) :
      0 ≤ (sourceOriginalPPrimePowerProduct (P g) (e g):ℝ) := by
    positivity
  have hGeneral (s : Finset G) :
      ((∏ g ∈ s, (sourceOriginalPPrimePowerProduct (P g) (e g):ℝ))^δ) =
      ∏ g ∈ s,
        ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)^δ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert g s hgs ih =>
      rw [Finset.prod_insert hgs, Finset.prod_insert hgs]
      rw [Real.mul_rpow (hFactor g)
        (Finset.prod_nonneg (fun h hh => hFactor h)), ih]
  unfold sourceOriginalPGlobalVectorProduct
  rw [Nat.cast_prod]
  exact hGeneral Finset.univ



/- Exact source owner: SourcePTiltedGlobalProduct.lean; original line 36. -/
theorem source_original_P_global_W1_tilted_pointwise
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ) (δ : ℝ) :
    sourceOriginalW1 P (sourceOriginalPGlobalVectorProduct P e) *
      ((sourceOriginalPGlobalVectorProduct P e:ℝ)^(δ-1)) =
      ∏ g : G,
        shiftTwoOriginalGroupFactor (P g)
          (sourceOriginalPPrimePowerProduct (P g) (e g)) *
          ((sourceOriginalPPrimePowerProduct (P g) (e g):ℝ)^(δ-1)) := by
  have hW := source_original_P_global_W1_factorization
    P hPrime hDisj e
  have hTilt := source_original_P_global_real_rpow_product
    P hPrime e (δ-1)
  rw [hW,hTilt]
  exact Finset.prod_mul_distrib.symm



/- Exact source owner: SourcePGlobalExponentAt.lean; original line 9. -/
theorem source_original_P_disjoint_exp_at
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ)
    (g : G) (p : ℕ) (hp : p ∈ P g) :
    (sourceOriginalPDisjointExponentEquiv P hDisj e)
      ⟨p,Finset.mem_biUnion.mpr
        ⟨g,Finset.mem_univ _,hp⟩⟩ =
      e g ⟨p,hp⟩ := by
  classical
  let S := sourceOriginalPDisjointSigmaEquiv P hDisj
  let z : {p // p ∈ Finset.univ.biUnion P} :=
    ⟨p,Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,hp⟩⟩
  have hh : S.symm z = ⟨g,⟨p,hp⟩⟩ := by
    apply S.injective
    rw [S.apply_symm_apply]
    apply Subtype.ext
    rfl
  change e (S.symm z).1 (S.symm z).2 = e g ⟨p,hp⟩
  rw [hh]



/- Exact source owner: SourcePGlobalProductEquiv.lean; original line 9. -/
theorem source_original_P_global_factorization_out
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (e : (g : G) → {p // p ∈ P g} → ℕ)
    (p : ℕ) (hp : p ∉ Finset.univ.biUnion P) :
    (sourceOriginalPGlobalVectorProduct P e).factorization p = 0 := by
  unfold sourceOriginalPGlobalVectorProduct
  rw [Nat.factorization_prod (by
    intro g hg
    exact source_original_P_power_product_ne_zero
      (P g) (hPrime g) (e g))]
  simp only [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro g hg
  apply source_original_P_power_factorization_out
    (P g) (hPrime g) (e g) p
  intro hpg
  exact hp (Finset.mem_biUnion.mpr
    ⟨g,Finset.mem_univ _,hpg⟩)

/- Exact equality of NATURAL products: the global union-of-primes
exponent vector and the disjoint family of P-group exponent vectors
represent the same source prime-powered integer, including repeats. -/



/- Exact source owner: SourcePGlobalProductEquiv.lean; original line 33. -/
theorem source_original_P_global_vector_product_eq
    {G : Type} [Fintype G]
    (P : G → Finset ℕ)
    (hPrime : ∀ g p, p ∈ P g → p.Prime)
    (hDisj : ∀ g h p, p ∈ P g → p ∈ P h → g = h)
    (e : (g : G) → {p // p ∈ P g} → ℕ) :
    sourceOriginalPGlobalVectorProduct P e =
      sourceOriginalPPrimePowerProduct
        (Finset.univ.biUnion P)
        (sourceOriginalPDisjointExponentEquiv P hDisj e) := by
  classical
  let Pall := Finset.univ.biUnion P
  have hAll : ∀ p ∈ Pall, p.Prime := by
    intro p hp
    obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    exact hPrime g p hpg
  have hLne := source_original_P_global_product_ne_zero P hPrime e
  have hRne := source_original_P_power_product_ne_zero
    Pall hAll (sourceOriginalPDisjointExponentEquiv P hDisj e)
  apply Nat.eq_of_factorization_eq hLne hRne
  intro p
  by_cases hp : p ∈ Pall
  · obtain ⟨g,hg,hpg⟩ := Finset.mem_biUnion.mp hp
    have hL := source_original_P_global_factorization_at
      P hPrime hDisj e g p hpg
    have hR := source_original_P_power_factorization_at
      Pall hAll (sourceOriginalPDisjointExponentEquiv P hDisj e) p hp
    have hCoord :
      (sourceOriginalPDisjointExponentEquiv P hDisj e)
        (⟨p,hp⟩ : {p // p ∈ Pall}) = e g ⟨p,hpg⟩ := by
      simpa only [Pall] using
        (source_original_P_disjoint_exp_at P hDisj e g p hpg)
    exact hL.trans (hCoord.symm.trans hR.symm)
  · have hL := source_original_P_global_factorization_out
      P hPrime e p hp
    have hR := source_original_P_power_factorization_out
      Pall hAll (sourceOriginalPDisjointExponentEquiv P hDisj e)
      p hp
    exact hL.trans hR.symm



/- Exact source owner: SourcePPrimePowerFibres.lean; original line 96. -/
noncomputable def sourceOriginalPExponentVector
    (P : Finset ℕ) (u : ℕ) : {p // p ∈ P} → ℕ :=
  fun z => u.factorization z.val



/- Exact source owner: SourcePPrimePowerSupport.lean; original line 9. -/
theorem source_original_P_power_primeFactors_subset
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) :
    (sourceOriginalPPrimePowerProduct P e).primeFactors ⊆ P := by
  intro q hq
  by_contra hnot
  have hzero := source_original_P_power_factorization_out
    P hPrime e q hnot
  have hpositive := source_original_P_power_product_ne_zero P hPrime e
  have hqPrime := (Nat.mem_primeFactors.mp hq).1
  have hqDvd := (Nat.mem_primeFactors.mp hq).2.1
  have hval : 1 ≤ (sourceOriginalPPrimePowerProduct P e).factorization q :=
    (Nat.Prime.dvd_iff_one_le_factorization hqPrime hpositive).mp hqDvd
  omega

/- For an actual positive integer supported entirely on P,
the source P-part operator fixes it exactly. -/



/- Exact source owner: SourcePPrimePowerFibres.lean; original line 100. -/
theorem source_original_P_prime_part_eq_vector_product
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (u : ℕ) (hu : u ≠ 0) :
    sourceOriginalPPrimePart P u =
      sourceOriginalPPrimePowerProduct P (sourceOriginalPExponentVector P u) := by
  classical
  unfold sourceOriginalPPrimePart sourceOriginalPPrimePowerProduct
  unfold sourceOriginalPExponentVector
  have hattach : (∏ z : {p // p ∈ P},
      z.val ^ u.factorization z.val) =
      ∏ p ∈ P, p ^ u.factorization p := by
    simpa only [Finset.attach_eq_univ] using
      (Finset.prod_attach P (fun p => p ^ u.factorization p))
  rw [hattach]
  have hfilter : u.primeFactors ∩ P = P.filter
      (fun p => p ∈ u.primeFactors) := by
    ext p
    simp [and_comm]
  rw [hfilter, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hmem : p ∈ u.primeFactors
  · simp [hmem]
  · have hnotdvd : ¬p ∣ u := by
      intro hpdvd
      exact hmem ((Nat.mem_primeFactors).mpr
        ⟨hPrime p hp, hpdvd, hu⟩)
    have hv : u.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnotdvd
    simp [hmem,hv]



/- Exact source owner: SourcePPrimePowerSupport.lean; original line 26. -/
theorem source_original_P_prime_part_of_supported
    (P : Finset ℕ) (u : ℕ) (hu : u ≠ 0)
    (hSupported : u.primeFactors ⊆ P) :
    sourceOriginalPPrimePart P u = u := by
  unfold sourceOriginalPPrimePart
  rw [Finset.inter_eq_left.mpr hSupported]
  exact (Nat.prod_primeFactors_pow_factorization hu).symm

/- Every positive source integer supported on P is in the
prime-power exponent product image; this is a RIGHT inverse. -/



/- Exact source owner: SourcePPrimePowerSupport.lean; original line 36. -/
theorem source_original_P_power_vector_reconstructs
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (u : ℕ) (hu : u ≠ 0)
    (hSupported : u.primeFactors ⊆ P) :
    sourceOriginalPPrimePowerProduct P (sourceOriginalPExponentVector P u) = u := by
  rw [← source_original_P_prime_part_eq_vector_product
    P hPrime u hu]
  exact source_original_P_prime_part_of_supported P u hu hSupported

/- The exponent vector can be recovered from the actual natural
product. This is a LEFT inverse, not merely injectivity. -/



/- Exact source owner: SourcePPrimePowerSupport.lean; original line 47. -/
theorem source_original_P_power_vector_recovers
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime)
    (e : {p // p ∈ P} → ℕ) :
    sourceOriginalPExponentVector P
      (sourceOriginalPPrimePowerProduct P e) = e := by
  funext z
  change (sourceOriginalPPrimePowerProduct P e).factorization z.val = e z
  simpa only [Subtype.coe_eta] using
    (source_original_P_power_factorization_at
      P hPrime e z.val z.property)



/- Exact source owner: SourcePPrimePowerEquiv.lean; original line 15. -/
noncomputable def source_original_P_power_equiv
    (P : Finset ℕ) (hPrime : ∀ p ∈ P, p.Prime) :
    ({p // p ∈ P} → ℕ) ≃ sourceOriginalPSupported P where
  toFun e := ⟨sourceOriginalPPrimePowerProduct P e,
    source_original_P_power_product_ne_zero P hPrime e,
    source_original_P_power_primeFactors_subset P hPrime e⟩
  invFun n := sourceOriginalPExponentVector P n.val
  left_inv e := source_original_P_power_vector_recovers P hPrime e
  right_inv n := by
    apply Subtype.ext
    exact source_original_P_power_vector_reconstructs P hPrime
      n.val n.property.1 n.property.2



/- Exact source owner: SourceShiftTwoPGroupTiltedEuler.lean; original line 11. -/
noncomputable def sourceOriginalGroupTiltedEulerMass
    (P : Finset ℕ) (D : ℕ → ℝ) : ℝ :=
  (∏ p ∈ P, (1 + (1/2:ℝ)/(D p - 1))) *
    ((∑ p ∈ P, (D p-(1/2:ℝ))⁻¹) /
      (∑ p ∈ P, (p:ℝ)⁻¹))



/- Exact source owner: SourceShiftTwoPGroupTiltedEuler.lean; original line 17. -/
theorem source_group_tilted_Euler_factor_le
    (p : ℕ) (D : ℕ → ℝ) (hp : 6 ≤ p)
    (hD : (p:ℝ) ≤ 3*D p) :
    1+(1/2:ℝ)/(D p-1) ≤
      Real.exp (3 * (p:ℝ)⁻¹) := by
  have hpR : (6:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hd : (0:ℝ) < D p-1 := by nlinarith
  have hcomp : (1/2:ℝ)/(D p-1) ≤ 3/(p:ℝ) :=
    (div_le_div_iff₀ hd hp0).2 (by nlinarith)
  have he := Real.add_one_le_exp (3*(p:ℝ)⁻¹)
  have hAlgebra : 3/(p:ℝ) = 3*(p:ℝ)⁻¹ := by ring
  linarith



/- Exact source owner: SourceShiftTwoPGroupTiltedEuler.lean; original line 31. -/
theorem source_group_tilted_Euler_inverse_le
    (p : ℕ) (D : ℕ → ℝ) (hp : 6 ≤ p)
    (hD : (p:ℝ) ≤ 3*D p) :
    (D p-(1/2:ℝ))⁻¹ ≤ 6*(p:ℝ)⁻¹ := by
  have hpR : (6:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hd : (0:ℝ) < D p-(1/2:ℝ) := by nlinarith
  have h := (div_le_div_iff₀ hd hp0).2
    (show (1:ℝ)*(p:ℝ) ≤ (6:ℝ)*(D p-(1/2:ℝ))
      by nlinarith)
  simpa only [one_div, div_eq_mul_inv, one_mul] using h



/- Exact source owner: SourceShiftTwoPGroupTiltedEuler.lean; original line 42. -/
theorem source_group_tilted_Euler_mass_uniform
    (P : Finset ℕ) (D : ℕ → ℝ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h6 : ∀ p ∈ P, 6 ≤ p)
    (hD : ∀ p ∈ P, (p:ℝ) ≤ 3*D p)
    (hPn : P.Nonempty)
    (hV4 : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4) :
    sourceOriginalGroupTiltedEulerMass P D ≤
      6 * Real.exp 12 := by
  let V : ℝ := ∑ p ∈ P, (p:ℝ)⁻¹
  let S : ℝ := ∑ p ∈ P, (D p-(1/2:ℝ))⁻¹
  let F : ℝ := ∏ p ∈ P, (1+(1/2:ℝ)/(D p-1))
  have hVpos : 0 < V := by
    dsimp [V]
    apply Finset.sum_pos
    · intro p hp
      have hp6 := h6 p hp
      exact inv_pos.mpr (by exact_mod_cast
        (lt_of_lt_of_le (by norm_num : 0 < 6) hp6))
    · exact hPn
  have hSbound : S ≤ 6*V := by
    calc
      S ≤ ∑ p ∈ P, 6*(p:ℝ)⁻¹ :=
        Finset.sum_le_sum (fun p hp =>
          source_group_tilted_Euler_inverse_le p D (h6 p hp) (hD p hp))
      _ = 6*V := by rw [Finset.mul_sum]
  have hSpos : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro p hp
    have hpR : (6:ℝ) ≤ p := by exact_mod_cast h6 p hp
    have hd : 0 < D p-(1/2:ℝ) := by
      have := hD p hp
      nlinarith
    exact (inv_pos.mpr hd).le
  have hFnonneg : 0 ≤ F := by
    dsimp [F]
    apply Finset.prod_nonneg
    intro p hp
    have hpR : (6:ℝ) ≤ p := by exact_mod_cast h6 p hp
    have hd : 0 < D p-1 := by
      have := hD p hp
      nlinarith
    have hx : (0:ℝ) ≤ (1/2:ℝ)/(D p-1) :=
      div_nonneg (by norm_num) hd.le
    linarith
  have hFbound : F ≤ Real.exp 12 := by
    have hpF : F ≤ ∏ p ∈ P, Real.exp (3*(p:ℝ)⁻¹) :=
      Finset.prod_le_prod₀ (by
        intro p hp
        have hpR : (6:ℝ) ≤ p := by exact_mod_cast h6 p hp
        have hd : 0 < D p-1 := by
          have := hD p hp
          nlinarith
        have hx : (0:ℝ) ≤ (1/2:ℝ)/(D p-1) :=
          div_nonneg (by norm_num) hd.le
        linarith)
        (fun p hp => source_group_tilted_Euler_factor_le
          p D (h6 p hp) (hD p hp))
    have he : (∏ p ∈ P, Real.exp (3*(p:ℝ)⁻¹)) =
        Real.exp (3*V) := by
      dsimp [V]
      rw [Finset.mul_sum, Real.exp_sum]
    calc
      F ≤ ∏ p ∈ P, Real.exp (3*(p:ℝ)⁻¹) := hpF
      _ = Real.exp (3*V) := he
      _ ≤ Real.exp 12 :=
        Real.exp_le_exp.mpr (by nlinarith [hV4])
  have hSratio : S/V ≤ (6:ℝ) :=
    (div_le_iff₀ hVpos).2 (by simpa using hSbound)
  have hSratio0 : 0 ≤ S/V := div_nonneg hSpos hVpos.le
  unfold sourceOriginalGroupTiltedEulerMass
  change F*(S/V) ≤ 6*Real.exp 12
  have ha := mul_le_mul_of_nonneg_right hFbound hSratio0
  have hb := mul_le_mul_of_nonneg_left hSratio (Real.exp_nonneg 12)
  nlinarith



/- Exact source owner: SourceShiftTwoPGroupTiltedDelta.lean; original line 10. -/
theorem source_tilted_prime_power_compare
    (p : ℕ) (δ T : ℝ)
    (hp : 6 ≤ p) (hδ : 0 ≤ δ)
    (hLog : Real.log (p:ℝ) ≤ T)
    (hδT : δ*T ≤ 1) :
    (p:ℝ) ≤ 3 * (p:ℝ)^(1-δ) := by
  have hpR : (6:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hδlog : δ*Real.log (p:ℝ) ≤ 1 := by
    calc
      δ*Real.log (p:ℝ) ≤ δ*T :=
        mul_le_mul_of_nonneg_left hLog hδ
      _ ≤ 1 := hδT
  have hPow : (p:ℝ)^δ ≤ 3 := by
    rw [Real.rpow_def_of_pos hp0 δ]
    have hexp : Real.exp (Real.log (p:ℝ)*δ) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact hexp.trans Real.exp_one_lt_three.le
  have hPowPos : 0 < (p:ℝ)^δ := Real.rpow_pos_of_pos hp0 δ
  rw [Real.rpow_sub hp0, Real.rpow_one]
  have hh : (p:ℝ) ≤ 3 * (p:ℝ) / (p:ℝ)^δ := by
    apply (le_div_iff₀ hPowPos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hPow hp0.le]
  convert hh using 1 <;> ring



/- Exact source owner: SourceShiftTwoPGroupTiltedDelta.lean; original line 35. -/
theorem source_group_tilted_delta_Euler_mass_upper
    (P : Finset ℕ) (δ T : ℝ)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h6 : ∀ p ∈ P, 6 ≤ p)
    (hPn : P.Nonempty)
    (hV4 : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4)
    (hδ : 0 ≤ δ) (hδT : δ*T ≤ 1)
    (hLog : ∀ p ∈ P, Real.log (p:ℝ) ≤ T) :
    sourceOriginalGroupTiltedEulerMass P
       (fun p => (p:ℝ)^(1-δ)) ≤ 6*Real.exp 12 := by
  exact source_group_tilted_Euler_mass_uniform P
    (fun p => (p:ℝ)^(1-δ)) hPrime h6
    (fun p hp => source_tilted_prime_power_compare p δ T
      (h6 p hp) hδ (hLog p hp) hδT)
    hPn hV4

/- The actual source tilt exponent delta=L^(-2/5), not a separate
probability law. The exponent-range assumption is exactly the upper
boundary in the original P groups [L^(1/10),L^(2/5)] and
[L^(3/10),L^(2/5)]. -/



/- Exact source owner: SourceShiftTwoPGroupTiltedDelta.lean; original line 55. -/
theorem source_group_source_delta_two_fifths_Euler_upper
    (P : Finset ℕ) (L : ℝ) (hL : 0 < L)
    (hPrime : ∀ p ∈ P, p.Prime)
    (h6 : ∀ p ∈ P, 6 ≤ p)
    (hPn : P.Nonempty)
    (hV4 : (∑ p ∈ P, (p:ℝ)⁻¹) ≤ 4)
    (hLog : ∀ p ∈ P,
       Real.log (p:ℝ) ≤ L^(2/5:ℝ)) :
    sourceOriginalGroupTiltedEulerMass P
       (fun p => (p:ℝ)^(1-L^(-(2/5:ℝ)))) ≤
      6*Real.exp 12 := by
  have hT : 0 < L^(2/5:ℝ) :=
    Real.rpow_pos_of_pos hL _
  have hδ : 0 ≤ L^(-(2/5:ℝ)) := by
    exact (Real.rpow_pos_of_pos hL _).le
  have hProd : L^(-(2/5:ℝ)) * L^(2/5:ℝ) = 1 := by
    rw [Real.rpow_neg hL.le]
    exact inv_mul_cancel₀ hT.ne'
  exact source_group_tilted_delta_Euler_mass_upper P
    (L^(-(2/5:ℝ))) (L^(2/5:ℝ))
    hPrime h6 hPn hV4 hδ (le_of_eq hProd) hLog



/- Exact source owner: SourcePTiltedFiniteUpper.lean; original line 9. -/
noncomputable def sourceOriginalPTiltedSubtypeEnvelope
    (P : Finset ℕ) (D : ℕ → ℝ) : ℝ :=
  (∑ z : {p // p ∈ P},
    (D z.val-1)⁻¹ *
      (∏ w ∈ (Finset.univ : Finset {p // p ∈ P}).erase z,
        (1+(1/2:ℝ)/(D w.val-1)))) /
    (∑ p ∈ P, (p:ℝ)⁻¹)

/- Finite true tilted W1 exponent-cube harmonic mass is
bounded by the exact differentiated P-group Euler envelope. -/



/- Exact source owner: SourcePFiniteCubeTsum.lean; original line 10. -/
theorem source_original_P_exponents_cofinal
    (P : Finset ℕ)
    (s : Finset ({p // p ∈ P} → ℕ)) :
    ∃ K : ℕ,
      ∀ e ∈ s, ∀ z : {p // p ∈ P}, e z ≤ K := by
  classical
  let K : ℕ := s.sup (fun e =>
    (Finset.univ : Finset {p // p ∈ P}).sup (fun z => e z))
  refine ⟨K, ?_⟩
  intro e he z
  have hInner : e z ≤
      (Finset.univ : Finset {p // p ∈ P}).sup
        (fun w => e w) :=
    Finset.le_sup (Finset.mem_univ z)
  have hOuter :
      (Finset.univ : Finset {p // p ∈ P}).sup
        (fun w => e w) ≤ K :=
    Finset.le_sup he
  exact hInner.trans hOuter

/- Strictly positive reciprocal of actual P-prime-power products. -/



/- Exact source owner: SourcePFiniteCubeTsum.lean; original line 49. -/
theorem source_original_P_cube_summable_of_uniform_bound
    (P : Finset ℕ)
    (f : ({p // p ∈ P} → ℕ) → ℝ)
    (B : ℝ) (hf : ∀ e, 0 ≤ f e)
    (hCube : ∀ K : ℕ,
      (∑ e : {p // p ∈ P} → Fin (K+1),
        f (fun z => (e z).val)) ≤ B) :
    Summable f ∧ (∑' e, f e) ≤ B := by
  classical
  let C := {p // p ∈ P}
  have hFinite (s : Finset (C → ℕ)) :
      (∑ e ∈ s, f e) ≤ B := by
    obtain ⟨K,hK⟩ := source_original_P_exponents_cofinal P s
    let lift : (C → Fin (K+1)) → (C → ℕ) :=
      fun e z => (e z).val
    have hInject : Function.Injective lift := by
      intro a b hab
      funext z
      apply Fin.ext
      exact congrFun hab z
    have hs : s ⊆
        (Finset.univ : Finset (C → Fin (K+1))).image lift := by
      intro e he
      apply Finset.mem_image.mpr
      refine ⟨(fun z => (⟨e z, Nat.lt_succ_of_le (hK e he z)⟩ :
          Fin (K+1))), Finset.mem_univ _, ?_⟩
      funext z
      rfl
    calc
      (∑ e ∈ s, f e) ≤
          ∑ e ∈ (Finset.univ : Finset (C → Fin (K+1))).image lift,
            f e :=
        Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun e he hnot => hf e)
      _ = ∑ e : C → Fin (K+1), f (lift e) := by
        rw [Finset.sum_image (fun a ha b hb hab => hInject hab)]
      _ ≤ B := hCube K
  exact ⟨summable_of_sum_le hf hFinite,
    Real.tsum_le_of_sum_le hf hFinite⟩

/- ACTUAL full, unrestricted P group W1 series is summable and
bounded by the pre-existing source H_g Euler factor. The finite
cube proof has been lifted to all repeated prime powers. -/



/- Exact source owner: SourcePVectorMarkedMasks.lean; original line 19. -/
noncomputable def sourceOriginalPVecBaseFactor
    {P : Finset ℕ} (z : {p // p ∈ P}) (k : ℕ) : ℝ :=
  (if k = 0 then 1 else (1/2:ℝ)) * ((z.val:ℝ)⁻¹)^k


end Green64Analytic.SourceBlockSieve

end

end

/-! ## PrimePowerNative -/

section

/- Compatibility import for the rough-divisor production port.
The exact five source P-prime-power declarations already belong to the
accepted B635Mass002434. Reuse that unique native owner; the independent
B656 discovery build is preserved under B656_inputs/retired_duplicate_foundation.
There is no new mathematical declaration in this module. -/

end

