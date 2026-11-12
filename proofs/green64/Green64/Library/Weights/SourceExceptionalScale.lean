module

public import Green64.Library.Weights.SourceExceptionalAbsorption
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Weights / SourceExceptionalScale

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceExceptionalScale -/

section

open Filter Asymptotics Topology

namespace Green64Analytic.CorrelationMellin

/-- Every fixed polynomial in L is eventually dominated by exp(η L^a). -/
private theorem eventually_poly_le_exp_rpow
    (a d z η : ℝ) (ha : 0 < a) (hz : 0 ≤ z) (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop, z * L ^ d ≤ Real.exp (η * L ^ a) := by
  have hsmall := (isLittleO_rpow_exp_pos_mul_atTop
    (d / a) hη).comp_tendsto (tendsto_rpow_atTop ha)
  have hε : (0 : ℝ) < 1 / (z + 1) := by positivity
  filter_upwards [isLittleO_iff.mp hsmall hε,
    eventually_ge_atTop (1 : ℝ)] with L hL hOne
  have hpow : (L ^ a) ^ (d / a) = L ^ d := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ L)]
    congr 1
    field_simp
  have hpos : 0 ≤ L ^ d := Real.rpow_nonneg (by linarith) _
  have hsmall' : L ^ d ≤ (1 / (z + 1)) * Real.exp (η * L ^ a) := by
    simpa only [Function.comp_apply, hpow, Real.norm_eq_abs,
      abs_of_nonneg hpos, abs_of_pos (Real.exp_pos _)] using hL
  have hz1 : 0 < z + 1 := by linarith
  have hzdiv : z / (z + 1) ≤ 1 := by
    apply (div_le_iff₀ hz1).mpr
    linarith
  calc
    z * L ^ d ≤ z * ((1 / (z + 1)) * Real.exp (η * L ^ a)) :=
      mul_le_mul_of_nonneg_left hsmall' hz
    _ = (z / (z + 1)) * Real.exp (η * L ^ a) := by ring
    _ ≤ 1 * Real.exp (η * L ^ a) :=
      mul_le_mul_of_nonneg_right hzdiv (Real.exp_pos _).le
    _ = _ := one_mul _

/-- An exact natural logarithm bound, without assuming a real-floor identity. -/
private theorem nat_log_le_of_exp_bound
    (base Y : ℕ) (c T : ℝ)
    (hY : 1 ≤ Y) (hc : 0 < c)
    (hBase : Real.exp c ≤ (base : ℝ))
    (hUpper : (Y : ℝ) ≤ Real.exp T) :
    (Nat.log base Y : ℝ) * c ≤ T := by
  have hNat : base ^ (Nat.log base Y) ≤ Y :=
    Nat.pow_log_le_self base (Nat.ne_of_gt hY)
  have hBasePow : (Real.exp c) ^ (Nat.log base Y) ≤
      (base : ℝ) ^ (Nat.log base Y) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hBase _
  have hAll : Real.exp ((Nat.log base Y : ℝ) * c) ≤ Real.exp T := by
    calc
      _ = (Real.exp c) ^ (Nat.log base Y) := by
        convert Real.exp_nat_mul c (Nat.log base Y) using 1 <;> ring
      _ ≤ (base : ℝ) ^ (Nat.log base Y) := hBasePow
      _ ≤ (Y : ℝ) := by exact_mod_cast hNat
      _ ≤ Real.exp T := hUpper
  exact (Real.exp_le_exp).mp hAll

/-- Prime-moment and dyadic logarithmic orders are at most linear
in L under the original source exponential prime and Y scales. -/
theorem source_moment_orders_coarse_bound
    (P Y : ℕ) (L a : ℝ)
    (hY : 1 ≤ Y) (hL : 1 ≤ L) (ha : 0 ≤ a)
    (hPmin : Real.exp (L ^ a) ≤ (2 * P : ℕ))
    (hYmax : (Y : ℝ) ≤ Real.exp (2 * L)) :
    (sourcePrimeMomentOrder P Y : ℝ) ≤ 2 * L ∧
    (((Nat.log2 Y + 1 : ℕ) : ℝ)) ≤ 4 * L + 1 := by
  have hpow : 1 ≤ L ^ a := Real.one_le_rpow hL ha
  have hbase : Real.exp (1 : ℝ) ≤ (2 * P : ℕ) :=
    (Real.exp_le_exp.mpr hpow).trans hPmin
  have hj : (sourcePrimeMomentOrder P Y : ℝ) ≤ 2 * L := by
    simpa only [sourcePrimeMomentOrder, mul_one] using
      nat_log_le_of_exp_bound (2 * P) Y 1 (2 * L)
        hY one_pos hbase hYmax
  have htwo : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    calc
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by
        have := Real.log_two_gt_d9
        linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have hk := nat_log_le_of_exp_bound 2 Y (1 / 2) (2 * L)
    hY (by norm_num) (by norm_num at htwo ⊢; exact htwo) hYmax
  constructor
  · exact hj
  · rw [Nat.log2_eq_log_two]
    push_cast
    linarith

/-- An exact finite factorial moment estimate. It uses genuine
source j₀ power support and an independent polynomial-scale bound,
rather than an assumed exceptional-count saving. -/
theorem source_factorial_moment_le_power
    (P Y j : ℕ) (H ε : ℝ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y)
    (hH : 0 ≤ H) (hε : 0 ≤ ε)
    (hPow : (2 * P)^j ≤ Y)
    (hScale : (j : ℝ) * H ≤ ((2 * P : ℕ) : ℝ) ^ ε) :
    (j.factorial : ℝ) * H^j ≤ (Y : ℝ)^ε := by
  have hf : (j.factorial : ℝ) ≤ (j : ℝ)^j := by
    exact_mod_cast Nat.factorial_le_pow j
  have hRealPow : (((2 * P : ℕ) : ℝ)^j) ≤ (Y : ℝ) := by
    exact_mod_cast hPow
  have hBase : 0 ≤ (((2 * P : ℕ) : ℝ)) := by positivity
  calc
    _ ≤ (j : ℝ)^j * H^j :=
      mul_le_mul_of_nonneg_right hf (pow_nonneg hH j)
    _ = ((j : ℝ) * H)^j := (mul_pow ..).symm
    _ ≤ (((2 * P : ℕ) : ℝ)^ε)^j :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hH) hScale j
    _ = (((2 * P : ℕ) : ℝ)^j)^ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBase,
        ← Real.rpow_natCast, ← Real.rpow_mul hBase]
      congr 1
      ring
    _ ≤ (Y : ℝ)^ε := by
      exact Real.rpow_le_rpow (pow_nonneg hBase j) hRealPow hε

/-- Finite self-term absorption once the actual moment and range
inequalities are numerically established. -/
private theorem absorb_numeric_moment
    (K Y B Bpow Q M D : ℝ)
    (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hB : 0 < B) (hBpow : 0 < Bpow)
    (hD : 0 ≤ D)
    (hRange : Y ≤ B * Bpow)
    (hMoment : M * Bpow ≤ Q * D)
    (hSaving : 896 * K * B * Q ≤ Real.sqrt Y) :
    896 * K * Real.sqrt Y * M ≤ D := by
  have hScaled : 896 * K * Real.sqrt Y * Q ≤ Bpow := by
    apply (mul_le_mul_iff_of_pos_left hB).mp
    calc
      B * (896 * K * Real.sqrt Y * Q) =
          (896 * K * B * Q) * Real.sqrt Y := by ring
      _ ≤ Real.sqrt Y * Real.sqrt Y :=
        mul_le_mul_of_nonneg_right hSaving (Real.sqrt_nonneg _)
      _ = Y := Real.mul_self_sqrt hY
      _ ≤ B * Bpow := hRange
  have hFinal : (896*K*Real.sqrt Y*M)*Bpow ≤ D*Bpow := by
    calc
      _ = (896*K*Real.sqrt Y)*(M*Bpow) := by ring
      _ ≤ (896*K*Real.sqrt Y)*(Q*D) :=
        mul_le_mul_of_nonneg_left hMoment
          (by positivity)
      _ = (896*K*Real.sqrt Y*Q)*D := by ring
      _ ≤ Bpow*D :=
        mul_le_mul_of_nonneg_right hScaled hD
      _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_right hBpow).mp hFinal

/-- Source large-prime upper scale exp(L^b), b<1, is negligible
compared with exp(η L), including fixed polynomial factors. -/
private theorem eventually_poly_exp_rpow_le_exp_linear
    (b d z η : ℝ) (hb : b < 1)
    (hz : 0 ≤ z) (hη : 0 < η) :
    ∀ᶠ L : ℝ in atTop,
      z * L ^ d * Real.exp (L ^ b) ≤ Real.exp (η * L) := by
  have hhalf : 0 < η / 2 := by linarith
  have hPow : ∀ᶠ L : ℝ in atTop, L ^ b ≤ (η/2)*L := by
    have ht : Tendsto (fun L : ℝ => L ^ (-(1 - b))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith : 0 < 1 - b)
    filter_upwards [ht.eventually (Iio_mem_nhds hhalf),
      eventually_ge_atTop (1 : ℝ)] with L hsmall hL
    have hpow' : L ^ b = L ^ (-(1-b)) * L := by
      calc
        L ^ b = L ^ (-(1-b)+1) := by congr 1; ring
        _ = L ^ (-(1-b)) * L := by
          rw [Real.rpow_add (by linarith : 0 < L), Real.rpow_one]
    rw [hpow']
    exact mul_le_mul_of_nonneg_right hsmall.le (by linarith)
  have hPoly := eventually_poly_le_exp_rpow 1 d z (η/2)
      one_pos hz hhalf
  filter_upwards [hPow, hPoly, eventually_ge_atTop (1 : ℝ)] with L hpow hpoly hL
  rw [Real.rpow_one] at hpoly
  calc
    z*L^d * Real.exp (L^b) ≤
        Real.exp ((η/2)*L) * Real.exp (L^b) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ ≤ Real.exp ((η/2)*L) * Real.exp ((η/2)*L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) (Real.exp_pos _).le
    _ = Real.exp (η * L) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The exact power cancellation behind the prime-polynomial moment. -/
private theorem scaled_moment_identity
    (B S δ : ℝ) (j : ℕ) (hδ : 0 < δ) :
    S^j * B^j = (B*S/δ^2)^j * δ^(2*j) := by
  have hδsq : δ^2 ≠ 0 := pow_ne_zero _ hδ.ne'
  have hPow : δ^(2*j) = (δ^2)^j := by
    exact pow_mul δ 2 j
  rw [hPow, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hδsq)]
  ring

/-- Combining the exact natural moment order, factorial moment, and
the quantitative numerical budget gives an unconditional self-term
absorption *from those two numerical bounds*. -/
theorem source_absorb_from_quantitative_budgets
    (P Y : ℕ) (C δ Q : ℝ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y) (hδ : 0 < δ)
    (hQ : (Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
      (4*C^2/δ^2)^(sourcePrimeMomentOrder P Y) ≤ Q)
    (hSaving : 896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*Q ≤
      Real.sqrt (Y:ℝ)) :
    896*((Nat.log2 Y+1:ℕ):ℝ)*Real.sqrt (Y:ℝ) *
      ((Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
        (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y)) ≤
      δ^(2*sourcePrimeMomentOrder P Y) := by
  let j := sourcePrimeMomentOrder P Y
  let B : ℝ := (2*P:ℕ)
  let S : ℝ := 2*C^2/(P:ℝ)
  let H : ℝ := 4*C^2/δ^2
  let D : ℝ := δ^(2*j)
  let M : ℝ := (j.factorial:ℝ)*S^j
  have hPpos : (0:ℝ) < P := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hP)
  have hB : 0 < B := by dsimp [B]; positivity
  have hBPow : 0 < B^j := pow_pos hB _
  have hYnonneg : 0 ≤ (Y:ℝ) := by positivity

  have hBS : B*S = 4*C^2 := by
    dsimp [B, S]
    push_cast
    field_simp
    ring
  have hHD : S^j*B^j = H^j*D := by
    have hH : H = B*S/δ^2 := by dsimp [H]; rw [hBS]
    rw [hH]
    exact scaled_moment_identity B S δ j hδ
  have hMoment : M*B^j ≤ Q*D := by
    have hMEq : M*B^j = ((j.factorial:ℝ)*H^j)*D := by
      dsimp [M]
      calc
        _ = (j.factorial:ℝ)*(S^j*B^j) := by ring
        _ = (j.factorial:ℝ)*(H^j*D) := by rw [hHD]
        _ = _ := by ring
    rw [hMEq]
    exact mul_le_mul_of_nonneg_right (by simpa only [j,H] using hQ)
      (pow_nonneg hδ.le _)
  have hRange : (Y:ℝ) ≤ B*B^j := by
    have hNat := (source_prime_moment_order_power_bounds P Y hP hY).2
    have hReal : (Y:ℝ) ≤ (((2*P:ℕ):ℝ)^(j+1)) := by
      have : Y ≤ (2*P)^(j+1) := hNat.le
      exact_mod_cast this
    simpa only [B, j, pow_succ, mul_comm] using hReal
  have hAbs := absorb_numeric_moment
    (((Nat.log2 Y+1:ℕ):ℝ)) (Y:ℝ) B (B^j) Q M D
    (by positivity) hYnonneg hB hBPow (by positivity)
    hRange hMoment (by simpa only [B] using hSaving)
  simpa only [j, S, D, M] using hAbs

/-- The source factorial moment is uniformly Y^ε, for every fixed
ε>0, in the exact P, Y logarithmic regimes. No saving hypothesis
is imposed on any prime coefficient. -/
theorem eventually_source_factorial_moment
    (a A C ε : ℝ)
    (ha : 0 < a) (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L ^ a) ≤ ((2*P:ℕ):ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      (Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
        (4*C^2*L^(2*A))^(sourcePrimeMomentOrder P Y) ≤ (Y:ℝ)^ε := by
  have hPoly := eventually_poly_le_exp_rpow
      a (2*A+1) (8*C^2) ε ha (by positivity) hε
  filter_upwards [hPoly, eventually_ge_atTop (1:ℝ)] with
      L hpoly hL P Y hP hY hPmin hYmax
  let j := sourcePrimeMomentOrder P Y
  have hJ := (source_moment_orders_coarse_bound
    P Y L a hY hL ha.le hPmin hYmax).1
  have hPow := (source_prime_moment_order_power_bounds P Y hP hY).1
  have hH : 0 ≤ 4*C^2*L^(2*A) := by positivity
  have hScale : (j:ℝ) * (4*C^2*L^(2*A)) ≤
      ((2*P:ℕ):ℝ)^ε := by
    calc
      _ ≤ (2*L)*(4*C^2*L^(2*A)) :=
        mul_le_mul_of_nonneg_right hJ hH
      _ = (8*C^2)*L^(2*A+1) := by
        rw [Real.rpow_add (by linarith : 0 < L), Real.rpow_one]
        ring
      _ ≤ Real.exp (ε*L^a) := hpoly
      _ = (Real.exp (L^a))^ε := by
        rw [← Real.exp_mul]
        congr 1
        ring
      _ ≤ ((2*P:ℕ):ℝ)^ε :=
        Real.rpow_le_rpow (Real.exp_pos _).le hPmin hε.le
  exact source_factorial_moment_le_power P Y j
    (4*C^2*L^(2*A)) ε hP hY hH hε.le hPow hScale

/-- The exact dyadic count and upper source prime scale are Y^o(1)
uniformly in P and Y, with all outer constants fixed first. -/
theorem eventually_source_exceptional_prefactor
    (a b μ : ℝ) (ha : 0 < a) (hb : b < 1) (hμ : 0 < μ) :
    ∀ᶠ L : ℝ in atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L ^ a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L ^ b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ) ≤ (Y:ℝ)^μ := by
  have hPoly := eventually_poly_exp_rpow_le_exp_linear
    b 1 (8960:ℝ) (μ/2) hb (by norm_num) (by linarith)
  filter_upwards [hPoly, eventually_ge_atTop (1:ℝ)] with
      L hpoly hL P Y hP hY hPmin hPmax hYmin hYmax
  have hK := (source_moment_orders_coarse_bound
    P Y L a hY hL ha.le hPmin hYmax).2
  have hK5 : (((Nat.log2 Y+1:ℕ):ℝ)) ≤ 5*L := by linarith
  have hB : (((2*P:ℕ):ℝ)) ≤ 2*Real.exp (L^b) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (mul_le_mul_of_nonneg_left hPmax (by norm_num : (0:ℝ)≤2))
  calc
    896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ) ≤
        896*(5*L)*(2*Real.exp (L^b)) := by
      gcongr
    _ = (8960:ℝ)*L*Real.exp (L^b) := by ring
    _ ≤ Real.exp ((μ/2)*L) := by simpa only [Real.rpow_one] using hpoly
    _ = (Real.exp (L/2))^μ := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ (Y:ℝ)^μ :=
      Real.rpow_le_rpow (Real.exp_pos _).le hYmin hμ.le

/-- Exactly match the source threshold δ=L^(-A) and the denominator
of the factorial moment. -/
private theorem source_threshold_moment_scale
    (L A C : ℝ) (hL : 0 < L) :
    4*C^2/(L^(-A))^2 = 4*C^2*L^(2*A) := by
  have hPow : (L^A)^2 = L^(2*A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [Real.rpow_neg hL.le, inv_pow, hPow]
  rw [div_inv_eq_mul]

/-- Uniform source-scale elimination of hAbsorb: fixed a,b,A,C
are quantified before the large-L threshold, and P,Y are arbitrary
admissible integers afterwards. -/
theorem eventually_source_exceptional_absorption
    (a b A C : ℝ) (ha : 0 < a) (hb : b < 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L ^ a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L ^ b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      896*((Nat.log2 Y+1:ℕ):ℝ)*Real.sqrt (Y:ℝ) *
        ((Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
           (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y)) ≤
        (L^(-A))^(2*sourcePrimeMomentOrder P Y) := by
  have hMom := eventually_source_factorial_moment a A C (1/8)
    ha hA hC (by norm_num)
  have hPre := eventually_source_exceptional_prefactor a b (1/4)
    ha hb (by norm_num)
  filter_upwards [hMom, hPre, eventually_ge_atTop (1:ℝ)] with
    L hMomL hPreL hL P Y hP hY hPmin hPmax hYmin hYmax
  have hY1 : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  let j := sourcePrimeMomentOrder P Y
  let Q : ℝ := (j.factorial:ℝ)*(4*C^2/(L^(-A))^2)^j
  have hQ : Q ≤ (Y:ℝ)^(1/8:ℝ) := by
    dsimp [Q]
    rw [source_threshold_moment_scale L A C (by linarith : 0 < L)]
    exact hMomL P Y hP hY hPmin hYmax
  have hPref : 896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ) ≤
      (Y:ℝ)^(1/4:ℝ) :=
    hPreL P Y hP hY hPmin hPmax hYmin hYmax
  have hKpos : 0 ≤ (896:ℝ)*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ) :=
    by positivity

  have hSaving : 896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*Q ≤
      Real.sqrt (Y:ℝ) := by
    calc
      _ ≤ (896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)) *
          ((Y:ℝ)^(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_left hQ hKpos
      _ ≤ ((Y:ℝ)^(1/4:ℝ))*((Y:ℝ)^(1/8:ℝ)) :=
        mul_le_mul_of_nonneg_right hPref (Real.rpow_nonneg (by positivity) _)
      _ = (Y:ℝ)^(3/8:ℝ) := by
        rw [← Real.rpow_add (by linarith : (0:ℝ) < Y)]
        congr 1
        norm_num
      _ ≤ (Y:ℝ)^(1/2:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
      _ = Real.sqrt (Y:ℝ) := (Real.sqrt_eq_rpow _).symm
  exact source_absorb_from_quantitative_budgets P Y C (L^(-A)) Q
    hP hY (Real.rpow_pos_of_pos (by linarith : 0 < L) _)
    (by simpa only [Q,j] using le_refl Q) hSaving

/-- The harmless logarithmic prefactor is at most 4L, using only
the original Y≤exp(2L) source window. -/
private theorem source_logarithmic_prefactor
    (Y : ℕ) (L : ℝ)
    (hY : 1 ≤ Y) (hL : 1 ≤ L)
    (hYmax : (Y:ℝ) ≤ Real.exp (2*L)) :
    1 + Real.log (2*(Y:ℝ)) ≤ 4*L := by
  have hYpos : (0:ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hLog := (Real.log_le_iff_le_exp hYpos).mpr hYmax
  have hLogTwo : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hYpos.ne']
  linarith

/-- Including the original (1+log(2Y)) time factor still produces
arbitrarily small Y-exponent, uniformly after the fixed constants. -/
theorem eventually_source_total_exceptional_prefactor
    (a b μ : ℝ) (ha : 0 < a) (hb : b < 1) (hμ : 0 < μ) :
    ∀ᶠ L : ℝ in atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L ^ a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L ^ b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
        (1+Real.log (2*(Y:ℝ))) ≤ (Y:ℝ)^μ := by
  have hPoly := eventually_poly_exp_rpow_le_exp_linear
    b 2 (35840:ℝ) (μ/2) hb (by norm_num) (by linarith)
  filter_upwards [hPoly, eventually_ge_atTop (1:ℝ)] with
    L hpoly hL P Y hP hY hPmin hPmax hYmin hYmax
  have hK := (source_moment_orders_coarse_bound
    P Y L a hY hL ha.le hPmin hYmax).2
  have hK5 : (((Nat.log2 Y+1:ℕ):ℝ)) ≤ 5*L := by linarith
  have hB : (((2*P:ℕ):ℝ)) ≤ 2*Real.exp (L^b) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (mul_le_mul_of_nonneg_left hPmax (by norm_num : (0:ℝ)≤2))
  have hR := source_logarithmic_prefactor Y L hY hL hYmax
  have hRpos : 0 ≤ 1+Real.log (2*(Y:ℝ)) := by
    have hYreal : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
    have hLog : 0 ≤ Real.log (2*(Y:ℝ)) :=
      Real.log_nonneg (by linarith)
    linarith
  calc
    896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
      (1+Real.log (2*(Y:ℝ))) ≤
        896*(5*L)*(2*Real.exp (L^b))*(4*L) := by
      gcongr
    _ = (35840:ℝ)*L^2*Real.exp (L^b) := by ring
    _ ≤ Real.exp ((μ/2)*L) := by simpa only [Real.rpow_ofNat] using hpoly
    _ = (Real.exp (L/2))^μ := by
      rw [← Real.exp_mul]
      congr 1
      ring
    _ ≤ (Y:ℝ)^μ :=
      Real.rpow_le_rpow (Real.exp_pos _).le hYmin hμ.le

/-- Exact moment identity with P, C and δ, not just equality of
coefficient L² norms. -/
private theorem source_prime_moment_power_identity
    (P j : ℕ) (C δ : ℝ) (hP : 1 ≤ P) (hδ : 0 < δ) :
    (j.factorial:ℝ)*(2*C^2/(P:ℝ))^j *
      (((2*P:ℕ):ℝ)^j) =
    (j.factorial:ℝ)*(4*C^2/δ^2)^j*δ^(2*j) := by
  have hPpos : (0:ℝ) < P := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hP)
  have hBS : (((2*P:ℕ):ℝ))*(2*C^2/(P:ℝ)) = 4*C^2 := by
    push_cast
    field_simp
    ring
  have hScaled := scaled_moment_identity
    (((2*P:ℕ):ℝ)) (2*C^2/(P:ℝ)) δ j hδ
  rw [hBS] at hScaled
  calc
    _ = (j.factorial:ℝ)*
        ((2*C^2/(P:ℝ))^j*(((2*P:ℕ):ℝ)^j)) := by ring
    _ = (j.factorial:ℝ)*
        ((4*C^2/δ^2)^j*δ^(2*j)) := by rw [hScaled]
    _ = _ := by ring

/-- The bound for Y times the original moment divided by δ^(2j):
sourcePrimeMomentOrder, its upper power inequality and the literal
factor normalization remain present. -/
theorem source_exceptional_moment_ratio
    (P Y : ℕ) (C δ Q : ℝ)
    (hP : 1 ≤ P) (hY : 1 ≤ Y) (hδ : 0 < δ)
    (hQ : (Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
      (4*C^2/δ^2)^(sourcePrimeMomentOrder P Y) ≤ Q) :
    ((Y:ℝ) * ((Nat.factorial (sourcePrimeMomentOrder P Y):ℝ) *
      (2*C^2/(P:ℝ))^(sourcePrimeMomentOrder P Y))) /
       δ^(2*sourcePrimeMomentOrder P Y) ≤ ((2*P:ℕ):ℝ)*Q := by
  let j := sourcePrimeMomentOrder P Y
  let B : ℝ := (2*P:ℕ)
  let M : ℝ := (j.factorial:ℝ)*(2*C^2/(P:ℝ))^j
  let D : ℝ := δ^(2*j)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 < D := pow_pos hδ _
  have hM : 0 ≤ M := by dsimp [M]; positivity

  have hYBound : (Y:ℝ) ≤ B*B^j := by
    have hn := (source_prime_moment_order_power_bounds P Y hP hY).2.le
    have hnr : (Y:ℝ) ≤ (((2*P:ℕ):ℝ)^(j+1)) := by
      exact_mod_cast hn
    simpa only [B,j,pow_succ,mul_comm] using hnr
  have hMoment : M*B^j ≤ Q*D := by
    have hid := source_prime_moment_power_identity P j C δ hP hδ
    have hMidentity : M*B^j =
        ((j.factorial:ℝ)*(4*C^2/δ^2)^j)*D := by
      simpa only [M,B,D] using hid
    rw [hMidentity]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [j] using hQ) hD.le
  have hProduct : (Y:ℝ)*M ≤ (B*Q)*D := by
    calc
      _ ≤ (B*B^j)*M := mul_le_mul_of_nonneg_right hYBound hM
      _ = B*(M*B^j) := by ring
      _ ≤ B*(Q*D) := mul_le_mul_of_nonneg_left hMoment hB
      _ = _ := by ring
  exact (div_le_iff₀ hD).mpr (by simpa only [j,B,M,D] using hProduct)

/-- True source-scale uniform exceptional count. Fixed a,b,A,C and
arbitrarily small ε are chosen BEFORE L; after the threshold, all
admissible P,Y, coefficients and separated exceptional points are
uniform. In particular, no hAbsorb or assumed saving occurs in
this statement. -/
theorem eventually_source_exceptional_count_uniform
    (a b A C ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ (P Y : ℕ),
      1 ≤ P → 1 ≤ Y →
      Real.exp (L ^ a) ≤ ((2*P:ℕ):ℝ) →
      (P:ℝ) ≤ Real.exp (L ^ b) →
      Real.exp (L/2) ≤ (Y:ℝ) →
      (Y:ℝ) ≤ Real.exp (2*L) →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (times : ι → ℝ) (s : Finset ℕ)
      (hprime : ∀ p ∈ s, Nat.Prime p)
      (hSupport : s ⊆ Finset.Icc P (2*P))
      (coeff : ℕ → ℂ) (hc : ∀ p ∈ s, ‖coeff p‖ ≤ C)
      (hRange : ∀ i, |times i| ≤ (Y:ℝ))
      (hSep : ∀ i j, i ≠ j → 1 ≤ |times i-times j|)
      (hlarge : ∀ i : ι,
        L^(-A) ≤ ‖∑ p : {p : ℕ // p ∈ s},
          (coeff p.val * ((p.val:ℂ)⁻¹)) * sourcePhase p.val (times i)‖),
      (Fintype.card ι : ℝ) ≤ (Y:ℝ)^ε := by
  have hAbs := eventually_source_exceptional_absorption
    a b A C ha hb hA hC
  have hMom := eventually_source_factorial_moment
    a A C (ε/2) ha hA hC (by linarith)
  have hPref := eventually_source_total_exceptional_prefactor
    a b (ε/2) ha hb (by linarith)
  filter_upwards [hAbs, hMom, hPref, eventually_ge_atTop (1:ℝ)] with
    L hAbsL hMomL hPrefL hL P Y hP hY hPmin hPmax hYmin hYmax
      ι _ _ times s hprime hSupport coeff hc hRange hSep hlarge
  let j := sourcePrimeMomentOrder P Y
  let δ : ℝ := L^(-A)
  let Q : ℝ := (j.factorial:ℝ)*(4*C^2/δ^2)^j
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by linarith) _
  have hYpos : (0:ℝ) < (Y:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hAbsLocal := hAbsL P Y hP hY hPmin hPmax hYmin hYmax

  have hQLocal : Q ≤ (Y:ℝ)^(ε/2) := by
    dsimp [Q, δ]
    rw [source_threshold_moment_scale L A C (by linarith : 0 < L)]
    exact hMomL P Y hP hY hPmin hYmax
  have hPrefLocal :
      896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
        (1+Real.log (2*(Y:ℝ))) ≤ (Y:ℝ)^(ε/2) :=
    hPrefL P Y hP hY hPmin hPmax hYmin hYmax
  have hRpos : 0 ≤ 1+Real.log (2*(Y:ℝ)) := by
    have hR0 : 0 ≤ Real.log (2*(Y:ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*Y by omega))
    linarith
  have hPrefNonneg :
      0 ≤ 896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
        (1+Real.log (2*(Y:ℝ))) := by positivity
  have hFullBudget :
      896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
        (1+Real.log (2*(Y:ℝ)))*Q ≤ (Y:ℝ)^ε := by
    calc
      _ ≤ (896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
          (1+Real.log (2*(Y:ℝ))))*((Y:ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_left hQLocal hPrefNonneg
      _ ≤ ((Y:ℝ)^(ε/2))*((Y:ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_right hPrefLocal (Real.rpow_nonneg hYpos.le _)
      _ = (Y:ℝ)^ε := by
        rw [← Real.rpow_add hYpos]
        congr 1
        ring
  have hCount := source_exceptional_count_absorbed
    times s P Y C δ hP hY hprime hSupport hC hδ coeff hc
      hRange hSep hlarge hAbsLocal
  have hRatio := source_exceptional_moment_ratio
    P Y C δ Q hP hY hδ
      (by simpa only [j,Q] using le_refl Q)

  have hKpos : 0 ≤ 896*((Nat.log2 Y+1:ℕ):ℝ)*
      (1+Real.log (2*(Y:ℝ))) := by positivity
  calc
    (Fintype.card ι : ℝ) ≤
      (896*((Nat.log2 Y+1:ℕ):ℝ)*(Y:ℝ)*
        (1+Real.log (2*(Y:ℝ))) *
        ((j.factorial:ℝ)*(2*C^2/(P:ℝ))^j)) / δ^(2*j) := by
      simpa only [j] using hCount
    _ = (896*((Nat.log2 Y+1:ℕ):ℝ)*
        (1+Real.log (2*(Y:ℝ))))*
      (((Y:ℝ)*((j.factorial:ℝ)*(2*C^2/(P:ℝ))^j))/δ^(2*j)) := by
      ring
    _ ≤ (896*((Nat.log2 Y+1:ℕ):ℝ)*
        (1+Real.log (2*(Y:ℝ)))) * (((2*P:ℕ):ℝ)*Q) :=
      mul_le_mul_of_nonneg_left (by simpa only [j] using hRatio) hKpos
    _ = 896*((Nat.log2 Y+1:ℕ):ℝ)*((2*P:ℕ):ℝ)*
      (1+Real.log (2*(Y:ℝ)))*Q := by ring
    _ ≤ (Y:ℝ)^ε := hFullBudget
end Green64Analytic.CorrelationMellin

end

