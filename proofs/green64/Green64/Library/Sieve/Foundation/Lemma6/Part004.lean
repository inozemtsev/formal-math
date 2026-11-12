module

public import Green64.Library.ChenTheorem.Lemma6.Coefficients
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Data.Finset.Sort
public import Green64.Library.ChenTheorem.SieveLemmas
public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Green64.Library.Sieve.Foundation.Lemma6.Part001

@[expose] public section

/-!
# Sieve / Foundation / Lemma6 / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma6.ExceptionalWeight -/

section

/-
# The squarefree exceptional weight in equation (18)

Chen absorbs `3 ^ ν(d)` into the dyadic factor `I_{l,x}`.  The key estimate
is obtained here without a prime number theorem: ordering the distinct prime
factors gives `ν(d)! ≤ d`, and Stirling's lower bound then gives the stronger
eventual estimate `ν(d) ≤ 2 log d / log log d`.
-/

open scoped Classical

namespace Chen

/-- The product of `k` distinct positive natural numbers is at least `k!`. -/
theorem factorial_card_le_prod_of_pos (s : Finset ℕ)
    (hs : ∀ n ∈ s, 1 ≤ n) : Nat.factorial s.card ≤ ∏ n ∈ s, n := by
  let e : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have hepos (i : Fin s.card) : 1 ≤ e i :=
    hs (e i) (s.orderEmbOfFin_mem rfl i)
  have hei (i : Fin s.card) : i.1 + 1 ≤ e i := by
    have hindex : ∀ n, (hn : n < s.card) →
        n + 1 ≤ e ⟨n, hn⟩ := by
      intro n
      induction n with
      | zero =>
          intro hn
          simpa using hepos ⟨0, hn⟩
      | succ n ih =>
          intro hn
          have hn' : n < s.card := (Nat.lt_succ_self n).trans hn
          have hprev := ih hn'
          have hlt : e ⟨n, hn'⟩ < e ⟨n + 1, hn⟩ :=
            e.strictMono (by simp)
          omega
    exact hindex i.1 i.2
  have hprod : (∏ i : Fin s.card, (i.1 + 1)) ≤ ∏ i : Fin s.card, e i := by
    apply Finset.prod_le_prod
    intro i _
    exact hei i
  calc
    Nat.factorial s.card = ∏ i ∈ Finset.range s.card, (i + 1) :=
      Finset.prod_range_add_one_eq_factorial _ |>.symm
    _ = ∏ i : Fin s.card, (i.1 + 1) :=
      (Fin.prod_univ_eq_prod_range (fun i : ℕ => i + 1) s.card).symm
    _ ≤ ∏ i : Fin s.card, e i := hprod
    _ = ∏ n ∈ s, n := by
      calc
        ∏ i : Fin s.card, e i = ∏ n : s, n.1 :=
          Fintype.prod_equiv (s.orderIsoOfFin rfl).toEquiv
            (fun i : Fin s.card => e i) (fun n : s => n.1) (fun _ => rfl)
        _ = ∏ n ∈ s, n := by
          rw [← s.attach_eq_univ]
          exact Finset.prod_attach s (fun n : ℕ => n)

/-- For squarefree `d`, the factorial of the number of prime factors is at
most `d`. -/
theorem factorial_primeFactors_card_le {d : ℕ} (hd : Squarefree d) :
    Nat.factorial d.primeFactors.card ≤ d := by
  calc
    Nat.factorial d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p :=
      factorial_card_le_prod_of_pos d.primeFactors
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le)
    _ = d := Nat.prod_primeFactors_of_squarefree hd

/-- A concrete large-`d` form of the standard estimate
`ν(d) ≪ log d / log log d`.  The constant `2` is stronger than needed for
equation (18). -/
theorem primeFactors_card_le_two_log_div_loglog
    {d : ℕ} (hd : Squarefree d) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    (d.primeFactors.card : ℝ) ≤
      2 * Real.log d / Real.log (Real.log d) := by
  let k : ℕ := d.primeFactors.card
  let t : ℝ := Real.log d
  let u : ℝ := Real.log t
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have ht : 0 < t := by
    dsimp only [t]
    exact Real.log_pos hdR
  have hu : 0 < u := by dsimp only [u, t]; linarith
  have hk : k ≠ 0 := by
    dsimp only [k]
    rw [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
    intro hempty
    have := Nat.primeFactors_eq_empty.mp hempty
    omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hfacNat : Nat.factorial k ≤ d := by
    simpa only [k] using factorial_primeFactors_card_le hd
  have hlogfac : Real.log (Nat.factorial k : ℝ) ≤ t := by
    dsimp only [t]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hfacNat)
  have hstirling := Stirling.le_log_factorial_stirling hk
  have hbase : (k : ℝ) * (Real.log k - 1) ≤ t := by
    calc
      (k : ℝ) * (Real.log k - 1) ≤
          (k : ℝ) * Real.log k - k + Real.log k / 2 +
            Real.log (2 * Real.pi) / 2 := by
        have hlogk : 0 ≤ Real.log (k : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk))
        have hlogpi : 0 ≤ Real.log (2 * Real.pi) :=
          Real.log_nonneg (by nlinarith [Real.pi_gt_three])
        linarith
      _ ≤ Real.log (Nat.factorial k : ℝ) := hstirling
      _ ≤ t := hlogfac
  by_contra hbound
  have hkgt : 2 * t / u < (k : ℝ) := lt_of_not_ge hbound
  have hqpos : 0 < 2 * t / u := div_pos (by positivity) hu
  have hlogu : Real.log u ≤ u / 2 - 1 + Real.log 2 := by
    calc
      Real.log u = Real.log (u / 2) + Real.log 2 := by
        rw [← Real.log_mul (by positivity) (by norm_num)]
        congr 1
        field_simp
      _ ≤ (u / 2 - 1) + Real.log 2 := by
        gcongr
        exact Real.log_le_sub_one_of_pos (by positivity)
  have hlogq : u / 2 + 1 ≤ Real.log (2 * t / u) := by
    have heq : Real.log (2 * t / u) = Real.log 2 + u - Real.log u := by
      rw [Real.log_div (by positivity) hu.ne', Real.log_mul (by norm_num) ht.ne']
    rw [heq]
    linarith
  have hloglt : Real.log (2 * t / u) < Real.log (k : ℝ) :=
    Real.strictMonoOn_log hqpos hkR hkgt
  have hku : t < (k : ℝ) * (u / 2) := by
    have := (div_lt_iff₀ hu).mp hkgt
    nlinarith
  have hprod : t < (k : ℝ) * (Real.log k - 1) := by
    have hloglarge : u / 2 < Real.log (k : ℝ) - 1 := by linarith
    nlinarith
  linarith

/-- The prime-factor exponential bound underlying equation (18). -/
theorem three_pow_primeFactors_card_le_exp
    {d : ℕ} (hd : Squarefree d) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    (3 : ℝ) ^ d.primeFactors.card ≤
      Real.exp (3 * Real.log d / Real.log (Real.log d)) := by
  have hcard := primeFactors_card_le_two_log_div_loglog hd hd2 hu1
  have ht : 0 < Real.log (d : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have hu : 0 < Real.log (Real.log (d : ℝ)) := by linarith
  have hlog3 : Real.log 3 ≤ (3 : ℝ) / 2 := by
    linarith [Real.log_three_lt_d9]
  have hexponent :
      (d.primeFactors.card : ℝ) * Real.log 3 ≤
        3 * Real.log d / Real.log (Real.log d) := by
    calc
      (d.primeFactors.card : ℝ) * Real.log 3 ≤
          (2 * Real.log d / Real.log (Real.log d)) * ((3 : ℝ) / 2) :=
        mul_le_mul hcard hlog3 (Real.log_nonneg (by norm_num))
          (div_nonneg (by positivity) hu.le)
      _ = 3 * Real.log d / Real.log (Real.log d) := by ring
  calc
    (3 : ℝ) ^ d.primeFactors.card =
        Real.exp (Real.log ((3 : ℝ) ^ d.primeFactors.card)) :=
      (Real.exp_log (by positivity)).symm
    _ = Real.exp ((d.primeFactors.card : ℝ) * Real.log 3) := by
      rw [Real.log_pow]
    _ ≤ Real.exp (3 * Real.log d / Real.log (Real.log d)) :=
      Real.exp_le_exp.mpr hexponent

/-- Equation (18), stated with the paper's hypothesis `μ(d) ≠ 0`. -/
theorem lemma6_equation18
    {d : ℕ} (hμ : ArithmeticFunction.moebius d ≠ 0) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    (3 : ℝ) ^ distinctPrimeFactors d ≤
      Real.exp (3 * Real.log d / Real.log (Real.log d)) := by
  have hd : Squarefree d :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hμ
  simpa only [distinctPrimeFactors] using
    three_pow_primeFactors_card_le_exp hd hd2 hu1

/-- Squared form of equation (18), ready for the weighted Cauchy and Hölder
inequalities used in (19). -/
theorem lemma6_equation18_sq
    {d : ℕ} (hμ : ArithmeticFunction.moebius d ≠ 0) (hd2 : 2 ≤ d)
    (hu1 : 1 < Real.log (Real.log (d : ℝ))) :
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
      Real.exp (6 * Real.log d / Real.log (Real.log d)) := by
  have h := lemma6_equation18 hμ hd2 hu1
  calc
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
        (Real.exp (3 * Real.log d / Real.log (Real.log d))) ^ 2 := by
      gcongr
    _ = Real.exp (6 * Real.log d / Real.log (Real.log d)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The explicit largeness condition in equation (18) is eventually
satisfied by every natural number. -/
theorem eventually_one_lt_log_log_nat :
    ∀ᶠ d : ℕ in Filter.atTop, 1 < Real.log (Real.log (d : ℝ)) := by
  have hreal : Filter.Tendsto (fun y : ℝ => Real.log (Real.log y))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  exact tendsto_natCast_atTop_atTop.eventually
    (hreal.eventually (Filter.eventually_gt_atTop 1))

/-- The increasing exponent `log Q / log log Q` in Chen's factor
`I_{l,x}`. -/
noncomputable def logLogRatio (y : ℝ) : ℝ :=
  Real.log y / Real.log (Real.log y)

theorem one_le_log_log_of_exp_exp_le {y : ℝ}
    (hy : Real.exp (Real.exp 1) ≤ y) :
    1 ≤ Real.log (Real.log y) := by
  have hypos : 0 < y := (by positivity : 0 < Real.exp (Real.exp 1)).trans_le hy
  have hlog : Real.exp 1 ≤ Real.log y := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ ≤ Real.log y := Real.log_le_log (by positivity) hy
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (Real.log y) := Real.log_le_log (by positivity) hlog

theorem one_lt_log_log_of_exp_exp_lt {y : ℝ}
    (hy : Real.exp (Real.exp 1) < y) :
    1 < Real.log (Real.log y) := by
  have hlog : Real.exp 1 < Real.log y := by
    calc
      Real.exp 1 = Real.log (Real.exp (Real.exp 1)) := by rw [Real.log_exp]
      _ < Real.log y := Real.strictMonoOn_log (Real.exp_pos _)
        ((Real.exp_pos _).trans hy) hy
  calc
    (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log (Real.log y) := Real.strictMonoOn_log (Real.exp_pos 1)
      ((Real.exp_pos 1).trans hlog) hlog

theorem hasDerivAt_logLogRatio {y : ℝ}
    (hy : Real.exp (Real.exp 1) ≤ y) :
    HasDerivAt logLogRatio
      ((Real.log (Real.log y) - 1) /
        (y * (Real.log (Real.log y)) ^ 2)) y := by
  have hEpos : 0 < Real.exp (Real.exp 1) := Real.exp_pos _
  have hypos : 0 < y := hEpos.trans_le hy
  have hy0 : y ≠ 0 := hypos.ne'
  have hy1 : y ≠ 1 := by
    have : (1 : ℝ) < Real.exp (Real.exp 1) :=
      Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
    linarith
  have hyneg1 : y ≠ -1 := by linarith
  have hloglogpos : 0 < Real.log (Real.log y) := by
    have := one_le_log_log_of_exp_exp_le hy
    linarith
  have hden : Real.log (Real.log y) ≠ 0 := hloglogpos.ne'
  have hlogyne : Real.log y ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hypos hy1
  unfold logLogRatio
  have hraw := (Real.hasDerivAt_log hy0).div
    (Real.hasDerivAt_log_log hy0 hy1 hyneg1) hden
  convert hraw using 1 <;> try {rfl}
  field_simp [hlogyne]

/-- `log Q / log log Q` is increasing once `Q ≥ exp(exp 1)`. -/
theorem monotoneOn_logLogRatio :
    MonotoneOn logLogRatio (Set.Ici (Real.exp (Real.exp 1))) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro y hy
    exact (hasDerivAt_logLogRatio hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    exact (hasDerivAt_logLogRatio hy.le).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_logLogRatio hy.le).deriv]
    have hloglog := one_le_log_log_of_exp_exp_le hy.le
    have hypos : 0 < y := (Real.exp_pos _).trans_le hy.le
    exact div_nonneg (sub_nonneg.mpr hloglog)
      (mul_nonneg hypos.le (sq_nonneg _))

/-- Chen's exceptional-factor envelope, written as a function of the
upper dyadic modulus endpoint `Q`. -/
noncomputable def lemma6ExceptionalFactor (Q : ℝ) : ℝ :=
  Real.exp (6 * logLogRatio Q)

theorem lemma6ExceptionalFactor_pos (Q : ℝ) :
    0 < lemma6ExceptionalFactor Q := by
  unfold lemma6ExceptionalFactor
  positivity

/-- Chen's exceptional factor is smaller than every fixed positive power.
This is the quantitative form used when the remaining powers of
`I_{l,x}` are absorbed in equations (19) and (20). -/
theorem eventually_lemma6ExceptionalFactor_le_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      lemma6ExceptionalFactor Q ≤ Q ^ δ := by
  have hloglog : Filter.Tendsto
      (fun Q : ℝ => Real.log (Real.log Q))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlarge := hloglog.eventually
    (Filter.eventually_ge_atTop (6 / δ))
  filter_upwards [hlarge, Filter.eventually_gt_atTop (1 : ℝ)] with Q hQlog hQ
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ.le
  have hloglogpos : 0 < Real.log (Real.log Q) := by
    have hthreshold : 0 < (6 : ℝ) / δ := div_pos (by norm_num) hδ
    linarith
  have hratio :
      (6 : ℝ) / Real.log (Real.log Q) ≤ δ := by
    apply (div_le_iff₀ hloglogpos).2
    have := (div_le_iff₀ hδ).1 hQlog
    nlinarith
  unfold lemma6ExceptionalFactor logLogRatio
  calc
    Real.exp (6 * (Real.log Q / Real.log (Real.log Q))) =
        Real.exp (Real.log Q *
          (6 / Real.log (Real.log Q))) := by
      congr 1
      field_simp
    _ ≤ Real.exp (Real.log Q * δ) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hratio hlogQ)
    _ = Q ^ δ :=
      (Real.rpow_def_of_pos (zero_lt_one.trans hQ) δ).symm

/-- Equation (18), squared and enlarged from `d` to a dyadic endpoint `Q`.
This is exactly the pointwise hypothesis consumed by the weighted
Cauchy--Hölder lemmas. -/
theorem lemma6_equation18_sq_le_exceptionalFactor
    {d : ℕ} (hμ : ArithmeticFunction.moebius d ≠ 0) (hd2 : 2 ≤ d)
    (hdlarge : Real.exp (Real.exp 1) < (d : ℝ))
    {Q : ℝ} (hdQ : (d : ℝ) ≤ Q) :
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
      lemma6ExceptionalFactor Q := by
  have hu1 := one_lt_log_log_of_exp_exp_lt hdlarge
  have hraw := lemma6_equation18_sq hμ hd2 hu1
  have hratio : logLogRatio (d : ℝ) ≤ logLogRatio Q :=
    monotoneOn_logLogRatio hdlarge.le (hdlarge.le.trans hdQ) hdQ
  calc
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
        Real.exp (6 * Real.log d / Real.log (Real.log d)) := hraw
    _ = Real.exp (6 * logLogRatio (d : ℝ)) := by
      unfold logLogRatio
      congr 1
      ring
    _ ≤ Real.exp (6 * logLogRatio Q) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hratio (by norm_num))
    _ = lemma6ExceptionalFactor Q := rfl

end Chen

end

/-! ## ChenTheorem.Lemma6.FourthMoment -/

section

/-
The precise fourth-moment input used in Lemma 6 of Chen's paper.

Lemma 3 itself estimates `L(s, χ)`. Immediately after equation (15), Chen
applies Cauchy's integral formula on the circle of radius `1 / log x` around
`β + iν`, then inserts Lemma 3 and the elementary dyadic estimate
`1 / φ(d) ≪ log d / d`. The result is the weighted fourth moment of `L'`
recorded below.
-/

open Filter Real MeasureTheory
open scoped Classical

namespace Chen

/-- The primitive-character fourth moment of `L'` at modulus `q`. -/
noncomputable def lDerivFourthTerm (q : ℕ) (s : ℂ) : ℝ :=
  if h : q = 0 then 0
  else
    have : NeZero q := ⟨h⟩
    primSum q (fun χ => ‖deriv (DirichletCharacter.LFunction χ) s‖ ^ 4)

/-- The vertical point `β + iν`, where `β = 1/2 + 1/log x`, used after
equation (15). -/
noncomputable def lemma6BetaPoint (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + (ν : ℂ) * Complex.I

@[simp]
theorem lemma6BetaPoint_re (x : ℕ) (ν : ℝ) :
    (lemma6BetaPoint x ν).re = 1 / 2 + 1 / Real.log x := by
  simp only [lemma6BetaPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp]
theorem lemma6BetaPoint_im (x : ℕ) (ν : ℝ) :
    (lemma6BetaPoint x ν).im = ν := by
  simp only [lemma6BetaPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

/-- The vertical line used in Lemma 6 lies in the half-plane covered by the
corrected statement of Lemma 3. -/
theorem half_le_lemma6BetaPoint_re {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) :
    (1 / 2 : ℝ) ≤ (lemma6BetaPoint x ν).re := by
  rw [lemma6BetaPoint_re]
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hdiv : 0 < (1 : ℝ) / Real.log (x : ℝ) :=
    div_pos zero_lt_one hlog
  exact le_add_of_nonneg_right hdiv.le

/-- Radius of the Cauchy circle used immediately after equation (15). -/
noncomputable def lemma6CauchyRadius (x : ℕ) : ℝ :=
  1 / Real.log x

theorem lemma6CauchyRadius_pos {x : ℕ} (hx : 2 ≤ x) :
    0 < lemma6CauchyRadius x := by
  unfold lemma6CauchyRadius
  exact div_pos zero_lt_one
    (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))

/-- Every point of the closed Cauchy disc remains in the half-plane covered
by the corrected Lemma 3.  Its leftmost boundary has real part exactly
`1 / 2`. -/
theorem half_le_re_of_mem_closedBall_lemma6BetaPoint
    {x : ℕ} (_hx : 2 ≤ x) (ν : ℝ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (lemma6BetaPoint x ν)
      (lemma6CauchyRadius x)) :
    (1 / 2 : ℝ) ≤ z.re := by
  have hdist : ‖z - lemma6BetaPoint x ν‖ ≤ lemma6CauchyRadius x := by
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hre : |(z - lemma6BetaPoint x ν).re| ≤
      lemma6CauchyRadius x :=
    (Complex.abs_re_le_norm _).trans hdist
  have hleft := neg_le_of_abs_le hre
  change -lemma6CauchyRadius x ≤
    z.re - (lemma6BetaPoint x ν).re at hleft
  rw [lemma6BetaPoint_re] at hleft
  unfold lemma6CauchyRadius at hleft
  linarith

/-- On the same disc the spectral factor grows by at most a factor two. -/
theorem norm_le_two_mul_norm_lemma6BetaPoint_of_mem_closedBall
    {x : ℕ} (hx : 2 ≤ x) (ν : ℝ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (lemma6BetaPoint x ν)
      (lemma6CauchyRadius x)) :
    ‖z‖ ≤ 2 * ‖lemma6BetaPoint x ν‖ := by
  let s := lemma6BetaPoint x ν
  let r := lemma6CauchyRadius x
  have hdist : ‖z - s‖ ≤ r := by
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hsre : (0 : ℝ) ≤ s.re :=
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
      (half_le_lemma6BetaPoint_re hx ν)
  have hrle : r ≤ ‖s‖ := by
    calc
      r ≤ s.re := by
        dsimp only [r, s, lemma6CauchyRadius]
        rw [lemma6BetaPoint_re]
        linarith
      _ = |s.re| := (abs_of_nonneg hsre).symm
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  calc
    ‖z‖ = ‖(z - s) + s‖ := by ring_nf
    _ ≤ ‖z - s‖ + ‖s‖ := norm_add_le _ _
    _ ≤ r + ‖s‖ := add_le_add_left hdist _
    _ ≤ 2 * ‖s‖ := by linarith

/-- A primitive character of modulus at least two is nonprincipal. -/
theorem primitiveCharacter_ne_one
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ ≠ 1 := by
  intro hχone
  have hcondOne : χ.conductor = 1 :=
    DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
  rw [DirichletCharacter.isPrimitive_def] at hχ
  omega

/-- Consequently every L-function occurring in the primitive sum is entire;
this discharges the analytic hypothesis of Cauchy's formula. -/
theorem primitiveCharacter_differentiable_LFunction
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction
    (primitiveCharacter_ne_one hq hχ)

/-- The derivative of a primitive nonprincipal Dirichlet L-function is
again entire.  This is the analytic input needed by the `B` contour shift. -/
theorem primitiveCharacter_differentiable_LFunction_deriv
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    Differentiable ℂ (fun s => deriv (DirichletCharacter.LFunction χ) s) := by
  intro s
  exact ((primitiveCharacter_differentiable_LFunction hq hχ).analyticAt s).deriv.differentiableAt

theorem lFourthTerm_nonneg (q : ℕ) (s : ℂ) :
    0 ≤ lFourthTerm q s := by
  unfold lFourthTerm
  split_ifs
  · exact le_rfl
  · unfold primSum
    apply tsum_nonneg
    intro χ
    split_ifs
    · positivity
    · exact le_rfl

/-- For a fixed positive modulus the primitive fourth moment is continuous
in the spectral parameter. -/
theorem continuous_lFourthTerm {q : ℕ} (hq : 2 ≤ q) :
    Continuous (lFourthTerm q) := by
  classical
  have hq0 : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq0⟩
  have heq : lFourthTerm q = fun s =>
      ∑ χ : DirichletCharacter ℂ q,
        if χ.IsPrimitive then
          ‖DirichletCharacter.LFunction χ s‖ ^ 4 else 0 := by
    funext s
    unfold lFourthTerm primSum
    rw [dif_neg hq0]
    simp only [tsum_fintype]
  rw [heq]
  apply continuous_finsetSum
  intro χ hχmem
  by_cases hχ : χ.IsPrimitive
  · simp only [hχ, if_true]
    exact (primitiveCharacter_differentiable_LFunction hq hχ).continuous.norm.pow 4
  · simpa only [hχ, if_false] using
      (continuous_const : Continuous (fun _ : ℂ => (0 : ℝ)))

/-- Cauchy--Hölder estimate after summing over primitive characters at one
fixed modulus. -/
theorem lDerivFourthTerm_le_circleIntegral
    {q : ℕ} (hq : 2 ≤ q) (s : ℂ) {r : ℝ} (hr : 0 < r) :
    lDerivFourthTerm q s ≤
      (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          lFourthTerm q (circleMap s r θ) := by
  classical
  have hq0 : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq0⟩
  let K : ℝ := (2 * Real.pi * r ^ 4)⁻¹
  let G : DirichletCharacter ℂ q → ℝ → ℝ := fun χ θ =>
    if χ.IsPrimitive then
      ‖DirichletCharacter.LFunction χ (circleMap s r θ)‖ ^ 4
    else 0
  have hGint : ∀ χ, IntervalIntegrable (G χ) volume 0 (2 * Real.pi) := by
    intro χ
    by_cases hχ : χ.IsPrimitive
    · have hdiff := primitiveCharacter_differentiable_LFunction hq hχ
      have hcont : Continuous (fun θ : ℝ =>
          ‖DirichletCharacter.LFunction χ (circleMap s r θ)‖ ^ 4) :=
        (hdiff.continuous.norm.comp (continuous_circleMap s r)).pow 4
      simpa only [G, hχ, if_true] using
        hcont.intervalIntegrable 0 (2 * Real.pi)
    · simpa only [G, hχ, if_false] using
        (continuous_const.intervalIntegrable (0 : ℝ) (2 * Real.pi) :
          IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 (2 * Real.pi))
  rw [lDerivFourthTerm, dif_neg hq0]
  unfold primSum
  simp only [tsum_fintype]
  calc
    ∑ χ : DirichletCharacter ℂ q,
        (if χ.IsPrimitive then
          ‖deriv (DirichletCharacter.LFunction χ) s‖ ^ 4 else 0) ≤
        ∑ χ : DirichletCharacter ℂ q,
          K * ∫ θ in (0 : ℝ)..2 * Real.pi, G χ θ := by
      apply Finset.sum_le_sum
      intro χ hχmem
      by_cases hχ : χ.IsPrimitive
      · rw [if_pos hχ]
        have hdiff := primitiveCharacter_differentiable_LFunction hq hχ
        simpa only [K, G, hχ, if_true] using
          norm_deriv_pow_four_le_circleIntegral hdiff hr
      · rw [if_neg hχ]
        simp [G, hχ]
    _ = K * ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∑ χ : DirichletCharacter ℂ q, G χ θ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (intervalIntegral.integral_finsetSum
        (fun χ _ => hGint χ)).symm
    _ = (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          lFourthTerm q (circleMap s r θ) := by
      dsimp only [K]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ hθ
      change (∑ χ : DirichletCharacter ℂ q, G χ θ) =
        lFourthTerm q (circleMap s r θ)
      unfold lFourthTerm primSum
      rw [dif_neg hq0]
      simp only [tsum_fintype, G]

/-- The dyadic modulus interval
`2^(l-1) (log x)^100 < d ≤ 2^l (log x)^100`. -/
noncomputable def lemma6ModulusBlock (x l : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d =>
    Squarefree d ∧
      (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 < d ∧
      (d : ℝ) ≤ (2 : ℝ) ^ l * (Real.log x) ^ 100

/-- Integer cutoff corresponding to the upper end of a dyadic modulus
block. -/
noncomputable def lemma6ModulusCutoff (x l : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ l * (Real.log x) ^ 100⌉₊

/-- Once `log x ≥ 1`, every dyadic cutoff with `l ≥ 1` is at least two. -/
theorem lemma6ModulusCutoff_two_le
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (hl : 1 ≤ l) :
    2 ≤ lemma6ModulusCutoff x l := by
  have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ l := by
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
  have hpowlog : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
    one_le_pow₀ hxlog
  have hU : (2 : ℝ) ≤
      (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 := by nlinarith
  have hceil := Nat.le_ceil
    ((2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100)
  rw [lemma6ModulusCutoff]
  exact_mod_cast hU.trans hceil

/-- The integer ceiling enlarges the upper endpoint by at most a factor two
in the range used by Lemma 6. -/
theorem lemma6ModulusCutoff_le_two_mul
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    (lemma6ModulusCutoff x l : ℝ) ≤
      2 * ((2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100) := by
  unfold lemma6ModulusCutoff
  apply Nat.ceil_le_two_mul
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
  have hpowlog : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
    one_le_pow₀ hxlog
  nlinarith

/-- If the dyadic block is nonempty then its integer cutoff is at most
polynomially comparable with `x`; hence its logarithm costs only `log x`. -/
theorem lemma6_log_modulusCutoff_le
    {x l : ℕ} (hx4 : 4 ≤ x) (hxlog : 1 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hne : (lemma6ModulusBlock x l).Nonempty) :
    Real.log (lemma6ModulusCutoff x l) ≤ 2 * Real.log x := by
  obtain ⟨d, hd⟩ := hne
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hddata.1
    omega
  have hpow_eq : (2 : ℝ) ^ l = 2 * (2 : ℝ) ^ (l - 1) := by
    calc
      (2 : ℝ) ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by ring
  have hU_lt : (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 <
      2 * (x : ℝ) := by
    rw [hpow_eq]
    have hdle : (d : ℝ) ≤ x := by exact_mod_cast hdx
    nlinarith [hddata.2.2.1]
  have hQle := lemma6ModulusCutoff_le_two_mul (x := x) (l := l) hxlog
  have hQle4x : (lemma6ModulusCutoff x l : ℝ) ≤ 4 * (x : ℝ) := by
    nlinarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hQpos : (0 : ℝ) < lemma6ModulusCutoff x l := by
    have hQ2 := lemma6ModulusCutoff_two_le hxlog hl
    exact_mod_cast (show 0 < lemma6ModulusCutoff x l by omega)
  calc
    Real.log (lemma6ModulusCutoff x l) ≤ Real.log (4 * (x : ℝ)) :=
      Real.log_le_log hQpos hQle4x
    _ = Real.log 4 + Real.log x := by
      rw [Real.log_mul (by norm_num) hxpos.ne']
    _ ≤ Real.log x + Real.log x := by
      have h4x : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx4
      simpa [add_comm] using
        add_le_add_right (Real.log_le_log (by norm_num) h4x) (Real.log x)
    _ = 2 * Real.log x := by ring

theorem lemma6ModulusBlock_subset_Icc
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    lemma6ModulusBlock x l ⊆ Finset.Icc 2 (lemma6ModulusCutoff x l) := by
  intro d hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hd
  rw [Finset.mem_Icc]
  have hlower : (1 : ℝ) ≤
      (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 := by
    have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (l - 1) := by
      exact one_le_pow₀ (by norm_num)
    have hpowlog : (1 : ℝ) ≤ (Real.log x) ^ 100 := by
      exact one_le_pow₀ hxlog
    nlinarith
  have hd2 : 2 ≤ d := by
    have : (1 : ℝ) < d := hlower.trans_lt hd.2.2.1
    exact_mod_cast this
  refine ⟨hd2, ?_⟩
  have hceil :
      (2 : ℝ) ^ l * (Real.log x) ^ 100 ≤
        (lemma6ModulusCutoff x l : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hd.2.2.2.trans hceil

/-- The totient weight on a squarefree dyadic modulus costs one logarithm. -/
theorem lemma6ModulusBlock_inv_totient_le
    {x l d : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hd : d ∈ lemma6ModulusBlock x l) :
    (Nat.totient d : ℝ)⁻¹ ≤
      (2 / Real.log 2) * Real.log x / d := by
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  have hdIcc := lemma6ModulusBlock_subset_Icc hxlog hd
  have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hdIcc).1
  have hdx : d ≤ x := by
    have := Finset.mem_range.mp hddata.1
    omega
  have hlog : Real.log d ≤ Real.log x :=
    Real.log_le_log (by positivity) (by exact_mod_cast hdx)
  have hc0 : 0 ≤ (2 / Real.log 2 : ℝ) := by positivity
  exact (inv_totient_le_log_div_self hddata.2.1 hd2).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog hc0) (by positivity))

/-- Lemma 3 already gives the required fourth moment of `L` on one dyadic
modulus block, including its `1 / φ(d)` weight.  This is the part of the
transfer preceding Cauchy's formula. -/
theorem lemma6_weighted_lFourth_block_le
    {C : ℝ}
    (hL : ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4)
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hQ2 : 2 ≤ lemma6ModulusCutoff x l) (s : ℂ)
    (hs : (1 / 2 : ℝ) ≤ s.re) :
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lFourthTerm d s ≤
      ((2 / Real.log 2) * Real.log x /
          ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
        (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
            (1 + ‖s‖))) ^ 4) := by
  let D : ℝ := (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100
  let K : ℝ := (2 / Real.log 2) * Real.log x / D
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hnum0 : 0 ≤ (2 / Real.log 2) * Real.log x := by positivity
  have hK0 : 0 ≤ K := div_nonneg hnum0 hDpos.le
  calc
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lFourthTerm d s ≤
        ∑ d ∈ lemma6ModulusBlock x l, K * lFourthTerm d s := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right _ (lFourthTerm_nonneg d s)
      have hddata := hd
      rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
      have hfirst := lemma6ModulusBlock_inv_totient_le hxlog hd
      apply hfirst.trans
      dsimp only [K, D]
      exact div_le_div_of_nonneg_left hnum0 hDpos hddata.2.2.1.le
    _ = K * ∑ d ∈ lemma6ModulusBlock x l, lFourthTerm d s := by
      rw [Finset.mul_sum]
    _ ≤ K * ∑ d ∈ Finset.Icc 2 (lemma6ModulusCutoff x l),
        lFourthTerm d s := by
      apply mul_le_mul_of_nonneg_left _ hK0
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (lemma6ModulusBlock_subset_Icc hxlog)
        (fun d hd hnot => lFourthTerm_nonneg d s)
    _ ≤ K * (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
            (1 + ‖s‖))) ^ 4) := by
      exact mul_le_mul_of_nonneg_left
        (hL (lemma6ModulusCutoff x l) s hQ2 hs) hK0
    _ = ((2 / Real.log 2) * Real.log x /
          ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
        (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
            (1 + ‖s‖))) ^ 4) := by rfl

/-- Cauchy--Hölder after interchanging both finite sums (moduli and
primitive characters) with the circle integral. -/
theorem lemma6_weighted_lDerivFourth_le_circleIntegral
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d s ≤
      (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∑ d ∈ lemma6ModulusBlock x l,
            (Nat.totient d : ℝ)⁻¹ *
              lFourthTerm d (circleMap s r θ) := by
  classical
  let K : ℝ := (2 * Real.pi * r ^ 4)⁻¹
  let F : ℕ → ℝ → ℝ := fun d θ =>
    (Nat.totient d : ℝ)⁻¹ * lFourthTerm d (circleMap s r θ)
  have hd2 : ∀ d ∈ lemma6ModulusBlock x l, 2 ≤ d := by
    intro d hd
    exact (Finset.mem_Icc.mp
      (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hFint : ∀ d ∈ lemma6ModulusBlock x l,
      IntervalIntegrable (F d) volume 0 (2 * Real.pi) := by
    intro d hd
    have hcont : Continuous (F d) := by
      dsimp only [F]
      exact continuous_const.mul
        ((continuous_lFourthTerm (hd2 d hd)).comp
          (continuous_circleMap s r))
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  calc
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d s ≤
        ∑ d ∈ lemma6ModulusBlock x l,
          (Nat.totient d : ℝ)⁻¹ *
            (K * ∫ θ in (0 : ℝ)..2 * Real.pi,
              lFourthTerm d (circleMap s r θ)) := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      · simpa only [K] using
          lDerivFourthTerm_le_circleIntegral (hd2 d hd) s hr
      · positivity
    _ = ∑ d ∈ lemma6ModulusBlock x l,
          K * ∫ θ in (0 : ℝ)..2 * Real.pi, F d θ := by
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [F]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = K * ∑ d ∈ lemma6ModulusBlock x l,
          ∫ θ in (0 : ℝ)..2 * Real.pi, F d θ := by
      rw [Finset.mul_sum]
    _ = K * ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∑ d ∈ lemma6ModulusBlock x l, F d θ := by
      congr 1
      exact (intervalIntegral.integral_finsetSum hFint).symm
    _ = (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ∑ d ∈ lemma6ModulusBlock x l,
            (Nat.totient d : ℝ)⁻¹ *
              lFourthTerm d (circleMap s r θ) := by rfl

/-- The direct output of applying Lemma 3 pointwise on the Cauchy circle.
This deliberately leaves the Cauchy radius and dyadic cutoff unsimplified;
the subsequent estimate is purely elementary arithmetic. -/
theorem lemma6_weighted_lDerivFourth_block_le_raw
    {C : ℝ} (hC : 0 < C)
    (hL : ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4)
    {x l : ℕ} (hx : 2 ≤ x) (hxlog : 1 ≤ Real.log (x : ℝ))
    (hQ2 : 2 ≤ lemma6ModulusCutoff x l) (ν : ℝ) :
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lDerivFourthTerm d (lemma6BetaPoint x ν) ≤
      (2 * Real.pi * (lemma6CauchyRadius x) ^ 4)⁻¹ *
        (2 * Real.pi) *
          (((2 / Real.log 2) * Real.log x /
              ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
            (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 *
              (2 * ‖lemma6BetaPoint x ν‖) ^ 2 *
              (Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
                (1 + 2 * ‖lemma6BetaPoint x ν‖))) ^ 4)) := by
  let s := lemma6BetaPoint x ν
  let r := lemma6CauchyRadius x
  let F : ℝ → ℝ := fun θ =>
    ∑ d ∈ lemma6ModulusBlock x l,
      (Nat.totient d : ℝ)⁻¹ * lFourthTerm d (circleMap s r θ)
  let B : ℝ :=
    ((2 / Real.log 2) * Real.log x /
        ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
      (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 * (2 * ‖s‖) ^ 2 *
        (Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
          (1 + 2 * ‖s‖))) ^ 4)
  have hr : 0 < r := lemma6CauchyRadius_pos hx
  have hFcont : Continuous F := by
    dsimp only [F]
    apply continuous_finsetSum
    intro d hd
    exact continuous_const.mul
      ((continuous_lFourthTerm
        ((Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1)).comp
        (continuous_circleMap s r))
  have hFB : ∀ θ : ℝ, F θ ≤ B := by
    intro θ
    have hz : circleMap s r θ ∈ Metric.closedBall s r :=
      circleMap_mem_closedBall s hr.le θ
    have hre : (1 / 2 : ℝ) ≤ (circleMap s r θ).re := by
      simpa only [s, r] using
        half_le_re_of_mem_closedBall_lemma6BetaPoint hx ν hz
    have hnorm : ‖circleMap s r θ‖ ≤ 2 * ‖s‖ := by
      simpa only [s, r] using
        norm_le_two_mul_norm_lemma6BetaPoint_of_mem_closedBall hx ν hz
    have hpoint := lemma6_weighted_lFourth_block_le
      hL hxlog hQ2 (circleMap s r θ) hre
    apply hpoint.trans
    dsimp only [F, B]
    have hlog0 : 0 ≤ Real.log
        (2 * (lemma6ModulusCutoff x l : ℝ) *
          (1 + ‖circleMap s r θ‖)) := by
      apply Real.log_nonneg
      have hQr : (2 : ℝ) ≤ lemma6ModulusCutoff x l := by
        exact_mod_cast hQ2
      nlinarith [norm_nonneg (circleMap s r θ)]
    gcongr
  have hint : (∫ θ in (0 : ℝ)..2 * Real.pi, F θ) ≤
      ∫ _θ in (0 : ℝ)..2 * Real.pi, B :=
    intervalIntegral.integral_mono (by positivity)
      (hFcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hFB
  have hcircle := lemma6_weighted_lDerivFourth_le_circleIntegral
    (x := x) (l := l) hxlog s hr
  change
    (∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d s) ≤
      (2 * Real.pi * r ^ 4)⁻¹ * (2 * Real.pi) * B
  calc
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d s ≤
      (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * Real.pi, F θ := hcircle
    _ ≤ (2 * Real.pi * r ^ 4)⁻¹ *
        ∫ _θ in (0 : ℝ)..2 * Real.pi, B := by
      exact mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (2 * Real.pi * r ^ 4)⁻¹ * (2 * Real.pi) * B := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring

/-- On an occupied dyadic block, the height-dependent logarithm supplied by
the corrected Lemma 3 is at most a fixed multiple of `log x` times the
Cauchy weight. -/
theorem lemma6_height_log_le_cauchy_weight
    {x l : ℕ} (hx4 : 4 ≤ x) (hxlog : 2 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (hne : (lemma6ModulusBlock x l).Nonempty) (ν : ℝ) :
    Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
        (1 + 2 * ‖lemma6BetaPoint x ν‖)) ≤
      6 * Real.log (x : ℝ) * Real.sqrt (1 + ν ^ 2) := by
  let L : ℝ := Real.log (x : ℝ)
  let Q : ℝ := lemma6ModulusCutoff x l
  let N : ℝ := ‖lemma6BetaPoint x ν‖
  let A : ℝ := 1 + ν ^ 2
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast (show 0 < lemma6ModulusCutoff x l by
      have := lemma6ModulusCutoff_two_le (by linarith) hl
      omega)
  have hlogQ : Real.log Q ≤ 2 * L := by
    simpa only [Q, L] using
      lemma6_log_modulusCutoff_le hx4 (by linarith) hl hne
  have hlog2 : Real.log 2 ≤ L := by
    dsimp only [L]
    exact Real.log_le_log (by norm_num)
      (by exact_mod_cast (show 2 ≤ x by omega))
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hsqrt1 : 1 ≤ Real.sqrt A := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ A by
      dsimp only [A]
      nlinarith [sq_nonneg ν])
    simpa using h
  have hNsq : N ^ 2 ≤ A := by
    have hlog : 0 < Real.log (x : ℝ) := by linarith
    have hinv : (1 : ℝ) / Real.log x ≤ 1 / 2 := by
      rw [div_le_iff₀ hlog]
      nlinarith
    have hre0 : 0 ≤ (lemma6BetaPoint x ν).re := by
      rw [lemma6BetaPoint_re]
      positivity
    have hre1 : (lemma6BetaPoint x ν).re ≤ 1 := by
      rw [lemma6BetaPoint_re]
      linarith
    dsimp only [N, A]
    rw [Complex.sq_norm, Complex.normSq_apply, lemma6BetaPoint_im]
    nlinarith
  have hN : N ≤ Real.sqrt A := by
    have hN0 : 0 ≤ N := by dsimp only [N]; positivity
    have hs0 : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hsquare : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
    nlinarith
  have hheight : Real.log (1 + 2 * N) ≤ 2 * Real.sqrt A := by
    have hpos : 0 < 1 + 2 * N := by
      dsimp only [N]
      positivity
    exact (Real.log_le_sub_one_of_pos hpos).trans (by nlinarith)
  change Real.log (2 * Q * (1 + 2 * N)) ≤
    6 * L * Real.sqrt A
  rw [Real.log_mul (mul_pos (by norm_num) hQpos).ne'
    (by positivity : 1 + 2 * N ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQpos.ne']
  have honeprod : 1 ≤ L * Real.sqrt A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hLone)
      (sub_nonneg.mpr hsqrt1)]
  nlinarith

/-- Elementary simplification of the raw Cauchy bound on a nonempty
dyadic block.  Before the final harmless slack, the calculation gives the
power `(log x)^109` displayed in the scan. -/
theorem lemma6_raw_deriv_bound_le
    {C : ℝ} (hC : 0 < C) {x l : ℕ}
    (hx4 : 4 ≤ x) (hxlog : 2 ≤ Real.log (x : ℝ)) (hl : 1 ≤ l)
    (hne : (lemma6ModulusBlock x l).Nonempty) (ν : ℝ) :
    (2 * Real.pi * (lemma6CauchyRadius x) ^ 4)⁻¹ *
        (2 * Real.pi) *
          (((2 / Real.log 2) * Real.log x /
              ((2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100)) *
            (C * (lemma6ModulusCutoff x l : ℝ) ^ 2 *
              (2 * ‖lemma6BetaPoint x ν‖) ^ 2 *
              (Real.log (2 * (lemma6ModulusCutoff x l : ℝ) *
                (1 + 2 * ‖lemma6BetaPoint x ν‖))) ^ 4)) ≤
      (82944 / Real.log 2 * C) * (2 : ℝ) ^ l *
        (Real.log x) ^ 110 * ‖lemma6BetaPoint x ν‖ ^ 2 *
          (1 + ν ^ 2) ^ 2 := by
  let L : ℝ := Real.log x
  let P : ℝ := (2 : ℝ) ^ l
  let D : ℝ := (2 : ℝ) ^ (l - 1) * L ^ 100
  let Q : ℝ := lemma6ModulusCutoff x l
  let N : ℝ := ‖lemma6BetaPoint x ν‖
  let A : ℝ := 1 + ν ^ 2
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by linarith
  have hPpos : 0 < P := by dsimp only [P]; positivity
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hQ2 : (2 : ℝ) ≤ Q := by
    dsimp only [Q]
    exact_mod_cast lemma6ModulusCutoff_two_le (by linarith) hl
  have hQ0 : 0 ≤ Q := hQ2.trans' (by norm_num)
  have hQle : Q ≤ 2 * (P * L ^ 100) := by
    simpa only [Q, P, L] using
      lemma6ModulusCutoff_le_two_mul (x := x) (l := l) (by linarith)
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hheight0 : 0 ≤ Real.log (2 * Q * (1 + 2 * N)) := by
    apply Real.log_nonneg
    nlinarith [norm_nonneg (lemma6BetaPoint x ν)]
  have hheight : Real.log (2 * Q * (1 + 2 * N)) ≤
      6 * L * Real.sqrt A := by
    simpa only [Q, L, N, A] using
      lemma6_height_log_le_cauchy_weight hx4 hxlog hl hne ν
  have hsqrt_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
  have hsqrt_four : (Real.sqrt A) ^ 4 = A ^ 2 := by
    calc
      (Real.sqrt A) ^ 4 = ((Real.sqrt A) ^ 2) ^ 2 := by ring
      _ = A ^ 2 := by rw [hsqrt_sq]
  have hheightpow : (6 * L * Real.sqrt A) ^ 4 =
      1296 * L ^ 4 * A ^ 2 := by
    rw [mul_pow, mul_pow, hsqrt_four]
    norm_num
  have hpow_eq : P = 2 * (2 : ℝ) ^ (l - 1) := by
    dsimp only [P]
    calc
      (2 : ℝ) ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by ring
  have hcauchy :
      (2 * Real.pi * (lemma6CauchyRadius x) ^ 4)⁻¹ *
          (2 * Real.pi) = L ^ 4 := by
    rw [lemma6CauchyRadius]
    dsimp only [L]
    field_simp
  change
    (2 * Real.pi * (lemma6CauchyRadius x) ^ 4)⁻¹ *
        (2 * Real.pi) *
          (((2 / Real.log 2) * L / D) *
            (C * Q ^ 2 * (2 * N) ^ 2 *
              (Real.log (2 * Q * (1 + 2 * N))) ^ 4)) ≤
      (82944 / Real.log 2 * C) * P * L ^ 110 * N ^ 2 * A ^ 2
  rw [hcauchy]
  calc
    L ^ 4 *
        (((2 / Real.log 2) * L / D) *
          (C * Q ^ 2 * (2 * N) ^ 2 *
            (Real.log (2 * Q * (1 + 2 * N))) ^ 4)) ≤
      L ^ 4 *
        (((2 / Real.log 2) * L / D) *
          (C * (2 * (P * L ^ 100)) ^ 2 *
            (2 * N) ^ 2 * (6 * L * Real.sqrt A) ^ 4)) := by
      gcongr
    _ = (82944 / Real.log 2 * C) * P * L ^ 109 * N ^ 2 * A ^ 2 := by
      dsimp only [D]
      rw [hpow_eq]
      rw [hheightpow]
      field_simp
      ring
    _ ≤ (82944 / Real.log 2 * C) * P * L ^ 110 * N ^ 2 * A ^ 2 := by
      gcongr
      omega

/-- The complete dyadic `L'` fourth-moment estimate at a fixed `x`, `l`,
and height.  Empty blocks are handled separately, which is essential since
the statement is uniform in every `l ≥ 1`. -/
theorem lemma6_weighted_lDerivFourth_block_le
    {C : ℝ} (hC : 0 < C)
    (hL : ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
      ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
        C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 *
          (Real.log (2 * (Q : ℝ) * (1 + ‖s‖))) ^ 4)
    {x l : ℕ} (hx4 : 4 ≤ x) (hxlog : 2 ≤ Real.log (x : ℝ))
    (hl : 1 ≤ l) (ν : ℝ) :
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lDerivFourthTerm d (lemma6BetaPoint x ν) ≤
      (82944 / Real.log 2 * C) * (2 : ℝ) ^ l *
        (Real.log x) ^ 110 * ‖lemma6BetaPoint x ν‖ ^ 2 *
          (1 + ν ^ 2) ^ 2 := by
  by_cases hne : (lemma6ModulusBlock x l).Nonempty
  · exact (lemma6_weighted_lDerivFourth_block_le_raw
      hC hL (show 2 ≤ x by omega) (by linarith)
        (lemma6ModulusCutoff_two_le (by linarith) hl) ν).trans
      (lemma6_raw_deriv_bound_le hC hx4 hxlog hl hne ν)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

/-- A rigorous one-log-slack version of the `L'` fourth-moment estimate used
by Lemma 6 after equation (15).

The scan writes exponent `109`: `100` from the dyadic scale, four from Lemma
3, and five from the Cauchy/Hölder step. It silently absorbs the unbounded
factor `d/φ(d)` into `≪`. Using the uniform elementary bound
`d/φ(d) ≪ log d` gives exponent `110`; this harmless slack is retained in the
formal interface. -/
def Lemma6DerivativeFourthMoment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (l : ℕ) (ν : ℝ), 1 ≤ l →
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d (lemma6BetaPoint x ν) ≤
      C * (2 : ℝ) ^ l * (Real.log x) ^ 110 *
        ‖lemma6BetaPoint x ν‖ ^ 2 * (1 + ν ^ 2) ^ 2

/-- Cauchy's integral formula plus the dyadic totient estimate transfers the
paper's Lemma 3 to the derivative fourth moment required in Lemma 6.

The half-plane geometry of the Cauchy disc, differentiability of every
primitive L-function, the dyadic cutoff, and the weighted application of
Lemma 3 are proved above.  What remains here is the analytic Cauchy--Hölder
inequality, its interchange with the finite primitive-character sum, and the
final elementary simplification of the dyadic cutoff. -/
theorem lemma6_deriv_fourth_moment_of_lFunction_fourth_moment_with_height_log
    (hL : Lemma3FourthMomentWithHeightLog) :
    Lemma6DerivativeFourthMoment := by
  obtain ⟨C, hC, hL⟩ := hL
  refine ⟨82944 / Real.log 2 * C, by positivity, ?_⟩
  have hlogTwoReal : ∀ᶠ y : ℝ in atTop, 2 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)
  have hlogTwo : ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogTwoReal
  filter_upwards [hlogTwo, eventually_ge_atTop 4] with x hxlog hx4
  intro l ν hl
  exact lemma6_weighted_lDerivFourth_block_le hC hL hx4 hxlog hl ν

end Chen

end

/-! ## ChenTheorem.Lemma6.Dyadic -/

section

/-
Dyadic conductor bookkeeping for equation (13) in the proof of Lemma 6.

The analytic fourth-moment bound is stated on `lemma6ModulusBlock x l`.
This file proves that the large squarefree conductors occurring in `N_m`
are covered by exactly one such positive block.
-/

open Real Filter
open scoped Classical

namespace Chen

/-- The real upper endpoint of the `l`-th dyadic modulus block. -/
noncomputable def lemma6DyadicModulusScale (x l : ℕ) : ℝ :=
  (2 : ℝ) ^ l * (Real.log x) ^ 100

/-- The exceptional factor `I_{l,x}` appearing after equation (18). -/
noncomputable def lemma6ExceptionalFactorAt (x l : ℕ) : ℝ :=
  lemma6ExceptionalFactor (lemma6DyadicModulusScale x l)

/-- Eventually the base scale `(log x)^100` is beyond the range where
the monotonic exceptional-factor envelope is valid. -/
theorem eventually_exp_exp_one_le_log_pow_hundred :
    ∀ᶠ x : ℕ in atTop,
      Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100 := by
  have hlog :
      Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually
    (eventually_ge_atTop (Real.exp (Real.exp 1)))
  filter_upwards [hlarge] with x hx
  have hbase : 1 ≤ Real.log (x : ℝ) := by
    exact (Real.one_le_exp (Real.exp_pos 1).le).trans hx
  calc
    Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) := hx
    _ = Real.log (x : ℝ) ^ 1 := by rw [pow_one]
    _ ≤ Real.log (x : ℝ) ^ 100 :=
      pow_le_pow_right₀ hbase (by norm_num)

/-- Uniformly in the dyadic index, the exceptional factor is bounded by
every prescribed positive power of its dyadic endpoint. -/
theorem eventually_lemma6ExceptionalFactorAt_le_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ∀ l : ℕ,
      lemma6ExceptionalFactorAt x l ≤
        (lemma6DyadicModulusScale x l) ^ δ := by
  obtain ⟨Q₀, hQ₀⟩ :=
    Filter.eventually_atTop.1
      (eventually_lemma6ExceptionalFactor_le_rpow hδ)
  have hlog :
      Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually
    (eventually_ge_atTop (max 1 Q₀))
  filter_upwards [hlarge] with x hx
  intro l
  have hlogone : 1 ≤ Real.log (x : ℝ) :=
    (le_max_left 1 Q₀).trans hx
  have hQlog : Q₀ ≤ Real.log (x : ℝ) :=
    (le_max_right 1 Q₀).trans hx
  have hQbase : Q₀ ≤ Real.log (x : ℝ) ^ 100 := by
    calc
      Q₀ ≤ Real.log (x : ℝ) := hQlog
      _ = Real.log (x : ℝ) ^ 1 := by rw [pow_one]
      _ ≤ Real.log (x : ℝ) ^ 100 :=
        pow_le_pow_right₀ hlogone (by norm_num)
  have hbaseScale :
      Real.log (x : ℝ) ^ 100 ≤ lemma6DyadicModulusScale x l := by
    unfold lemma6DyadicModulusScale
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (by positivity : 0 ≤ Real.log (x : ℝ) ^ 100))
  exact hQ₀ _ (hQbase.trans hbaseScale)

/-- Equation (18), in the pointwise squared form actually used on a
dyadic modulus block in equations (19) and (20). -/
theorem lemma6_equation18_sq_le_on_modulusBlock
    {x l d : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hd : d ∈ lemma6ModulusBlock x l) :
    ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
      lemma6ExceptionalFactorAt x l := by
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (l - 1) :=
    one_le_pow₀ (by norm_num)
  have hlogpow : 0 ≤ Real.log (x : ℝ) ^ 100 :=
    hxlarge.trans' (Real.exp_pos _).le
  have hlower : Real.exp (Real.exp 1) ≤
      (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 := by
    calc
      Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100 := hxlarge
      _ = 1 * Real.log (x : ℝ) ^ 100 := by rw [one_mul]
      _ ≤ (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 :=
        mul_le_mul_of_nonneg_right hpow hlogpow
  have hdlarge : Real.exp (Real.exp 1) < (d : ℝ) :=
    hlower.trans_lt hddata.2.2.1
  have hd2 : 2 ≤ d := by
    have htwo : (2 : ℝ) < Real.exp (Real.exp 1) := by
      exact Real.exp_one_gt_two.trans
        (Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr zero_lt_one))
    exact_mod_cast (htwo.trans hdlarge).le
  have hμ : ArithmeticFunction.moebius d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hddata.2.1
  exact lemma6_equation18_sq_le_exceptionalFactor hμ hd2 hdlarge
    hddata.2.2.2

/-- For all sufficiently large `x`, the equation-(18) exceptional factor
uniformly controls every modulus in every dyadic block. -/
theorem eventually_lemma6_equation18_sq_le_on_modulusBlock :
    ∀ᶠ x : ℕ in atTop, ∀ l d : ℕ,
      d ∈ lemma6ModulusBlock x l →
        ((3 : ℝ) ^ distinctPrimeFactors d) ^ 2 ≤
          lemma6ExceptionalFactorAt x l := by
  filter_upwards [eventually_exp_exp_one_le_log_pow_hundred] with x hx
  intro l d hd
  exact lemma6_equation18_sq_le_on_modulusBlock hx hd

/-- Weighted Cauchy--Schwarz after equation (17), with equation (18)
already absorbed uniformly over the modulus block.  The auxiliary index
type can include both a modulus and a primitive character. -/
theorem lemma6_weighted_cauchy_on_modulusBlock
    {ι : Type*} (s : Finset ι) (modulus : ι → ℕ)
    (w f g : ι → ℝ) {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hmodulus : ∀ i ∈ s, modulus i ∈ lemma6ModulusBlock x l)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s,
        w i * (3 : ℝ) ^ distinctPrimeFactors (modulus i) * f i * g i) ^ 2 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ s, w i * f i ^ 2) *
        ∑ i ∈ s, w i * g i ^ 2 := by
  apply weighted_cauchy_sq_of_sq_le
  · exact hw
  · exact (lemma6ExceptionalFactor_pos _).le
  · intro i hi
    exact lemma6_equation18_sq_le_on_modulusBlock hxlarge
      (hmodulus i hi)

/-- The `2,4,4` Hölder estimate used for the `B` integral in equation
(19), again with equation (18) already absorbed into `I_{l,x}`. -/
theorem lemma6_weighted_holder_244_on_modulusBlock
    {ι : Type*} (s : Finset ι) (modulus : ι → ℕ)
    (w f g h : ι → ℝ) {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (hmodulus : ∀ i ∈ s, modulus i ∈ lemma6ModulusBlock x l)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) :
    (∑ i ∈ s,
        w i * (3 : ℝ) ^ distinctPrimeFactors (modulus i) *
          f i * g i * h i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ s, w i * f i ^ 2) ^ 2 *
        (∑ i ∈ s, w i * g i ^ 4) *
          ∑ i ∈ s, w i * h i ^ 4 := by
  apply weighted_holder_244_pow_four_of_sq_le
  · exact hw
  · intro i hi
    positivity
  · exact hf
  · exact hg
  · exact hh
  · exact (lemma6ExceptionalFactor_pos _).le
  · intro i hi
    exact lemma6_equation18_sq_le_on_modulusBlock hxlarge
      (hmodulus i hi)

/-- Every squarefree conductor above `(log x)^100` and at most `x` belongs
to a positive dyadic modulus block. -/
theorem exists_mem_lemma6ModulusBlock
    {x d : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ))
    (hdlarge : Real.log (x : ℝ) ^ 100 < (d : ℝ))
    (hdsq : Squarefree d) (hdx : d ≤ x) :
    ∃ l : ℕ, 1 ≤ l ∧ d ∈ lemma6ModulusBlock x l := by
  let T : ℝ := Real.log (x : ℝ) ^ 100
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hr : (1 : ℝ) < (d : ℝ) / T := by
    rw [lt_div_iff₀ hTpos]
    simpa only [one_mul, T] using hdlarge
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_nat_pow_near hr.le (by norm_num : (1 : ℝ) < 2)
  have hdmem : d ∈ Finset.range (x + 1) :=
    Finset.mem_range.mpr (by omega)
  by_cases heq : (2 : ℝ) ^ n = (d : ℝ) / T
  · have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      subst n
      norm_num at heq
      linarith
    refine ⟨n, by omega, ?_⟩
    rw [lemma6ModulusBlock, Finset.mem_filter]
    refine ⟨hdmem, hdsq, ?_, ?_⟩
    · have hpow : (2 : ℝ) ^ (n - 1) < (2 : ℝ) ^ n :=
        pow_lt_pow_right₀ (by norm_num) (Nat.sub_one_lt hnpos.ne')
      calc
        (2 : ℝ) ^ (n - 1) * Real.log (x : ℝ) ^ 100 =
            (2 : ℝ) ^ (n - 1) * T := by rfl
        _ < (2 : ℝ) ^ n * T := mul_lt_mul_of_pos_right hpow hTpos
        _ = ((d : ℝ) / T) * T := by rw [heq]
        _ = d := div_mul_cancel₀ _ hTpos.ne'
    · calc
        (d : ℝ) = ((d : ℝ) / T) * T :=
          (div_mul_cancel₀ _ hTpos.ne').symm
        _ = (2 : ℝ) ^ n * T := by rw [heq]
        _ ≤ (2 : ℝ) ^ n * Real.log (x : ℝ) ^ 100 := by rfl
  · refine ⟨n + 1, by omega, ?_⟩
    rw [lemma6ModulusBlock, Finset.mem_filter]
    refine ⟨hdmem, hdsq, ?_, ?_⟩
    · have hnlow' : (2 : ℝ) ^ n < (d : ℝ) / T :=
        lt_of_le_of_ne hnlow heq
      calc
        (2 : ℝ) ^ (n + 1 - 1) * Real.log (x : ℝ) ^ 100 =
            (2 : ℝ) ^ n * T := by congr 2
        _ < ((d : ℝ) / T) * T :=
          mul_lt_mul_of_pos_right hnlow' hTpos
        _ = d := div_mul_cancel₀ _ hTpos.ne'
    · calc
        (d : ℝ) = ((d : ℝ) / T) * T :=
          (div_mul_cancel₀ _ hTpos.ne').symm
        _ ≤ (2 : ℝ) ^ (n + 1) * T :=
          (mul_lt_mul_of_pos_right hnup hTpos).le
        _ = (2 : ℝ) ^ (n + 1) * Real.log (x : ℝ) ^ 100 := by rfl

/-- The half-open dyadic convention makes the block index unique. -/
theorem lemma6ModulusBlock_index_unique
    {x d l k : ℕ}
    (hdl : d ∈ lemma6ModulusBlock x l)
    (hdk : d ∈ lemma6ModulusBlock x k) :
    l = k := by
  have hldata := hdl
  have hkdata := hdk
  rw [lemma6ModulusBlock, Finset.mem_filter] at hldata hkdata
  rcases lt_trichotomy l k with hlk | rfl | hkl
  · have hexp : l ≤ k - 1 := by omega
    have hpow : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ (k - 1) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul : (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 ≤
        (2 : ℝ) ^ (k - 1) * Real.log (x : ℝ) ^ 100 :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    linarith [hldata.2.2.2, hkdata.2.2.1]
  · rfl
  · have hexp : k ≤ l - 1 := by omega
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (l - 1) :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul : (2 : ℝ) ^ k * Real.log (x : ℝ) ^ 100 ≤
        (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    linarith [hkdata.2.2.2, hldata.2.2.1]

/-- Canonical index of a modulus block.  The fallback value is irrelevant
outside the union of the blocks. -/
noncomputable def lemma6ModulusBlockIndex (x d : ℕ) : ℕ :=
  if h : ∃ l : ℕ, d ∈ lemma6ModulusBlock x l then Nat.find h else 0

theorem lemma6ModulusBlockIndex_mem
    {x d : ℕ} (h : ∃ l : ℕ, d ∈ lemma6ModulusBlock x l) :
    d ∈ lemma6ModulusBlock x (lemma6ModulusBlockIndex x d) := by
  rw [lemma6ModulusBlockIndex, dif_pos h]
  exact Nat.find_spec h

/-- On an actual block, the canonical index is that block's index. -/
theorem lemma6ModulusBlockIndex_eq
    {x d l : ℕ} (hd : d ∈ lemma6ModulusBlock x l) :
    lemma6ModulusBlockIndex x d = l :=
  lemma6ModulusBlock_index_unique
    (lemma6ModulusBlockIndex_mem ⟨l, hd⟩) hd

/-- The `k`-th dyadic prime-pair block in equation (13). -/
noncomputable def lemma6PairBlock (x k : ℕ) : Finset (ℕ × ℕ) :=
  (chenPairs x).filter fun q =>
    (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30) <
        (q.1 * q.2 : ℕ) ∧
      ((q.1 * q.2 : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (k + 1) * (x : ℝ) ^ ((13 : ℝ) / 30)

/-- Every Chen prime pair lies above the initial product scale
`x^(13/30)`. -/
theorem chenPair_product_lower
    {x : ℕ} (hx : 1 ≤ x) {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    (x : ℝ) ^ ((13 : ℝ) / 30) < (q.1 * q.2 : ℕ) := by
  have hqdata := (Finset.mem_filter.mp hq).2
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  calc
    (x : ℝ) ^ ((13 : ℝ) / 30) =
        (x : ℝ) ^ ((1 : ℝ) / 10) *
          (x : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    _ < (q.1 : ℝ) * q.2 := by
      exact mul_lt_mul hqdata.2.2.1 hqdata.2.2.2.2.1.le
        (Real.rpow_pos_of_pos hxpos _) (by positivity)
    _ = (q.1 * q.2 : ℕ) := by norm_num

/-- Every Chen prime pair belongs to a pair-product dyadic block. -/
theorem exists_mem_lemma6PairBlock
    {x : ℕ} (hx : 1 ≤ x) {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    ∃ k : ℕ, q ∈ lemma6PairBlock x k := by
  let T : ℝ := (x : ℝ) ^ ((13 : ℝ) / 30)
  let p : ℝ := (q.1 * q.2 : ℕ)
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hpT : T < p := by
    simpa only [T, p] using chenPair_product_lower hx hq
  have hr : (1 : ℝ) < p / T := by
    rw [lt_div_iff₀ hTpos]
    simpa only [one_mul] using hpT
  obtain ⟨n, hnlow, hnup⟩ :=
    exists_nat_pow_near hr.le (by norm_num : (1 : ℝ) < 2)
  by_cases heq : (2 : ℝ) ^ n = p / T
  · have hnpos : 0 < n := by
      by_contra hn
      have hnzero : n = 0 := by omega
      subst n
      norm_num at heq
      linarith
    refine ⟨n - 1, ?_⟩
    rw [lemma6PairBlock, Finset.mem_filter]
    refine ⟨hq, ?_, ?_⟩
    · have hpow : (2 : ℝ) ^ (n - 1) < (2 : ℝ) ^ n :=
        pow_lt_pow_right₀ (by norm_num) (Nat.sub_one_lt hnpos.ne')
      change (2 : ℝ) ^ (n - 1) * T < p
      calc
        (2 : ℝ) ^ (n - 1) * T < (2 : ℝ) ^ n * T :=
          mul_lt_mul_of_pos_right hpow hTpos
        _ = (p / T) * T := by rw [heq]
        _ = p := div_mul_cancel₀ _ hTpos.ne'
    · change p ≤ (2 : ℝ) ^ (n - 1 + 1) * T
      calc
        p = (p / T) * T := (div_mul_cancel₀ _ hTpos.ne').symm
        _ = (2 : ℝ) ^ n * T := by rw [heq]
        _ ≤ (2 : ℝ) ^ (n - 1 + 1) * T := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  · refine ⟨n, ?_⟩
    rw [lemma6PairBlock, Finset.mem_filter]
    refine ⟨hq, ?_, ?_⟩
    · have hnlow' : (2 : ℝ) ^ n < p / T :=
        lt_of_le_of_ne hnlow heq
      change (2 : ℝ) ^ n * T < p
      calc
        (2 : ℝ) ^ n * T < (p / T) * T :=
          mul_lt_mul_of_pos_right hnlow' hTpos
        _ = p := div_mul_cancel₀ _ hTpos.ne'
    · change p ≤ (2 : ℝ) ^ (n + 1) * T
      calc
        p = (p / T) * T := (div_mul_cancel₀ _ hTpos.ne').symm
        _ ≤ (2 : ℝ) ^ (n + 1) * T :=
          (mul_lt_mul_of_pos_right hnup hTpos).le

/-- Pair-product dyadic blocks are disjoint. -/
theorem lemma6PairBlock_index_unique
    {x : ℕ} {q : ℕ × ℕ} {k j : ℕ}
    (hqk : q ∈ lemma6PairBlock x k)
    (hqj : q ∈ lemma6PairBlock x j) :
    k = j := by
  have hkdata := (Finset.mem_filter.mp hqk).2
  have hjdata := (Finset.mem_filter.mp hqj).2
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · have hexp : k + 1 ≤ j := by omega
    have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul :
        (2 : ℝ) ^ (k + 1) * (x : ℝ) ^ ((13 : ℝ) / 30) ≤
          (2 : ℝ) ^ j * (x : ℝ) ^ ((13 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (by positivity) _)
    linarith [hkdata.2, hjdata.1]
  · rfl
  · have hexp : j + 1 ≤ k := by omega
    have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) hexp
    have hmul :
        (2 : ℝ) ^ (j + 1) * (x : ℝ) ^ ((13 : ℝ) / 30) ≤
          (2 : ℝ) ^ k * (x : ℝ) ^ ((13 : ℝ) / 30) :=
      mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (by positivity) _)
    linarith [hjdata.2, hkdata.1]

/-- Canonical `k`-index of a Chen prime pair. -/
noncomputable def lemma6PairBlockIndex (x : ℕ) (q : ℕ × ℕ) : ℕ :=
  if h : ∃ k : ℕ, q ∈ lemma6PairBlock x k then Nat.find h else 0

theorem lemma6PairBlockIndex_mem
    {x : ℕ} {q : ℕ × ℕ}
    (h : ∃ k : ℕ, q ∈ lemma6PairBlock x k) :
    q ∈ lemma6PairBlock x (lemma6PairBlockIndex x q) := by
  rw [lemma6PairBlockIndex, dif_pos h]
  exact Nat.find_spec h

theorem lemma6PairBlockIndex_eq
    {x k : ℕ} {q : ℕ × ℕ} (hq : q ∈ lemma6PairBlock x k) :
    lemma6PairBlockIndex x q = k :=
  lemma6PairBlock_index_unique (lemma6PairBlockIndex_mem ⟨k, hq⟩) hq

/-- Comparison between the integer binary logarithm used to count dyadic
blocks and the real logarithm used in the analytic estimates. -/
theorem natLog_two_cast_le {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have hn0 : n ≠ 0 := by omega
  have hpowNat : (2 : ℕ) ^ Nat.log 2 n ≤ n :=
    Nat.pow_log_le_self 2 hn0
  have hpowR : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  simpa [mul_comm] using hlog

end Chen

end

/-! ## ChenTheorem.Lemma6.BlockIntegrand -/

section

/-
The prime-pair Dirichlet polynomial and the `A`, `B` summands introduced
between equations (16) and (17) in Chen's proof of Lemma 6.

The set of prime pairs is kept as an explicit finite parameter here.  In
`Core.lean` it is instantiated by one admissible `(k,m)` block.
-/

open Real
open scoped Classical

namespace Chen

/-- Prime pairs surviving the cofactor coprimality condition in `N_m`. -/
noncomputable def lemma6AdmissiblePairs (x m : ℕ) : Finset (ℕ × ℕ) :=
  (chenPairs x).filter (fun q => Nat.Coprime (q.1 * q.2) m)

/-- The finite set of pair-product dyadic indices occupied for a fixed
cofactor. -/
noncomputable def lemma6PairBlockIndices (x m : ℕ) : Finset ℕ :=
  (lemma6AdmissiblePairs x m).image (lemma6PairBlockIndex x)

/-- The actual admissible `(k,m)` prime-pair block from equation (13). -/
noncomputable def lemma6AdmissiblePairBlock
    (x m k : ℕ) : Finset (ℕ × ℕ) :=
  (lemma6AdmissiblePairs x m).filter
    (fun q => q ∈ lemma6PairBlock x k)

/-- The prime-pair Dirichlet polynomial occurring in `A(l,k,s,m,H)` and
`B(l,k,s,m,H)`. -/
noncomputable def lemma6PairDirichletPolynomial
    {d : ℕ} (x : ℕ) (pairs : Finset (ℕ × ℕ)) (s : ℂ)
    (χ : DirichletCharacter ℂ d) : ℂ :=
  ∑ q ∈ pairs,
    χ (q.1 * q.2 : ZMod d) /
      (((q.1 * q.2 : ℕ) : ℂ) ^ s *
        (Real.log ((x : ℝ) / ((q.1 * q.2 : ℕ) : ℝ)) : ℂ))

/-- The prime-pair polynomial specialized to the actual `(k,m)` block. -/
noncomputable def lemma6PairBlockPolynomial
    {d : ℕ} (x m k : ℕ) (s : ℂ)
    (χ : DirichletCharacter ℂ d) : ℂ :=
  lemma6PairDirichletPolynomial x
    (lemma6AdmissiblePairBlock x m k) s χ

/-- Membership in an actual admissible pair block exposes the two
primality hypotheses used both by Mellin inversion and by holomorphy of
the associated Dirichlet polynomial. -/
theorem primes_of_mem_lemma6AdmissiblePairBlock
    {x m k : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ lemma6AdmissiblePairBlock x m k) :
    q.1.Prime ∧ q.2.Prime := by
  have hqadmissible : q ∈ lemma6AdmissiblePairs x m :=
    (Finset.mem_filter.mp hq).1
  have hqchen : q ∈ chenPairs x :=
    (Finset.mem_filter.mp hqadmissible).1
  have hqdata := (Finset.mem_filter.mp hqchen).2
  exact ⟨hqdata.1, hqdata.2.1⟩

/-- The actual prime-pair block is an entire Dirichlet polynomial in its
complex argument.  The possible zero of the fixed logarithmic denominator
is harmless because Lean's division is totalized; it gives the constant
zero summand in that case. -/
theorem differentiable_lemma6PairBlockPolynomial
    {d : ℕ} (x m k : ℕ) (χ : DirichletCharacter ℂ d) :
    Differentiable ℂ (fun s => lemma6PairBlockPolynomial x m k s χ) := by
  unfold lemma6PairBlockPolynomial lemma6PairDirichletPolynomial
  simp only [Nat.cast_mul]
  apply Differentiable.fun_sum
  intro q hq
  obtain ⟨hp1, hp2⟩ := primes_of_mem_lemma6AdmissiblePairBlock hq
  have hn0 : (q.1 * q.2 : ℂ) ≠ 0 := by
    norm_cast
    exact Nat.mul_ne_zero hp1.ne_zero hp2.ne_zero
  letI : NeZero (q.1 * q.2 : ℂ) := ⟨hn0⟩
  have hpow : Differentiable ℂ (fun s : ℂ => (q.1 * q.2 : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero _
  by_cases hlog : Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) = 0
  · have hlogC :
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ) = 0 := by
      exact_mod_cast hlog
    simp only [hlogC, mul_zero, div_zero]
    exact differentiable_const _
  · have hden : Differentiable ℂ (fun s : ℂ =>
        (q.1 * q.2 : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ)) := by
      fun_prop
    have hdeninv : Differentiable ℂ (fun s : ℂ =>
        ((q.1 * q.2 : ℂ) ^ s *
          (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)) : ℂ))⁻¹) :=
      hden.inv (fun s => mul_ne_zero
        (Complex.cpow_ne_zero_iff.mpr (Or.inl hn0))
        (Complex.ofReal_ne_zero.mpr hlog))
    have hmul := hdeninv.const_mul
      (χ (q.1 : ZMod d) * χ (q.2 : ZMod d))
    simpa only [div_eq_mul_inv, Nat.cast_mul, map_mul] using hmul

/-- The one-modulus `A` summand after equation (16). -/
noncomputable def lemma6AModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) : ℝ :=
  primSum d (fun χ =>
    ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
      ‖1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ‖)

/-- The raw first summand obtained directly from equation (16), before
using the standard bound for `L'/L` on `Re s > 1`.  Chen absorbs that bound
into the factor `x (log x)^2` preceding the printed `A` integral. -/
noncomputable def lemma6RawAModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) : ℝ :=
  primSum d (fun χ =>
    ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
      ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ *
      ‖1 - DirichletCharacter.LFunction χ s *
        lemma6MollifierAt H s χ‖)

/-- The one-modulus `B` summand after equation (16). -/
noncomputable def lemma6BModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) : ℝ :=
  primSum d (fun χ =>
    ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
      ‖deriv (DirichletCharacter.LFunction χ) s‖ *
      ‖lemma6MollifierAt H s χ‖)

/-- Summing the pointwise equation-(16) norm split over primitive
characters gives the raw `A + B` decomposition preceding (17). -/
theorem lemma6_primitive_logDeriv_sum_le_rawA_add_B_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      lemma6RawAModulus (d := d) x H pairs (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  simp only [lemma6RawAModulus, lemma6BModulus, primSum, tsum_fintype]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ.IsPrimitive
  · simp only [hχ, if_true]
    exact lemma6_pair_mul_logDeriv_norm_le_A_add_B (H := H) hx ν χ
      (lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ)
  · simp only [hχ, if_false]
    norm_num

/-- The explicit interface for the standard `L'/L` bound that Chen absorbs
into the factor `(log x)^2` in (17).  Once a uniform bound `C` is supplied,
the raw first summand is at most `C` times the printed `A` summand. -/
theorem lemma6RawAModulus_le_mul_AModulus
    {d : ℕ} [NeZero d] (x H : ℕ) (pairs : Finset (ℕ × ℕ))
    (s : ℂ) {C : ℝ}
    (hlogDeriv : ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive →
      ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤ C) :
    lemma6RawAModulus (d := d) x H pairs s ≤
      C * lemma6AModulus (d := d) x H pairs s := by
  simp only [lemma6RawAModulus, lemma6AModulus, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ.IsPrimitive
  · simp only [hχ, if_true]
    calc
      ‖lemma6PairDirichletPolynomial x pairs s χ‖ *
            ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ *
          ‖1 - DirichletCharacter.LFunction χ s *
            lemma6MollifierAt H s χ‖ ≤
        ‖lemma6PairDirichletPolynomial x pairs s χ‖ * C *
          ‖1 - DirichletCharacter.LFunction χ s *
            lemma6MollifierAt H s χ‖ := by
          gcongr
          exact hlogDeriv χ hχ
      _ = C *
          (‖lemma6PairDirichletPolynomial x pairs s χ‖ *
            ‖1 - DirichletCharacter.LFunction χ s *
              lemma6MollifierAt H s χ‖) := by ring
  · simp only [hχ, if_false, mul_zero]
    exact le_rfl

/-- On Chen's `α`-line, the raw `A` summand is controlled by the universal
von Mangoldt majorant times the printed `A` summand. -/
theorem lemma6RawAModulus_le_majorant_mul_AModulus_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    lemma6RawAModulus (d := d) x H pairs (lemma6AlphaPoint x ν) ≤
      lemma6LogDerivMajorant (lemma6AlphaPoint x ν) *
        lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  apply lemma6RawAModulus_le_mul_AModulus
  intro χ hχ
  exact lemma6_norm_logDeriv_le_majorant χ
    (one_lt_lemma6AlphaPoint_re hx ν)

/-- Equation (16) followed by the standard majorization step that produces
the two printed integrands `A` and `B` in equation (17). -/
theorem lemma6_primitive_logDeriv_sum_le_majorant_mul_A_add_B_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      lemma6LogDerivMajorant (lemma6AlphaPoint x ν) *
          lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  have hsplit :=
    lemma6_primitive_logDeriv_sum_le_rawA_add_B_at_alpha
      (d := d) (H := H) hx pairs ν
  have hraw :=
    lemma6RawAModulus_le_majorant_mul_AModulus_at_alpha
      (d := d) (H := H) hx pairs ν
  exact hsplit.trans (add_le_add hraw le_rfl)

/-- The raw `A` summand with Chen's explicit `(log x)^2` loss. -/
theorem lemma6RawAModulus_le_four_log_sq_mul_AModulus_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    lemma6RawAModulus (d := d) x H pairs (lemma6AlphaPoint x ν) ≤
      (4 * Real.log (x : ℝ) ^ 2) *
        lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  apply lemma6RawAModulus_le_mul_AModulus
  intro χ hχ
  exact (lemma6_norm_logDeriv_le_majorant χ
    (one_lt_lemma6AlphaPoint_re hx ν)).trans
      (lemma6LogDerivMajorant_alpha_le hx ν)

/-- The complete one-modulus equation-(16) estimate in the normalization
used in equation (17): `4 (log x)^2 A + B`. -/
theorem lemma6_primitive_logDeriv_sum_le_four_log_sq_mul_A_add_B_at_alpha
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (pairs : Finset (ℕ × ℕ)) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairDirichletPolynomial x pairs (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      (4 * Real.log (x : ℝ) ^ 2) *
          lemma6AModulus (d := d) x H pairs (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H pairs (lemma6AlphaPoint x ν) := by
  have hsplit :=
    lemma6_primitive_logDeriv_sum_le_rawA_add_B_at_alpha
      (d := d) (H := H) hx pairs ν
  have hraw :=
    lemma6RawAModulus_le_four_log_sq_mul_AModulus_at_alpha
      (d := d) (H := H) hx pairs ν
  exact hsplit.trans (add_le_add hraw le_rfl)

/-- The equation-(17) one-modulus estimate for the project's actual
admissible `(k,m)` prime-pair block. -/
theorem lemma6_pairBlock_logDeriv_sum_le_four_log_sq_mul_A_add_B
    {d x H : ℕ} [NeZero d] (hx : 2 ≤ x)
    (m k : ℕ) (ν : ℝ) :
    primSum d (fun χ =>
        ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
          (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
            DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖) ≤
      (4 * Real.log (x : ℝ) ^ 2) *
          lemma6AModulus (d := d) x H
            (lemma6AdmissiblePairBlock x m k) (lemma6AlphaPoint x ν) +
        lemma6BModulus (d := d) x H
          (lemma6AdmissiblePairBlock x m k) (lemma6AlphaPoint x ν) := by
  simpa only [lemma6PairBlockPolynomial] using
    lemma6_primitive_logDeriv_sum_le_four_log_sq_mul_A_add_B_at_alpha
      (d := d) (H := H) hx (lemma6AdmissiblePairBlock x m k) ν

/-- The printed `A` summand, totalized at modulus zero so it can be summed
over an unrestricted finite set of natural moduli. -/
noncomputable def lemma6AModulusTotal
    (d x m k H : ℕ) (s : ℂ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    lemma6AModulus (d := d) x H
      (lemma6AdmissiblePairBlock x m k) s

/-- The `B` summand, totalized at modulus zero. -/
noncomputable def lemma6BModulusTotal
    (d x m k H : ℕ) (s : ℂ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    lemma6BModulus (d := d) x H
      (lemma6AdmissiblePairBlock x m k) s

/-- The unsplit logarithmic-derivative summand on the `α`-line,
totalized at modulus zero. -/
noncomputable def lemma6LogDerivModulusAtAlpha
    (d x m k : ℕ) (ν : ℝ) : ℝ :=
  if hd : d = 0 then 0
  else
    letI : NeZero d := ⟨hd⟩
    primSum d (fun χ =>
      ‖lemma6PairBlockPolynomial x m k (lemma6AlphaPoint x ν) χ *
        (deriv (DirichletCharacter.LFunction χ) (lemma6AlphaPoint x ν) /
          DirichletCharacter.LFunction χ (lemma6AlphaPoint x ν))‖)

theorem lemma6LogDerivModulusAtAlpha_le
    (d : ℕ) {x H : ℕ} (hx : 2 ≤ x) (m k : ℕ) (ν : ℝ) :
    lemma6LogDerivModulusAtAlpha d x m k ν ≤
      (4 * Real.log (x : ℝ) ^ 2) *
          lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) +
        lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν) := by
  by_cases hd : d = 0
  · simp [lemma6LogDerivModulusAtAlpha, lemma6AModulusTotal,
      lemma6BModulusTotal, hd]
  · letI : NeZero d := ⟨hd⟩
    simp only [lemma6LogDerivModulusAtAlpha, lemma6AModulusTotal,
      lemma6BModulusTotal, dif_neg hd]
    exact lemma6_pairBlock_logDeriv_sum_le_four_log_sq_mul_A_add_B
      (d := d) (H := H) hx m k ν

/-- The equation-(17) `A` sum over one dyadic modulus block. -/
noncomputable def lemma6ABlockAtAlpha
    (x m l k H : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d *
      lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)

/-- The equation-(17) `B` sum on the original `α`-line over one dyadic
modulus block.  Moving this term to `β` is the next contour step. -/
noncomputable def lemma6BBlockAtAlpha
    (x m l k H : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d *
      lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν)

/-- The unsplit logarithmic-derivative sum over one dyadic modulus block. -/
noncomputable def lemma6LogDerivBlockAtAlpha
    (x m l k : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d * lemma6LogDerivModulusAtAlpha d x m k ν

/-- Blockwise form of equation (16), in the normalization used at the
start of equation (17). -/
theorem lemma6LogDerivBlockAtAlpha_le
    {x H : ℕ} (hx : 2 ≤ x) (m l k : ℕ) (ν : ℝ) :
    lemma6LogDerivBlockAtAlpha x m l k ν ≤
      (4 * Real.log (x : ℝ) ^ 2) * lemma6ABlockAtAlpha x m l k H ν +
        lemma6BBlockAtAlpha x m l k H ν := by
  unfold lemma6LogDerivBlockAtAlpha lemma6ABlockAtAlpha
    lemma6BBlockAtAlpha
  calc
    (∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d * lemma6LogDerivModulusAtAlpha d x m k ν) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        lemma6LinearWeight d *
          ((4 * Real.log (x : ℝ) ^ 2) *
              lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν) +
            lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (lemma6LogDerivModulusAtAlpha_le d hx m k ν)
        (lemma6LinearWeight_nonneg d)
    _ = ∑ d ∈ lemma6ModulusBlock x l,
          ((4 * Real.log (x : ℝ) ^ 2) *
              (lemma6LinearWeight d *
                lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)) +
            lemma6LinearWeight d *
              lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν)) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = (4 * Real.log (x : ℝ) ^ 2) *
          (∑ d ∈ lemma6ModulusBlock x l,
            lemma6LinearWeight d *
              lemma6AModulusTotal d x m k H (lemma6AlphaPoint x ν)) +
        ∑ d ∈ lemma6ModulusBlock x l,
          lemma6LinearWeight d *
            lemma6BModulusTotal d x m k H (lemma6AlphaPoint x ν) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- All characters over one dyadic modulus block, represented by a single
finite dependent index set. -/
noncomputable def lemma6CharacterBlock (x l : ℕ) :
    Finset (Σ d : ℕ, DirichletCharacter ℂ d) :=
  (lemma6ModulusBlock x l).sigma fun _d => Finset.univ

/-- The nonnegative base weight `|μ(d)|/d`, with nonprimitive characters
assigned weight zero.  The exceptional factor `3^ν(d)` remains separate
so equation (18) can absorb it. -/
noncomputable def lemma6PrimitiveBaseWeight
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  (|((ArithmeticFunction.moebius i.1 : ℤ) : ℝ)| / (i.1 : ℝ)) *
    if i.2.IsPrimitive then 1 else 0

theorem lemma6PrimitiveBaseWeight_nonneg
    (i : Σ d : ℕ, DirichletCharacter ℂ d) :
    0 ≤ lemma6PrimitiveBaseWeight i := by
  unfold lemma6PrimitiveBaseWeight
  positivity

/-- Norm of the actual prime-pair polynomial at a character-block index. -/
noncomputable def lemma6PairBlockNorm
    (x m k : ℕ) (s : ℂ)
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  ‖lemma6PairBlockPolynomial x m k s i.2‖

/-- Norm of `1-LS`, the second factor in the printed `A` integrand. -/
noncomputable def lemma6RemainderNorm
    (H : ℕ) (s : ℂ)
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  if hd : i.1 = 0 then 0
  else
    letI : NeZero i.1 := ⟨hd⟩
    ‖1 - DirichletCharacter.LFunction i.2 s * lemma6MollifierAt H s i.2‖

/-- Norm of the Möbius mollifier in the `B` integrand. -/
noncomputable def lemma6MollifierNorm
    (H : ℕ) (s : ℂ)
    (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  ‖lemma6MollifierAt H s i.2‖

/-- Norm of `L'` in the `B` integrand. -/
noncomputable def lemma6LDerivNorm
    (s : ℂ) (i : Σ d : ℕ, DirichletCharacter ℂ d) : ℝ :=
  if hd : i.1 = 0 then 0
  else
    letI : NeZero i.1 := ⟨hd⟩
    ‖deriv (DirichletCharacter.LFunction i.2) s‖

/-- The `B` block after moving the contour from `α` to `β`.  Keeping this
as a separate definition makes the still-required contour-shift step
explicit rather than silently identifying the two lines. -/
noncomputable def lemma6BBlockAtBeta
    (x m l k H : ℕ) (ν : ℝ) : ℝ :=
  ∑ d ∈ lemma6ModulusBlock x l,
    lemma6LinearWeight d *
      lemma6BModulusTotal d x m k H (lemma6BetaPoint x ν)

/-- Expand the equation-(17) `A` block into the single dependent character
block used by the moment inequalities. -/
theorem lemma6ABlockAtAlpha_eq_characterBlock_sum
    (x m l k H : ℕ) (ν : ℝ) :
    lemma6ABlockAtAlpha x m l k H ν =
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i *
          lemma6RemainderNorm H (lemma6AlphaPoint x ν) i := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  unfold lemma6ABlockAtAlpha
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by
    have hdmem := hd
    rw [lemma6ModulusBlock, Finset.mem_filter] at hdmem
    by_contra h
    subst d
    norm_num at hdmem
  simp only [lemma6LinearWeight, lemma6AModulusTotal, hd0, ↓reduceDIte,
    lemma6AModulus, lemma6PrimitiveBaseWeight, lemma6PairBlockNorm,
    lemma6PairBlockPolynomial, lemma6RemainderNorm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    ring
  · simp [hp]

/-- Expand the shifted `B` block into the dependent character block used
by equations (19) and (20). -/
theorem lemma6BBlockAtBeta_eq_characterBlock_sum
    (x m l k H : ℕ) (ν : ℝ) :
    lemma6BBlockAtBeta x m l k H ν =
      ∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  unfold lemma6BBlockAtBeta
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by
    have hdmem := hd
    rw [lemma6ModulusBlock, Finset.mem_filter] at hdmem
    by_contra h
    subst d
    norm_num at hdmem
  simp only [lemma6LinearWeight, lemma6BModulusTotal, hd0, ↓reduceDIte,
    lemma6BModulus, lemma6PrimitiveBaseWeight, lemma6PairBlockNorm,
    lemma6PairBlockPolynomial, lemma6MollifierNorm, lemma6LDerivNorm,
    primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    ring
  · simp [hp]

/-- Formula (19), `A` part: weighted Cauchy--Schwarz on the actual
modulus/primitive-character block, with equation (18) absorbed into
`I_{l,x}`. -/
theorem lemma6_equation19_A_cauchy
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i *
          lemma6RemainderNorm H (lemma6AlphaPoint x ν) i) ^ 2 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν) i ^ 2) *
        ∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6RemainderNorm H (lemma6AlphaPoint x ν) i ^ 2 := by
  apply lemma6_weighted_cauchy_on_modulusBlock
      (lemma6CharacterBlock x l) (fun i => i.1)
      lemma6PrimitiveBaseWeight
      (lemma6PairBlockNorm x m k (lemma6AlphaPoint x ν))
      (lemma6RemainderNorm H (lemma6AlphaPoint x ν)) hxlarge
  · intro i hi
    rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
    exact hi.1
  · intro i hi
    exact lemma6PrimitiveBaseWeight_nonneg i

/-- Formula (19), `B` part: the weighted `2,4,4` Hölder inequality for
the prime-pair polynomial, mollifier, and `L'` fourth moments on `β+iν`. -/
theorem lemma6_equation19_B_holder
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4 := by
  apply lemma6_weighted_holder_244_on_modulusBlock
      (lemma6CharacterBlock x l) (fun i => i.1)
      lemma6PrimitiveBaseWeight
      (lemma6PairBlockNorm x m k (lemma6BetaPoint x ν))
      (lemma6MollifierNorm H (lemma6BetaPoint x ν))
      (lemma6LDerivNorm (lemma6BetaPoint x ν)) hxlarge
  · intro i hi
    rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
    exact hi.1
  · intro i hi
    exact lemma6PrimitiveBaseWeight_nonneg i
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    unfold lemma6LDerivNorm
    split_ifs <;> positivity

/-- Formula (20), `B` part: the same weighted `2,4,4` Hölder inequality,
but with the mollifier in the second moment and the pair polynomial in the
fourth moment.  This is the factor ordering printed across pages 12--13. -/
theorem lemma6_equation20_B_holder
    {x l : ℕ}
    (hxlarge : Real.exp (Real.exp 1) ≤ Real.log (x : ℝ) ^ 100)
    (m k H : ℕ) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          (3 : ℝ) ^ distinctPrimeFactors i.1 *
          lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i) ^ 4 ≤
      (lemma6ExceptionalFactorAt x l *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ^ 2 *
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) *
          ∑ i ∈ lemma6CharacterBlock x l,
            lemma6PrimitiveBaseWeight i *
              lemma6PairBlockNorm x m k (lemma6BetaPoint x ν) i ^ 4 := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (lemma6_weighted_holder_244_on_modulusBlock
      (lemma6CharacterBlock x l) (fun i => i.1)
      lemma6PrimitiveBaseWeight
      (lemma6MollifierNorm H (lemma6BetaPoint x ν))
      (lemma6LDerivNorm (lemma6BetaPoint x ν))
      (lemma6PairBlockNorm x m k (lemma6BetaPoint x ν)) hxlarge
      (by
        intro i hi
        rw [lemma6CharacterBlock, Finset.mem_sigma] at hi
        exact hi.1)
      (by intro i hi; exact lemma6PrimitiveBaseWeight_nonneg i)
      (by intro i hi; exact norm_nonneg _)
      (by
        intro i hi
        unfold lemma6LDerivNorm
        split_ifs <;> positivity)
      (by intro i hi; exact norm_nonneg _))

end Chen

end

/-! ## ChenTheorem.Lemma6.MomentConnection -/

section

/-
Connections between the actual character blocks in equation (19) and the
fourth-moment estimates proved for `L'` and the truncated Möbius mollifier.

This file performs the dependent-sum rewrites, replaces the squarefree
weight `|μ(d)| / d` by `1 / φ(d)`, and applies equations (15) and Lemma 3
on the exact dyadic modulus interval.
-/

open Real
open scoped Classical ArithmeticFunction.Moebius

namespace Chen

theorem lemma6_lDerivFourth_characterBlock_eq
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lDerivFourthTerm d (lemma6BetaPoint x ν) := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hd0 : d ≠ 0 := by omega
  rw [lDerivFourthTerm, dif_neg hd0]
  simp only [lemma6PrimitiveBaseWeight, lemma6LDerivNorm, hd0,
    ↓reduceDIte, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

theorem lemma6_lDerivFourth_characterBlock_le_inv_totient
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (ν : ℝ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lDerivFourthTerm d (lemma6BetaPoint x ν) := by
  rw [lemma6_lDerivFourth_characterBlock_eq hxlog ν]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hd0 : d ≠ 0 := by omega
  have hterm : 0 ≤ lDerivFourthTerm d (lemma6BetaPoint x ν) := by
    rw [lDerivFourthTerm, dif_neg hd0, primSum, tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

noncomputable def lemma6MollifierPhase (s : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ s)⁻¹

theorem lemma6_mollifierAt_sq_eq
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6MollifierAt H s χ ^ 2 =
      ∑ n ∈ Finset.Icc 1 (H * H),
        ((lemma6MollifierSquareCoeff H n : ℂ) *
          lemma6MollifierPhase s n) * χ n := by
  have hpoly :
      lemma6MollifierAt H s χ =
        lemma6MollifierPolynomial H (fun n => χ n / (n : ℂ) ^ s) := by
    unfold lemma6MollifierAt lemma6MollifierPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hpoly, lemma6_mollifierPolynomial_sq]
  · apply Finset.sum_congr rfl
    intro n hn
    unfold lemma6MollifierPhase
    ring
  · intro m n hm hn
    have hχ : χ ((m * n : ℕ) : ZMod q) =
        χ (m : ZMod q) * χ (n : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    have hpow : ((m * n : ℕ) : ℂ) ^ s =
        (m : ℂ) ^ s * (n : ℂ) ^ s :=
      by simpa only [Nat.cast_mul] using
        Complex.natCast_mul_natCast_cpow m n s
    rw [hχ, hpow]
    ring

theorem lemma6_mollifierPhase_norm_sq_le
    {s : ℂ} {n : ℕ} (hn : 1 ≤ n) (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖lemma6MollifierPhase s n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  have hnpos : 0 < n := by omega
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(s.re * 2) ≤ (-1 : ℝ) := by linarith
  rw [lemma6MollifierPhase, norm_inv,
    Complex.norm_natCast_cpow_of_pos hnpos]
  calc
    ((n : ℝ) ^ s.re)⁻¹ ^ 2 = (((n : ℝ) ^ s.re) ^ 2)⁻¹ :=
      inv_pow _ _
    _ = ((n : ℝ) ^ (s.re * 2))⁻¹ := by
      rw [Real.rpow_mul hnnonneg]
      norm_num
    _ = (n : ℝ) ^ (-(s.re * 2)) := by
      rw [Real.rpow_neg hnnonneg]
    _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnone hexp
    _ = (n : ℝ)⁻¹ := Real.rpow_neg_one _

/-- The mollifier as the ordinary Dirichlet polynomial used by the
character large sieve in equation (20). -/
theorem lemma6MollifierAt_eq_sum_phase
    {q : ℕ} (H : ℕ) (s : ℂ) (χ : DirichletCharacter ℂ q) :
    lemma6MollifierAt H s χ =
      ∑ n ∈ Finset.Icc 1 H,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          lemma6MollifierPhase s n * χ n := by
  unfold lemma6MollifierAt lemma6MollifierPhase
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Primitive-character second moment of the finite Möbius mollifier. -/
noncomputable def lemma6MollifierSecondTerm
    (H q : ℕ) (s : ℂ) : ℝ :=
  primSum q (fun χ => ‖lemma6MollifierAt H s χ‖ ^ 2)

/-- Rewrite the mollifier second moment on the dependent character block. -/
theorem lemma6_mollifierSecond_characterBlock_eq
    {x l H : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 2) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lemma6MollifierSecondTerm H d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6MollifierNorm,
    lemma6MollifierSecondTerm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

/-- Replace the squarefree base weight by `1/φ(d)` in the mollifier second
moment used in equation (20). -/
theorem lemma6_mollifierSecond_characterBlock_le_inv_totient
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6MollifierSecondTerm H d s := by
  rw [lemma6_mollifierSecond_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ lemma6MollifierSecondTerm H d s := by
    unfold lemma6MollifierSecondTerm primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

/-- The second moment written in the exact finite-polynomial form expected
by the character large sieve. -/
theorem lemma6_mollifierSecondTerm_eq_polynomial
    (H q : ℕ) (s : ℂ) :
    lemma6MollifierSecondTerm H q s =
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖∑ n ∈ Finset.Icc 1 H,
          (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
            lemma6MollifierPhase s n) * χ n‖ ^ 2
      else 0 := by
  unfold lemma6MollifierSecondTerm primSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [← lemma6MollifierAt_eq_sum_phase]
  · simp [hp]

/-- At `Re s ≥ 1/2`, the coefficient square sum of the unsquared mollifier
is bounded by the harmonic sum. -/
theorem lemma6_mollifier_second_coeff_sum_le_harmonic
    {H : ℕ} {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    (∑ n ∈ Finset.Icc 1 H,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          lemma6MollifierPhase s n‖ ^ 2) ≤
      (harmonic H : ℝ) := by
  rw [← lemma6_sum_Icc_inv_eq_harmonic]
  apply Finset.sum_le_sum
  intro n hn
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hμ :
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
        lemma6MollifierPhase s n‖ ^ 2 =
      ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ^ 2 *
        ‖lemma6MollifierPhase s n‖ ^ 2 := by
      rw [norm_mul, mul_pow]
    _ ≤ 1 ^ 2 * (n : ℝ)⁻¹ := by
      gcongr
      exact lemma6_mollifierPhase_norm_sq_le hn1 hs
    _ = (n : ℝ)⁻¹ := by ring

/-- Primitive-character fourth moment of Chen's finite Möbius mollifier. -/
noncomputable def lemma6MollifierFourthTerm
    (H q : ℕ) (s : ℂ) : ℝ :=
  primSum q (fun χ => ‖lemma6MollifierAt H s χ‖ ^ 4)

theorem lemma6_mollifierFourth_characterBlock_eq
    {x l H : ℕ} (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 4) =
      ∑ d ∈ lemma6ModulusBlock x l,
        (|((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ)) *
          lemma6MollifierFourthTerm H d s := by
  rw [lemma6CharacterBlock, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [lemma6PrimitiveBaseWeight, lemma6MollifierNorm,
    lemma6MollifierFourthTerm, primSum, tsum_fintype]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp [hp]
  · simp [hp]

theorem lemma6_mollifierFourthTerm_eq_squarePolynomial
    (H q : ℕ) (s : ℂ) :
    lemma6MollifierFourthTerm H q s =
      ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
        ‖∑ n ∈ Finset.Icc 1 (H * H),
          ((lemma6MollifierSquareCoeff H n : ℂ) *
            lemma6MollifierPhase s n) * χ n‖ ^ 2
      else 0 := by
  unfold lemma6MollifierFourthTerm primSum
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro χ hχ
  by_cases hp : χ.IsPrimitive
  · simp only [hp, if_true]
    rw [← lemma6_mollifierAt_sq_eq]
    rw [norm_pow]
    ring
  · simp [hp]

theorem lemma6_mollifierFourth_characterBlock_le_inv_totient
    {x l H : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) (s : ℂ) :
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H s i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lemma6MollifierFourthTerm H d s := by
  rw [lemma6_mollifierFourth_characterBlock_eq]
  apply Finset.sum_le_sum
  intro d hd
  have hd2 : 2 ≤ d :=
    (Finset.mem_Icc.mp (lemma6ModulusBlock_subset_Icc hxlog hd)).1
  have hterm : 0 ≤ lemma6MollifierFourthTerm H d s := by
    unfold lemma6MollifierFourthTerm primSum
    rw [tsum_fintype]
    positivity
  apply mul_le_mul_of_nonneg_right _ hterm
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| / (d : ℝ) ≤
        1 / (d : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · positivity
    _ ≤ (Nat.totient d : ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d) :
            (0 : ℝ) < Nat.totient d)
          (by exact_mod_cast Nat.totient_le d :
            (Nat.totient d : ℝ) ≤ d))

theorem lemma6_deriv_fourth_moment_characterBlock_of
    (hfourth : Lemma6DerivativeFourthMoment) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ∀ (l : ℕ) (ν : ℝ), 1 ≤ l →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6LDerivNorm (lemma6BetaPoint x ν) i ^ 4) ≤
          C * (2 : ℝ) ^ l * (Real.log x) ^ 110 *
            ‖lemma6BetaPoint x ν‖ ^ 2 * (1 + ν ^ 2) ^ 2 := by
  rcases hfourth with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  have hlogReal : ∀ᶠ y : ℝ in Filter.atTop, 1 ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ Real.log (x : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  filter_upwards [hbound, hlog] with x hx hxl
  intro l ν hl
  exact (lemma6_lDerivFourth_characterBlock_le_inv_totient hxl ν).trans
    (hx l ν hl)

noncomputable def lemma6ModulusLowerCutoff (x l : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100⌋₊

theorem lemma6ModulusLowerCutoff_one_le
    {x l : ℕ} (hxlog : 1 ≤ Real.log (x : ℝ)) :
    1 ≤ lemma6ModulusLowerCutoff x l := by
  unfold lemma6ModulusLowerCutoff
  apply Nat.le_floor
  have hpow2 : (1 : ℝ) ≤ (2 : ℝ) ^ (l - 1) :=
    one_le_pow₀ (by norm_num)
  have hpowlog : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 100 :=
    one_le_pow₀ hxlog
  simpa only [Nat.cast_one, one_mul] using
    mul_le_mul hpow2 hpowlog (by positivity) (by positivity)

theorem lemma6ModulusBlock_subset_Ioc_cutoffs
    {x l : ℕ} :
    lemma6ModulusBlock x l ⊆
      Finset.Ioc (lemma6ModulusLowerCutoff x l)
        (lemma6ModulusCutoff x l) := by
  intro d hd
  have hddata := hd
  rw [lemma6ModulusBlock, Finset.mem_filter] at hddata
  rw [Finset.mem_Ioc]
  constructor
  · apply (Nat.floor_lt (by positivity)).2
    exact hddata.2.2.1
  · have hceil :
        (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 ≤
          (lemma6ModulusCutoff x l : ℝ) := by
      unfold lemma6ModulusCutoff
      exact Nat.le_ceil _
    exact_mod_cast hddata.2.2.2.trans hceil

theorem lemma6ModulusLowerCutoff_le_cutoff (x l : ℕ) :
    lemma6ModulusLowerCutoff x l ≤ lemma6ModulusCutoff x l := by
  have hlogpow : 0 ≤ Real.log (x : ℝ) ^ 100 := by positivity
  have hlower :
      (lemma6ModulusLowerCutoff x l : ℝ) ≤
        (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 := by
    unfold lemma6ModulusLowerCutoff
    exact Nat.floor_le (by positivity)
  have hscales :
      (2 : ℝ) ^ (l - 1) * Real.log (x : ℝ) ^ 100 ≤
        (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 := by
    apply mul_le_mul_of_nonneg_right _ hlogpow
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le l 1)
  have hupper :
      (2 : ℝ) ^ l * Real.log (x : ℝ) ^ 100 ≤
        (lemma6ModulusCutoff x l : ℝ) := by
    unfold lemma6ModulusCutoff
    exact Nat.le_ceil _
  exact_mod_cast hlower.trans (hscales.trans hupper)

/-- Equation (20)'s second moment of the unsquared mollifier, obtained by
applying the dyadic character large sieve before squaring `S`. -/
theorem lemma6_mollifier_second_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l H : ℕ) (ν : ℝ), 1 ≤ Real.log (x : ℝ) →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              (H : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
            (1 + Real.log H) := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l H ν hxlog
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  let s := lemma6BetaPoint x ν
  let a : ℕ → ℂ := fun n =>
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      lemma6MollifierPhase s n
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hinterval : Finset.Ioc 0 H = Finset.Icc 1 H := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    dsimp only [s]
    rw [lemma6BetaPoint_re]
    have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
    have hinv : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hraw := hlarge D Q 0 H a hD hDQ
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 2) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lemma6MollifierSecondTerm H d (lemma6BetaPoint x ν) :=
      lemma6_mollifierSecond_characterBlock_le_inv_totient hxlog _
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 H, a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lemma6_mollifierSecondTerm_eq_polynomial]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 H, a n * χ n‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) *
          ∑ n ∈ Finset.Icc 1 H, ‖a n‖ ^ 2 := by
      simpa only [zero_add, hinterval] using hraw
    _ ≤ C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) *
          (harmonic H : ℝ) := by
      gcongr
      simpa only [a] using
        lemma6_mollifier_second_coeff_sum_le_harmonic (H := H) hs
    _ ≤ C * ((Q : ℝ) + (H : ℝ) / (D : ℝ)) *
          (1 + Real.log H) := by
      gcongr
      exact harmonic_le_one_add_log H
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          (H : ℝ) / (lemma6ModulusLowerCutoff x l : ℝ)) *
          (1 + Real.log H) := by rfl

theorem lemma6_mollifier_fourth_moment_characterBlock :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x l H : ℕ) (ν : ℝ),
        1 ≤ Real.log (x : ℝ) → 2 ≤ H →
        (∑ i ∈ lemma6CharacterBlock x l,
          lemma6PrimitiveBaseWeight i *
            lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤
          C * ((lemma6ModulusCutoff x l : ℝ) +
              ((H * H : ℕ) : ℝ) /
                (lemma6ModulusLowerCutoff x l : ℝ)) *
            (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by
  rcases lemma6_mollifierSquare_fourthMoment with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro x l H ν hxlog hH
  let D := lemma6ModulusLowerCutoff x l
  let Q := lemma6ModulusCutoff x l
  let s := lemma6BetaPoint x ν
  let u := lemma6MollifierPhase s
  have hD : 1 ≤ D := lemma6ModulusLowerCutoff_one_le hxlog
  have hDQ : D ≤ Q := lemma6ModulusLowerCutoff_le_cutoff x l
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    dsimp only [s]
    rw [lemma6BetaPoint_re]
    have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hxlog
    have hinv : 0 ≤ 1 / Real.log (x : ℝ) := by positivity
    linarith
  have hu : ∀ n ∈ Finset.Icc 1 (H * H),
      ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
    intro n hn
    exact lemma6_mollifierPhase_norm_sq_le (Finset.mem_Icc.mp hn).1 hs
  have hraw := hlarge D Q H u hD hDQ hH hu
  calc
    (∑ i ∈ lemma6CharacterBlock x l,
        lemma6PrimitiveBaseWeight i *
          lemma6MollifierNorm H (lemma6BetaPoint x ν) i ^ 4) ≤
      ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          lemma6MollifierFourthTerm H d (lemma6BetaPoint x ν) :=
      lemma6_mollifierFourth_characterBlock_le_inv_totient hxlog _
    _ = ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 (H * H),
              ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lemma6_mollifierFourthTerm_eq_squarePolynomial]
    _ ≤ ∑ d ∈ Finset.Ioc D Q,
        (Nat.totient d : ℝ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ d, if χ.IsPrimitive then
            ‖∑ n ∈ Finset.Icc 1 (H * H),
              ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [D, Q] using
          (lemma6ModulusBlock_subset_Ioc_cutoffs (x := x) (l := l))
      · intro d hd hnot
        positivity
    _ ≤ C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
          (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := hraw
    _ = C * ((lemma6ModulusCutoff x l : ℝ) +
          ((H * H : ℕ) : ℝ) /
            (lemma6ModulusLowerCutoff x l : ℝ)) *
          (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by rfl

end Chen

end

