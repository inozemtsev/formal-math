module

public import Green64.Library.ChenTheorem.Lemma5.Boundary.Selberg
public import Green64.Library.Sieve.Foundation.LargeSieve.Part001
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

@[expose] public section

/-!
# Sieve / Foundation / Lemma5 / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ChenTheorem.Lemma5.Boundary.Weights -/

section

/-!
# Optimal truncated Selberg weights for Chen's Lemma 5

This file performs Möbius inversion on the upper divisor lattice of the
squarefree sieve product.  It constructs weights whose diagonal
coordinates are the standard optimal Selberg coordinates.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

theorem div_div_self_of_dvd {P n : ℕ} (hP : 0 < P) (hn : n ∣ P) :
    P / (P / n) = n := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn hP
  have hquotpos : 0 < P / n :=
    Nat.div_pos (Nat.le_of_dvd hP hn) hnpos
  apply Nat.div_eq_of_eq_mul_left hquotpos
  exact (Nat.mul_div_cancel' hn).symm

/-- Möbius inversion coefficient on the upper divisor interval
`{d | d ∣ P}`. -/
noncomputable def upperMobiusCoefficient
    (P : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ uv ∈ (P / d).divisorsAntidiagonal,
    (ArithmeticFunction.moebius uv.1 : ℝ) * y (P / uv.2)

/-- Upper-divisor Möbius inversion. -/
theorem upperMobiusCoefficient_sum
    {P k : ℕ} (y : ℕ → ℝ) (hP : 0 < P) (hk : k ∣ P) :
    (∑ d ∈ P.divisors,
      if k ∣ d then upperMobiusCoefficient P y d else 0) = y k := by
  have hinv :
      ∀ n > 0, n ∣ P →
        (∑ i ∈ n.divisors,
          upperMobiusCoefficient P y (P / i)) = y (P / n) := by
    apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      {n : ℕ | n ∣ P} (by
        intro m n hmn hnP
        exact hmn.trans hnP)).mpr
    intro n hnpos hnP
    rw [upperMobiusCoefficient, div_div_self_of_dvd hP hnP]
  rw [← Nat.sum_div_divisors P]
  have hcond :
      ∀ i ∈ P.divisors, (k ∣ P / i ↔ i ∣ P / k) := by
    intro i hi
    have hiP := Nat.dvd_of_mem_divisors hi
    rw [Nat.dvd_div_iff_mul_dvd hiP,
      Nat.dvd_div_iff_mul_dvd hk]
    exact mul_comm k i ▸ Iff.rfl
  calc
    (∑ i ∈ P.divisors,
        if k ∣ P / i then
          upperMobiusCoefficient P y (P / i) else 0) =
        ∑ i ∈ P.divisors,
          if i ∣ P / k then
            upperMobiusCoefficient P y (P / i) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [hcond i hi]
    _ = ∑ i ∈ (P / k).divisors,
          upperMobiusCoefficient P y (P / i) := by
      rw [← Nat.divisors_filter_dvd_of_dvd hP.ne'
          (Nat.div_dvd_of_dvd hk),
        Finset.sum_filter]
    _ = y (P / (P / k)) := by
      have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk hP
      have hquotpos : 0 < P / k :=
        Nat.div_pos (Nat.le_of_dvd hP hk) hkpos
      exact hinv (P / k) hquotpos (Nat.div_dvd_of_dvd hk)
    _ = y k := by rw [div_div_self_of_dvd hP hk]

/-- If all coordinates above `d` vanish, then so does its inverse
coefficient. -/
theorem upperMobiusCoefficient_eq_zero
    {P d : ℕ} (y : ℕ → ℝ) (hP : 0 < P) (hdP : d ∣ P)
    (hy : ∀ l, 0 < l → d ∣ l → y l = 0) :
    upperMobiusCoefficient P y d = 0 := by
  unfold upperMobiusCoefficient
  apply Finset.sum_eq_zero
  intro uv huv
  have huv' := (Nat.mem_divisorsAntidiagonal.mp huv).1
  have hdprod : d * (P / d) = P := Nat.mul_div_cancel' hdP
  have hvpos : 0 < uv.2 :=
    Nat.pos_of_ne_zero
      (Nat.right_ne_zero_of_mem_divisorsAntidiagonal huv)
  have hquot :
      P / uv.2 = d * uv.1 := by
    apply Nat.div_eq_of_eq_mul_right hvpos
    calc
      P = d * (P / d) := hdprod.symm
      _ = d * (uv.1 * uv.2) := by rw [huv']
      _ = (d * uv.1) * uv.2 := by ring
      _ = uv.2 * (d * uv.1) := by ring
  have hvP : uv.2 ∣ P := by
    exact (dvd_of_mul_left_dvd huv'.dvd).trans
      (Nat.div_dvd_of_dvd hdP)
  have hlpos : 0 < P / uv.2 :=
    Nat.div_pos (Nat.le_of_dvd hP hvP) hvpos
  rw [hy (P / uv.2) hlpos ⟨uv.1, hquot⟩, mul_zero]

/-- The desired diagonal coordinates of the optimal truncated Selberg
weight. -/
noncomputable def optimalSelbergCoordinate
    (s : BoundingSieve) (R : ℕ) (l : ℕ) : ℝ :=
  if l ∈ truncatedSieveDivisors s.prodPrimes R then
    (ArithmeticFunction.moebius l : ℝ) *
      s.selbergTerms l / truncatedSelbergMass s R
  else 0

/-- The optimal truncated Selberg weight, obtained from the desired
coordinates by upper-divisor Möbius inversion. -/
noncomputable def optimalSelbergWeight
    (s : BoundingSieve) (R : ℕ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ *
      upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d
  else 0

theorem optimalSelbergCoordinate_eq_zero_of_not_le
    (s : BoundingSieve) {R l : ℕ} (hlR : ¬l ≤ R) :
    optimalSelbergCoordinate s R l = 0 := by
  simp [optimalSelbergCoordinate, truncatedSieveDivisors, hlR]

theorem optimalSelbergCoordinate_abs_le_one
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) (l : ℕ) :
    |optimalSelbergCoordinate s R l| ≤ 1 := by
  by_cases hlD :
      l ∈ truncatedSieveDivisors s.prodPrimes R
  · have hlP :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hlD).1
    have hlsq : Squarefree l :=
      s.squarefree_of_dvd_prodPrimes hlP
    have hmu :
        |(ArithmeticFunction.moebius l : ℝ)| = 1 := by
      exact_mod_cast
        ArithmeticFunction.abs_moebius_eq_one_of_squarefree hlsq
    have hgpos : 0 < s.selbergTerms l :=
      s.selbergTerms_pos hlP
    have hGpos := truncatedSelbergMass_pos s hR
    have hleG :
        s.selbergTerms l ≤ truncatedSelbergMass s R := by
      unfold truncatedSelbergMass
      exact Finset.single_le_sum
        (fun i hi => (s.selbergTerms_pos
          (Nat.dvd_of_mem_divisors
            (Finset.mem_filter.mp hi).1)).le)
        hlD
    rw [optimalSelbergCoordinate, if_pos hlD,
      abs_div, abs_mul, hmu, one_mul,
      abs_of_pos hgpos, abs_of_pos hGpos]
    exact (div_le_one hGpos).2 hleG
  · simp [optimalSelbergCoordinate, hlD]

/-- The inverse Möbius coefficient is bounded by the number of possible
nonzero level-`R` coordinates. -/
theorem abs_upperMobiusCoefficient_optimal_le
    (s : BoundingSieve) {R d : ℕ} (hR : 1 ≤ R)
    (hdP : d ∣ s.prodPrimes) :
    |upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d| ≤ R + 1 := by
  let A := (s.prodPrimes / d).divisorsAntidiagonal
  let T := A.filter fun uv => s.prodPrimes / uv.2 ≤ R
  have hPpos : 0 < s.prodPrimes :=
    Nat.pos_of_ne_zero s.prodPrimes_ne_zero
  have hTcard : T.card ≤ R + 1 := by
    have hmap :
        Set.MapsTo (fun uv : ℕ × ℕ => s.prodPrimes / uv.2)
          (T : Set (ℕ × ℕ)) (Finset.range (R + 1) : Set ℕ) := by
      intro uv huv
      change s.prodPrimes / uv.2 ∈ Finset.range (R + 1)
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_filter.mp huv).2
    have hinj :
        Set.InjOn (fun uv : ℕ × ℕ => s.prodPrimes / uv.2)
          (T : Set (ℕ × ℕ)) := by
      intro u hu v hv huvEq
      have huA := (Nat.mem_divisorsAntidiagonal.mp
        (Finset.mem_filter.mp hu).1)
      have hvA := (Nat.mem_divisorsAntidiagonal.mp
        (Finset.mem_filter.mp hv).1)
      have hu2dvdQ : u.2 ∣ s.prodPrimes / d :=
        ⟨u.1, by simpa [mul_comm] using huA.1.symm⟩
      have hv2dvdQ : v.2 ∣ s.prodPrimes / d :=
        ⟨v.1, by simpa [mul_comm] using hvA.1.symm⟩
      have hu2P : u.2 ∣ s.prodPrimes :=
        hu2dvdQ.trans (Nat.div_dvd_of_dvd hdP)
      have hv2P : v.2 ∣ s.prodPrimes :=
        hv2dvdQ.trans (Nat.div_dvd_of_dvd hdP)
      have huv2 : u.2 = v.2 :=
        (Nat.div_eq_iff_eq_of_dvd_dvd
          s.prodPrimes_ne_zero hu2P hv2P).mp huvEq
      apply Prod.ext
      · have hu2pos : 0 < u.2 :=
          Nat.pos_of_ne_zero
            (Nat.right_ne_zero_of_mem_divisorsAntidiagonal
              (Finset.mem_filter.mp hu).1)
        apply Nat.mul_right_cancel hu2pos
        calc
          u.1 * u.2 = s.prodPrimes / d := huA.1
          _ = v.1 * v.2 := hvA.1.symm
          _ = v.1 * u.2 := by rw [huv2]
      · exact huv2
    simpa using Finset.card_le_card_of_injOn
      (fun uv : ℕ × ℕ => s.prodPrimes / uv.2) hmap hinj
  unfold upperMobiusCoefficient
  change |∑ uv ∈ A,
      (ArithmeticFunction.moebius uv.1 : ℝ) *
        optimalSelbergCoordinate s R (s.prodPrimes / uv.2)| ≤
    (R : ℝ) + 1
  calc
    |∑ uv ∈ A,
        (ArithmeticFunction.moebius uv.1 : ℝ) *
          optimalSelbergCoordinate s R (s.prodPrimes / uv.2)| ≤
        ∑ uv ∈ A,
          |(ArithmeticFunction.moebius uv.1 : ℝ) *
            optimalSelbergCoordinate s R (s.prodPrimes / uv.2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ uv ∈ A,
          if s.prodPrimes / uv.2 ≤ R then 1 else 0 := by
      apply Finset.sum_le_sum
      intro uv huv
      by_cases huvR : s.prodPrimes / uv.2 ≤ R
      · rw [if_pos huvR, abs_mul]
        have hmu :
            |(ArithmeticFunction.moebius uv.1 : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [optimalSelbergCoordinate_abs_le_one s hR
          (s.prodPrimes / uv.2),
          abs_nonneg (ArithmeticFunction.moebius uv.1 : ℝ),
          abs_nonneg (optimalSelbergCoordinate s R
            (s.prodPrimes / uv.2))]
      · rw [if_neg huvR,
          optimalSelbergCoordinate_eq_zero_of_not_le s huvR,
          mul_zero, abs_zero]
    _ = T.card := by
      simp [T, A]
    _ ≤ R + 1 := by exact_mod_cast hTcard

theorem smoothingTransitionRootCount_pos
    (x : ℕ) (q : ℕ × ℕ) {d : ℕ} (hd : 0 < d) :
    0 < smoothingTransitionRootCount x q d := by
  unfold smoothingTransitionRootCount
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [smoothingTransitionRootResidues, hd]

theorem smoothingTransitionNu_inv_le
    (x : ℕ) (q : ℕ × ℕ) {d : ℕ} (hd : 0 < d) :
    (smoothingTransitionNu x q d)⁻¹ ≤ (d : ℝ) := by
  rw [smoothingTransitionNu_apply, inv_div]
  have hrpos :
      0 < smoothingTransitionRootCount x q d :=
    smoothingTransitionRootCount_pos x q hd
  rw [div_le_iff₀ (Nat.cast_pos.2 hrpos)]
  have hrone :
      (1 : ℝ) ≤ smoothingTransitionRootCount x q d := by
    exact_mod_cast hrpos
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  nlinarith

/-- A polynomial bound for the optimal transition weights.  The exact
classical bound is `|λ_d| ≤ 1`; this weaker bound already makes the
indexed congruence error negligible after choosing a sufficiently small
power level. -/
theorem abs_optimalTransitionSelbergWeight_le
    {x R d : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R)
    (hd : d ∈ truncatedSieveDivisors
      (transitionSieveProduct x) R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    |optimalSelbergWeight s R d| ≤
      (R : ℝ) * ((R : ℝ) + 1) := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  change |optimalSelbergWeight s R d| ≤
    (R : ℝ) * ((R : ℝ) + 1)
  have hdP : d ∣ transitionSieveProduct x :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdR : d ≤ R := (Finset.mem_filter.mp hd).2
  have hdPs : d ∣ s.prodPrimes := by exact hdP
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdP
      (Nat.pos_of_ne_zero (transitionSieveProduct_ne_zero x))
  have hcoeff :=
    abs_upperMobiusCoefficient_optimal_le s hR hdP
  have hnuinv :=
    smoothingTransitionNu_inv_le x q hdpos
  have hnupos :
      0 < s.nu d :=
    s.nu_pos_of_dvd_prodPrimes hdPs
  rw [optimalSelbergWeight, if_pos hdPs, abs_mul,
    abs_inv, abs_of_pos hnupos]
  have hdRreal : (d : ℝ) ≤ R := by exact_mod_cast hdR
  have hRnonneg : (0 : ℝ) ≤ R := by positivity
  have hcoeffnonneg :
      0 ≤ |upperMobiusCoefficient s.prodPrimes
        (optimalSelbergCoordinate s R) d| := abs_nonneg _
  calc
    (s.nu d)⁻¹ *
        |upperMobiusCoefficient s.prodPrimes
          (optimalSelbergCoordinate s R) d| ≤
        (d : ℝ) * ((R : ℝ) + 1) := by
      exact mul_le_mul hnuinv hcoeff
        (by positivity) (by positivity)
    _ ≤ (R : ℝ) * ((R : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_right hdRreal (by positivity)

/-- The congruence-count error for the optimal weights remains
polynomial in the chosen level. -/
theorem transitionErrorQuadratic_optimalSelbergWeight_le
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    transitionErrorQuadratic x q R (optimalSelbergWeight s R) ≤
      ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
        ((R + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (R : ℝ) ^ 2 + 1) := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  let K : ℝ := (R : ℝ) * ((R : ℝ) + 1)
  let w := optimalSelbergWeight s R
  let wn : ℕ → ℝ := fun d => w d / K
  have hKpos : 0 < K := by
    dsimp only [K]
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have hwn :
      ∀ d ∈ truncatedSieveDivisors
        (transitionSieveProduct x) R, |wn d| ≤ 1 := by
    intro d hd
    have hw := abs_optimalTransitionSelbergWeight_le
      hx hxEven hq hR hd
    change |w d / K| ≤ 1
    rw [abs_div, abs_of_pos hKpos]
    exact (div_le_one hKpos).2 (by
      simpa only [w, K, s] using hw)
  have herr :=
    transitionErrorQuadratic_le x q R wn hwn
  have herrEq :
      transitionErrorQuadratic x q R w =
        K ^ 2 * transitionErrorQuadratic x q R wn := by
    unfold transitionErrorQuadratic
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    dsimp only [wn]
    simp only [abs_mul, abs_div, abs_of_pos hKpos]
    field_simp
  change transitionErrorQuadratic x q R w ≤
    K ^ 2 * ((R + 1 : ℕ) : ℝ) ^ 2 *
      (3 * (R : ℝ) ^ 2 + 1)
  rw [herrEq]
  nlinarith [sq_nonneg K]

/-- The inverse weight is supported at level `R`. -/
theorem optimalSelbergWeight_eq_zero_of_not_le
    (s : BoundingSieve) {R d : ℕ} (hdR : ¬d ≤ R) :
    optimalSelbergWeight s R d = 0 := by
  by_cases hdP : d ∣ s.prodPrimes
  · rw [optimalSelbergWeight, if_pos hdP,
      upperMobiusCoefficient_eq_zero _
        (Nat.pos_of_ne_zero s.prodPrimes_ne_zero) hdP]
    · simp
    · intro l hlpos hdl
      apply optimalSelbergCoordinate_eq_zero_of_not_le
      exact fun hlR => hdR (Nat.le_trans
        (Nat.le_of_dvd hlpos hdl) hlR)
  · simp [optimalSelbergWeight, hdP]

@[simp]
theorem smoothingTruncatedWeight_optimalSelbergWeight
    (s : BoundingSieve) (R d : ℕ) :
    smoothingTruncatedWeight R (optimalSelbergWeight s R) d =
      optimalSelbergWeight s R d := by
  by_cases hdR : d ≤ R
  · exact smoothingTruncatedWeight_of_le hdR
  · rw [smoothingTruncatedWeight_of_not_le hdR,
      optimalSelbergWeight_eq_zero_of_not_le s hdR]

/-- The constructed weight has exactly the prescribed diagonal
coordinates. -/
theorem optimalSelbergWeight_coordinate
    (s : BoundingSieve) (R : ℕ) {l : ℕ}
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d then s.nu d * optimalSelbergWeight s R d else 0) =
      optimalSelbergCoordinate s R l := by
  calc
    (∑ d ∈ s.prodPrimes.divisors,
        if l ∣ d then s.nu d * optimalSelbergWeight s R d else 0) =
        ∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            upperMobiusCoefficient s.prodPrimes
              (optimalSelbergCoordinate s R) d
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP := Nat.dvd_of_mem_divisors hd
      have hnu : s.nu d ≠ 0 :=
        ne_of_gt (s.nu_pos_of_dvd_prodPrimes hdP)
      by_cases hld : l ∣ d
      · simp only [hld, if_true, optimalSelbergWeight, hdP]
        field_simp
      · simp [hld]
    _ = optimalSelbergCoordinate s R l :=
      upperMobiusCoefficient_sum _ (Nat.pos_of_ne_zero
        s.prodPrimes_ne_zero) hl

/-- The diagonal quadratic form at the optimal coordinates is exactly
the reciprocal of the truncated Selberg mass. -/
theorem optimalSelbergCoordinate_diagonal
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    (∑ l ∈ s.prodPrimes.divisors,
      (s.selbergTerms l)⁻¹ *
        (optimalSelbergCoordinate s R l) ^ 2) =
      (truncatedSelbergMass s R)⁻¹ := by
  have hGpos := truncatedSelbergMass_pos s hR
  calc
    (∑ l ∈ s.prodPrimes.divisors,
        (s.selbergTerms l)⁻¹ *
          (optimalSelbergCoordinate s R l) ^ 2) =
        ∑ l ∈ s.prodPrimes.divisors,
          if l ≤ R then
            s.selbergTerms l / (truncatedSelbergMass s R) ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hlR : l ≤ R
      · rw [if_pos hlR]
        have hlD :
            l ∈ truncatedSieveDivisors s.prodPrimes R :=
          Finset.mem_filter.mpr ⟨hl, hlR⟩
        have hlsq : Squarefree l :=
          s.squarefree_of_dvd_prodPrimes
            (Nat.dvd_of_mem_divisors hl)
        have hmu :
            ((ArithmeticFunction.moebius l : ℝ) ^ 2) = 1 := by
          exact_mod_cast
            ArithmeticFunction.moebius_sq_eq_one_of_squarefree hlsq
        have hgpos :
            0 < s.selbergTerms l :=
          s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)
        rw [optimalSelbergCoordinate, if_pos hlD]
        field_simp
        nlinarith
      · rw [if_neg hlR]
        have hlD :
            l ∉ truncatedSieveDivisors s.prodPrimes R := by
          simp [truncatedSieveDivisors, hlR]
        simp [optimalSelbergCoordinate, hlD]
    _ = (∑ l ∈ truncatedSieveDivisors s.prodPrimes R,
          s.selbergTerms l) /
        (truncatedSelbergMass s R) ^ 2 := by
      rw [← Finset.sum_filter]
      simp only [truncatedSieveDivisors]
      rw [Finset.sum_div]
    _ = (truncatedSelbergMass s R) /
        (truncatedSelbergMass s R) ^ 2 := by
      rfl
    _ = (truncatedSelbergMass s R)⁻¹ := by
      field_simp

theorem upperMobiusCoefficient_optimal_one
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    upperMobiusCoefficient s.prodPrimes
      (optimalSelbergCoordinate s R) 1 = 1 := by
  have hPpos : 0 < s.prodPrimes :=
    Nat.pos_of_ne_zero s.prodPrimes_ne_zero
  have hGpos := truncatedSelbergMass_pos s hR
  unfold upperMobiusCoefficient
  rw [Nat.div_one,
    Nat.sum_divisorsAntidiagonal
      (fun i j => (ArithmeticFunction.moebius i : ℝ) *
        optimalSelbergCoordinate s R (s.prodPrimes / j))]
  calc
    (∑ i ∈ s.prodPrimes.divisors,
        (ArithmeticFunction.moebius i : ℝ) *
          optimalSelbergCoordinate s R
            (s.prodPrimes / (s.prodPrimes / i))) =
        ∑ i ∈ s.prodPrimes.divisors,
          if i ≤ R then
            s.selbergTerms i / truncatedSelbergMass s R
          else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_div_self_of_dvd hPpos
        (Nat.dvd_of_mem_divisors hi)]
      by_cases hiR : i ≤ R
      · rw [if_pos hiR]
        have hiD :
            i ∈ truncatedSieveDivisors s.prodPrimes R :=
          Finset.mem_filter.mpr ⟨hi, hiR⟩
        have hisq : Squarefree i :=
          s.squarefree_of_dvd_prodPrimes
            (Nat.dvd_of_mem_divisors hi)
        have hmu :
            ((ArithmeticFunction.moebius i : ℝ) ^ 2) = 1 := by
          exact_mod_cast
            ArithmeticFunction.moebius_sq_eq_one_of_squarefree hisq
        rw [optimalSelbergCoordinate, if_pos hiD]
        calc
          (ArithmeticFunction.moebius i : ℝ) *
              ((ArithmeticFunction.moebius i : ℝ) *
                s.selbergTerms i / truncatedSelbergMass s R) =
              ((ArithmeticFunction.moebius i : ℝ) ^ 2) *
                s.selbergTerms i / truncatedSelbergMass s R := by ring
          _ = s.selbergTerms i / truncatedSelbergMass s R := by
            rw [hmu, one_mul]
      · rw [if_neg hiR]
        have hiD :
            i ∉ truncatedSieveDivisors s.prodPrimes R := by
          simp [truncatedSieveDivisors, hiR]
        simp [optimalSelbergCoordinate, hiD]
    _ = (∑ i ∈ truncatedSieveDivisors s.prodPrimes R,
          s.selbergTerms i) / truncatedSelbergMass s R := by
      rw [← Finset.sum_filter]
      simp only [truncatedSieveDivisors]
      rw [Finset.sum_div]
    _ = truncatedSelbergMass s R /
        truncatedSelbergMass s R := by rfl
    _ = 1 := div_self hGpos.ne'

@[simp]
theorem optimalSelbergWeight_one
    (s : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    optimalSelbergWeight s R 1 = 1 := by
  rw [optimalSelbergWeight, if_pos (one_dvd _),
    s.nu_mult.map_one, inv_one, one_mul]
  exact upperMobiusCoefficient_optimal_one s hR

/-- The transition main quadratic form at the constructed optimal
weights is exactly `1 / G(R)`. -/
theorem transitionMainQuadratic_optimalSelbergWeight
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    transitionMainQuadratic x q R (optimalSelbergWeight s R) =
      (truncatedSelbergMass s R)⁻¹ := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  change transitionMainQuadratic x q R
      (optimalSelbergWeight s R) =
    (truncatedSelbergMass s R)⁻¹
  rw [transitionMainQuadratic_eq_diagonal hx hxEven hq]
  calc
    (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ s.prodPrimes.divisors,
          if l ∣ d then
            s.nu d * smoothingTruncatedWeight R
              (optimalSelbergWeight s R) d
          else 0) ^ 2) =
        ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
          (optimalSelbergCoordinate s R l) ^ 2 := by
      apply Finset.sum_congr rfl
      intro l hl
      simp_rw [smoothingTruncatedWeight_optimalSelbergWeight]
      rw [optimalSelbergWeight_coordinate s R
        (Nat.dvd_of_mem_divisors hl)]
    _ = (truncatedSelbergMass s R)⁻¹ :=
      optimalSelbergCoordinate_diagonal s hR

/-- Per-pair transition sieve bound with the optimized main term and a
fully explicit polynomial error. -/
theorem smoothingTransitionSifted_card_le_optimal
    {x R : ℕ} {q : ℕ × ℕ} (hx : 1 < x) (hxEven : Even x)
    (hq : q ∈ chenPairs x) (hR : 1 ≤ R) :
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) *
        (truncatedSelbergMass s R)⁻¹ +
      ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
        ((R + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (R : ℝ) ^ 2 + 1) := by
  dsimp only
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  have hsieve :=
    smoothingTransitionSifted_card_le_main_add_error hq
      (optimalSelbergWeight s R) hR
      (optimalSelbergWeight_one s hR)
  calc
    ((smoothingTransitionSiftedIndices x q).card : ℝ) ≤
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          transitionMainQuadratic x q R
            (optimalSelbergWeight s R) +
          transitionErrorQuadratic x q R
            (optimalSelbergWeight s R) := hsieve
    _ ≤ ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          (truncatedSelbergMass s R)⁻¹ +
        ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
          ((R + 1 : ℕ) : ℝ) ^ 2 *
            (3 * (R : ℝ) ^ 2 + 1) := by
      rw [transitionMainQuadratic_optimalSelbergWeight
        hx hxEven hq hR]
      have herr :
          transitionErrorQuadratic x q R
              (optimalSelbergWeight s R) ≤
            ((R : ℝ) * ((R : ℝ) + 1)) ^ 2 *
              ((R + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (R : ℝ) ^ 2 + 1) := by
        simpa only [s] using
          transitionErrorQuadratic_optimalSelbergWeight_le
            hx hxEven hq hR
      exact add_le_add le_rfl herr

end Chen

end

/-! ## ChenTheorem.Lemma5.Boundary.Mass -/

section

/-!
# Lower bounds for the Selberg normalization in Chen's Lemma 5

This file supplies the squarefree harmonic-mass and Euler-penalty
estimates used to lower-bound the truncated dimension-two Selberg mass.
-/

open Finset Real Filter
open scoped Nat.Prime Classical ArithmeticFunction

namespace Chen

noncomputable def coprimeDivisorCountAF (x : ℕ) :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors fun p =>
    if p ∣ x then 1 else 2

theorem coprimeDivisorCountAF_isMultiplicative (x : ℕ) :
    (coprimeDivisorCountAF x).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.prodPrimeFactors _

theorem coprimeDivisorCountAF_prime
    (x : ℕ) {p : ℕ} (hp : p.Prime) :
    coprimeDivisorCountAF x p =
      if p ∣ x then 1 else 2 := by
  unfold coprimeDivisorCountAF
  simp [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp]

theorem smoothingTransitionNu_eq_coprimeDivisorCount_div
    {x l : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hq : q ∈ chenPairs x)
    (hlP : l ∣ transitionSieveProduct x)
    (hlsf : Squarefree l) :
    smoothingTransitionNu x q l =
      coprimeDivisorCountAF x l / l := by
  have hlocal :
      ∀ p ∈ l.primeFactors,
        smoothingTransitionNu x q p =
          coprimeDivisorCountAF x p / p := by
    intro p hpL
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
    have hpl : p ∣ l :=
      (Nat.mem_primeFactors.mp hpL).2.1
    have hpP : p ∣ transitionSieveProduct x := hpl.trans hlP
    rw [smoothingTransitionNu_prime hp
      (transitionSievePrime_not_dvd_pair hx hq hp hpP),
      coprimeDivisorCountAF_prime x hp]
  have hnu :=
    (smoothingTransitionNu_isMultiplicative x q).prod_primeFactors hlsf
  have hcount :=
    (coprimeDivisorCountAF_isMultiplicative x).prod_primeFactors hlsf
  rw [← hnu]
  calc
    ∏ p ∈ l.primeFactors, smoothingTransitionNu x q p =
        ∏ p ∈ l.primeFactors,
          coprimeDivisorCountAF x p / p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hlocal p hp
    _ = (∏ p ∈ l.primeFactors, coprimeDivisorCountAF x p) /
        ∏ p ∈ l.primeFactors, (p : ℝ) := by
      rw [Finset.prod_div_distrib]
    _ = coprimeDivisorCountAF x l / l := by
      rw [hcount, ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree hlsf]

theorem coprimeDivisorCount_div_le_selbergTerms
    {x l : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hxEven : Even x) (hq : q ∈ chenPairs x)
    (hlP : l ∣ transitionSieveProduct x)
    (hlsf : Squarefree l) :
    coprimeDivisorCountAF x l / l ≤
      (smoothingTransitionBoundingSieve x q hx hxEven hq).selbergTerms l := by
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  have hnu :
      s.nu l = coprimeDivisorCountAF x l / l := by
    exact smoothingTransitionNu_eq_coprimeDivisorCount_div
      hx hq hlP hlsf
  have hnupos : 0 < s.nu l := s.nu_pos_of_dvd_prodPrimes hlP
  have hprod :
      1 ≤ ∏ p ∈ l.primeFactors, (1 - s.nu p)⁻¹ := by
    apply Finset.one_le_prod₀
    intro p hpL
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
    have hpl : p ∣ l := (Nat.mem_primeFactors.mp hpL).2.1
    have hpP : p ∣ s.prodPrimes := hpl.trans hlP
    have hnuppos : 0 < s.nu p := s.nu_pos_of_dvd_prodPrimes hpP
    have hnult : s.nu p < 1 := s.nu_lt_one_of_prime p hp hpP
    exact (one_le_inv₀ (sub_pos.mpr hnult)).2 (by linarith)
  rw [(s.selbergTerms_apply l), ← hnu]
  nlinarith

theorem sum_squarefreeDivisors_inv_eq_powerset
    {x : ℕ} (hx : x ≠ 0) :
    ∑ d ∈ x.divisors.filter Squarefree, (d : ℝ)⁻¹ =
      ∑ t ∈ x.primeFactors.powerset,
        ((∏ p ∈ t, p : ℕ) : ℝ)⁻¹ := by
  refine Finset.sum_bij'
    (fun d _ => d.primeFactors)
    (fun t _ => ∏ p ∈ t, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_powerset]
    intro p hp
    have hd' := Finset.mem_filter.mp hd
    have hdvd : d ∣ x := Nat.dvd_of_mem_divisors hd'.1
    have hp' := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨hp'.1, hp'.2.1.trans hdvd, hx⟩
  · intro t ht
    have ht' := Finset.mem_powerset.mp ht
    apply Finset.mem_filter.mpr
    constructor
    · apply Nat.mem_divisors.mpr
      constructor
      · exact Nat.dvd_trans
          (Finset.prod_dvd_prod_of_subset
            t x.primeFactors id ht')
          (Nat.prod_primeFactors_dvd x)
      · exact hx
    · apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        change IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes
          (Nat.prime_of_mem_primeFactors (ht' hp))
          (Nat.prime_of_mem_primeFactors (ht' hq))).2 hpq
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors (ht' hp)).squarefree
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree
      (Finset.mem_filter.mp hd).2
  · intro t ht
    exact Nat.primeFactors_prod (fun p hp =>
      Nat.prime_of_mem_primeFactors
        (Finset.mem_powerset.mp ht hp))
  · intro d hd
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree
      (Finset.mem_filter.mp hd).2).symm

theorem sum_squarefreeDivisors_inv_eq_penalty
    {x : ℕ} (hx : x ≠ 0) :
    ∑ d ∈ x.divisors.filter Squarefree, (d : ℝ)⁻¹ =
      primeFactorEulerPenalty x := by
  rw [sum_squarefreeDivisors_inv_eq_powerset hx]
  unfold primeFactorEulerPenalty
  calc
    ∑ t ∈ x.primeFactors.powerset,
        ((∏ p ∈ t, p : ℕ) : ℝ)⁻¹ =
      ∑ t ∈ x.primeFactors.powerset,
        (∏ p ∈ t, (p : ℝ)⁻¹) *
          ∏ _p ∈ x.primeFactors \ t, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.cast_prod]
      simp
    _ = ∏ p ∈ x.primeFactors, ((p : ℝ)⁻¹ + 1) := by
      rw [← Finset.prod_add]
    _ = ∏ p ∈ x.primeFactors, (1 + (p : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro p hp
      ring

def squarefreeUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter Squarefree

def squarefreeCoprimeUpTo (x Y : ℕ) : Finset ℕ :=
  (squarefreeUpTo Y).filter fun n => n.Coprime x

noncomputable def squarefreeHarmonic (Y : ℕ) : ℝ :=
  ∑ n ∈ squarefreeUpTo Y, (n : ℝ)⁻¹

noncomputable def squarefreeCoprimeHarmonic (x Y : ℕ) : ℝ :=
  ∑ n ∈ squarefreeCoprimeUpTo x Y, (n : ℝ)⁻¹

theorem squarefreeHarmonic_le_penalty_mul_coprime
    {x Y : ℕ} (hx : x ≠ 0) :
    squarefreeHarmonic Y ≤
      primeFactorEulerPenalty x *
        squarefreeCoprimeHarmonic x Y := by
  let S := squarefreeUpTo Y
  let D := x.divisors.filter Squarefree
  let B := squarefreeCoprimeUpTo x Y
  let f : ℕ → ℕ × ℕ := fun n => (n.gcd x, n / n.gcd x)
  have hfprod (n : ℕ) :
      (f n).1 * (f n).2 = n := by
    dsimp only [f]
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n x)]
  have hfinj :
      ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b := by
    intro a ha b hb hab
    have hprod := congrArg (fun z : ℕ × ℕ => z.1 * z.2) hab
    simpa only [hfprod] using hprod
  have hfmem :
      S.image f ⊆ D ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnS, rfl⟩
    have hn := Finset.mem_filter.mp hnS
    have hnIcc := Finset.mem_Icc.mp hn.1
    have hnsf := hn.2
    have hgcdpos : 0 < n.gcd x :=
      Nat.gcd_pos_of_pos_left x (by omega)
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n x, hx⟩
      · exact hnsf.squarefree_of_dvd (Nat.gcd_dvd_left n x)
    · unfold B squarefreeCoprimeUpTo
      apply Finset.mem_filter.mpr
      constructor
      · unfold squarefreeUpTo
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_of_gt
                (Nat.div_pos
                  (Nat.gcd_le_left x (by omega)) hgcdpos))
          · exact (Nat.div_le_self n _).trans hnIcc.2
        · exact hnsf.squarefree_of_dvd
            (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n x))
      · exact Nat.coprime_div_gcd_of_squarefree hnsf hx
  have himage :
      (∑ z ∈ S.image f,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹)) =
        ∑ n ∈ S, (n : ℝ)⁻¹ := by
    rw [Finset.sum_image hfinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hfprod]
  have hsubset :
      (∑ z ∈ S.image f,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹)) ≤
        ∑ z ∈ D ×ˢ B,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hfmem
    intro z hzDB hzImage
    positivity
  have hproduct :
      (∑ z ∈ D ×ˢ B,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹)) =
        (∑ d ∈ D, (d : ℝ)⁻¹) *
          ∑ b ∈ B, (b : ℝ)⁻¹ := by
    rw [Finset.sum_product]
    simp_rw [Nat.cast_mul, mul_inv]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  unfold squarefreeHarmonic squarefreeCoprimeHarmonic
  change (∑ n ∈ S, (n : ℝ)⁻¹) ≤
    primeFactorEulerPenalty x * ∑ n ∈ B, (n : ℝ)⁻¹
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) =
        ∑ z ∈ S.image f,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ D ×ˢ B,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := hsubset
    _ = (∑ d ∈ D, (d : ℝ)⁻¹) *
          ∑ b ∈ B, (b : ℝ)⁻¹ := hproduct
    _ = primeFactorEulerPenalty x *
          ∑ b ∈ B, (b : ℝ)⁻¹ := by
      rw [show D = x.divisors.filter Squarefree by rfl,
        sum_squarefreeDivisors_inv_eq_penalty hx]

theorem exists_prime_sq_dvd_of_not_squarefree
    {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, p.Prime ∧ p * p ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at hn
  push Not at hn
  exact hn

noncomputable def repeatedPrime (n : ℕ) : ℕ :=
  if hn : ¬ Squarefree n then
    Classical.choose (exists_prime_sq_dvd_of_not_squarefree hn)
  else 2

theorem repeatedPrime_prime
    {n : ℕ} (hn : ¬ Squarefree n) :
    (repeatedPrime n).Prime := by
  unfold repeatedPrime
  rw [dif_pos hn]
  exact (Classical.choose_spec
    (exists_prime_sq_dvd_of_not_squarefree hn)).1

theorem repeatedPrime_sq_dvd
    {n : ℕ} (hn : ¬ Squarefree n) :
    repeatedPrime n * repeatedPrime n ∣ n := by
  unfold repeatedPrime
  rw [dif_pos hn]
  exact (Classical.choose_spec
    (exists_prime_sq_dvd_of_not_squarefree hn)).2

theorem sum_inv_sq_Icc_le_aux
    {Y : ℕ} (hY : 2 ≤ Y) :
    ∑ p ∈ Finset.Icc 2 Y, ((p : ℝ) ^ 2)⁻¹ ≤
      3 / 4 - 1 / (Y : ℝ) := by
  induction Y, hY using Nat.le_induction with
  | base =>
      simp
      norm_num
  | succ Y hY ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hYpos : (0 : ℝ) < Y := by positivity
      have hYsuccpos : (0 : ℝ) < Y + 1 := by positivity
      have hstep :
          (((Y + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
            1 / (Y : ℝ) - 1 / ((Y + 1 : ℕ) : ℝ) := by
        field_simp
        norm_num only [Nat.cast_add, Nat.cast_one] at *
        nlinarith
      calc
        ∑ p ∈ Finset.Icc 2 Y, ((p : ℝ) ^ 2)⁻¹ +
            ((((Y + 1 : ℕ) : ℝ) ^ 2)⁻¹) ≤
          (3 / 4 - 1 / (Y : ℝ)) +
            (1 / (Y : ℝ) - 1 / ((Y + 1 : ℕ) : ℝ)) :=
              add_le_add ih hstep
        _ = 3 / 4 - 1 / (((Y + 1 : ℕ) : ℝ)) := by ring

theorem sum_inv_sq_Icc_le (Y : ℕ) :
    ∑ p ∈ Finset.Icc 2 Y, ((p : ℝ) ^ 2)⁻¹ ≤ 3 / 4 := by
  by_cases hY : 2 ≤ Y
  · have hnonneg : 0 ≤ 1 / (Y : ℝ) := by positivity
    exact (sum_inv_sq_Icc_le_aux hY).trans (by linarith)
  · have hempty : Finset.Icc 2 Y = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hempty]
    norm_num

noncomputable def harmonicUpTo (Y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Y, (n : ℝ)⁻¹

noncomputable def nonsquarefreeHarmonic (Y : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Squarefree n),
    (n : ℝ)⁻¹

theorem nonsquarefreeHarmonic_le (Y : ℕ) :
    nonsquarefreeHarmonic Y ≤ (3 / 4) * harmonicUpTo Y := by
  let Bad := (Finset.Icc 1 Y).filter (fun n => ¬ Squarefree n)
  let P := Finset.Icc 2 Y
  let M := Finset.Icc 1 Y
  let f : ℕ → ℕ × ℕ := fun n =>
    let p := repeatedPrime n
    (p, n / (p * p))
  have hfprod {n : ℕ} (hn : n ∈ Bad) :
      (f n).1 ^ 2 * (f n).2 = n := by
    have hnBad := (Finset.mem_filter.mp hn).2
    dsimp only [f]
    rw [pow_two]
    rw [Nat.mul_div_cancel' (repeatedPrime_sq_dvd hnBad)]
  have hfinj :
      ∀ a ∈ Bad, ∀ b ∈ Bad, f a = f b → a = b := by
    intro a ha b hb hab
    have hprod := congrArg
      (fun z : ℕ × ℕ => z.1 ^ 2 * z.2) hab
    simpa only [hfprod ha, hfprod hb] using hprod
  have hfmem : Bad.image f ⊆ P ×ˢ M := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hnBad, rfl⟩
    have hn := Finset.mem_filter.mp hnBad
    have hnIcc := Finset.mem_Icc.mp hn.1
    have hnNot := hn.2
    have hp := repeatedPrime_prime hnNot
    have hpdvd := repeatedPrime_sq_dvd hnNot
    have hpSqLe : repeatedPrime n * repeatedPrime n ≤ n :=
      Nat.le_of_dvd (by omega) hpdvd
    have hpLe : repeatedPrime n ≤ n := by
      nlinarith [hp.two_le]
    have hpSqPos : 0 < repeatedPrime n * repeatedPrime n := by
      exact Nat.mul_pos hp.pos hp.pos
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨hp.two_le, hpLe.trans hnIcc.2⟩
    · exact Finset.mem_Icc.mpr
        ⟨Nat.div_pos hpSqLe hpSqPos,
          (Nat.div_le_self n _).trans hnIcc.2⟩
  have himage :
      (∑ z ∈ Bad.image f,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹)) =
        ∑ n ∈ Bad, (n : ℝ)⁻¹ := by
    rw [Finset.sum_image hfinj]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Nat.cast_pow, ← Nat.cast_mul, hfprod hn]
  have hsubset :
      (∑ z ∈ Bad.image f,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹)) ≤
        ∑ z ∈ P ×ˢ M,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hfmem
    intro z hzPM hzImage
    positivity
  have hproduct :
      (∑ z ∈ P ×ˢ M,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹)) =
        (∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹) *
          ∑ m ∈ M, (m : ℝ)⁻¹ := by
    rw [Finset.sum_product]
    simp_rw [mul_inv]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  unfold nonsquarefreeHarmonic harmonicUpTo
  change (∑ n ∈ Bad, (n : ℝ)⁻¹) ≤
    (3 / 4) * ∑ n ∈ M, (n : ℝ)⁻¹
  calc
    (∑ n ∈ Bad, (n : ℝ)⁻¹) =
        ∑ z ∈ Bad.image f,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ P ×ˢ M,
          ((((z.1 : ℝ) ^ 2) * z.2)⁻¹) := hsubset
    _ = (∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹) *
          ∑ m ∈ M, (m : ℝ)⁻¹ := hproduct
    _ ≤ (3 / 4) * ∑ m ∈ M, (m : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact sum_inv_sq_Icc_le Y
      · positivity

theorem harmonicUpTo_eq_harmonic (Y : ℕ) :
    harmonicUpTo Y = (harmonic Y : ℝ) := by
  unfold harmonicUpTo
  have h := congrArg (fun q : ℚ => (q : ℝ))
    (harmonic_eq_sum_Icc (n := Y))
  simpa only [Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using h.symm

theorem log_add_one_le_harmonicUpTo (Y : ℕ) :
    Real.log (Y + 1) ≤ harmonicUpTo Y := by
  rw [harmonicUpTo_eq_harmonic]
  exact_mod_cast log_add_one_le_harmonic Y

theorem quarter_harmonicUpTo_le_squarefreeHarmonic (Y : ℕ) :
    (1 / 4) * harmonicUpTo Y ≤ squarefreeHarmonic Y := by
  have hbad := nonsquarefreeHarmonic_le Y
  have hpartition :
      harmonicUpTo Y =
        squarefreeHarmonic Y + nonsquarefreeHarmonic Y := by
    unfold harmonicUpTo squarefreeHarmonic nonsquarefreeHarmonic
      squarefreeUpTo
    simpa only using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.Icc 1 Y) (p := Squarefree)
        (f := fun n => (n : ℝ)⁻¹)).symm
  have hHnonneg : 0 ≤ harmonicUpTo Y := by
    unfold harmonicUpTo
    positivity
  nlinarith

theorem primeFactorEulerPenalty_le_self
    {n : ℕ} (hn : 1 ≤ n) :
    primeFactorEulerPenalty n ≤ n := by
  unfold primeFactorEulerPenalty
  calc
    ∏ p ∈ n.primeFactors, (1 + (p : ℝ)⁻¹) ≤
        ∏ p ∈ n.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hpPos : (0 : ℝ) < p := by positivity
        have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
          simpa [one_div] using
            (inv_le_inv₀ hpPos (by norm_num)).2 hpR
        nlinarith
    _ ≤ (n : ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.zero_lt_of_lt hn)
          (Nat.prod_primeFactors_dvd n)

theorem exists_global_primeFactorEulerPenalty_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100) := by
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1
      eventually_primeFactorEulerPenalty_le_log_rpow
  let N : ℕ := max N₀ 1
  have hN : ∀ n, N ≤ n →
      primeFactorEulerPenalty n ≤
        (Real.log n) ^ ((1 : ℝ) / 100) := by
    intro n hn
    exact hN₀ n ((le_max_left N₀ 1).trans hn)
  have hNone : 1 ≤ N := le_max_right N₀ 1
  let b : ℝ := (1 : ℝ) / 100
  let L : ℝ := (Real.log 2) ^ b
  let C : ℝ := max 1 ((N : ℝ) / L)
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro n
  have hlogmono :
      Real.log 2 ≤ Real.log (n + 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by norm_num)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hbase :
      L ≤ (Real.log (n + 2)) ^ b := by
    exact Real.rpow_le_rpow hlog2.le hlogmono hb.le
  by_cases hnN : N ≤ n
  · have hnlarge := hN n hnN
    have hnone : 1 ≤ n := hNone.trans hnN
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hnone
    have hlogn :
        Real.log n ≤ Real.log (n + 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast (show n ≤ n + 2 by omega)
    have hpow :
        (Real.log n) ^ b ≤
          (Real.log (n + 2)) ^ b := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0))
      · exact hlogn
      · exact hb.le
    calc
      primeFactorEulerPenalty n ≤ (Real.log n) ^ b := hnlarge
      _ ≤ (Real.log (n + 2)) ^ b := hpow
      _ ≤ C * (Real.log (n + 2)) ^ b := by
        exact le_mul_of_one_le_left
          (Real.rpow_nonneg (Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ n + 2 by omega))) _)
          (le_max_left _ _)
      _ = C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100) := by rfl
  · have hnlt : n < N := by omega
    have hpen : primeFactorEulerPenalty n ≤ max 1 (N : ℝ) := by
      by_cases hn0 : n = 0
      · subst n
        simp [primeFactorEulerPenalty]
      · calc
          primeFactorEulerPenalty n ≤ n :=
            primeFactorEulerPenalty_le_self
              (Nat.one_le_iff_ne_zero.mpr hn0)
          _ ≤ N := by exact_mod_cast (Nat.le_of_lt hnlt)
          _ ≤ max 1 (N : ℝ) := le_max_right _ _
    have hNL : (N : ℝ) ≤ C * L := by
      dsimp only [C]
      calc
        (N : ℝ) = ((N : ℝ) / L) * L := by
          field_simp
        _ ≤ max 1 ((N : ℝ) / L) * L :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le
    have honeL : (1 : ℝ) ≤ C * L := by
      have hNoneR : (1 : ℝ) ≤ N := by exact_mod_cast hNone
      exact hNoneR.trans hNL
    calc
      primeFactorEulerPenalty n ≤ max 1 (N : ℝ) := hpen
      _ ≤ C * L := max_le honeL hNL
      _ ≤ C * (Real.log (n + 2)) ^ b :=
        mul_le_mul_of_nonneg_left hbase hC.le
      _ = C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100) := by rfl

noncomputable def coprimePairHarmonic (x Y : ℕ) : ℝ :=
  ∑ b ∈ squarefreeCoprimeUpTo x Y,
    (b : ℝ)⁻¹ * squarefreeCoprimeHarmonic b Y

theorem squarefreeHarmonic_sq_le_pairHarmonic
    {C : ℝ} (hC : 0 < C)
    (hglobal : ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100))
    {x Y : ℕ} (hx : x ≠ 0) :
    (squarefreeHarmonic Y) ^ 2 ≤
      primeFactorEulerPenalty x *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
          coprimePairHarmonic x Y := by
  let B := squarefreeCoprimeUpTo x Y
  let H := squarefreeHarmonic Y
  let K := C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)
  have hlog : 0 < Real.log (Y + 2) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y + 2 by omega))
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hH : 0 ≤ H := by
    dsimp only [H, squarefreeHarmonic]
    positivity
  have hB : 0 ≤ squarefreeCoprimeHarmonic x Y := by
    unfold squarefreeCoprimeHarmonic
    positivity
  have hremoveX :
      H ≤ primeFactorEulerPenalty x *
        squarefreeCoprimeHarmonic x Y := by
    exact squarefreeHarmonic_le_penalty_mul_coprime hx
  have hpoint :
      ∀ b ∈ B,
        H ≤ K * squarefreeCoprimeHarmonic b Y := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbS := Finset.mem_filter.mp hb'.1
    have hbY := (Finset.mem_Icc.mp hbS.1).2
    have hremoveB :=
      squarefreeHarmonic_le_penalty_mul_coprime
        (x := b) (Y := Y)
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hbS.1).1)
    have hlogmono :
        Real.log (b + 2) ≤ Real.log (Y + 2) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast (show b + 2 ≤ Y + 2 by omega)
    have hrpow :
        (Real.log (b + 2)) ^ ((1 : ℝ) / 100) ≤
          (Real.log (Y + 2)) ^ ((1 : ℝ) / 100) := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ b + 2 by omega))
      · exact hlogmono
      · norm_num
    have hpen : primeFactorEulerPenalty b ≤ K := by
      dsimp only [K]
      exact (hglobal b).trans
        (mul_le_mul_of_nonneg_left hrpow hC.le)
    calc
      H ≤ primeFactorEulerPenalty b *
          squarefreeCoprimeHarmonic b Y := hremoveB
      _ ≤ K * squarefreeCoprimeHarmonic b Y :=
        mul_le_mul_of_nonneg_right hpen (by
          unfold squarefreeCoprimeHarmonic
          positivity)
  have hweighted :
      H * squarefreeCoprimeHarmonic x Y ≤
        K * coprimePairHarmonic x Y := by
    have hsum :
        (∑ b ∈ B, (b : ℝ)⁻¹ * H) ≤
          ∑ b ∈ B,
            (b : ℝ)⁻¹ *
              (K * squarefreeCoprimeHarmonic b Y) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpoint b hb) (by positivity)
    unfold coprimePairHarmonic
    change H * (∑ b ∈ B, (b : ℝ)⁻¹) ≤
      K * ∑ b ∈ B,
        (b : ℝ)⁻¹ * squarefreeCoprimeHarmonic b Y
    calc
      H * (∑ b ∈ B, (b : ℝ)⁻¹) =
          ∑ b ∈ B, (b : ℝ)⁻¹ * H := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ ≤ ∑ b ∈ B,
            (b : ℝ)⁻¹ *
              (K * squarefreeCoprimeHarmonic b Y) := hsum
      _ = K * ∑ b ∈ B,
            (b : ℝ)⁻¹ * squarefreeCoprimeHarmonic b Y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have hpenx : 0 ≤ primeFactorEulerPenalty x := by
    unfold primeFactorEulerPenalty
    positivity
  calc
    H ^ 2 = H * H := by ring
    _ ≤ H * (primeFactorEulerPenalty x *
          squarefreeCoprimeHarmonic x Y) :=
      mul_le_mul_of_nonneg_left hremoveX hH
    _ = primeFactorEulerPenalty x *
        (H * squarefreeCoprimeHarmonic x Y) := by ring
    _ ≤ primeFactorEulerPenalty x *
        (K * coprimePairHarmonic x Y) :=
      mul_le_mul_of_nonneg_left hweighted hpenx
    _ = primeFactorEulerPenalty x *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
          coprimePairHarmonic x Y := by
      dsimp only [K]
      ring

def allowedPrimeSubsets (x l : ℕ) : Finset (Finset ℕ) :=
  l.primeFactors.powerset.filter fun t =>
    ∀ p ∈ t, ¬ p ∣ x

theorem allowedPrimeSubsets_eq (x l : ℕ) :
    allowedPrimeSubsets x l =
      (l.primeFactors.filter fun p => ¬ p ∣ x).powerset := by
  ext t
  simp only [allowedPrimeSubsets, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨ht, hcop⟩
    intro p hp
    exact Finset.mem_filter.mpr ⟨ht hp, hcop p hp⟩
  · intro ht
    constructor
    · intro p hp
      exact (Finset.mem_filter.mp (ht hp)).1
    · intro p hp
      exact (Finset.mem_filter.mp (ht hp)).2

theorem allowedPrimeSubsets_card
    {x l : ℕ} (hl : Squarefree l) :
    ((allowedPrimeSubsets x l).card : ℝ) =
      coprimeDivisorCountAF x l := by
  rw [allowedPrimeSubsets_eq]
  unfold coprimeDivisorCountAF
  rw [ArithmeticFunction.prodPrimeFactors_apply hl.ne_zero]
  rw [Finset.card_powerset]
  push_cast
  rw [Finset.prod_ite]
  simp

theorem coprimePairHarmonic_le_truncatedSelbergMass
    {x Y R : ℕ} {q : ℕ × ℕ}
    (hx : 1 < x) (hxEven : Even x) (hq : q ∈ chenPairs x)
    (hYsq : Y ^ 2 ≤ R)
    (hRcut : R ≤ transitionSieveCutoff x) :
    coprimePairHarmonic x Y ≤
      truncatedSelbergMass
        (smoothingTransitionBoundingSieve x q hx hxEven hq) R := by
  let B := squarefreeCoprimeUpTo x Y
  let A : ℕ → Finset ℕ := fun b => squarefreeCoprimeUpTo b Y
  let D := truncatedSieveDivisors (transitionSieveProduct x) R
  let T : ℕ → Finset (Finset ℕ) := fun l => allowedPrimeSubsets x l
  let source := B.sigma A
  let target := D.sigma T
  let f : (Σ _b : ℕ, ℕ) → (Σ _l : ℕ, Finset ℕ) := fun z =>
    ⟨z.1 * z.2, z.1.primeFactors⟩
  have hsource_mem {z : Σ _b : ℕ, ℕ} (hz : z ∈ source) :
      z.1 ∈ B ∧ z.2 ∈ A z.1 :=
    Finset.mem_sigma.mp hz
  have htarget : source.image f ⊆ target := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
    have hw' := hsource_mem hw
    have hb := Finset.mem_filter.mp hw'.1
    have hbS := Finset.mem_filter.mp hb.1
    have hbIcc := Finset.mem_Icc.mp hbS.1
    have hbSf := hbS.2
    have hbx := hb.2
    have ha := Finset.mem_filter.mp hw'.2
    have haS := Finset.mem_filter.mp ha.1
    have haIcc := Finset.mem_Icc.mp haS.1
    have haSf := haS.2
    have hab := ha.2
    have hlSf : Squarefree (w.1 * w.2) :=
      (Nat.squarefree_mul hab.symm).2 ⟨hbSf, haSf⟩
    have hlLe : w.1 * w.2 ≤ R := by
      have : w.1 * w.2 ≤ Y ^ 2 := by
        nlinarith
      exact this.trans hYsq
    have hlP : w.1 * w.2 ∣ transitionSieveProduct x := by
      unfold transitionSieveProduct primorial
      rw [← Nat.prod_primeFactors_of_squarefree hlSf]
      apply Finset.prod_dvd_prod_of_subset
        (w.1 * w.2).primeFactors
        ((Finset.range (transitionSieveCutoff x + 1)).filter Nat.Prime)
        id
      intro p hpL
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpL
      have hpl : p ∣ w.1 * w.2 :=
        (Nat.mem_primeFactors.mp hpL).2.1
      have hpLeL : p ≤ w.1 * w.2 :=
        Nat.le_of_dvd
          (Nat.mul_pos
            (Nat.zero_lt_of_lt hbIcc.1)
            (Nat.zero_lt_of_lt haIcc.1))
          hpl
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_range]
        exact Nat.lt_succ_of_le
          (hpLeL.trans (hlLe.trans hRcut))
      · exact hp
    apply Finset.mem_sigma.mpr
    constructor
    · unfold D truncatedSieveDivisors
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr
          ⟨hlP, transitionSieveProduct_ne_zero x⟩, hlLe⟩
    · unfold T allowedPrimeSubsets
      apply Finset.mem_filter.mpr
      constructor
      · rw [Finset.mem_powerset]
        intro p hpb
        have hpbDvd : p ∣ w.1 :=
          (Nat.mem_primeFactors.mp hpb).2.1
        have hp := Nat.prime_of_mem_primeFactors hpb
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hpbDvd.trans (Nat.dvd_mul_right _ _),
            mul_ne_zero
              (Nat.one_le_iff_ne_zero.mp hbIcc.1)
              (Nat.one_le_iff_ne_zero.mp haIcc.1)⟩
      · intro p hpb hpx
        have hp := Nat.prime_of_mem_primeFactors hpb
        have hpgcd : p ∣ w.1.gcd x := Nat.dvd_gcd
          (Nat.mem_primeFactors.mp hpb).2.1 hpx
        rw [hbx] at hpgcd
        exact hp.not_dvd_one hpgcd
  have hfinj :
      ∀ a ∈ source, ∀ b ∈ source, f a = f b → a = b := by
    intro a ha b hb habEq
    have ha' := hsource_mem ha
    have hb' := hsource_mem hb
    have ha1 := Finset.mem_filter.mp
      (Finset.mem_filter.mp ha'.1).1
    have haIcc := Finset.mem_Icc.mp ha1.1
    have hb1 := Finset.mem_filter.mp
      (Finset.mem_filter.mp hb'.1).1
    have hpf : a.1.primeFactors = b.1.primeFactors :=
      congrArg Sigma.snd habEq
    have hfirst : a.1 = b.1 := by
      rw [← Nat.prod_primeFactors_of_squarefree ha1.2,
        ← Nat.prod_primeFactors_of_squarefree hb1.2, hpf]
    have hmul : a.1 * a.2 = b.1 * b.2 :=
      congrArg Sigma.fst habEq
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    simp only at hfirst hmul ⊢
    subst b1
    have hsecond : a2 = b2 :=
      Nat.mul_left_cancel (Nat.zero_lt_of_lt haIcc.1) hmul
    subst b2
    rfl
  have himage :
      (∑ z ∈ source.image f,
          ((z.1 : ℝ)⁻¹)) =
        ∑ z ∈ source,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    rw [Finset.sum_image hfinj]
  have hsubset :
      (∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹)) ≤
        ∑ z ∈ target, ((z.1 : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg htarget
    intro z hzT hzI
    positivity
  have hsourceSum :
      coprimePairHarmonic x Y =
        ∑ z ∈ source,
          (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := by
    unfold coprimePairHarmonic squarefreeCoprimeHarmonic
    change
      (∑ b ∈ B, (b : ℝ)⁻¹ * ∑ a ∈ A b, (a : ℝ)⁻¹) =
        ∑ z ∈ source, (((z.1 * z.2 : ℕ) : ℝ)⁻¹)
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.cast_mul, mul_inv]
  have htargetMass :
      (∑ z ∈ target, ((z.1 : ℝ)⁻¹)) ≤
        truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q hx hxEven hq) R := by
    let s := smoothingTransitionBoundingSieve x q hx hxEven hq
    unfold truncatedSelbergMass
    change (∑ z ∈ D.sigma T, ((z.1 : ℝ)⁻¹)) ≤
      ∑ l ∈ D, s.selbergTerms l
    rw [Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro l hlD
    have hlP : l ∣ transitionSieveProduct x :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hlD).1
    have hlsf : Squarefree l :=
      (transitionSieveProduct_squarefree x).squarefree_of_dvd hlP
    calc
      ∑ _t ∈ T l, (l : ℝ)⁻¹ =
          ((T l).card : ℝ) * (l : ℝ)⁻¹ := by simp
      _ = coprimeDivisorCountAF x l / l := by
        rw [show T l = allowedPrimeSubsets x l by rfl,
          allowedPrimeSubsets_card hlsf]
        ring
      _ ≤ s.selbergTerms l := by
        exact coprimeDivisorCount_div_le_selbergTerms
          hx hxEven hq hlP hlsf
  calc
    coprimePairHarmonic x Y =
        ∑ z ∈ source, (((z.1 * z.2 : ℕ) : ℝ)⁻¹) := hsourceSum
    _ = ∑ z ∈ source.image f, ((z.1 : ℝ)⁻¹) := himage.symm
    _ ≤ ∑ z ∈ target, ((z.1 : ℝ)⁻¹) := hsubset
    _ ≤ truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q hx hxEven hq) R :=
      htargetMass

end Chen

end

/-! ## ChenTheorem.Lemma5.Boundary.Analytic -/

section

/-!
# Analytic estimates for the boundary term in Chen's Lemma 5

The algebraic Selberg optimization is complete in
`Lemma5/Boundary/Weights.lean`.  This file chooses a small power level and
develops the remaining uniform estimates for its normalization and for
the outer prime-pair sum.
-/

open Filter Real
open scoped Classical Topology

namespace Chen

/-- The reciprocal weight of the admissible Chen pairs is bounded by
the square of the prime harmonic sum.  Retaining primality here avoids
the two full logarithms lost by the ordinary harmonic-series bound. -/
theorem sum_pairQuotient_le_primeReciprocalSq (x : ℕ) :
    ∑ q ∈ chenPairs x,
        (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
      (x : ℝ) *
        (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 := by
  let box : Finset (ℕ × ℕ) := x.primesLE ×ˢ x.primesLE
  have hsubset : chenPairs x ⊆ box := by
    intro q hq
    have hq' := hq
    simp only [chenPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hq'
    exact Finset.mem_product.mpr
      ⟨Nat.mem_primesLE.mpr ⟨by omega, hq'.2.1⟩,
        Nat.mem_primesLE.mpr ⟨by omega, hq'.2.2.1⟩⟩
  calc
    ∑ q ∈ chenPairs x,
        (x : ℝ) / ((q.1 : ℝ) * q.2) ≤
        ∑ q ∈ box,
          (x : ℝ) / ((q.1 : ℝ) * q.2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q _ _
      positivity
    _ = (x : ℝ) *
          (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 := by
      simp only [box, Finset.sum_product, div_eq_mul_inv, mul_inv]
      calc
        (∑ a ∈ x.primesLE, ∑ b ∈ x.primesLE,
            (x : ℝ) * ((a : ℝ)⁻¹ * (b : ℝ)⁻¹)) =
            (x : ℝ) *
              ((∑ a ∈ x.primesLE, (a : ℝ)⁻¹) *
                ∑ b ∈ x.primesLE, (b : ℝ)⁻¹) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = (x : ℝ) *
            (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 := by ring

theorem exp_two_mul_sub_one_le_four_mul
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : 2 * t ≤ 1) :
    Real.exp (2 * t) - 1 ≤ 4 * t := by
  let u : ℝ := 2 * t
  have hu0 : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hu1 : ‖u‖ ≤ 1 := by
    rw [Real.norm_of_nonneg hu0]
    exact ht1
  have hrem := Real.norm_exp_sub_one_sub_id_le hu1
  have hremUpper :
      Real.exp u - 1 - u ≤ u ^ 2 := by
    calc
      Real.exp u - 1 - u ≤ ‖Real.exp u - 1 - u‖ :=
        le_norm_self _
      _ ≤ ‖u‖ ^ 2 := hrem
      _ = u ^ 2 := by rw [Real.norm_of_nonneg hu0]
  have husq : u ^ 2 ≤ u := by
    nlinarith
  dsimp only [u] at hremUpper husq ⊢
  nlinarith

/-- The transition interval has relative width
`O((log x)^(-1/10))`, with the harmless extra `1` coming from its
integer endpoints. -/
theorem smoothingTransition_width_le
    {x : ℕ} {q : ℕ × ℕ} (hq : q ∈ chenPairs x)
    (hsmall :
      2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ 1) :
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ) ≤
      4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
          (Real.log x) ^ (-(0.1 : ℝ)) + 1 := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  let t : ℝ := (Real.log x) ^ (-(0.1 : ℝ))
  let E : ℝ := Real.exp (2 * t)
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    positivity
  have hEpos : 0 < E := by
    dsimp only [E]
    positivity
  have hEone : 1 ≤ E := by
    dsimp only [E]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  have hEsub :
      E - 1 ≤ 4 * t := by
    dsimp only [E]
    exact exp_two_mul_sub_one_le_four_mul ht0 (by
      dsimp only [t]
      exact hsmall)
  have hY0 : 0 ≤ Y := by
    dsimp only [Y]
    positivity
  have hLU :
      smoothingTransitionLower x q ≤
        smoothingTransitionUpper x q :=
    smoothingTransitionLower_le_upper hq
  have hU :
      (smoothingTransitionUpper x q : ℝ) ≤ Y := by
    unfold smoothingTransitionUpper
    dsimp only [Y]
    exact Nat.floor_le (by positivity)
  have hL :
      Y / E - 1 ≤
        (smoothingTransitionLower x q : ℝ) := by
    have hfloor :
        Y / E <
          (smoothingTransitionLower x q : ℝ) + 1 := by
      unfold smoothingTransitionLower
      dsimp only [Y, E, t]
      exact Nat.lt_floor_add_one
        (((x : ℝ) / ((q.1 : ℝ) * q.2)) /
          Real.exp
            (2 * (Real.log x) ^ (-(0.1 : ℝ))))
    linarith
  have hwidth :
      ((smoothingTransitionUpper x q -
          smoothingTransitionLower x q : ℕ) : ℝ) ≤
        Y - Y / E + 1 := by
    rw [Nat.cast_sub hLU]
    linarith
  have hYdiv : Y / E ≤ Y := div_le_self hY0 hEone
  have hidentity :
      Y - Y / E = (Y / E) * (E - 1) := by
    field_simp
  have hrelative :
      Y - Y / E ≤ Y * (E - 1) := by
    rw [hidentity]
    exact mul_le_mul hYdiv le_rfl (sub_nonneg.mpr hEone) hY0
  calc
    ((smoothingTransitionUpper x q -
        smoothingTransitionLower x q : ℕ) : ℝ) ≤
        Y - Y / E + 1 := hwidth
    _ ≤ Y * (E - 1) + 1 := by linarith
    _ ≤ Y * (4 * t) + 1 := by gcongr
    _ = 4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
          (Real.log x) ^ (-(0.1 : ℝ)) + 1 := by
      dsimp only [Y, t]
      ring

theorem eventually_transition_width_small :
    ∀ᶠ x : ℕ in atTop,
      2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ 1 := by
  have hreal :
      Tendsto (fun y : ℝ =>
        2 * y ^ (-(0.1 : ℝ))) atTop (𝓝 0) := by
    have hrpow :
        Tendsto (fun y : ℝ => y ^ (-(0.1 : ℝ)))
          atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.1)
    have htwo :
        Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) :=
      tendsto_const_nhds
    simpa only [mul_zero] using htwo.mul hrpow
  have hlogNat :
      Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (hreal.comp hlogNat).eventually
    (eventually_le_nhds zero_lt_one)

/-- The pair range supplies exactly the logarithm needed to cancel the
von Mangoldt bound in the boundary sum. -/
theorem pairLog_inv_mul_log_le_three
    {x : ℕ} {q : ℕ × ℕ} (hx : 1 < x)
    (hq : q ∈ chenPairs x) :
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        Real.log x ≤ 3 := by
  let Y : ℝ := (x : ℝ) / ((q.1 : ℝ) * q.2)
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx)
  have hY : (x : ℝ) ^ ((1 : ℝ) / 3) < Y :=
    rpow_third_lt_pairQuotient hq
  have hpowpos :
      0 < (x : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hlogLower :
      (1 : ℝ) / 3 * Real.log x ≤ Real.log Y := by
    calc
      (1 : ℝ) / 3 * Real.log x =
          Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)) := by
        rw [Real.log_rpow hxpos]
      _ ≤ Real.log Y :=
        Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr hpowpos)
          (Set.mem_Ioi.mpr (hpowpos.trans hY)) hY.le
  have hlogY : 0 < Real.log Y := by
    linarith
  change (Real.log Y)⁻¹ * Real.log x ≤ 3
  rw [inv_mul_eq_div, div_le_iff₀ hlogY]
  nlinarith

theorem sum_smoothingTransition_width_le
    {x : ℕ}
    (hsmall :
      2 * (Real.log x) ^ (-(0.1 : ℝ)) ≤ 1) :
    ∑ q ∈ chenPairs x,
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) ≤
      4 * (Real.log x) ^ (-(0.1 : ℝ)) * (x : ℝ) *
          (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 +
        ((chenPairs x).card : ℝ) := by
  calc
    ∑ q ∈ chenPairs x,
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) ≤
        ∑ q ∈ chenPairs x,
          (4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
              (Real.log x) ^ (-(0.1 : ℝ)) + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      exact smoothingTransition_width_le hq hsmall
    _ = 4 * (Real.log x) ^ (-(0.1 : ℝ)) *
          (∑ q ∈ chenPairs x,
            (x : ℝ) / ((q.1 : ℝ) * q.2)) +
          ((chenPairs x).card : ℝ) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul]
      calc
        (∑ q ∈ chenPairs x,
            4 * ((x : ℝ) / ((q.1 : ℝ) * q.2)) *
              (Real.log x) ^ (-(0.1 : ℝ))) +
              ((chenPairs x).card : ℝ) * 1 =
            (∑ q ∈ chenPairs x,
              4 * (Real.log x) ^ (-(0.1 : ℝ)) *
                ((x : ℝ) / ((q.1 : ℝ) * q.2))) +
              ((chenPairs x).card : ℝ) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro q hq
            ring
          · ring
        _ = 4 * (Real.log x) ^ (-(0.1 : ℝ)) *
              (∑ q ∈ chenPairs x,
                (x : ℝ) / ((q.1 : ℝ) * q.2)) +
              ((chenPairs x).card : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ 4 * (Real.log x) ^ (-(0.1 : ℝ)) *
          ((x : ℝ) *
            (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2) +
          ((chenPairs x).card : ℝ) := by
      gcongr
      exact sum_pairQuotient_le_primeReciprocalSq x
    _ = 4 * (Real.log x) ^ (-(0.1 : ℝ)) * (x : ℝ) *
          (∑ p ∈ x.primesLE, (p : ℝ)⁻¹) ^ 2 +
        ((chenPairs x).card : ℝ) := by ring

/-- A deliberately small Selberg level.  The exponent leaves ample room
for the polynomial congruence-count error. -/
noncomputable def transitionSelbergLevel (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 10000)⌋₊

theorem one_le_transitionSelbergLevel {x : ℕ} (hx : 1 ≤ x) :
    1 ≤ transitionSelbergLevel x := by
  unfold transitionSelbergLevel
  rw [Nat.le_floor_iff (by positivity)]
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  simpa using Real.one_le_rpow hxR (by norm_num :
    (0 : ℝ) ≤ (1 : ℝ) / 10000)

theorem transitionSelbergLevel_le_cutoff {x : ℕ} (hx : 1 ≤ x) :
    transitionSelbergLevel x ≤ transitionSieveCutoff x := by
  unfold transitionSelbergLevel transitionSieveCutoff
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hx) (by norm_num)

theorem transitionSelbergLevel_cast_le_rpow (x : ℕ) :
    (transitionSelbergLevel x : ℝ) ≤
      (x : ℝ) ^ ((1 : ℝ) / 10000) := by
  unfold transitionSelbergLevel
  exact Nat.floor_le (by positivity)

/-- Half the logarithmic Selberg level, used for the two squarefree
factors in the lower-bound convolution. -/
noncomputable def transitionSelbergHalfLevel (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((1 : ℝ) / 20000)⌋₊

theorem transitionSelbergHalfLevel_sq_le_level
    {x : ℕ} (hx : 1 ≤ x) :
    transitionSelbergHalfLevel x ^ 2 ≤ transitionSelbergLevel x := by
  unfold transitionSelbergLevel
  rw [Nat.le_floor_iff (by positivity)]
  have hY :
      (transitionSelbergHalfLevel x : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 20000) := by
    unfold transitionSelbergHalfLevel
    exact Nat.floor_le (by positivity)
  have hYnonneg : (0 : ℝ) ≤ transitionSelbergHalfLevel x := by positivity
  have hsq :
      (transitionSelbergHalfLevel x : ℝ) ^ 2 ≤
        ((x : ℝ) ^ ((1 : ℝ) / 20000)) ^ 2 :=
    pow_le_pow_left₀ hYnonneg hY 2
  norm_num only [Nat.cast_pow]
  calc
    (transitionSelbergHalfLevel x : ℝ) ^ 2 ≤
        ((x : ℝ) ^ ((1 : ℝ) / 20000)) ^ 2 := hsq
    _ = (x : ℝ) ^ ((1 : ℝ) / 10000) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul
        (by exact_mod_cast (Nat.zero_le x))]
      congr 1
      norm_num

theorem rpow_lt_transitionSelbergHalfLevel_add_one (x : ℕ) :
    (x : ℝ) ^ ((1 : ℝ) / 20000) <
      transitionSelbergHalfLevel x + 1 := by
  unfold transitionSelbergHalfLevel
  exact_mod_cast Nat.lt_floor_add_one
    ((x : ℝ) ^ ((1 : ℝ) / 20000))

theorem transitionSelbergMass_cross_lower
    {C : ℝ} (hC : 0 < C)
    (hglobal : ∀ n : ℕ,
      primeFactorEulerPenalty n ≤
        C * (Real.log (n + 2)) ^ ((1 : ℝ) / 100))
    {x : ℕ} (hx : 1 < x) (hxEven : Even x)
    {q : ℕ × ℕ} (hq : q ∈ chenPairs x) :
    ((1 / 4) *
        Real.log (transitionSelbergHalfLevel x + 1)) ^ 2 ≤
      primeFactorEulerPenalty x *
        (C * (Real.log (transitionSelbergHalfLevel x + 2)) ^
          ((1 : ℝ) / 100)) *
        truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q hx hxEven hq)
          (transitionSelbergLevel x) := by
  let Y := transitionSelbergHalfLevel x
  let R := transitionSelbergLevel x
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  have hlogH :
      (1 / 4) * Real.log (Y + 1) ≤
        squarefreeHarmonic Y := by
    calc
      (1 / 4) * Real.log (Y + 1) ≤
          (1 / 4) * harmonicUpTo Y :=
        mul_le_mul_of_nonneg_left
          (log_add_one_le_harmonicUpTo Y) (by norm_num)
      _ ≤ squarefreeHarmonic Y :=
        quarter_harmonicUpTo_le_squarefreeHarmonic Y
  have hlogNonneg : 0 ≤ Real.log (Y + 1) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ Y + 1 by omega)
  have hsq :
      ((1 / 4) * Real.log (Y + 1)) ^ 2 ≤
        (squarefreeHarmonic Y) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hlogNonneg) hlogH 2
  have hpair :=
    squarefreeHarmonic_sq_le_pairHarmonic
      hC hglobal (x := x) (Y := Y) (by omega)
  have hpairMass :=
    coprimePairHarmonic_le_truncatedSelbergMass
      hx hxEven hq
      (transitionSelbergHalfLevel_sq_le_level
        (show 1 ≤ x by omega))
      (transitionSelbergLevel_le_cutoff
        (show 1 ≤ x by omega))
  have hfactor :
      0 ≤ primeFactorEulerPenalty x *
        (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) := by
    apply mul_nonneg
    · unfold primeFactorEulerPenalty
      positivity
    · exact mul_nonneg hC.le
        (Real.rpow_nonneg
          (Real.log_nonneg (by
            exact_mod_cast (show 1 ≤ Y + 2 by omega))) _)
  calc
    ((1 / 4) * Real.log (Y + 1)) ^ 2 ≤
        (squarefreeHarmonic Y) ^ 2 := hsq
    _ ≤ primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
            coprimePairHarmonic x Y := hpair
    _ ≤ primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ ((1 : ℝ) / 100)) *
            truncatedSelbergMass s R :=
      mul_le_mul_of_nonneg_left hpairMass hfactor

/-- At the chosen level the Selberg normalization has essentially
dimension-two logarithmic size, uniformly in the admissible Chen pair. -/
theorem eventually_transitionSelbergMass_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop,
      ∀ hx : 1 < x, ∀ hxEven : Even x, ∀ q,
        ∀ hq : q ∈ chenPairs x,
        c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
          truncatedSelbergMass
            (smoothingTransitionBoundingSieve x q
              hx hxEven hq)
            (transitionSelbergLevel x) := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_global_primeFactorEulerPenalty_bound
  let a : ℝ := (1 : ℝ) / 20000
  let b : ℝ := (1 : ℝ) / 100
  let c : ℝ := a ^ 2 / (32 * C)
  have ha : 0 < a := by
    dsimp only [a]
    norm_num
  have hb : 0 < b := by
    dsimp only [b]
    norm_num
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, ?_⟩
  have hxlarge : ∀ᶠ x : ℕ in atTop, 2 ≤ x :=
    eventually_ge_atTop 2
  have hlogone : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log x :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop 1)
  filter_upwards
      [hxlarge, hlogone,
        eventually_primeFactorEulerPenalty_le_log_rpow] with
      x hx2 hxlog1 hpen
  intro hx hxEven q hq
  let Y := transitionSelbergHalfLevel x
  let R := transitionSelbergLevel x
  let s := smoothingTransitionBoundingSieve x q hx hxEven hq
  let L := Real.log x
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast hx)
  have hYcast :
      (Y : ℝ) ≤ (x : ℝ) ^ a := by
    dsimp only [Y, a, transitionSelbergHalfLevel]
    exact Nat.floor_le (by positivity)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hrpowx : (x : ℝ) ^ a ≤ x := by
    exact Real.rpow_le_self_of_one_le hxR (by
      dsimp only [a]
      norm_num)
  have hYxR : (Y : ℝ) ≤ x := hYcast.trans hrpowx
  have hYx : Y ≤ x := by exact_mod_cast hYxR
  have hYlogUpper :
      Real.log (Y + 2) ≤ 2 * L := by
    have harg : (Y + 2 : ℕ) ≤ 2 * x := by omega
    have hlogmono :
        Real.log (Y + 2) ≤ Real.log (2 * x) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact Set.mem_Ioi.mpr (by positivity)
      · exact_mod_cast harg
    have hlog2le : Real.log 2 ≤ L := by
      dsimp only [L]
      exact Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (by norm_num))
        (Set.mem_Ioi.mpr (by exact_mod_cast (show 0 < x by omega)))
        (by exact_mod_cast hx2)
    calc
      Real.log (Y + 2) ≤ Real.log (2 * x) := hlogmono
      _ = Real.log 2 + L := by
        dsimp only [L]
        rw [Real.log_mul (by norm_num) (by exact_mod_cast (show x ≠ 0 by omega))]
      _ ≤ 2 * L := by linarith
  have hYpow :
      (Real.log (Y + 2)) ^ b ≤ 2 * L ^ b := by
    have hbase :
        (Real.log (Y + 2)) ^ b ≤ (2 * L) ^ b := by
      apply Real.rpow_le_rpow
      · exact Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ Y + 2 by omega))
      · exact hYlogUpper
      · exact hb.le
    have hmul :
        (2 * L) ^ b = (2 : ℝ) ^ b * L ^ b :=
      Real.mul_rpow (by norm_num) hL.le
    have htwo : (2 : ℝ) ^ b ≤ 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by
        dsimp only [b]
        norm_num)
    calc
      (Real.log (Y + 2)) ^ b ≤ (2 * L) ^ b := hbase
      _ = (2 : ℝ) ^ b * L ^ b := hmul
      _ ≤ 2 * L ^ b :=
        mul_le_mul_of_nonneg_right htwo
          (Real.rpow_nonneg hL.le _)
  have hYlogLower :
      a * L ≤ Real.log (Y + 1) := by
    have hlt := rpow_lt_transitionSelbergHalfLevel_add_one x
    have hlogmono :
        Real.log ((x : ℝ) ^ a) ≤ Real.log (Y + 1) := by
      apply Real.strictMonoOn_log.monotoneOn
      · exact Set.mem_Ioi.mpr (Real.rpow_pos_of_pos (by positivity) _)
      · exact Set.mem_Ioi.mpr (by positivity)
      · simpa only [Y, a] using hlt.le
    rw [Real.log_rpow (by positivity) a] at hlogmono
    simpa only [L] using hlogmono
  have hcross :=
    transitionSelbergMass_cross_lower
      hC hglobal hx hxEven hq
  have hmassPos : 0 < truncatedSelbergMass s R := by
    apply truncatedSelbergMass_pos
    exact one_le_transitionSelbergLevel (show 1 ≤ x by omega)
  have hpen' : primeFactorEulerPenalty x ≤ L ^ b := by
    simpa only [L, b] using hpen
  have hfactorUpper :
      primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ b) ≤
        2 * C * (L ^ b) ^ 2 := by
    calc
      primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ b) ≤
        L ^ b * (C * (Real.log (Y + 2)) ^ b) := by
          exact mul_le_mul_of_nonneg_right hpen'
            (mul_nonneg hC.le
              (Real.rpow_nonneg
                (Real.log_nonneg (by
                  exact_mod_cast (show 1 ≤ Y + 2 by omega))) _))
      _ ≤ L ^ b * (C * (2 * L ^ b)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hYpow hC.le)
            (Real.rpow_nonneg hL.le _)
      _ = 2 * C * (L ^ b) ^ 2 := by ring
  have hleftLower :
      ((a / 4) * L) ^ 2 ≤
        ((1 / 4) * Real.log (Y + 1)) ^ 2 := by
    apply pow_le_pow_left₀
    · positivity
    · calc
        (a / 4) * L = (1 / 4) * (a * L) := by ring
        _ ≤ (1 / 4) * Real.log (Y + 1) :=
          mul_le_mul_of_nonneg_left hYlogLower (by norm_num)
  have hcore :
      ((a / 4) * L) ^ 2 ≤
        (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R := by
    calc
      ((a / 4) * L) ^ 2 ≤
          ((1 / 4) * Real.log (Y + 1)) ^ 2 := hleftLower
      _ ≤ primeFactorEulerPenalty x *
          (C * (Real.log (Y + 2)) ^ b) *
            truncatedSelbergMass s R := by
        simpa only [Y, R, s] using hcross
      _ ≤ (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R :=
        mul_le_mul_of_nonneg_right hfactorUpper hmassPos.le
  have hpowIdentity :
      L ^ (2 : ℕ) =
        (L ^ b) ^ 2 * L ^ ((99 : ℝ) / 50) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    congr 1
    dsimp only [b]
    norm_num
  have hscaled :
      (2 * C * (L ^ b) ^ 2) *
          (c * L ^ ((99 : ℝ) / 50)) ≤
        (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R := by
    calc
      (2 * C * (L ^ b) ^ 2) *
          (c * L ^ ((99 : ℝ) / 50)) =
        ((a / 4) * L) ^ 2 := by
          dsimp only [c]
          calc
            (2 * C * (L ^ b) ^ 2) *
                (a ^ 2 / (32 * C) * L ^ ((99 : ℝ) / 50)) =
              (a ^ 2 / 16) *
                ((L ^ b) ^ 2 * L ^ ((99 : ℝ) / 50)) := by
                field_simp
                ring
            _ = (a ^ 2 / 16) * L ^ 2 := by rw [← hpowIdentity]
            _ = ((a / 4) * L) ^ 2 := by ring
      _ ≤ (2 * C * (L ^ b) ^ 2) *
          truncatedSelbergMass s R := hcore
  have hcoefPos : 0 < 2 * C * (L ^ b) ^ 2 := by positivity
  have h198 :
      c * L ^ ((99 : ℝ) / 50) ≤
        truncatedSelbergMass s R := by
    nlinarith [hscaled]
  have h197 :
      L ^ ((197 : ℝ) / 100) ≤
        L ^ ((99 : ℝ) / 50) := by
    apply Real.rpow_le_rpow_of_exponent_le hxlog1
    norm_num
  calc
    c * (Real.log x) ^ ((197 : ℝ) / 100) =
        c * L ^ ((197 : ℝ) / 100) := by rfl
    _ ≤ c * L ^ ((99 : ℝ) / 50) :=
      mul_le_mul_of_nonneg_left h197 hc.le
    _ ≤ truncatedSelbergMass s R := h198

/-- The explicit polynomial error at the chosen level has a fixed power
saving even after summing over the crude `x^(5/6)` bound for Chen pairs.
This purely asymptotic estimate is kept separate from the normalization
lower bound. -/
theorem eventually_transitionLevel_error_power_bound :
    ∀ᶠ x : ℕ in atTop,
      ((transitionSelbergLevel x : ℝ) *
          ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
        ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
          (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1) *
            (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x ≤
        (x : ℝ) ^ ((9 : ℝ) / 10) := by
  have hxone : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ x :=
    eventually_atTop.2 ⟨1, fun _ hx => by exact_mod_cast hx⟩
  have hlog :
      ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ≤
        (x : ℝ) ^ ((1 : ℝ) / 1000) := by
    have hδ : (0 : ℝ) < (1 : ℝ) / 1000 := by norm_num
    have hreal :
        ∀ᶠ y : ℝ in atTop,
          ‖Real.log y ^ (1 : ℝ)‖ ≤
            ‖y ^ ((1 : ℝ) / 1000)‖ :=
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ) hδ).eventuallyLE
    have hnat :=
      tendsto_natCast_atTop_atTop.eventually hreal
    filter_upwards [hnat, eventually_gt_atTop 1] with x hx hx1
    have hxpos : (0 : ℝ) < x := by positivity
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx1)
    simpa [Real.norm_of_nonneg hlogpos.le,
      Real.norm_of_nonneg
        (Real.rpow_nonneg hxpos.le _)] using hx
  have hgap : (0 : ℝ) <
      (9 : ℝ) / 10 - (12527 : ℝ) / 15000 := by norm_num
  have hpowerReal :
      ∀ᶠ y : ℝ in atTop,
        2304 * y ^ ((12527 : ℝ) / 15000) ≤
          y ^ ((9 : ℝ) / 10) := by
    have hlarge :=
      (tendsto_rpow_atTop hgap).eventually
        (eventually_ge_atTop (2304 : ℝ))
    filter_upwards [hlarge, eventually_gt_atTop 0] with y hy hypos
    calc
      2304 * y ^ ((12527 : ℝ) / 15000) ≤
          y ^ ((9 : ℝ) / 10 - (12527 : ℝ) / 15000) *
            y ^ ((12527 : ℝ) / 15000) :=
        mul_le_mul_of_nonneg_right hy
          (Real.rpow_nonneg hypos.le _)
      _ = y ^ ((9 : ℝ) / 10) := by
        rw [← Real.rpow_add hypos]
        congr 1
        ring
  have hpower :
      ∀ᶠ x : ℕ in atTop,
        2304 * (x : ℝ) ^ ((12527 : ℝ) / 15000) ≤
          (x : ℝ) ^ ((9 : ℝ) / 10) :=
    tendsto_natCast_atTop_atTop.eventually hpowerReal
  filter_upwards [hxone, hlog, hpower] with x hx1 hlog hpower
  let R : ℝ := transitionSelbergLevel x
  have hR0 : 0 ≤ R := by positivity
  have hRle :
      R ≤ (x : ℝ) ^ ((1 : ℝ) / 10000) :=
    transitionSelbergLevel_cast_le_rpow x
  have hpow1 :
      (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 10000) :=
    Real.one_le_rpow hx1 (by norm_num)
  have hRadd :
      R + 1 ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 10000) := by
    nlinarith
  have hNatAdd :
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ≤
        2 * (x : ℝ) ^ ((1 : ℝ) / 10000) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact hRadd
  have hthree :
      3 * R ^ 2 + 1 ≤
        4 * ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 2 := by
    have hsq :
        R ^ 2 ≤ ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 2 :=
      (sq_le_sq₀ hR0 (Real.rpow_nonneg (by positivity) _)).2 hRle
    nlinarith [hpow1]
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans_le hx1
  let X : ℝ := (x : ℝ) ^ ((1 : ℝ) / 10000)
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hRR :
      R * (R + 1) ≤ 2 * X ^ 2 := by
    dsimp only [X]
    calc
      R * (R + 1) ≤
          (x : ℝ) ^ ((1 : ℝ) / 10000) *
            (2 * (x : ℝ) ^ ((1 : ℝ) / 10000)) :=
        mul_le_mul hRle hRadd (by positivity) (by positivity)
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 2 := by ring
  have hfirst :
      (R * (R + 1)) ^ 2 ≤ 4 * X ^ 4 := by
    have hsquare :=
      pow_le_pow_left₀ (mul_nonneg hR0 (by positivity)) hRR 2
    nlinarith [sq_nonneg (X ^ 2)]
  have hsecond :
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 ≤
        4 * X ^ 2 := by
    have hsquare :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
        (transitionSelbergLevel x + 1 : ℕ)) hNatAdd 2
    dsimp only [X]
    nlinarith [sq_nonneg ((x : ℝ) ^ ((1 : ℝ) / 10000))]
  have hthird :
      3 * R ^ 2 + 1 ≤ 4 * X ^ 2 := by
    simpa only [X] using hthree
  have hrpowmul :
      ((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 *
          (x : ℝ) ^ ((5 : ℝ) / 6) *
            (x : ℝ) ^ ((1 : ℝ) / 1000) =
        (x : ℝ) ^ ((12527 : ℝ) / 15000) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le,
      ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    congr 1
    norm_num
  calc
    (R * (R + 1)) ^ 2 *
          ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
            (3 * R ^ 2 + 1) *
              (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                Real.log x ≤
        2304 *
          (((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 *
            (x : ℝ) ^ ((5 : ℝ) / 6) *
              (x : ℝ) ^ ((1 : ℝ) / 1000)) := by
      calc
        (R * (R + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * R ^ 2 + 1) *
                  (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                    Real.log x ≤
            (4 * X ^ 4) * (4 * X ^ 2) * (4 * X ^ 2) *
              (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
                ((x : ℝ) ^ ((1 : ℝ) / 1000)) := by
          gcongr
        _ = 576 * (X ^ 8 *
              (x : ℝ) ^ ((5 : ℝ) / 6) *
                (x : ℝ) ^ ((1 : ℝ) / 1000)) := by ring
        _ ≤ 2304 * (((x : ℝ) ^ ((1 : ℝ) / 10000)) ^ 8 *
              (x : ℝ) ^ ((5 : ℝ) / 6) *
                (x : ℝ) ^ ((1 : ℝ) / 1000)) := by
          dsimp only [X]
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 2304 * (x : ℝ) ^ ((12527 : ℝ) / 15000) := by
      rw [hrpowmul]
    _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := hpower

/-- The optimized upper-bound sieve, normalized by the uniform lower
bound for `G(R)`, applied to one admissible prime pair. -/
theorem smoothingBoundaryLargeBase_pair_le
    {x : ℕ} {q : ℕ × ℕ} {c : ℝ}
    (hx : 2 ≤ x) (hxEven : Even x) (hq : q ∈ chenPairs x)
    (hc : 0 < c)
    (hmass :
      c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
        truncatedSelbergMass
          (smoothingTransitionBoundingSieve x q
            (by omega) hxEven hq)
          (transitionSelbergLevel x)) :
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        (∑ n ∈ (smoothingBoundaryIndices x q).filter
            (fun n =>
              ¬(n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
          ArithmeticFunction.vonMangoldt n) ≤
      3 *
        (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((transitionSelbergLevel x : ℝ) *
              ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
            ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
              (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)) := by
  let s :=
    smoothingTransitionBoundingSieve x q (by omega) hxEven hq
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  let W : ℝ :=
    (smoothingTransitionUpper x q -
      smoothingTransitionLower x q : ℕ)
  have hR : 1 ≤ transitionSelbergLevel x :=
    one_le_transitionSelbergLevel (by omega)
  have hinner :=
    smoothingBoundaryLargeBase_inner_le_siftedCard hx q
  have hsieve :=
    smoothingTransitionSifted_card_le_optimal
      (x := x) (q := q) (R := transitionSelbergLevel x)
      (by omega) hxEven hq hR
  dsimp only at hsieve
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hleftPos :
      0 < c * (Real.log x) ^ ((197 : ℝ) / 100) := by
    positivity
  have hGpos :
      0 < truncatedSelbergMass s (transitionSelbergLevel x) :=
    truncatedSelbergMass_pos s hR
  have hinv :
      (truncatedSelbergMass s
          (transitionSelbergLevel x))⁻¹ ≤
        (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ :=
    (inv_le_inv₀ hGpos hleftPos).2 (by
      simpa only [s] using hmass)
  have hpairLog :=
    pairLog_inv_mul_log_le_three
      (show 1 < x by omega) hq
  have hweight0 :
      0 ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
    have hY := one_lt_pairQuotient hq
    exact inv_nonneg.mpr (Real.log_nonneg hY.le)
  have hmain0 :
      0 ≤
        ((smoothingTransitionUpper x q -
            smoothingTransitionLower x q : ℕ) : ℝ) *
          (truncatedSelbergMass s
            (transitionSelbergLevel x))⁻¹ + E := by
    dsimp only [E]
    positivity
  calc
    (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
        (∑ n ∈ (smoothingBoundaryIndices x q).filter
            (fun n =>
              ¬(n.minFac : ℝ) ≤
                (x : ℝ) ^ ((1 : ℝ) / 100)),
          ArithmeticFunction.vonMangoldt n) ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          (Real.log x *
            (smoothingTransitionSiftedIndices x q).card) := by
      gcongr
    _ ≤
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          (Real.log x *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) *
              (truncatedSelbergMass s
                (transitionSelbergLevel x))⁻¹ + E)) := by
      gcongr
    _ =
        ((Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          Real.log x) *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) *
              (truncatedSelbergMass s
                (transitionSelbergLevel x))⁻¹ + E) := by ring
    _ ≤ 3 *
          (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (truncatedSelbergMass s
              (transitionSelbergLevel x))⁻¹ + E) :=
      mul_le_mul_of_nonneg_right hpairLog hmain0
    _ ≤ 3 *
          (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
            E) := by
      gcongr
    _ = 3 *
        (((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((transitionSelbergLevel x : ℝ) *
              ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
            ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
              (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)) := by
      rfl

theorem smoothingBoundaryLargeBaseMass_le_explicit
    {x : ℕ} {c : ℝ} (hx : 2 ≤ x) (hxEven : Even x)
    (hc : 0 < c)
    (hmass :
      ∀ q, ∀ hq : q ∈ chenPairs x,
        c * (Real.log x) ^ ((197 : ℝ) / 100) ≤
          truncatedSelbergMass
            (smoothingTransitionBoundingSieve x q
              (by omega) hxEven hq)
            (transitionSelbergLevel x)) :
    smoothingBoundaryLargeBaseMass x ≤
      3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((chenPairs x).card : ℝ) *
            (((transitionSelbergLevel x : ℝ) *
                ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1))) := by
  unfold smoothingBoundaryLargeBaseMass
  let A : ℝ :=
    (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  calc
    ∑ q ∈ chenPairs x,
        (Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ *
          ∑ n ∈ (smoothingBoundaryIndices x q).filter
              (fun n =>
                ¬(n.minFac : ℝ) ≤
                  (x : ℝ) ^ ((1 : ℝ) / 100)),
            ArithmeticFunction.vonMangoldt n ≤
        ∑ q ∈ chenPairs x,
          3 *
            (((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ) * A + E) := by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [A, E] using
        smoothingBoundaryLargeBase_pair_le
          hx hxEven hq hc (hmass q hq)
    _ = 3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) * A +
          ((chenPairs x).card : ℝ) * E) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_const]
      simp only [nsmul_eq_mul]
    _ = 3 *
        ((∑ q ∈ chenPairs x,
            ((smoothingTransitionUpper x q -
                smoothingTransitionLower x q : ℕ) : ℝ)) *
            (c * (Real.log x) ^ ((197 : ℝ) / 100))⁻¹ +
          ((chenPairs x).card : ℝ) *
            (((transitionSelbergLevel x : ℝ) *
                ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
              ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
                (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1))) := by
      rfl

/-- The large-base part of the smoothing boundary has the logarithmic
saving required in Lemma 5. -/
theorem eventually_smoothingBoundaryLargeBaseMass_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, Even x →
      smoothingBoundaryLargeBaseMass x ≤
        C * (x : ℝ) / (Real.log x) ^ (2.01 : ℝ) := by
  obtain ⟨c, hc, hmass⟩ :=
    eventually_transitionSelbergMass_lower
  let C : ℝ := 3 * (13 * c⁻¹ + 1)
  have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have hpowFiveSixths :=
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 6) (r := (2.01 : ℝ)) (by norm_num)
  have hpowNineTenths :=
    eventually_rpow_one_sub_le_div_log_rpow
      (δ := (1 : ℝ) / 10) (r := (2.01 : ℝ)) (by norm_num)
  filter_upwards [hmass, eventually_transition_width_small,
      eventually_sum_inv_primesLE_sq_le_log_rpow,
      eventually_transitionLevel_error_power_bound,
      hpowFiveSixths, hpowNineTenths,
      eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop 1)] with
      x hmass hsmall hprime herr hpowFiveSixths
        hpowNineTenths hx hL
  intro hxEven
  let L : ℝ := Real.log x
  let P : ℝ := ∑ p ∈ x.primesLE, (p : ℝ)⁻¹
  let A : ℝ := (c * L ^ ((197 : ℝ) / 100))⁻¹
  let E : ℝ :=
    ((transitionSelbergLevel x : ℝ) *
        ((transitionSelbergLevel x : ℝ) + 1)) ^ 2 *
      ((transitionSelbergLevel x + 1 : ℕ) : ℝ) ^ 2 *
        (3 * (transitionSelbergLevel x : ℝ) ^ 2 + 1)
  let Q : ℝ := ((chenPairs x).card : ℝ)
  let T : ℝ :=
    (x : ℝ) / (Real.log x) ^ (2.01 : ℝ)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact zero_lt_one.trans_le hL
  have hLone : 1 ≤ L := by
    simpa only [L, Function.comp_apply] using hL
  have hP : P ^ 2 ≤ L ^ ((1 : ℝ) / 25) := by
    simpa only [P, L] using hprime
  have hQ : Q ≤ 9 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
    dsimp only [Q]
    exact chenPairs_card_cast_le x (by omega)
  have hwidth :=
    sum_smoothingTransition_width_le (x := x) hsmall
  have hexplicit :=
    smoothingBoundaryLargeBaseMass_le_explicit
      hx hxEven hc (fun q hq =>
        hmass (show 1 < x by omega) hxEven q hq)
  have hAeq :
      A = c⁻¹ * L ^ (-(197 : ℝ) / 100) := by
    dsimp only [A]
    rw [mul_inv, ← Real.rpow_neg hLpos.le]
    congr 2
    ring
  have hApos : 0 < A := by
    dsimp only [A]
    positivity
  have hAle : A ≤ c⁻¹ := by
    have hpowOne :
        1 ≤ L ^ ((197 : ℝ) / 100) :=
      Real.one_le_rpow hL (by norm_num)
    have hbase :
        c ≤ c * L ^ ((197 : ℝ) / 100) := by
      nlinarith [mul_le_mul_of_nonneg_left hpowOne hc.le]
    dsimp only [A]
    exact (inv_le_inv₀ (mul_pos hc (by positivity)) hc).2 hbase
  have hpowCombine :
      L ^ (-(0.1 : ℝ)) *
          L ^ ((1 : ℝ) / 25) *
            L ^ (-(197 : ℝ) / 100) =
        L ^ (-(203 : ℝ) / 100) := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    congr 1
    norm_num
  have hlogPower :
      L ^ (-(203 : ℝ) / 100) ≤
        (L ^ (2.01 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hLpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hL
    norm_num
  have hmainShort :
      4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A ≤
        4 * c⁻¹ * T := by
    calc
      4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A ≤
          4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) *
            L ^ ((1 : ℝ) / 25) * A := by
        gcongr
      _ = 4 * c⁻¹ * (x : ℝ) *
          L ^ (-(203 : ℝ) / 100) := by
        rw [hAeq, ← hpowCombine]
        ring
      _ ≤ 4 * c⁻¹ * (x : ℝ) *
          (L ^ (2.01 : ℝ))⁻¹ := by
        gcongr
      _ = 4 * c⁻¹ * T := by
        dsimp only [T, L]
        rw [div_eq_mul_inv]
        ring
  have hcardMain :
      Q * A ≤ 9 * c⁻¹ * T := by
    calc
      Q * A ≤
          (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * c⁻¹ := by
        gcongr
      _ = 9 * c⁻¹ * (x : ℝ) ^ ((5 : ℝ) / 6) := by ring
      _ ≤ 9 * c⁻¹ * T := by
        apply mul_le_mul_of_nonneg_left
        · dsimp only [T]
          simpa only [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num]
            using hpowFiveSixths
        · positivity
  have herror :
      Q * E ≤ T := by
    have hQE :
        Q * E * L ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        Q * E * L ≤
            (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) * E * L := by
          gcongr
        _ = E * (9 * (x : ℝ) ^ ((5 : ℝ) / 6)) *
              Real.log x := by
          dsimp only [L]
          ring
        _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
          simpa only [E] using herr
    have hQE0 : 0 ≤ Q * E := by
      dsimp only [Q, E]
      positivity
    have hdrop : Q * E ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := by
      calc
        Q * E = Q * E * 1 := by ring
        _ ≤ Q * E * L :=
          mul_le_mul_of_nonneg_left hLone hQE0
        _ ≤ (x : ℝ) ^ ((9 : ℝ) / 10) := hQE
    have hp :
        (x : ℝ) ^ ((9 : ℝ) / 10) ≤ T := by
      dsimp only [T]
      simpa only [show (1 : ℝ) - 1 / 10 = 9 / 10 by norm_num]
        using hpowNineTenths
    exact hdrop.trans hp
  have hwidthA :
      (∑ q ∈ chenPairs x,
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ)) * A ≤
        (4 * c⁻¹ + 9 * c⁻¹) * T := by
    calc
      (∑ q ∈ chenPairs x,
          ((smoothingTransitionUpper x q -
              smoothingTransitionLower x q : ℕ) : ℝ)) * A ≤
          (4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 + Q) *
            A := by
        gcongr
      _ = 4 * L ^ (-(0.1 : ℝ)) * (x : ℝ) * P ^ 2 * A +
          Q * A := by ring
      _ ≤ 4 * c⁻¹ * T + 9 * c⁻¹ * T :=
        add_le_add hmainShort hcardMain
      _ = (4 * c⁻¹ + 9 * c⁻¹) * T := by ring
  calc
    smoothingBoundaryLargeBaseMass x ≤
        3 *
          ((∑ q ∈ chenPairs x,
              ((smoothingTransitionUpper x q -
                  smoothingTransitionLower x q : ℕ) : ℝ)) * A +
            Q * E) := by
      simpa only [A, E, Q, L] using hexplicit
    _ ≤ 3 * (((4 * c⁻¹ + 9 * c⁻¹) * T) + T) := by
      gcongr
    _ = C * (x : ℝ) /
        (Real.log x) ^ (2.01 : ℝ) := by
      dsimp only [C, T]
      ring

end Chen

end

