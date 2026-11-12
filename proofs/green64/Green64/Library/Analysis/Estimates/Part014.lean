module

public import Green64.Library.Weights.RoughMarkedInvariance

@[expose] public section

/-!
# Analysis / Estimates / Part014

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ParityConjugatePrimeSlot -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The first literal core in Parity (4.16); the original alpha is conjugated. -/
def b633ParityFirstCore434
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi2 rho sigma : ℝ) : PrimeSlotCore where
  alpha := fun m => star (alpha m)
  residual := residual
  q := q
  character := chi
  sigma₀ := xi2-rho
  sigma₁ := sigma
  lo := lo
  hi := hi

/-- The second literal core in Parity (4.16), with the SAME original alpha. -/
def b633ParitySecondCore434
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi1 rho sigma : ℝ) : PrimeSlotCore where
  alpha := alpha
  residual := fun r => star (residual r)
  q := q
  character := chi.ringHomComp (starRingEnd ℂ)
  sigma₀ := xi1+rho
  sigma₁ := -sigma
  lo := lo
  hi := hi

/-- E's first input has the ORIGINAL alpha, conjugated character/residual,
and negated frequencies. No Liouville twist is inserted into alpha. -/
def b633ParityEFirstCore434
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi2 rho sigma : ℝ) : PrimeSlotCore where
  alpha := alpha
  residual := fun r => star (residual r)
  q := q
  character := chi.ringHomComp (starRingEnd ℂ)
  sigma₀ := -(xi2-rho)
  sigma₁ := -sigma
  lo := lo
  hi := hi

/-- Conjugation of the genuine complex power, including the value at zero. -/
theorem b633_imaginary_power_conjugate434 (n : ℕ) (t : ℝ) :
    imaginaryPower n (-t) = star (imaginaryPower n t) := by
  have harg : (n : ℂ).arg ≠ Real.pi := by
    have hz : (n : ℂ).arg = 0 := by
      simpa only [Complex.ofReal_natCast] using
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    rw [hz]
    exact Real.pi_pos.ne
  simpa only [imaginaryPower, Complex.star_def, map_mul, map_natCast, Complex.conj_I,
    Complex.conj_ofReal, Complex.ofReal_neg, mul_neg, neg_mul] using
    Complex.cpow_conj (n : ℂ) (Complex.I * (t : ℂ)) harg

/-- The two physical factor phases are genuinely multiplicative. -/
theorem b633_imaginary_power_mul434 (m n : ℕ) (t : ℝ) :
    imaginaryPower (m*n) t = imaginaryPower m t * imaginaryPower n t := by
  simpa only [imaginaryPower, Nat.cast_mul, Complex.ofReal_natCast] using
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m)
      (Nat.cast_nonneg n : (0:ℝ) ≤ n) (Complex.I*(t:ℂ))

/-- Frequency addition is used only at the actual positive integer position. -/
theorem b633_imaginary_power_add434 (n : ℕ) (hn : 0<n) (s t : ℝ) :
    imaginaryPower n (s+t) = imaginaryPower n s * imaginaryPower n t := by
  unfold imaginaryPower
  rw [Complex.ofReal_add, mul_add]
  exact Complex.cpow_add _ _ (by exact_mod_cast hn.ne')

/-- E's first prime-slot endpoint is exactly the conjugate of Parity's F,
with both m and p divisor sums and every residual term retained. -/
theorem b633_parity_E_first_literal_conjugate434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi2 rho sigma : ℝ) (n : ℕ) :
    primeSlotCoreValue P (b633ParityEFirstCore434 alpha residual q chi lo hi xi2 rho sigma) n =
      star (primeSlotCoreValue P
        (b633ParityFirstCore434 alpha residual q chi lo hi xi2 rho sigma) n) := by
  unfold primeSlotCoreValue
  simp only [b633ParityEFirstCore434, b633ParityFirstCore434, star_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro p hp
  change (if p.Prime ∧ p ∈ Finset.Icc lo hi then
    alpha m * star (chi m) * imaginaryPower m (-(xi2-rho)) *
      imaginaryPower p (-sigma) *
      star (residual (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n/m/p)) else 0) =
    star (if p.Prime ∧ p ∈ Finset.Icc lo hi then
      star (alpha m) * chi m * imaginaryPower m (xi2-rho) *
        imaginaryPower p sigma *
        residual (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n/m/p) else 0)
  by_cases h : p.Prime ∧ p ∈ Finset.Icc lo hi
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [star_mul, star_star, b633_imaginary_power_conjugate434]
    ring
  · rw [ite_eq_right h, ite_eq_right h, star_zero]

/-- Conjugation does not alter either coefficient bound or rough support.
The bound is exactly the supplied fixed bound, independent of any proxy mesh. -/
theorem b633_parity_E_input_coefficients434
    (alpha residual : ℕ → ℂ) (q : ℕ) (chi : DirichletCharacter ℂ q)
    (lo hi : ℕ) (xi2 rho sigma A C W : ℝ)
    (ha : ∀m, ‖alpha m‖ ≤ A) (hc : ∀r, ‖residual r‖ ≤ C)
    (hs : ∀m, alpha m ≠ 0 → sourceD20Rough W m) :
    let E := b633ParityEFirstCore434 alpha residual q chi lo hi xi2 rho sigma
    E.alpha = alpha ∧
    (∀m, ‖E.alpha m‖ ≤ A) ∧ (∀r, ‖E.residual r‖ ≤ C) ∧
    (∀m, E.alpha m ≠ 0 → sourceD20Rough W m) := by
  refine ⟨rfl, ha, ?_, hs⟩
  intro r
  simpa only [b633ParityEFirstCore434, norm_star] using hc r
end Green64Analytic.Parity

end

end

/-! ## ParityPhysicalCofactor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- The full prime-slot remainder, before insertion of its rough factor. -/
def b633PrimeRest434 (lo hi : ℕ) (sigma : ℝ) (residual : ℕ → ℂ) (u : ℕ) : ℂ :=
  ∑ p  ∈  u.divisors, if p.Prime ∧ p  ∈  Finset.Icc lo hi then
    imaginaryPower p sigma * residual (u/p) else 0

/-- Literal contraction of the inner prime divisor sum, with no estimate. -/
theorem b633_prime_core_full_rest_expansion434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore) (z : ℕ) :
    primeSlotCoreValue P F z =
      ∑ m  ∈  (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors,
        F.alpha m * F.character m * imaginaryPower m F.sigma₀ *
          b633PrimeRest434 F.lo F.hi F.sigma₁ F.residual
            (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z/m) := by
  unfold primeSlotCoreValue b633PrimeRest434
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.Prime ∧ p  ∈  Finset.Icc F.lo F.hi
  · rw [ite_eq_left h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- The second true remainder is the conjugate of the first at the same
ordinary integer; all prime and residual terms remain in the finite sum. -/
theorem b633_prime_rest_conjugate434
    (lo hi : ℕ) (sigma : ℝ) (residual : ℕ → ℂ) (u : ℕ) :
    b633PrimeRest434 lo hi (-sigma) (fun r => star (residual r)) u =
      star (b633PrimeRest434 lo hi sigma residual u) := by
  unfold b633PrimeRest434
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.Prime ∧ p  ∈  Finset.Icc lo hi
  · rw [ite_eq_left h, ite_eq_left h, star_mul,
      b633_imaginary_power_conjugate434]
    ring
  · rw [ite_eq_right h, ite_eq_right h, star_zero]

/-- A genuine rough divisor of the ordinary part is a positive physical
divisor. Dividing it out preserves all P weights and the selected P sign. -/
theorem b633_parity_rough_physical_divisor434
    {G : Type} [Fintype G] (P : G → Finset ℕ)
    (W q0 : ℝ) (ell : ℕ) (tw : Bool) (z m : ℕ) (hz : 0 < z)
    (hp : ∀g p, p ∈ P g → p.Prime) (hW : ∀g p, p ∈ P g → (p:ℝ) ≤ W)
    (hm : m  ∈  (sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z).divisors)
    (hr : sourceD20Rough W m) :
    m  ∣  z ∧ 0 < z/m ∧
    sourceOriginalOrdinaryPart (Finset.univ.biUnion P) z/m =
      sourceOriginalOrdinaryPart (Finset.univ.biUnion P) (z/m) ∧
    sourceMarkedWeight q0 ell P z = sourceMarkedWeight q0 ell P (z/m) ∧
    groupSign P tw z = groupSign P tw (z/m) := by
  let Pall := (Finset.univ : Finset G).biUnion P
  have hm0 : 0 < m := Nat.pos_of_mem_divisors hm
  have hmd : m ∣ z := (Nat.mem_divisors.mp hm).1.trans
    (source_ordinary_part_dvd Pall z hz.ne')
  have hv : 0 < z/m := Nat.div_pos (Nat.le_of_dvd hz hmd) hm0
  have hfact : m*(z/m)=z := by rw [mul_comm]; exact Nat.div_mul_cancel hmd
  have avoid : ∀p ∈ Pall, ¬p ∣ m := by
    intro p hP hdiv
    obtain ⟨g,_,hg⟩ := Finset.mem_biUnion.mp hP
    have hmin : (m.minFac:ℝ) ≤ (p:ℝ) := by
      exact_mod_cast Nat.minFac_le_of_dvd (hp g p hg).two_le hdiv
    exact (not_lt_of_ge (hmin.trans (hW g p hg))) hr.2
  have hsplit := b618_original_P_ordinary_mul434 Pall m (z/m) hm0 hv avoid
  rw [hfact] at hsplit
  have hpart : sourceOriginalOrdinaryPart Pall z/m =
      sourceOriginalOrdinaryPart Pall (z/m) := by
    rw [hsplit.2.1, Nat.mul_div_cancel_left _ hm0]
  have homega : ∀g, shiftTwoGroupOmega (P g) z =
      shiftTwoGroupOmega (P g) (z/m) := by
    intro g
    unfold shiftTwoGroupOmega
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP,hd⟩
      rw [←hfact] at hd
      exact ⟨hP,((hp g p hP).dvd_mul.mp hd).resolve_left
        (avoid p (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ g,hP⟩))⟩
    · rintro ⟨hP,hd⟩
      exact ⟨hP,by rw [←hfact];exact dvd_mul_of_dvd_right hd m⟩
  refine ⟨hmd,hv,hpart,?_,?_⟩
  · simp only [sourceMarkedWeight,homega]
  · simp only [groupSign,show sourceOriginalPParityExponent (Finset.univ.biUnion P) z =
      sourceOriginalPParityExponent (Finset.univ.biUnion P) (z/m) from hsplit.2.2]

/-- Exact phase redistribution at the physical positions mp*v and m*vp.
There are TWO position phases, and no absolute value is taken. -/
theorem b633_parity_physical_phase434
    (m mp v vp : ℕ) (hm : 0 < m) (hmp : 0 < mp) (hv : 0 < v)
    (xi1 xi2 xi3 rho : ℝ) :
    imaginaryPower m xi1 * imaginaryPower mp xi2 *
      imaginaryPower (mp*v) xi3 * imaginaryPower v rho * imaginaryPower vp (-rho) =
    imaginaryPower (mp*v) (rho+xi3) * imaginaryPower (m*vp) (-rho) *
      imaginaryPower mp (xi2-rho) * imaginaryPower m (xi1+rho) := by
  have hmpadd : imaginaryPower mp (xi2-rho) * imaginaryPower mp rho =
      imaginaryPower mp xi2 := by
    rw [←b633_imaginary_power_add434 mp hmp]
    congr 1
    ring
  have hmadd : imaginaryPower m (xi1+rho) * imaginaryPower m (-rho) =
      imaginaryPower m xi1 := by
    rw [←b633_imaginary_power_add434 m hm]
    congr 1
    ring
  rw [b633_imaginary_power_add434 (mp*v) (Nat.mul_pos hmp hv),
    b633_imaginary_power_mul434 mp v rho,
    b633_imaginary_power_mul434 m vp (-rho)]
  calc
    _ = (imaginaryPower m (xi1+rho) * imaginaryPower m (-rho)) *
      (imaginaryPower mp (xi2-rho) * imaginaryPower mp rho) *
      imaginaryPower (mp*v) xi3 * imaginaryPower v rho * imaginaryPower vp (-rho) := by
        rw [hmadd,hmpadd]
    _ = _ := by ring
end Green64Analytic.Parity

end

end

