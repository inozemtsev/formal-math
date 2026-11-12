module

public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.Euler
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Hecke / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem LFunction_one_ne_zero_quadratic (χ : Character)
    (hχ : χ.residue ≠ 1) (hquad : χ.residue ^ 2 = 1) : LFunction χ 1 ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact HeckeBoundary.quadratic_one_ne_zero_of_entire χ.modulus χ.residue
    χ.unit_trivial hquad (LFunction χ) (LFunction_entire_nonprincipal χ hχ)
      (fun s hs => LFunction_eq_series χ hs)

theorem LFunction_boundary_ne_zero (χ : Character) (t : ℝ)
    (hpole : t ≠ 0 ∨ χ.residue ≠ 1)
    (hsquare : t ≠ 0 ∨ χ.residue ^ 2 ≠ 1) :
    LFunction χ (1 + Complex.I * t) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  have h1 (t : ℝ) (ht : t ≠ 0) : (1 + Complex.I * t : ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add] at hi
    exact ht hi
  have h0 (t : ℝ) : (1 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply HeckeBoundary.residue_boundary_ne_zero_of_series_eq χ.modulus χ.residue
    χ.unit_trivial (LFunction χ) (LFunction (χ.power 2))
    (fun s hs => LFunction_eq_series χ hs)
    (fun s hs => LFunction_eq_series (χ.power 2) hs) t
  · apply LFunction_differentiableAt χ (h0 t)
    exact hpole.imp (h1 t) id
  · have heq : (1 + 2 * Complex.I * t : ℂ) = 1 + Complex.I * (2 * t : ℝ) := by
      push_cast
      ring
    rw [heq]
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply LFunction_differentiableAt (χ.power 2) (h0 (2*t))
    rcases hsquare with ht | hsq
    · exact Or.inl (h1 (2*t) (mul_ne_zero (by norm_num) ht))
    · exact Or.inr hsq

theorem LFunction_one_ne_zero_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    LFunction χ 1 ≠ 0 := by
  by_cases hquad : χ.residue ^ 2 = 1
  · exact LFunction_one_ne_zero_quadratic χ hχ hquad
  · simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      LFunction_boundary_ne_zero χ 0 (Or.inr hχ) (Or.inr hquad)

theorem LFunction_ne_zero_of_re_eq_one (χ : Character) {s : ℂ}
    (hs : s.re = 1) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  have heq : s = 1 + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  by_cases ht : s.im = 0
  · have hs1 : s = 1 := by rw [heq, ht]; simp
    subst s
    exact LFunction_one_ne_zero_nonprincipal χ (hpole.resolve_left (not_not.mpr rfl))
  · rw [heq]
    exact LFunction_boundary_ne_zero χ s.im (Or.inl ht) (Or.inl ht)

theorem LFunction_ne_zero_of_one_le_re (χ : Character) {s : ℂ}
    (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  rcases eq_or_lt_of_le hs with h | h
  · exact LFunction_ne_zero_of_re_eq_one χ h.symm hpole
  · exact LFunction_ne_zero_of_one_lt_re χ h

end SevenEighths.HeckeFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O

def cutoffCoefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) : ℂ :=
  if I = 0 then 0 else
    ∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)

theorem fiber_norm_le {I : Ideal O} (hI : I ≠ 0) (p : MulFiber I) :
    Ideal.absNorm p.val.1 ≤ Ideal.absNorm I := by
  apply Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  exact map_dvd Ideal.absNorm ⟨p.val.2, p.property.symm⟩

theorem cutoffCoefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal O) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    cutoffCoefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [cutoffCoefficient, hI0]
  · rw [cutoffCoefficient, ite_eq_right hI0]
    have heq : (fun p : MulFiber I => (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)) =
        (fun p : MulFiber I => (moebius p.val.1 : ℂ)) := by
      funext p
      rw [hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast fiber_norm_le hI0 p : (Ideal.absNorm p.val.1 : ℝ) ≤ Ideal.absNorm I).trans hI
    rw [heq]
    exact mulFiber_moebius_sum I hI0

theorem cutoffCoefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal O) :
    cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      cutoffCoefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [cutoffCoefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, ite_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [hI1, ite_false, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, ite_eq_right hI1, sub_zero]

theorem weighted_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, ite_eq_right hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

def exponentialTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

theorem exponentialTerm_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (idealCoeff χ) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end SevenEighths.HeckeDetectorWitnessArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorPartition -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorPartition
open DyadicTransfer

theorem partition (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (n J : ℕ) (hn : 1 ≤ n) (hJ : (n : ℝ) ≤ (2 : ℝ)^J) :
    (∑ j ∈ Finset.range (J+1), annularCutoff V ((n : ℝ)/(2 : ℝ)^j)) = 1 := by
  rw [partial_partition]
  rw [hsmall _ (by positivity) ((div_le_one (by positivity)).mpr hJ)]
  rw [hlarge _ (by exact_mod_cast (show 2 ≤ 2*n by omega))]
  ring

theorem finite_pair_reassembly {A : Type*} (S : Finset A) (a : A → ℂ)
    (n m : A → ℕ) (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (J K : ℕ)
    (hn : ∀ p ∈ S, 1 ≤ n p ∧ (n p : ℝ) ≤ (2 : ℝ)^J)
    (hm : ∀ p ∈ S, 1 ≤ m p ∧ (m p : ℝ) ≤ (2 : ℝ)^K) :
    (∑ p ∈ S, a p) =
      ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), ∑ p ∈ S,
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
  symm
  calc
    _ = ∑ p ∈ S, ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1),
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
      calc
        _ = ∑ j ∈ Finset.range (J+1), ∑ p ∈ S, ∑ k ∈ Finset.range (K+1),
            a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
              annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [← Finset.mul_sum]
      rw [partition V hsmall hlarge (m p) K (hm p hp).1 (hm p hp).2]
      simp only [mul_one]
      rw [← Finset.mul_sum, partition V hsmall hlarge (n p) J (hn p hp).1 (hn p hp).2,
        mul_one]

theorem annular_support (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hne : annularCutoff V (x/(2 : ℝ)^j) ≠ 0) :
    (2 : ℝ)^j / 2 < x ∧ x < 2*(2 : ℝ)^j := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hy : 0 ≤ x/(2 : ℝ)^j := div_nonneg hx hp.le
  have hlo : 1/2 < x/(2 : ℝ)^j := by
    by_contra h
    have hh := le_of_not_gt h
    apply hne
    rw [annularCutoff, hsmall _ hy (by linarith), hsmall _ (by positivity) (by linarith)]
    ring
  have hhi : x/(2 : ℝ)^j < 2 := by
    by_contra h
    apply hne
    exact annularCutoff_eq_zero_of_two_le V hlarge (le_of_not_gt h)
  constructor
  · have := (lt_div_iff₀ hp).mp hlo
    linarith
  · exact (div_lt_iff₀ hp).mp hhi

def length (X : ℝ) : ℕ := ⌈Real.logb 2 X⌉₊

theorem norm_le_last_scale (X : ℝ) (hX : 0 < X) : X ≤ (2 : ℝ)^(length X) := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hX).mp
    (Nat.le_ceil (Real.logb 2 X))
  simpa only [Real.rpow_natCast, length] using h

theorem length_bound (X : ℝ) (hX : 1 ≤ X) :
    (length X : ℝ) + 1 < Real.logb 2 X + 2 := by
  have hlog : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have h := Nat.ceil_lt_add_one hlog
  change (⌈Real.logb 2 X⌉₊ : ℝ) + 1 < _
  linarith

theorem pair_scale_bounds (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (hterm : ∀ y : ℝ, 2 ≤ y → T y = 0)
    (x y D U : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hD : 0 < D) (hU : 0 < U)
    (j k : ℕ)
    (hj : annularCutoff V (x/(2 : ℝ)^j) ≠ 0)
    (hk : annularCutoff V (y/(2 : ℝ)^k) ≠ 0)
    (hfirst : V (x/D) ≠ 0)
    (hproduct : 1 - V (2*(x*y)/D) ≠ 0)
    (hterminal : T (x*y/U) ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨hjlo,hjhi⟩ := annular_support V hsmall hlarge x hx j hj
  obtain ⟨hklo,hkhi⟩ := annular_support V hsmall hlarge y hy k hk
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have hK : 0 < (2 : ℝ)^k := by positivity
  have hxd : x < 2*D := by
    by_contra h
    apply hfirst
    apply hlarge
    exact (le_div_iff₀ hD).mpr (le_of_not_gt h)
  have hprod : D < 2*(x*y) := by
    by_contra h
    apply hproduct
    rw [hsmall _ (by positivity) ((div_le_one hD).mpr (le_of_not_gt h))]
    ring
  have hxyU : x*y < 2*U := by
    by_contra h
    apply hterminal
    apply hterm
    exact (le_div_iff₀ hU).mpr (le_of_not_gt h)
  have hlo : (2 : ℝ)^j*(2 : ℝ)^k/4 < x*y := by
    have h1 := mul_lt_mul_of_pos_right hjlo (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hklo (show 0 < (2 : ℝ)^j/2 by positivity)
    nlinarith
  have hhi : x*y < 4*((2 : ℝ)^j*(2 : ℝ)^k) := by
    have h1 := mul_lt_mul_of_pos_right hjhi (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hkhi (show 0 < 2*(2 : ℝ)^j by positivity)
    nlinarith
  constructor
  · linarith
  constructor <;> linarith

def pairCoefficient (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (D Y U : ℝ) (s : ℂ) (p : Ideal HeckeFamily.O × Ideal HeckeFamily.O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ)/D) *
    IdealEuler.weighted (HeckeFamily.idealCoeff χ) s (p.1*p.2) *
    Complex.exp (-((Ideal.absNorm (p.1*p.2) : ℝ) : ℂ)/(Y : ℂ)) *
    (1-V (2*(Ideal.absNorm (p.1*p.2) : ℝ)/D)) * T ((Ideal.absNorm (p.1*p.2) : ℝ)/U)

theorem actual_pair_reassembly (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (D Y U X Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (s : ℂ)
    (S : Finset (Ideal HeckeFamily.O × Ideal HeckeFamily.O))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      (Ideal.absNorm p.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.2 : ℝ) ≤ Z) :
    (∑ p ∈ S, pairCoefficient χ V T D Y U s p) =
      ∑ j ∈ Finset.range (length X+1), ∑ k ∈ Finset.range (length Z+1), ∑ p ∈ S,
        pairCoefficient χ V T D Y U s p *
          annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k) := by
  apply finite_pair_reassembly S _ _ _ V hsmall hlarge
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).1),
      (hS p hp).2.2.1.trans (norm_le_last_scale X hX)⟩
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).2.1),
      (hS p hp).2.2.2.trans (norm_le_last_scale Z hZ)⟩

theorem exists_large_pair (J K : ℕ) (F : ℕ → ℕ → ℂ) :
    ∃ j ∈ Finset.range (J+1), ∃ k ∈ Finset.range (K+1),
      ‖∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), F j k‖ ≤
        ((J+1 : ℕ) : ℝ)*((K+1 : ℕ) : ℝ)*‖F j k‖ := by
  let S := (Finset.range (J+1)) ×ˢ (Finset.range (K+1))
  have hS : S.Nonempty := ⟨(0,0), by simp [S]⟩
  obtain ⟨p,hp,hmax⟩ := S.exists_max_image (fun p => ‖F p.1 p.2‖) hS
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hp
  refine ⟨p.1,hj,p.2,hk,?_⟩
  calc
    _ = ‖∑ q ∈ S, F q.1 q.2‖ := by rw [Finset.sum_product]
    _ ≤ ∑ q ∈ S, ‖F q.1 q.2‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, ‖F p.1 p.2‖ := Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = _ := by simp [S, Finset.card_product, mul_assoc]

end SevenEighths.HeckeDetectorPartition

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorFourierActual -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

def inverseCoefficient (χ : Character) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (idealCoeff χ) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : Character) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (idealCoeff χ) s I*W ((Ideal.absNorm I : ℝ)/N)

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold HeckeDetectorPartition.pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

theorem actual_finite_pair_separation (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩs : ContDiff ℝ ∞ Ω)
    (hVs : ContDiff ℝ ∞ V) (hTs : ContDiff ℝ ∞ T)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (S R : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ J ∈ R, J ≠ 0)
    (hΩ : ∀ I ∈ S, ∀ J ∈ R,
      W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    (∑ I ∈ S, ∑ J ∈ R, HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N)) =
      ∫ t : ℝ,
        (𝓕 (logSource Ω V T hΩc hΩs hVs hTs (2*D*N/Dstar) (D*N/Y) (D*N/U))) t*
        phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
          (fun I => Real.log ((Ideal.absNorm I : ℝ)/D)) t*
        phasePolynomial R (plainCoefficient χ W₂ N s)
          (fun J => Real.log ((Ideal.absNorm J : ℝ)/N)) t := by
  rw [← finite_pair_separation]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  exact actual_pair_profile χ Ω V T W₁ W₂ Dstar D N Y U hD hN s I J
    (hS I hI) (hR J hJ) (hΩ I hI J hJ)

end
end SevenEighths.HeckeDetectorFourier

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesCutoffs -/

section

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

abbrev cutoff : SchwartzMap ℝ ℂ := QuadraticInitialBound.sieveCutoff

lemma cutoff_one (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : cutoff x = 1 := by
  simp only [cutoff, QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1, Complex.ofReal_one]

lemma cutoff_zero (x : ℝ) (hx : 2 ≤ x) : cutoff x = 0 := by
  rw [QuadraticInitialBound.sieveCutoff_apply]
  have hh := QuadraticInitialBound.sieveBump.zero_of_le_dist (x := x)
    (show QuadraticInitialBound.sieveBump.rOut ≤ dist x 0 by
      change 2 ≤ dist x 0
      simpa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] using hx)
  rw [hh, Complex.ofReal_zero]

lemma cutoff_norm_le (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
  exact QuadraticInitialBound.sieveBump.le_one

lemma annular_log_bound (x : ℝ) (hx : 0 ≤ x)
    (hactive : DyadicTransfer.annularCutoff cutoff x ≠ 0) : |Real.log x| ≤ Real.log 2 := by
  have hh := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
    (by simpa using hactive)
  norm_num at hh
  have hx0 : 0 < x := by linarith
  have hlo := Real.log_le_log (by norm_num : 0 < (2 : ℝ)⁻¹)
    (show (2 : ℝ)⁻¹ ≤ x by linarith)
  rw [Real.log_inv] at hlo
  exact abs_le.mpr ⟨hlo,Real.log_le_log hx0 hh.2.le⟩

theorem exists_product_log_cutoff :
    ∃ Ω : ℝ → ℂ, HasCompactSupport Ω ∧ ContDiff ℝ ∞ Ω ∧
      tsupport Ω ⊆ Set.Icc (-(2*Real.log 2+1)) (2*Real.log 2+1) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        DyadicTransfer.annularCutoff cutoff x ≠ 0 → DyadicTransfer.annularCutoff cutoff y ≠ 0 →
        Ω (Real.log x+Real.log y) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨Ω,hc,hs,hone,hsupp,hzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (2*Real.log 2) (by positivity)
  refine ⟨Ω,hc,hs,hsupp,?_⟩
  intro x y hx hy hax hay
  apply hone
  have hb1 := annular_log_bound x hx hax
  have hb2 := annular_log_bound y hy hay
  exact (abs_add_le _ _).trans (by linarith)

end
end SevenEighths.HeckeDetectorProfiles

end OAI

end

