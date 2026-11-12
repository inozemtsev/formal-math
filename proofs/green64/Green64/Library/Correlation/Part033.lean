module

public import Green64.Library.Analysis.Estimates.Part009
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part021
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Green64.Library.Weights.Part012
public import Green64.Library.Correlation.Part004
public import Mathlib.Algebra.Order.Floor.Semiring
public import Green64.Library.Weights.Part016
public import Green64.Library.Weights.Part035
public import Green64.Library.Weights.Part038
public import Green64.Library.Weights.Part011
public import Green64.Library.Weights.Part042
public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.Part043

@[expose] public section

/-!
# Correlation / Part033

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceLogCollarPhysicalExact -/

section

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 2500000

/-- Exact identification of the logarithmic collar with the previously
bounded physical Q. Includes the angular/cycle Jacobian H/(2*pi*Y). -/
theorem source_log_collar_physical_exact434
    (chi K : 𝓢(ℝ,ℂ)) (F : Finset ℕ) (a : ℕ → ℂ)
    (H Y v : ℝ) (hH : 0 < H) (hY : 0 < Y) (hv : 0 < v)
    (hF : ∀ n ∈ F, 0 < n) :
    ((H/(2*Real.pi*Y):ℝ):ℂ) *
      sourceActualPhysicalQ434 chi (𝓕 K) (H/Y)
        (sourceLiteralTwistedMellin434 Y F a) (Real.log (v/Y)) =
    chi (Real.log (v/Y)) *
      (∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H)) := by
  let u := Real.log (v/Y)
  let d : ℝ := H/(2*Real.pi*v)
  let g : ℝ → ℂ := fun ξ => (𝓕 K) ξ *
    Complex.exp (((-2*Real.pi*ξ*v/H*Real.log v:ℝ):ℂ)*Complex.I) *
      (∑ n ∈ F, a n*sourcePhase n (2*Real.pi*ξ*v/H))
  have hd : 0 < d := by dsimp [d]; positivity
  have he : Real.exp (-u) = Y/v := by
    dsimp [u]
    rw [Real.exp_neg, Real.exp_log (div_pos hv hY)]
    field_simp
  have ht (t : ℝ) : 2*Real.pi*(d*t)*v/H = t := by
    dsimp [d]
    field_simp
  have hp (t : ℝ) :
      Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) *
        Complex.exp (((-t*Real.log Y:ℝ):ℂ)*Complex.I) =
      Complex.exp (((-t*Real.log v:ℝ):ℂ)*Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [u]
    rw [Real.log_div hv.ne' hY.ne']
    push_cast
    ring
  have hker (t : ℝ) :
      sourceActualPhysicalTimeKernel434 chi (𝓕 K) (H/Y)
        (sourceLiteralTwistedMellin434 Y F a) u t =
      (chi u * ((Y/v:ℝ):ℂ)) * g (d*t) := by
    have hz : collarZ434 (H/Y) t u = d*t := by
      unfold collarZ434
      rw [he]
      dsimp [d]
      field_simp
    have hx : -2*Real.pi*(d*t)*v/H*Real.log v = -t*Real.log v := by
      calc
        _ = -(2*Real.pi*(d*t)*v/H)*Real.log v := by ring
        _ = _ := by rw [ht]
    unfold sourceActualPhysicalTimeKernel434 sourceCompactCollarSymbol434
      sourceLiteralTwistedMellin434 sourceLiteralFiniteMellin434
    simp only [source_literal_phase_eq_original434]
    rw [he,hz]
    dsimp [g]
    rw [ht,hx]
    calc
      _ = (chi u * ((Y/v:ℝ):ℂ)) * (𝓕 K) (d*t) *
          (Complex.exp (((-(u*t):ℝ):ℂ)*Complex.I) *
            Complex.exp (((-t*Real.log Y:ℝ):ℂ)*Complex.I)) *
          (∑ n ∈ F, a n*sourcePhase n t) := by ring
      _ = _ := by rw [hp]; ring
  have hInt : (∫ t : ℝ, g (d*t)) =
      ((d⁻¹:ℝ):ℂ) * (∫ ξ : ℝ, g ξ) := by
    rw [Measure.integral_comp_mul_left g d,abs_of_pos (inv_pos.mpr hd)]
    simp only [Complex.real_smul,smul_eq_mul]
  have hLog : (∫ ξ : ℝ, g ξ) =
      ∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H) :=
    (source_collar_log_bochner434 F a K H v hv hF).symm
  have hScalar : ((H/(2*Real.pi*Y):ℝ):ℂ) *
      (((Y/v:ℝ):ℂ) * ((d⁻¹:ℝ):ℂ)) = 1 := by
    dsimp [d]
    push_cast
    have hHC : (H:ℂ) ≠ 0 := by exact_mod_cast hH.ne'
    have hYC : (Y:ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    have hpC : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  change ((H/(2*Real.pi*Y):ℝ):ℂ) *
    (∫ t : ℝ, sourceActualPhysicalTimeKernel434 chi (𝓕 K) (H/Y)
      (sourceLiteralTwistedMellin434 Y F a) u t) =
    chi u * (∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H))
  simp_rw [hker]
  rw [integral_const_mul,hInt,hLog]
  calc
    _ = (chi u * (∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H))) *
        (((H/(2*Real.pi*Y):ℝ):ℂ)*(((Y/v:ℝ):ℂ)*((d⁻¹:ℝ):ℂ))) := by ring
    _ = _ := by rw [hScalar,mul_one]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceAdditivePhysicalTransfer -/

section

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 1600000

/-- Complete analytic transfer from the additive arc to the actual
previously bounded physical Q, with all regularity proved upstream. -/
theorem source_additive_physical_transfer434
    (chi K : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (F : Finset ℕ) (a : ℕ → ℂ) (H Y A δ M c : ℝ)
    (hH : 1 ≤ H) (hY : 0 < Y) (hA : 1 ≤ A)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hc : 0 < c)
    (hHcap : H ≤ Y/(8*A)) (hF : ∀ n ∈ F, 0 < n)
    (hCoef : ∀ n ∈ F, a n ≠ 0 → Y/A ≤ (n:ℝ) ∧ (n:ℝ) ≤ A*Y)
    (hSupport : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hLip : ∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|)
    (hLower : ∀ t : ℝ, |t| ≤ 1 → c ≤ ‖(𝓕 (K : ℝ → ℂ)) t‖)
    (hOne : ∀ v ∈ Set.Icc (Y/(2*A)) (2*A*Y), chi (Real.log (v/Y)) = 1) :
    c^2 * (∫ beta in Set.Icc (-(1/H)) (1/H),
      ‖sourceNatFourierPoly F a (beta : AddCircle (1:ℝ))‖^2) ≤
    2*(H^2)⁻¹ * (∫ v in Set.Ioi (0:ℝ), (H/(2*Real.pi*Y))^2 *
      ‖sourceActualPhysicalQ434 chi (𝓕 K) (H/Y)
        (sourceLiteralTwistedMellin434 Y F a) (Real.log (v/Y))‖^2) +
    2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*(H/Y)^2 *
      ∑ n ∈ F, ‖a n‖^2) := by
  have hHp : 0 < H := by linarith
  let V := Set.Icc (Y/(2*A)) (2*A*Y)
  let R : ℝ → ℂ := fun v => ∑ n ∈ F, a n*K (v*Real.log ((n:ℝ)/v)/H)
  let g : ℝ → ℝ := fun v => (H/(2*Real.pi*Y))^2 *
    ‖sourceActualPhysicalQ434 chi (𝓕 K) (H/Y)
      (sourceLiteralTwistedMellin434 Y F a) (Real.log (v/Y))‖^2
  have hI : IntegrableOn g (Set.Ioi 0) :=
    source_literal_physical_log_integrable434 chi (𝓕 K) B hB hchi F a H Y hHp hY
  have hSub : V ⊆ Set.Ioi 0 := by
    intro v hv
    exact (div_pos hY (by positivity)).trans_le hv.1
  have hEq (v : ℝ) (hv : v ∈ V) : ‖R v‖^2 = g v := by
    have he := source_log_collar_physical_exact434 chi K F a H Y v hHp hY (hSub hv) hF
    rw [hOne v hv,one_mul] at he
    dsimp [R,g]
    rw [← he,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hEnergy : (∫ v in V, ‖R v‖^2) ≤ ∫ v in Set.Ioi 0, g v := by
    calc
      _ = ∫ v in V, g v := by
        apply setIntegral_congr_fun measurableSet_Icc
        exact hEq
      _ ≤ _ := setIntegral_mono_set hI
        (Filter.Eventually.of_forall (fun _ => by dsimp [g]; positivity))
        (Filter.Eventually.of_forall hSub)
  have hArc := source_linear_to_log_arc434 K F a H Y A δ M c
    hH hY hA hδ hδ1 hM hc hHcap hF hCoef hSupport hLip hLower
  exact hArc.trans (add_le_add
    (mul_le_mul_of_nonneg_left hEnergy (by positivity : 0 ≤ 2*(H^2)⁻¹)) le_rfl)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalNamedPhysicalNormalized -/

section

open MeasureTheory
open scoped SchwartzMap BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1900000

/-- The already kernel-proven source physical collar bound applies to
the FROZEN sourceOriginalPhysicalEndpointCoefficient434, not a surrogate.
K is fixed BEFORE all source coefficient, character, gcd, mark, and
rational parameters; the exact Mellin RHS includes their unchanged weight. -/
theorem source_original_named_physical_normalized434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ) (k qBase : ℕ)
        (alpha c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase)
        (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
        (psi1 : ℝ → ℂ) (v1 : ℝ) (H Y : ℝ),
        0 < H → 0 < Y →
        (H^2)⁻¹ *
          (∫ v in Set.Ioi (0:ℝ),
            (H/(2*Real.pi*Y))^2 *
            ‖sourceActualPhysicalQ434 chi kappa (H/Y)
              (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N)
                (sourceOriginalPhysicalEndpointCoefficient434
                  G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
                  k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1))
              (Real.log (v/Y))‖^2) ≤
        (K/Y) * (∫ t : ℝ,
          ((1+(H/Y)*|t|)^j)⁻¹ *
          ‖(Y:ℂ) * sourceOriginalPhysicalMellin434
            G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
            k qBase alpha c chi0 sigma0 sigma1 N den h hden
            (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) := by
  obtain ⟨K,hK,hbase⟩ :=
    source_literal_finite_physical_normalized434 chi kappa B hB hchi j hj
  refine ⟨K,hK,?_⟩
  intro ι β instι decι instβ decβ
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    psi1 v1 H Y hH hY
  let a : ℕ → ℂ :=
    sourceOriginalPhysicalEndpointCoefficient434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
  have he (t : ℝ) :
      sourceLiteralFiniteMellin434 (Finset.Icc 1 N) a t =
      (Y:ℂ) * sourceOriginalPhysicalMellin434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t :=
    source_original_literal_mellin_identification434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
      alpha c chi0 sigma0 sigma1 N den h hden Y psi1 v1 t hY
  have hi := hbase H Y hH hY (Finset.Icc 1 N) a
  change (H^2)⁻¹ * (∫ v in Set.Ioi (0:ℝ),
    (H/(2*Real.pi*Y))^2 *
      ‖sourceActualPhysicalQ434 chi kappa (H/Y)
        (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N) a)
        (Real.log (v/Y))‖^2) ≤ _ 
  simpa only [he] using hi
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCutoffExact -/

section

open scoped BigOperators

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 900000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (den h : ℕ) (hden : 0 < den)

/-- The ORIGINAL marked coefficient is zero beyond the smooth physical
window n ≤ ceil(A Y), independent of the artificial bookkeeping N.
Every gcd, character, mark, and twist remains in the coefficient. -/
theorem source_original_marked_cutoff_ceil434
    (Y A : ℝ) (hY : 0 < Y)
    (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hUpper : ∀ u, psi1 u ≠ 0 → u ≤ A)
    (n : ℕ) (hn : Nat.ceil (A*Y) < n) :
    sourceOriginalPhysicalEndpointCoefficient434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
      k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1 n = 0 := by
  have hGt : A*Y < (n:ℝ) := by
    have hceil : A*Y ≤ (Nat.ceil (A*Y):ℝ) := Nat.le_ceil _
    exact lt_of_le_of_lt hceil (by exact_mod_cast hn)
  have hcut : psi1 ((n:ℝ)/Y) = 0 := by
    by_contra hh
    have hle : ((n:ℝ)/Y) ≤ A := hUpper _ hh
    have hmul : (n:ℝ) ≤ A*Y := (div_le_iff₀ hY).mp hle
    exact (not_lt_of_ge hmul) hGt
  unfold sourceOriginalPhysicalEndpointCoefficient434
  simp only [hcut, zero_mul]
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalDivisorCard -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 680000

/-- True outside-part n_* divides the original integer n and
therefore has no more divisors; repeated prime powers are retained. -/
theorem source_original_outside_card_le434
    (G : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    ((sourceOutsidePart G n).divisors.card : ℝ) ≤
      (n.divisors.card : ℝ) := by
  have hdvd : sourceOutsidePart G n ∣ n :=
    ⟨sourceInsidePart G n, (sourceParts_mul G n hn).symm⟩
  exact_mod_cast Finset.card_le_card
    (Nat.divisors_subset_of_dvd hn hdvd)

/-- Each ORIGINAL designated small prime divisor is counted by
the ordinary divisor set, including composite / nonsquarefree n. -/
theorem source_original_small_support_card_le434
    (S : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    ((smallPrimeSupport S n).card : ℝ) ≤
       (n.divisors.card : ℝ) := by
  have hsub : smallPrimeSupport S n ⊆ n.divisors := by
    intro ps hp
    exact Nat.mem_divisors.mpr
      ⟨(Finset.mem_filter.mp hp).2, hn⟩
  exact_mod_cast Finset.card_le_card hsub
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLowLiteralTransfer -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1400000

/-- The EXACT original-source literal low-time conclusion (not a new
source saving premise) implies the normalized collar low-time term
with physical factor Y. The hypothesis is the precisely shaped bound
already proved by SourceOriginalLiteralGlobalTerminal434 and must be
instantiated using that theorem in the final evental statement. -/
theorem source_original_literal_low_to_physical434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
    (Y Hprime L Carc : ℝ)
    (hY : 0 < Y) (hHprime : 0 < Hprime) (hL : 3 ≤ L)
    (psi1 : ℝ → ℂ) (v1 : ℝ) (E : ℝ)
    (hOriginalLiteral :
      (∫ t in Set.Icc
          (-(2*L*Y/(Hprime/L^Carc))) (2*L*Y/(Hprime/L^Carc)),
        ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
          q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0 sigma0
          sigma1 N den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤ E) :
    (1/Y) * (∫ t in Set.Icc
        (-(L*Y/(Hprime/L^Carc))) (L*Y/(Hprime/L^Carc)),
      ‖(Y:ℂ)*sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
        sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      Y * E := by
  let P : ℝ → ℂ := fun t =>
    sourceOriginalPhysicalMellin434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
      sigma0 sigma1 N den h hden
      (sourceActualOriginalWindowWeight Y psi1 v1) t
  let T : ℝ := L*Y/(Hprime/L^Carc)
  have hT : 0 ≤ T := by
    dsimp [T]
    have hLc : 0 < L^Carc := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hPos : (0:ℝ) ≤ Y := le_of_lt hY
  have hCont : Continuous P :=
    source_original_physical_mellin_continuous434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
      Y hY psi1 v1
  have hTwo : 2*T = 2*L*Y/(Hprime/L^Carc) := by
    dsimp [T]
    ring
  have hLeft : -2*T = -(2*L*Y/(Hprime/L^Carc)) := by
    calc
      -2*T = -(2*T) := by ring
      _ = _ := congrArg Neg.neg hTwo
  have hSrc : (∫ t in Set.Icc (-2*T) (2*T), ‖P t‖^2) ≤ E := by
    simpa only [P,hLeft,hTwo] using hOriginalLiteral
  have hSmall := source_original_low_time_Y_conversion434
    P hCont Y T E hPos hT hSrc
  have hOneOverY : 0 ≤ (1/Y:ℝ) := by positivity
  calc
    _ ≤ (1/Y) * (Y^2*E) :=
      mul_le_mul_of_nonneg_left hSmall hOneOverY
    _ = Y*E := by
      have hn : Y ≠ 0 := hY.ne'
      field_simp
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMarkedCoeffNorm -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1400000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (den h : ℕ) (hden : 0 < den)

/-- Exact ORIGINAL physical coefficient absolute value. The only
remaining nontrivial source moment input is a pointwise bound for the
real grouped marked sum, with no character-family count substituted. -/
theorem source_original_marked_coefficient_norm434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (n : ℕ) :
    ‖sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
        sigma0 sigma1 den h hden Y psi1 v1 n‖ =
      ‖psi1 ((n:ℝ)/Y)‖ *
      ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
        sigma0 sigma1 n den h hden‖ := by
  unfold sourceOriginalPhysicalEndpointCoefficient434
  rw [norm_mul, norm_mul, sourcePhase_norm, mul_one]

/-- True-source arithmetic reduction from the original smooth cutoff
and grouped marked coefficient to the DIVISOR-CUBE pointwise majorant.
The marked-group cap is displayed as the next unresolved mathematical
obligation; it is NOT silently substituted for source energy saving. -/
theorem source_original_marked_coefficient_from_group_bound434
    (Y : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ) (n : ℕ)
    (Bpsi Bgroup : ℝ) (hpsi : 0 ≤ Bpsi) (hgroup : 0 ≤ Bgroup)
    (hCut : ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi)
    (hMark : ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
      Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
      sigma0 sigma1 n den h hden‖ ≤
      Bgroup*(n.divisors.card:ℝ)^3) :
    ‖sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot
      Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
      sigma0 sigma1 den h hden Y psi1 v1 n‖ ≤
      (Bpsi*Bgroup)*(n.divisors.card:ℝ)^3 := by
  rw [source_original_marked_coefficient_norm434]
  calc
    _ ≤ Bpsi*(Bgroup*(n.divisors.card:ℝ)^3) :=
      mul_le_mul hCut hMark (norm_nonneg _) hpsi
    _ = _ := by ring
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalMarkedSupportedMoment -/

section

open scoped BigOperators

namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1300000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase)
    (sigma0 sigma1 : ℝ) (den h : ℕ) (hden : 0 < den)

/-- Actual SOURCE physical marked-coefficient moment, localized at
ceil(A*Y) rather than the much larger bookkeeping N. The only open
obligation is an explicit source-grouped pointwise bound, never a
source energy/saving premise. The frozen phase and all marks remain. -/
theorem source_original_marked_supported_moment434
    (N : ℕ) (Y A : ℝ) (hY : 0 < Y)
    (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hUpper : ∀ u, psi1 u ≠ 0 → u ≤ A)
    (Bpsi Bgroup : ℝ) (hpsi : 0 ≤ Bpsi) (hgroup : 0 ≤ Bgroup)
    (hCut : ∀ n ∈ Finset.Icc 1 N,
      ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi)
    (hGroup : ∀ n ∈ Finset.Icc 1 N,
      ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
         Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
         sigma0 sigma1 n den h hden‖ ≤
        Bgroup * (n.divisors.card:ℝ)^3) :
    (∑ n ∈ Finset.Icc 1 N,
      ‖sourceOriginalPhysicalEndpointCoefficient434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
        k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1 n‖^2)
      ≤ (Bpsi*Bgroup)^2 * (Nat.ceil (A*Y):ℝ) *
          (1+Real.log (Nat.ceil (A*Y):ℝ))^63 := by
  let a : ℕ → ℂ :=
    sourceOriginalPhysicalEndpointCoefficient434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
      k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
  have hSupport : ∀ n ∈ Finset.Icc 1 N,
      Nat.ceil (A*Y) < n → a n = 0 := by
    intro n hn hm
    exact source_original_marked_cutoff_ceil434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
      k qBase alpha c chi0 sigma0 sigma1 den h hden
      Y A hY psi1 v1 hUpper n hm
  have hPoint : ∀ n ∈ Finset.Icc 1 N,
      ‖a n‖ ≤ (Bpsi*Bgroup)*(n.divisors.card:ℝ)^3 := by
    intro n hn
    exact source_original_marked_coefficient_from_group_bound434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
      k qBase alpha c chi0 sigma0 sigma1 den h hden
      Y psi1 v1 n Bpsi Bgroup hpsi hgroup (hCut n hn) (hGroup n hn)
  exact source_supported_divisor_cubed_moment434
    N (Nat.ceil (A*Y)) a (Bpsi*Bgroup)
    (mul_nonneg hpsi hgroup) hSupport hPoint
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalNamedWholeRealTail -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1450000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
  (k qBase : ℕ) (alpha c : ℕ → ℂ)
  (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- TRUE frozen source physical Mellin with exact entire ± angular-time
tail, with M=ceil(A Y) in both the coefficient moment and time shells.
No source tail energy is assumed. The sole marked coefficient premise
is an explicit source grouped pointwise bound that is proved separately
under original admissibility by SourceOriginalGroupedUniform434. -/
theorem source_original_named_whole_real_tail_from_group434
    (Y A : ℝ) (hY : 0 < Y)
    (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hUpper : ∀ u, psi1 u ≠ 0 → u ≤ A)
    (Bpsi Bgroup : ℝ) (hpsi : 0 ≤ Bpsi) (hgroup : 0 ≤ Bgroup)
    (hCut : ∀ n ∈ Finset.Icc 1 N, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi)
    (hGrp : ∀ n ∈ Finset.Icc 1 N,
      ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 n den h hden‖ ≤
          Bgroup * (n.divisors.card:ℝ)^3)
    (ω L : ℝ) (hω : 0 < ω) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) :
    (∫ t in {t : ℝ | L/ω ≤ |t|},
      ((1+ω*|t|)^j)⁻¹ *
      ‖(Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      (4 * ((L^(j-2))⁻¹ *
        (L/ω+16*(Nat.ceil (A*Y):ℝ) *
          (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
      ((Bpsi*Bgroup)^2 * (Nat.ceil (A*Y):ℝ) *
        (1+Real.log (Nat.ceil (A*Y):ℝ))^63) := by
  let a : ℕ → ℂ :=
    sourceOriginalPhysicalEndpointCoefficient434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
  have hz : ∀ n ∈ Finset.Icc 1 N, Nat.ceil (A*Y) < n →
      a n = 0 := by
    intro n hn hm
    exact source_original_marked_cutoff_ceil434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 den h hden
      Y A hY psi1 v1 hUpper n hm
  have hp (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      ‖a n‖ ≤ (Bpsi*Bgroup)*(n.divisors.card:ℝ)^3 :=
    source_original_marked_coefficient_from_group_bound434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 den h hden
      Y psi1 v1 n Bpsi Bgroup hpsi hgroup (hCut n hn) (hGrp n hn)
  have hP (t : ℝ) :
      (Y:ℂ) * sourceOriginalPhysicalMellin434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k qBase alpha c chi0 sigma0 sigma1
        N den h hden (sourceActualOriginalWindowWeight Y psi1 v1) t =
      sourceLiteralFiniteMellin434 (Finset.Icc 1 N) a t :=
    (source_original_literal_mellin_identification434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
      Y psi1 v1 t hY).symm
  have hTail := source_actual_full_time_tail_supported434
    N (Nat.ceil (A*Y)) a (Bpsi*Bgroup)
    (mul_nonneg hpsi hgroup) hz hp ω L hω hL j hj
  convert hTail using 1
  apply integral_congr_ae
  filter_upwards with t
  rw [hP]
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalNamedWholeTimeSplit -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1200000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
  (k qBase : ℕ) (alpha c : ℕ → ℂ)
  (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- Actual frozen source P(t)=Y Mellin(t) with no frequency cutoff
alterations, including all character, gcd and marked data. -/
noncomputable def sourceFrozenP434 (Y : ℝ) (psi1 : ℝ → ℂ)
    (v1 t : ℝ) : ℂ :=
  (Y:ℂ) * sourceOriginalPhysicalMellin434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    (sourceActualOriginalWindowWeight Y psi1 v1) t

/-- Proof that sourceFrozenP434 is precisely the originally named
normalized marked source Mellin, no changed marks or coefficients. -/
theorem source_frozen_P_exact_finite434
    (Y : ℝ) (hY : 0 < Y) (psi1 : ℝ → ℂ)
    (v1 t : ℝ) :
    sourceFrozenP434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
      ts tb coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
      Y psi1 v1 t =
    sourceLiteralFiniteMellin434 (Finset.Icc 1 N)
      (sourceOriginalPhysicalEndpointCoefficient434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k qBase alpha c chi0 sigma0 sigma1
        den h hden Y psi1 v1) t := by
  unfold sourceFrozenP434
  exact (source_original_literal_mellin_identification434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    Y psi1 v1 t hY).symm

/-- Exact source low-time/high-time splitting of the ORIGINAL
weighted full-real physical Mellin. Both sides of infinity retained. -/
theorem source_original_named_real_low_high434
    (Y : ℝ) (hY : 0 < Y) (psi1 : ℝ → ℂ) (v1 : ℝ)
    (ω T : ℝ) (hω : 0 < ω) (hT : 0 ≤ T)
    (j : ℕ) (hj : 2 ≤ j) :
    (∫ t : ℝ, ((1+ω*|t|)^j)⁻¹ *
      ‖sourceFrozenP434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
        Y psi1 v1 t‖^2) ≤
      (∫ t in Set.Icc (-T) T,
        ‖sourceFrozenP434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
          Y psi1 v1 t‖^2) +
      (∫ t in {t : ℝ | T ≤ |t|},
        ((1+ω*|t|)^j)⁻¹ *
        ‖sourceFrozenP434 G Parity S primeSlot Ts Tb q0 Vs
          Vsmall Vbig ts tb coef k qBase alpha c chi0
          sigma0 sigma1 N den h hden Y psi1 v1 t‖^2) := by

  let a : ℕ → ℂ :=
    sourceOriginalPhysicalEndpointCoefficient434
      G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
  have heq (t : ℝ) :
      sourceFrozenP434 G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
        Y psi1 v1 t =
      sourceLiteralFiniteMellin434 (Finset.Icc 1 N) a t :=
    source_frozen_P_exact_finite434 G Parity S primeSlot Ts Tb
      q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
      sigma0 sigma1 N den h hden Y hY psi1 v1 t
  have hs := source_original_real_time_weight_low_high434
    (Finset.Icc 1 N) a ω hω j hj T hT
  simpa only [heq] using hs
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPeeledAdditiveLiteral -/

section

open scoped BigOperators FourierTransform
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 2100000

/-- The TRUE ORIGINAL source cutoff-weighted peeled Fourier endpoint at
an arbitrary rational center h/den is exactly a sourceNatFourierPoly
in beta with coefficients sourcePeeledGroupedPhysicalSum retaining
ALL real gcd/character families, parity, small/big marks and 1/Vs.
Neither a box surrogate nor an assumed Fourier-coefficient identity. -/
theorem source_original_weighted_peeled_additive_literal434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
          ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Ptwist ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (L a tau Carc : ℝ) (den h : ℕ) (hden : 0 < den)
    (hdenCap : (den:ℝ) ≤ L^Carc)
    (hW : L^Carc ≤ Real.exp (Real.sqrt L))
    (hsmall : L^Carc < Real.exp (L^a))
    (hlong : L^Carc < Real.exp (tau*L))
    (hAlphaRough : ∀ m, alpha m ≠ 0 →
       SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
       Real.exp (tau*L) ≤ (p:ℝ))
    (Lambda : ℕ → ℂ) (beta : ℝ) :
    sourceWeightedPeeledMarkedFourier N qBase S Ts Tb
       q0 Vs Vsmall Vbig ts tb b k primeSlot Ptwist
       alpha c chi0 sigma0 sigma1 Lambda
       ((((h:ℝ)/(den:ℝ)+beta):ℝ):AddCircle (1:ℝ)) =
      sourceNatFourierPoly (Finset.Icc 1 N)
        (fun n => Lambda n *
          sourcePeeledGroupedPhysicalSum G Ptwist S primeSlot Ts Tb
            q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0
            sigma0 sigma1 n den h hden)
        (beta:AddCircle (1:ℝ)) := by
  classical
  change sourceNatFourierPoly (Finset.Icc 1 N)
    (fun n => (Lambda n * literalSourceParity Ptwist n) *
      sourceEndpoint
        (sourceOutsidePart (S ∪
          ((Finset.univ : Finset ι).biUnion Ts) ∪
          ((Finset.univ : Finset β).biUnion Tb)))
        (fun z => ((1/Vs:ℝ):ℂ) *
          ∑ ps ∈ smallPrimeSupport S z,
            literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
              ts tb b k (z/ps))
        primeSlot alpha c qBase chi0 sigma0 sigma1 n)
      ((((h:ℝ)/(den:ℝ)+beta):ℝ):AddCircle (1:ℝ)) = _
  rw [source_nat_fourier_literal, source_nat_fourier_literal]
  apply Finset.sum_congr rfl
  intro n hn
  have hCoef := source_peeled_fourier_coefficient_exact
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Ptwist alpha c chi0 sigma0 sigma1 n
  rw [if_pos hn] at hCoef
  have hGrouped := source_original_fourier_grouped_physical_exact
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Ptwist alpha c chi0 sigma0 sigma1 G
    hG hParityG hSPrime hTsPrime hTbPrime
    L a tau Carc n den h hden
    hdenCap hW hsmall hlong hAlphaRough hSRange hSlotRange
  rw [if_pos hn] at hGrouped
  have hPhase := source_original_additive_center_phase434 n den h beta
  rw [hPhase]
  calc
    _ = (Lambda n *
      fourierCoeff (T:=1)
        (sourcePeeledMarkedFourier N qBase S Ts Tb
          q0 Vs Vsmall Vbig ts tb b k primeSlot
          Ptwist alpha c chi0 sigma0 sigma1) (n:ℤ)) *
      (sourceRationalPhase den h n *
        fourier (T:=1) (n:ℤ) (beta:AddCircle (1:ℝ))) := by
        rw [hCoef]
        ring
    _ = (Lambda n *
      sourcePeeledGroupedPhysicalSum G Ptwist S primeSlot Ts Tb
        q0 Vs Vsmall Vbig ts tb b k qBase
        alpha c chi0 sigma0 sigma1 n den h hden) *
      fourier (T:=1) (n:ℤ) (beta:AddCircle (1:ℝ)) := by
        rw [← hGrouped]
        ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPeeledPhysicalArc -/

section

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 2600000

/-- The ORIGINAL weighted peeled additive endpoint, not a surrogate:
complete rational/gcd/character data and source marks are retained. -/
theorem source_original_peeled_physical_arc434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptwist : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
      ((Finset.univ : Finset β).biUnion Tb)) (hParityG : Ptwist ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (L aexp tau Carc : ℝ) (den h : ℕ) (hden : 0 < den)
    (hdenCap : (den:ℝ) ≤ L^Carc) (hW : L^Carc ≤ Real.exp (Real.sqrt L))
    (hsmall : L^Carc < Real.exp (L^aexp)) (hlong : L^Carc < Real.exp (tau*L))
    (hAlphaRough : ∀ m, alpha m ≠ 0 → SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^aexp) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot, Real.exp (tau*L) ≤ (p:ℝ))
    (chi K : 𝓢(ℝ,ℂ)) (B H Y A δ M cband : ℝ) (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hB : 0 < B) (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (hH : 1 ≤ H) (hY : 0 < Y) (hA : 1 ≤ A)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hcband : 0 < cband)
    (hHcap : H ≤ Y/(8*A))
    (hPsi : ∀ u, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A)
    (hSupport : ∀ z, K z ≠ 0 → |z| ≤ δ)
    (hLip : ∀ z z', ‖K z-K z'‖ ≤ M*|z-z'|)
    (hLower : ∀ t : ℝ, |t| ≤ 1 → cband ≤ ‖(𝓕 (K : ℝ → ℂ)) t‖)
    (hOne : ∀ v ∈ Set.Icc (Y/(2*A)) (2*A*Y), chi (Real.log (v/Y)) = 1) :
    let aPhys := sourceOriginalPhysicalEndpointCoefficient434
      G Ptwist S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase
      alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
    cband^2 * (∫ beta in Set.Icc (-(1/H)) (1/H),
      ‖sourceWeightedPeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k primeSlot Ptwist alpha c chi0 sigma0 sigma1
        (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
        (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ))‖^2) ≤
    2*(H^2)⁻¹ * (∫ v in Set.Ioi (0:ℝ), (H/(2*Real.pi*Y))^2 *
      ‖sourceActualPhysicalQ434 chi (𝓕 K) (H/Y)
        (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N) aPhys)
        (Real.log (v/Y))‖^2) +
    2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*(H/Y)^2 *
      ∑ n ∈ Finset.Icc 1 N, ‖aPhys n‖^2) := by
  dsimp only
  let aPhys := sourceOriginalPhysicalEndpointCoefficient434
    G Ptwist S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase
    alpha c chi0 sigma0 sigma1 den h hden Y psi1 v1
  have hEq (beta : ℝ) :
      sourceWeightedPeeledMarkedFourier N qBase S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k primeSlot Ptwist alpha c chi0 sigma0 sigma1
        (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
        (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ)) =
      sourceNatFourierPoly (Finset.Icc 1 N) aPhys (beta:AddCircle (1:ℝ)) := by
    dsimp only [aPhys]
    unfold sourceOriginalPhysicalEndpointCoefficient434
    exact source_original_weighted_peeled_additive_literal434
        N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k primeSlot Ptwist
        alpha c chi0 sigma0 sigma1 G hG hParityG hSPrime hTsPrime hTbPrime
        L aexp tau Carc den h hden hdenCap hW hsmall hlong
        hAlphaRough hSRange hSlotRange
        (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1) beta
  simp_rw [hEq]
  apply source_additive_physical_transfer434 chi K B hB hchi
    (Finset.Icc 1 N) aPhys H Y A δ M cband hH hY hA hδ hδ1 hM hcband hHcap
    (fun n hn => (Finset.mem_Icc.mp hn).1) _ hSupport hLip hLower hOne
  intro n hn hNZ
  exact source_original_physical_endpoint_support434
    G Ptwist S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb b k qBase
    alpha c chi0 sigma0 sigma1 den h hden Y A psi1 v1 hY hPsi n hNZ
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRationalPhaseUnit -/

section

open Green64Analytic.CorrelationD
namespace Green64Analytic.CorrelationSquare
set_option maxHeartbeats 450000

/-- The *original* unreduced rational-center phase has unit norm
for every q,h,n, including q=0's inherited zero convention. -/
theorem source_original_rational_phase_norm434 (q h n : ℕ) :
    ‖sourceRationalPhase q h n‖ = 1 := by
  have harg :
      ((h:ℂ)*(n:ℂ))/(q:ℂ) * (2*(Real.pi:ℂ)*Complex.I) =
      (((((h:ℝ)*(n:ℝ)/(q:ℝ))*2*Real.pi):ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  unfold sourceRationalPhase
  rw [harg, Complex.norm_exp_ofReal_mul_I]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGroupedPeeledExact -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1400000

/-- EXACT original-source rationally grouped coefficient, with all gcd
and imprimitive character families, is the unreduced rational phase
times the original ungrouped marked peeled endpoint. No source-savings
or independent character-cardinality loss is introduced. -/
theorem source_original_grouped_peeled_raw_exact434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : ((g : β) → Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Parity : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Parity ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (L a tau C : ℝ) (n den h : ℕ)
    (hn : n ∈ Finset.Icc 1 N)
    (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^C)
    (hW : L^C ≤ Real.exp (Real.sqrt L))
    (hsmall : L^C < Real.exp (L^a))
    (hlong : L^C < Real.exp (tau*L))
    (hAlpha : ∀ m, alpha m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
        Real.exp (tau*L) ≤ (p:ℝ)) :
    sourcePeeledGroupedPhysicalSum G Parity S primeSlot Ts Tb
       q0 Vs Vsmall Vbig ts tb b k qBase alpha c chi0 sigma0 sigma1
       n den h hden =
    sourceRationalPhase den h n * (
       literalSourceParity Parity n *
       sourceEndpoint (sourceOutsidePart G)
         (fun z => ((1/Vs:ℝ):ℂ) *
            ∑ ps ∈ smallPrimeSupport S z,
              literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
                ts tb b k (z/ps))
         primeSlot alpha c qBase chi0 sigma0 sigma1 n) := by
  have hFourier := source_original_fourier_grouped_physical_exact
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Parity alpha c chi0 sigma0 sigma1 G
    hG hParityG hSPrime hTsPrime hTbPrime
    L a tau C n den h hden hdenCap hW hsmall hlong
    hAlpha hSRange hSlotRange
  have hCoefficient := source_peeled_fourier_coefficient_exact
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Parity alpha c chi0 sigma0 sigma1 n
  rw [hCoefficient, if_pos hn] at hFourier
  rw [← hG] at hFourier
  simpa only [if_pos hn] using hFourier.symm
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSelectedWeightCap -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 650000

/-- The exact peeled distinguished small-group weight has no more
summands than the real divisor count. The cap on each actual marked
weight is the original pointwise weight input, not an L² assumption. -/
theorem source_original_selected_weight_norm_le434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k n : ℕ) (hn : n ≠ 0) (hVs : 0 < Vs)
    (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ ps ∈ smallPrimeSupport S n,
       ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
           ts tb coef k (n/ps)‖ ≤ B) :
    ‖(((1/Vs : ℝ):ℂ) *
       ∑ ps ∈ smallPrimeSupport S n,
         literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
           ts tb coef k (n/ps))‖ ≤
      (1/Vs) * (n.divisors.card:ℝ) * B := by
  let supp := smallPrimeSupport S n
  let f : ℕ → ℂ := fun ps =>
      literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k (n/ps)
  have hCard : (supp.card:ℝ) ≤ (n.divisors.card:ℝ) :=
    source_original_small_support_card_le434 S n hn
  have hSum : ‖∑ ps ∈ supp, f ps‖ ≤ (supp.card:ℝ)*B := by
    calc
      _ ≤ ∑ ps ∈ supp, ‖f ps‖ := norm_sum_le _ _
      _ ≤ ∑ _ps ∈ supp, B :=
        Finset.sum_le_sum (fun ps hps => hW ps hps)
      _ = (supp.card:ℝ)*B := by simp
  have hInv : 0 < (1/Vs : ℝ) := one_div_pos.mpr hVs
  have hInvNorm : ‖(((1/Vs:ℝ):ℂ))‖ = 1/Vs := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hInv]
  calc
    _ = (1/Vs)*‖∑ ps ∈ supp, f ps‖ := by
      simp only [norm_mul, hInvNorm]
      rfl
    _ ≤ (1/Vs)*((supp.card:ℝ)*B) :=
      mul_le_mul_of_nonneg_left hSum hInv.le
    _ ≤ (1/Vs)*((n.divisors.card:ℝ)*B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hCard hB) hInv.le
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalRawPeeledCap -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 950000

/-- The REAL ungrouped original source endpoint has divisor-cube
majorant, with original sourceCore two divisor sums and the third
factor from the distinguished small-group support. No squarefree
assumptions; the only weight premise is an explicit pointwise mark cap. -/
theorem source_original_raw_peeled_divisor_cube434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (G S primeSlot : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
    (k qBase : ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
    (n : ℕ) (hn : n ≠ 0)
    (hVs : 0 < Vs) (A C B : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hAlpha : ∀ m, ‖alpha m‖ ≤ A)
    (hc : ∀ r, ‖c r‖ ≤ C)
    (hWeight : ∀ ps ∈ smallPrimeSupport S n,
      ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k (n/ps)‖ ≤ B) :
    ‖sourceEndpoint (sourceOutsidePart G)
       (fun z => ((1/Vs:ℝ):ℂ) *
          ∑ ps ∈ smallPrimeSupport S z,
            literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
              ts tb coef k (z/ps))
       primeSlot alpha c qBase chi0 sigma0 sigma1 n‖ ≤
       (A*C*(1/Vs)*B)*(n.divisors.card:ℝ)^3 := by
  let W : ℕ → ℂ := fun z =>
      ((1/Vs:ℝ):ℂ) * ∑ ps ∈ smallPrimeSupport S z,
        literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k (z/ps)
  let T : ℝ := (n.divisors.card : ℝ)
  have hCard : ((sourceOutsidePart G n).divisors.card:ℝ) ≤ T :=
    source_original_outside_card_le434 G n hn
  have hCardSq :
      ((sourceOutsidePart G n).divisors.card:ℝ)^2 ≤ T^2 :=
    pow_le_pow_left₀ (by positivity) hCard 2
  have hCore := sourceCore_divisor_bound
    (sourceOutsidePart G n) qBase primeSlot alpha c
    chi0 sigma0 sigma1 A C hA hC hAlpha hc
  have hCoreBound :
      ‖sourceCore (sourceOutsidePart G n) primeSlot alpha c
          qBase chi0 sigma0 sigma1‖ ≤ A*C*T^2 :=
    hCore.trans
      (mul_le_mul_of_nonneg_left hCardSq (mul_nonneg hA hC))
  have hW : ‖W n‖ ≤ (1/Vs)*T*B :=
    source_original_selected_weight_norm_le434
      S Ts Tb q0 Vs Vsmall Vbig ts tb coef k n hn
      hVs B hB hWeight
  have hBase : 0 ≤ A*C*T^2 := by positivity
  change ‖sourceCore (sourceOutsidePart G n) primeSlot alpha c
      qBase chi0 sigma0 sigma1 * W n‖ ≤ _
  calc
    _ = ‖sourceCore (sourceOutsidePart G n) primeSlot alpha c
          qBase chi0 sigma0 sigma1‖ * ‖W n‖ := norm_mul _ _
    _ ≤ (A*C*T^2) * ‖W n‖ :=
      mul_le_mul_of_nonneg_right hCoreBound (norm_nonneg _)
    _ ≤ (A*C*T^2)*((1/Vs)*T*B) :=
      mul_le_mul_of_nonneg_left hW hBase
    _ = (A*C*(1/Vs)*B)*T^3 := by ring
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGroupedNormReduction -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 1500000

/-- Source grouped coefficient divisor-cube bound with the TRUE
roughness, gcd/character, parity and small/long prime admissibility.
The remaining pointwise marked-weight cap is explicitly displayed. -/
theorem source_original_grouped_norm_from_weight_cap434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
    [Fintype β] [DecidableEq β]
    (N qBase : ℕ) (S : Finset ℕ)
    (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Parity : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
    (G : Finset ℕ)
    (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb))
    (hParityG : Parity ⊆ G)
    (hSPrime : ∀ v ∈ S, v.Prime)
    (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
    (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
    (L a tau Carc : ℝ) (n den h : ℕ)
    (hn : n ∈ Finset.Icc 1 N)
    (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^Carc)
    (hW : L^Carc ≤ Real.exp (Real.sqrt L))
    (hsmall : L^Carc < Real.exp (L^a))
    (hlong : L^Carc < Real.exp (tau*L))
    (hAlphaRough : ∀ m, alpha m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L)))
    (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
    (hSlotRange : ∀ p ∈ primeSlot,
        Real.exp (tau*L) ≤ (p:ℝ))
    (hVs : 0 < Vs) (A C B : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hAlphaBound : ∀ m, ‖alpha m‖ ≤ A)
    (hcBound : ∀ r, ‖c r‖ ≤ C)
    (hMark : ∀ ps ∈ smallPrimeSupport S n,
        ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k (n/ps)‖ ≤ B) :
    ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
       Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
       sigma0 sigma1 n den h hden‖ ≤
      (A*C*(1/Vs)*B)*(n.divisors.card:ℝ)^3 := by
  have heq := source_original_grouped_peeled_raw_exact434
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb coef k
    primeSlot Parity alpha c chi0 sigma0 sigma1 G
    hG hParityG hSPrime hTsPrime hTbPrime
    L a tau Carc n den h hn hden hdenCap hW hsmall hlong
    hAlphaRough hSRange hSlotRange
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hraw := source_original_raw_peeled_divisor_cube434
    G S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
    k qBase alpha c chi0 sigma0 sigma1 n hn0 hVs
    A C B hA hC hB hAlphaBound hcBound hMark
  rw [heq, norm_mul, source_original_rational_phase_norm434,
      one_mul, norm_mul, literal_source_parity_norm_one,
      one_mul]
  exact hraw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalGroupedUniform -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 1800000

/-- TRUE SOURCE-GROUPED ORIGINAL DIVISOR CUBE MAJORANT.
The constant K comes from the already checked literal marked-weight
uniform theorem and is fixed BEFORE all original group, character,
mark, congruence, factor and time parameters. The real source
admissibility is stated explicitly. No high/low/tail energy premise. -/
theorem source_original_grouped_uniform_divisor_cube434
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hvmin : 0 < vmin) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (N qBase : ℕ) (S : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
        (k : ℕ) (primeSlot Parity : Finset ℕ)
        (alpha c : ℕ → ℂ)
        (chi0 : DirichletCharacter ℂ qBase) (sigma0 sigma1 : ℝ)
        (G : Finset ℕ)
        (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                   ((Finset.univ : Finset β).biUnion Tb))
        (hParityG : Parity ⊆ G)
        (hSPrime : ∀ v ∈ S, v.Prime)
        (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
        (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
        (L a tau Carc : ℝ) (n den h : ℕ)
        (hn : n ∈ Finset.Icc 1 N)
        (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^Carc)
        (hW : L^Carc ≤ Real.exp (Real.sqrt L))
        (hsmall : L^Carc < Real.exp (L^a))
        (hlong : L^Carc < Real.exp (tau*L))
        (hAlphaRough : ∀ m, alpha m ≠ 0 →
          SourceRoughAbove m (Real.exp (Real.sqrt L)))
        (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
        (hSlotRange : ∀ p ∈ primeSlot,
          Real.exp (tau*L) ≤ (p:ℝ)),
        k ≤ tmax → vmin ≤ Vs →
        (∀ g, ts g ≤ tmax) → (∀ g, tb g ≤ tmax) →
        (∀ g, vmin ≤ Vsmall g) →
        (∀ g, vmin ≤ Vbig g) →
        (∀ lists, ‖coef lists‖ ≤ 1) →
        ∀ (A C : ℝ), 0 ≤ A → 0 ≤ C →
          (∀ m, ‖alpha m‖ ≤ A) →
          (∀ r, ‖c r‖ ≤ C) →
        ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          alpha c chi0 sigma0 sigma1 n den h hden‖ ≤
        (A*C*(1/Vs)*
          K^(Fintype.card ι+Fintype.card β+1)) *
          (n.divisors.card:ℝ)^3 := by
  obtain ⟨K,hK,hmark⟩ :=
    source_literal_weight_uniform_all_groups
      q0 vmin tmax hq0 hq1 hvmin
  refine ⟨K,hK,?_⟩
  intro ι β instι decι instβ decβ N qBase S Ts Tb Vs Vsmall Vbig
    ts tb coef k primeSlot Parity alpha c chi0 sigma0 sigma1 G
    hG hParityG hSPrime hTsPrime hTbPrime
    L a tau Carc n den h hn hden hdenCap hW hsmall hlong
    hAlphaRough hSRange hSlotRange
    hk hVs hts htb hVsmall hVbig hcoef A C hA hC hAlphaBound hcBound
  have hvsPos : 0 < Vs := lt_of_lt_of_le hvmin hVs
  have hKpow : 0 ≤ K^(Fintype.card ι+Fintype.card β+1) := by
    positivity
  have hWeight (ps : ℕ) (hps : ps ∈ smallPrimeSupport S n) :
      ‖literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig
        ts tb coef k (n/ps)‖ ≤
      K^(Fintype.card ι+Fintype.card β+1) :=
    hmark S Ts Tb Vs Vsmall Vbig ts tb coef k (n/ps)
      hk hVs hts htb hVsmall hVbig hcoef
  exact source_original_grouped_norm_from_weight_cap434
    N qBase S Ts Tb q0 Vs Vsmall Vbig ts tb coef k
    primeSlot Parity alpha c chi0 sigma0 sigma1 G
    hG hParityG hSPrime hTsPrime hTbPrime
    L a tau Carc n den h hn hden hdenCap hW hsmall hlong
    hAlphaRough hSRange hSlotRange
    hvsPos A C (K^(Fintype.card ι+Fintype.card β+1))
    hA hC hKpow hAlphaBound hcBound hWeight
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalCutGroupedBound -/

section

open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1300000

/-- ACTUAL original alpha dyadic cutoff keeps the original pointwise
norm budget. This is NOT a new source hypothesis: it follows by
the literal Icc-filter definition. -/
theorem source_original_alpha_cut_pointwise434
    (alpha : ℕ → ℂ) (lo hi : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hAlpha : ∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ A) :
    ∀ m, ‖sourceAlphaDyadicCut alpha lo hi m‖ ≤ A := by
  intro m
  by_cases hm : m ∈ Finset.Icc lo hi
  · simpa only [sourceAlphaDyadicCut, if_pos hm] using hAlpha m hm
  · simp only [sourceAlphaDyadicCut, if_neg hm, norm_zero]
    exact hA

/-- The REAL grouped/peeled source coefficient with frozen dyadic
alpha and original character/gcd/parity/marking data has the divisor
cube bound, with Kg fixed BEFORE every group and source parameter.
It is DERIVED from source-original admissibility; no hGrp input. -/
theorem source_original_cut_grouped_uniform_divisor_cube434
    (q0 vmin : ℝ) (tmax : ℕ)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hvmin : 0 < vmin) :
    ∃ Kg : ℝ, 1 ≤ Kg ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (N qBase : ℕ) (S : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
        (k : ℕ) (primeSlot Parity : Finset ℕ)
        (alpha c : ℕ → ℂ) (lo hi : ℕ)
        (chi0 : DirichletCharacter ℂ qBase)
        (sigma0 sigma1 : ℝ) (G : Finset ℕ)
        (hG : G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
                   ((Finset.univ : Finset β).biUnion Tb))
        (hParityG : Parity ⊆ G)
        (hSPrime : ∀ v ∈ S, v.Prime)
        (hTsPrime : ∀ g, ∀ v ∈ Ts g, v.Prime)
        (hTbPrime : ∀ g, ∀ v ∈ Tb g, v.Prime)
        (L a tau Carc : ℝ) (den h : ℕ)
        (hden : 0 < den) (hdenCap : (den:ℝ) ≤ L^Carc)
        (hW : L^Carc ≤ Real.exp (Real.sqrt L))
        (hsmall : L^Carc < Real.exp (L^a))
        (hlong : L^Carc < Real.exp (tau*L))
        (hAlphaRough : ∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
          SourceRoughAbove m (Real.exp (Real.sqrt L)))
        (hSRange : ∀ ps ∈ S, Real.exp (L^a) ≤ (ps:ℝ))
        (hSlotRange : ∀ p ∈ primeSlot,
          Real.exp (tau*L) ≤ (p:ℝ)),
        k ≤ tmax → vmin ≤ Vs →
        (∀ g, ts g ≤ tmax) → (∀ g, tb g ≤ tmax) →
        (∀ g, vmin ≤ Vsmall g) →
        (∀ g, vmin ≤ Vbig g) →
        (∀ lists, ‖coef lists‖ ≤ 1) →
        ∀ (Aalpha Cc : ℝ), 0 ≤ Aalpha → 0 ≤ Cc →
          (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ Aalpha) →
          (∀ r, ‖c r‖ ≤ Cc) →
        ∀ (n : ℕ), n ∈ Finset.Icc 1 N →
          ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
            Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
            (sourceAlphaDyadicCut alpha lo hi) c chi0
            sigma0 sigma1 n den h hden‖ ≤
          (Aalpha*Cc*(1/Vs)*
            Kg^(Fintype.card ι+Fintype.card β+1)) *
            (n.divisors.card:ℝ)^3 := by
  obtain ⟨Kg,hKg,hbound⟩ :=
    source_original_grouped_uniform_divisor_cube434
      q0 vmin tmax hq0 hq1 hvmin
  refine ⟨Kg,hKg,?_⟩
  intro ι β instι decι instβ decβ N qBase S Ts Tb Vs
    Vsmall Vbig ts tb coef k primeSlot Parity alpha c lo hi
    chi0 sigma0 sigma1 G hG hParityG hSPrime hTsPrime hTbPrime
    L a tau Carc den h hden hdenCap hW hsmall hlong
    hAlphaRough hSRange hSlotRange
    hk hVs hts htb hVsmall hVbig hcoef
    Aalpha Cc hA hC hAlphaBound hcBound n hn
  have hAlphaCut := source_original_alpha_cut_pointwise434
    alpha lo hi Aalpha hA hAlphaBound
  exact hbound N qBase S Ts Tb Vs Vsmall Vbig ts tb
    coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi)
    c chi0 sigma0 sigma1 G
    hG hParityG hSPrime hTsPrime hTbPrime
    L a tau Carc n den h hn hden hdenCap hW hsmall hlong
    hAlphaRough hSRange hSlotRange
    hk hVs hts htb hVsmall hVbig hcoef
    Aalpha Cc hA hC hAlphaCut hcBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSignedEndpoint -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option maxHeartbeats 4500000

/-- Genuine original FULL endpoint coefficients before either independent
parity choice. Integer indexing is only the existing Fourier embedding. -/
noncomputable def sourceOriginalFullEndpointCoefficients434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (q : ℕ) (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ)
    (Lambda : ℕ → ℂ) (z : ℤ) : ℂ :=
  Lambda z.toNat * sourceEndpoint
    (sourceOutsidePart (S ∪ Finset.univ.biUnion Ts ∪ Finset.univ.biUnion Tb))
    (literalSourceWeight S Ts Tb q0 Vs Vsmall Vbig ts tb b (k+1))
    primeSlot alpha c q chi sigma0 sigma1 z.toNat

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
variable (N q : ℕ) (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k : ℕ)
    (primeSlot Ptw : Finset ℕ) (alpha c : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) (Lambda : ℕ → ℂ)

/-- Each endpoint sign is the original source parity for P or the empty
set. This supplies both first-endpoint choices, not just a shared twist. -/
theorem source_original_full_signed_fourier434 (eps : Bool) :
    sourceCircleFourierPoly ((Finset.Icc 1 N).image (fun n : ℕ => (n:ℤ)))
      (sourceSignedCoefficients434 Ptw eps
        (sourceOriginalFullEndpointCoefficients434 q S Ts Tb q0 Vs Vsmall Vbig
          ts tb b k primeSlot alpha c chi sigma0 sigma1 Lambda)) =
    sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot (if eps then Ptw else ∅) alpha c chi sigma0 sigma1 Lambda := by
  unfold sourceWeightedFullMarkedFourier sourceNatFourierPoly
  apply congrArg (sourceCircleFourierPoly _)
  funext z
  dsimp only [sourceSignedCoefficients434,sourceOriginalFullEndpointCoefficients434]
  cases eps
  · simp [sourceEndpointSign434,literalSourceParity]
  · simp only [sourceEndpointSign434,ite_true]
    ring

/-- Source global FULL energy is exactly the unsigned coefficient square
budget required by comparison, for any parity subset at the endpoint. -/
theorem source_original_full_coefficient_parseval434 :
    (∑ z ∈ (Finset.Icc 1 N).image (fun n : ℕ => (n:ℤ)),
      ‖sourceOriginalFullEndpointCoefficients434 q S Ts Tb q0 Vs Vsmall Vbig
        ts tb b k primeSlot alpha c chi sigma0 sigma1 Lambda z‖^2) =
    ∫ theta : AddCircle (1:ℝ),
      ‖sourceWeightedFullMarkedFourier N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
        primeSlot Ptw alpha c chi sigma0 sigma1 Lambda theta‖^2 ∂AddCircle.haarAddCircle := by
  have hPoly := source_original_full_signed_fourier434 N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Ptw alpha c chi sigma0 sigma1 Lambda true
  simp only [ite_true] at hPoly
  rw [← hPoly,source_circle_fourier_parseval,source_signed_coefficients_square434]

/-- Exact interface from the frozen original arc conclusion to the
independently signed first endpoint used in all four comparisons. -/
theorem source_original_full_signed_arc_iff434 (eps : Bool) (L Y Hprime Carc A K : ℝ)
    (h den : ℕ) :
    SourceOriginalArcConclusion434 N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot (if eps then Ptw else ∅) alpha c chi sigma0 sigma1 Lambda
      L Y Hprime Carc A K h den ↔
    (∫ beta in {beta : ℝ | |beta| ≤ L^Carc/Hprime},
      ‖sourceCircleFourierPoly ((Finset.Icc 1 N).image (fun n : ℕ => (n:ℤ)))
        (sourceSignedCoefficients434 Ptw eps
          (sourceOriginalFullEndpointCoefficients434 q S Ts Tb q0 Vs Vsmall Vbig
            ts tb b k primeSlot alpha c chi sigma0 sigma1 Lambda))
        (((h:ℝ)/(den:ℝ)+beta:ℝ):AddCircle (1:ℝ))‖^2) ≤ K*Y*L^(-A) := by
  unfold SourceOriginalArcConclusion434
  rw [source_original_full_signed_fourier434 N q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
    primeSlot Ptw alpha c chi sigma0 sigma1 Lambda eps]
end

theorem source_parity_choice_subset434 (P G : Finset ℕ) (hP : P ⊆ G) (eps : Bool) :
    (if eps then P else ∅) ⊆ G := by
  cases eps
  · exact Finset.empty_subset G
  · exact hP
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalEndpointSplit -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

theorem source_original_group_union_split434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ) :
    Finset.univ.biUnion (Sum.elim (fun _ : Unit => S) (Sum.elim Ts Tb)) =
      S ∪ Finset.univ.biUnion Ts ∪ Finset.univ.biUnion Tb := by
  ext p
  simp only [Finset.mem_biUnion,Finset.mem_union,Finset.mem_univ,true_and,
    Sum.exists,Sum.elim_inl,Sum.elim_inr,exists_const,or_assoc]

/-- Source physical all-group weight times the ACTUAL invariant core
is exactly C's original FULL endpoint, not a new surrogate endpoint. -/
theorem source_original_marked_core_endpoint_split434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S : Finset ℕ) (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
    (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
    (k : ℕ) (ts : ι → ℕ) (tb : β → ℕ)
    (b : (∀ j,Fin (tb j) → ℕ) → ℂ) (n q : ℕ)
    (primeSlot : Finset ℕ) (alpha c Lambda : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ) :
    let P := Sum.elim (fun _ : Unit => S) (Sum.elim Ts Tb)
    Lambda n*sourceCore (sourceOutsidePart (Finset.univ.biUnion P) n)
      primeSlot alpha c q chi s0 s1*
      actualBigMarkDecoration P (Sum.elim (fun _ : Unit => k+1) (Sum.elim ts tb)) q0
        (Sum.elim (fun _ : Unit => Vs) (Sum.elim Vsmall Vbig))
        (fun a => b (fun j => a (.inr (.inr j)))) n =
    sourceOriginalFullEndpointCoefficients434 q S Ts Tb q0 Vs Vsmall Vbig ts tb b k
      primeSlot alpha c chi s0 s1 Lambda (n:ℤ) := by
  dsimp only
  rw [source_original_group_union_split434,source_original_marked_weight_split434]
  simp only [sourceOriginalFullEndpointCoefficients434,Int.toNat_natCast,sourceEndpoint]
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalWholeTimeAssembled -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1100000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
  (k qBase : ℕ) (alpha c : ℕ → ℂ)
  (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- TRUE original physical full-time weighted source Mellin norm is
bounded by the low-time actual SOURCE energy plus a COMPLETELY
DERIVED full-real tail. The ONLY explicit source pointwise norm input
is the genuine grouped divisor-cube majorant (independently provable
under unchanged source admissibility). No extra source-saving
assumption is introduced. -/
theorem source_original_named_whole_time_from_group434
    (Y A : ℝ) (hY : 0 < Y)
    (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hUpper : ∀ u, psi1 u ≠ 0 → u ≤ A)
    (Bpsi Bgroup : ℝ) (hpsi : 0 ≤ Bpsi) (hgroup : 0 ≤ Bgroup)
    (hCut : ∀ n ∈ Finset.Icc 1 N, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi)
    (hGrp : ∀ n ∈ Finset.Icc 1 N,
      ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 n den h hden‖ ≤
          Bgroup * (n.divisors.card:ℝ)^3)
    (ω L : ℝ) (hω : 0 < ω) (hL : 1 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) :
    (∫ t : ℝ, ((1+ω*|t|)^j)⁻¹ *
      ‖(Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      (∫ t in Set.Icc (-(L/ω)) (L/ω),
        ‖(Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          alpha c chi0 sigma0 sigma1 N den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) +
      (4 * ((L^(j-2))⁻¹ *
        (L/ω+16*(Nat.ceil (A*Y):ℝ) *
          (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
        ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ) *
          (1+Real.log (Nat.ceil (A*Y):ℝ))^63) := by
  have hT : 0 ≤ L/ω := div_nonneg (zero_le_one.trans hL) hω.le
  have hSplit := source_original_named_real_low_high434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    Y hY psi1 v1 ω (L/ω) hω hT j hj
  have hTail := source_original_named_whole_real_tail_from_group434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    Y A hY psi1 v1 hUpper Bpsi Bgroup hpsi hgroup
    hCut hGrp ω L hω hL j hj
  have hStep : (∫ t : ℝ, ((1+ω*|t|)^j)⁻¹ *
      ‖(Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      (∫ t in Set.Icc (-(L/ω)) (L/ω),
        ‖(Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          alpha c chi0 sigma0 sigma1 N den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) +
      (∫ t in {t : ℝ | L/ω ≤ |t|},
        ((1+ω*|t|)^j)⁻¹ *
        ‖(Y:ℂ) * sourceOriginalPhysicalMellin434 G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          alpha c chi0 sigma0 sigma1 N den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) := by
    simpa only [sourceFrozenP434] using hSplit
  exact hStep.trans (add_le_add_right hTail _)
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalWholeTimeLowBridge -/

section

open MeasureTheory
open scoped BigOperators
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 1700000

section
variable {ι β : Type} [Fintype ι] [DecidableEq ι]
  [Fintype β] [DecidableEq β]
variable (G Parity S primeSlot : Finset ℕ)
  (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
  (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
  (ts : ι → ℕ) (tb : β → ℕ)
  (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
  (k qBase : ℕ) (alpha c : ℕ → ℂ)
  (chi0 : DirichletCharacter ℂ qBase)
  (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)

/-- Actual source physical full-time weighted Mellin is controlled
by precisely the original literal-cell low-time certificate plus the
DERIVED source full-real ± angular-time tail. The source low-time
premise is the EXACT existing literal theorem conclusion, never a
synthetic savings assumption. Physical time is omega=H/Y,
H=Hprime/L^Carc, with the original 1/Y normalization. -/
theorem source_original_whole_time_from_literal_low434
    (Y A : ℝ) (hY : 0 < Y)
    (psi1 : ℝ → ℂ) (v1 : ℝ)
    (hUpper : ∀ u, psi1 u ≠ 0 → u ≤ A)
    (Bpsi Bgroup : ℝ) (hpsi : 0 ≤ Bpsi) (hgroup : 0 ≤ Bgroup)
    (hCut : ∀ n ∈ Finset.Icc 1 N, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi)
    (hGrp : ∀ n ∈ Finset.Icc 1 N,
      ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 n den h hden‖ ≤
          Bgroup*(n.divisors.card:ℝ)^3)
    (Hprime L Carc : ℝ) (hHprime : 0 < Hprime) (hL : 3 ≤ L)
    (j : ℕ) (hj : 2 ≤ j) (E : ℝ)
    (hOriginalLiteral :
      (∫ t in Set.Icc (-(2*L*Y/(Hprime/L^Carc))) (2*L*Y/(Hprime/L^Carc)),
        ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          alpha c chi0 sigma0 sigma1 N den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤ E) :
    (1/Y)*(∫ t : ℝ,
      ((1+((Hprime/L^Carc)/Y)*|t|)^j)⁻¹ *
      ‖(Y:ℂ)*sourceOriginalPhysicalMellin434 G Parity S primeSlot
        Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
        alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤
      Y*E + (1/Y) *
        ((4 * ((L^(j-2))⁻¹ *
          (L*Y/(Hprime/L^Carc)+16*(Nat.ceil (A*Y):ℝ) *
            (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
          ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ) *
            (1+Real.log (Nat.ceil (A*Y):ℝ))^63)) := by
  let ω : ℝ := (Hprime/L^Carc)/Y
  have hLc : 0 < L^Carc :=
    Real.rpow_pos_of_pos (by linarith) _
  have hHp : 0 < Hprime/L^Carc := div_pos hHprime hLc
  have hω : 0 < ω := div_pos hHp hY
  have hTime : L/ω = L*Y/(Hprime/L^Carc) := by
    dsimp [ω]
    have hHp0 : Hprime/L^Carc ≠ 0 := hHp.ne'
    have hY0 : Y ≠ 0 := hY.ne'
    field_simp
  have hWhole := source_original_named_whole_time_from_group434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
    k qBase alpha c chi0 sigma0 sigma1 N den h hden
    Y A hY psi1 v1 hUpper Bpsi Bgroup hpsi hgroup hCut hGrp
    ω L hω (by linarith : 1 ≤ L) j hj
  rw [hTime] at hWhole
  have hLow := source_original_literal_low_to_physical434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    Y Hprime L Carc hY hHprime hL psi1 v1 E hOriginalLiteral
  have hInv : 0 ≤ (1/Y:ℝ) := by positivity
  calc
    _ ≤ (1/Y) *
      ((∫ t in Set.Icc
        (-(L*Y/(Hprime/L^Carc))) (L*Y/(Hprime/L^Carc)),
        ‖(Y:ℂ)*sourceOriginalPhysicalMellin434
          G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
          k qBase alpha c chi0 sigma0 sigma1 N den h hden
          (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) +
        ((4 * ((L^(j-2))⁻¹ *
          (L*Y/(Hprime/L^Carc)+16*(Nat.ceil (A*Y):ℝ) *
            (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
          ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ) *
            (1+Real.log (Nat.ceil (A*Y):ℝ))^63))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [ω] using hWhole) hInv
    _ = (1/Y) *
        (∫ t in Set.Icc
          (-(L*Y/(Hprime/L^Carc))) (L*Y/(Hprime/L^Carc)),
          ‖(Y:ℂ)*sourceOriginalPhysicalMellin434
            G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
            k qBase alpha c chi0 sigma0 sigma1 N den h hden
            (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) +
        (1/Y) *
          ((4 * ((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc)+16*(Nat.ceil (A*Y):ℝ) *
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
            ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ) *
              (1+Real.log (Nat.ceil (A*Y):ℝ))^63)) := by ring
    _ ≤ _ := add_le_add_left hLow _
end
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFullLiteral -/

section

open MeasureTheory
open scoped BigOperators SchwartzMap
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationMellin
set_option maxHeartbeats 2500000

/-- ORIGINAL source physical log-center collar with full angular R:
native physical 1/Y Plancherel-Schur, original small-time literal-cell
source certificate, and genuine source full positive/negative real
time tail. The only displayed source input is the exact low-time
conclusion supplied by the already-proved SourceAlphaDiscrepancy
literal theorem; grouped mark bound follows from original
admissibility, not from hHigh/hLow/hApprox/hTail. -/
theorem source_original_physical_collar_literal_full434
    (chi kappa : 𝓢(ℝ,ℂ)) (B : ℝ) (hB : 0 < B)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-B) B)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β]
        (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (q0 Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : ((g : β) → Fin (tb g) → ℕ) → ℂ)
        (k qBase : ℕ) (alpha c : ℕ → ℂ)
        (chi0 : DirichletCharacter ℂ qBase)
        (sigma0 sigma1 : ℝ) (N den h : ℕ) (hden : 0 < den)
        (Y A : ℝ) (hY : 0 < Y) (psi1 : ℝ → ℂ) (v1 : ℝ)
        (hUpper : ∀ u, psi1 u ≠ 0 → u ≤ A)
        (Bpsi Bgroup : ℝ) (hpsi : 0 ≤ Bpsi) (hgroup : 0 ≤ Bgroup)
        (hCut : ∀ n ∈ Finset.Icc 1 N, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi)
        (hGrp : ∀ n ∈ Finset.Icc 1 N,
          ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
            Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
            alpha c chi0 sigma0 sigma1 n den h hden‖ ≤
              Bgroup * (n.divisors.card:ℝ)^3)
        (Hprime L Carc : ℝ) (hHprime : 0 < Hprime) (hL : 3 ≤ L)
        (E : ℝ)
        (hSource :
          (∫ t in Set.Icc
            (-(2*L*Y/(Hprime/L^Carc))) (2*L*Y/(Hprime/L^Carc)),
            ‖sourceOriginalPhysicalMellin434 G Parity S primeSlot
              Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase alpha c chi0
              sigma0 sigma1 N den h hden
              (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2) ≤ E),
      (((Hprime/L^Carc)^2)⁻¹) *
        (∫ v in Set.Ioi (0:ℝ),
          ((Hprime/L^Carc)/(2*Real.pi*Y))^2 *
          ‖sourceActualPhysicalQ434 chi kappa ((Hprime/L^Carc)/Y)
            (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N)
              (sourceOriginalPhysicalEndpointCoefficient434
                G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
                coef k qBase alpha c chi0 sigma0 sigma1
                den h hden Y psi1 v1))
            (Real.log (v/Y))‖^2) ≤
        K*(Y*E+(1/Y)*
          ((4*((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc)+16*(Nat.ceil (A*Y):ℝ) *
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
            ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ) *
              (1+Real.log (Nat.ceil (A*Y):ℝ))^63))) := by
  obtain ⟨K,hK,hPhysical⟩ :=
    source_original_named_physical_normalized434
      chi kappa B hB hchi j hj
  refine ⟨K,hK,?_⟩
  intro ι β _ _ _ _
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
    Y A hY psi1 v1 hUpper Bpsi Bgroup hpsi hgroup hCut hGrp
    Hprime L Carc hHprime hL E hSource
  let H : ℝ := Hprime/L^Carc
  have hLp : 0 < L^Carc :=
    Real.rpow_pos_of_pos (by linarith : 0 < L) _
  have hH : 0 < H := div_pos hHprime hLp
  let mass : ℝ :=
    ∫ t : ℝ, ((1+(H/Y)*|t|)^j)⁻¹ *
      ‖(Y:ℂ)*sourceOriginalPhysicalMellin434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef
        k qBase alpha c chi0 sigma0 sigma1 N den h hden
        (sourceActualOriginalWindowWeight Y psi1 v1) t‖^2
  let tail : ℝ :=
    (4 * ((L^(j-2))⁻¹ *
      (L*Y/(Hprime/L^Carc)+16*(Nat.ceil (A*Y):ℝ) *
        (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
      ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ) *
        (1+Real.log (Nat.ceil (A*Y):ℝ))^63)
  have hP : (H^2)⁻¹ *
      (∫ v in Set.Ioi (0:ℝ),
        (H/(2*Real.pi*Y))^2 *
        ‖sourceActualPhysicalQ434 chi kappa (H/Y)
          (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N)
            (sourceOriginalPhysicalEndpointCoefficient434
              G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
              coef k qBase alpha c chi0 sigma0 sigma1
              den h hden Y psi1 v1))
          (Real.log (v/Y))‖^2) ≤ (K/Y)*mass :=
    hPhysical G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
      coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
      psi1 v1 H Y hH hY
  have hW : (1/Y)*mass ≤ Y*E+(1/Y)*tail := by
    simpa only [mass,tail,H] using
      (source_original_whole_time_from_literal_low434
        G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
        coef k qBase alpha c chi0 sigma0 sigma1 N den h hden
        Y A hY psi1 v1 hUpper
        Bpsi Bgroup hpsi hgroup hCut hGrp
        Hprime L Carc hHprime hL j hj E hSource)
  change (H^2)⁻¹ *
      (∫ v in Set.Ioi (0:ℝ),
        (H/(2*Real.pi*Y))^2 *
        ‖sourceActualPhysicalQ434 chi kappa (H/Y)
          (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 N)
            (sourceOriginalPhysicalEndpointCoefficient434
              G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
              coef k qBase alpha c chi0 sigma0 sigma1
              den h hden Y psi1 v1))
          (Real.log (v/Y))‖^2) ≤ K*(Y*E+(1/Y)*tail)
  calc
    _ ≤ (K/Y)*mass := hP
    _ = K*((1/Y)*mass) := by ring
    _ ≤ K*(Y*E+(1/Y)*tail) :=
      mul_le_mul_of_nonneg_left hW hK.le
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalPhysicalFromDiscrepancy -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 8500000

/-- DIRECT original SourceAlphaDiscrepancy source saving, full real
positive/negative angular-time tail, and the exact PHYSICAL
Plancherel-Schur K_j/Y log-center collar. K_j depends ONLY on the
fixed collar Schwartz symbol/compact support and j, chosen BEFORE
all source prime groups, marks, rational parameters and cutoffs.
The explicit grouped divisor-cube pointwise arithmetic condition is
kernel-derived under genuine original source admissibility; NO
source-energy-saving premise hLow/hHigh/hTail/hApprox is introduced.
Still a physical peeled collar, not yet the full additive sh:arc-target. -/
theorem eventually_source_original_physical_from_discrepancy434
    (chi kappa : 𝓢(ℝ,ℂ)) (Bchi : ℝ) (hBchi : 0 < Bchi)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-Bchi) Bchi)
    (j : ℕ) (hj : 2 ≤ j)
    (aexp bexp cexp Carc τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 0 < K ∧
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (hUpper : ∀ u : ℝ, psi1 u ≠ 0 → u ≤ A) →
      ∀ (Bpsi Bgroup : ℝ), 0 ≤ Bpsi → 0 ≤ Bgroup →
      (∀ n ∈ Finset.Icc 1 Ncap, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi) →
      (∀ n ∈ Finset.Icc 1 Ncap,
        ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1
          n den h hden‖ ≤ Bgroup*(n.divisors.card:ℝ)^3) →
      (((Hprime/L^Carc)^2)⁻¹) *
        (∫ v in Set.Ioi (0:ℝ),
          ((Hprime/L^Carc)/(2*Real.pi*Y))^2 *
          ‖sourceActualPhysicalQ434 chi kappa ((Hprime/L^Carc)/Y)
            (sourceLiteralTwistedMellin434 Y (Finset.Icc 1 Ncap)
              (sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot
                Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
                (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1
                den h hden Y psi1 v1))
            (Real.log (v/Y))‖^2) ≤
        K * (Y * ((1/Vs)^2 * (den:ℝ)^2 *
          (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹) +
          (1/Y) * ((4*((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc) + 16*(Nat.ceil (A*Y):ℝ)*
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
              ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ)*
                (1+Real.log (Nat.ceil (A*Y):ℝ))^63))) := by
  obtain ⟨K,hK,hPhysical⟩ :=
    source_original_physical_collar_literal_full434
      chi kappa Bchi hBchi hchi j hj
  obtain ⟨B,X0,hX0,hOriginal⟩ :=
    eventually_source_original_global_physical_from_literal_cells434
      aexp bexp cexp Carc τ η Cχ C0 q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut epsi
      A Cpsi Kpsi hA hCpsi hKpsi hepsi hFcut
      haexp hab hb hbc hτ hτη hη hCχ hC0 hq0 hq1 hv
  refine ⟨K,hK,B,X0,hX0,?_⟩
  filter_upwards [hOriginal] with L hOriginalL
  intro x hx hLog hL Y Hprime hY hYmax hH hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  intro psi1 hSmooth hSupport v1 hv1 hBudget hden
  intro hUpper Bpsi Bgroup hBpsi hBgroup hPsiCap hGrp
  have hSrc := hOriginalL x hx hLog hL Y Hprime hY hYmax hH hYstrong
    hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
    G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
    F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
    psi1 hSmooth hSupport v1 hv1 hBudget hden
  exact hPhysical
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb
    coef k qBase (sourceAlphaDyadicCut alpha lo hi) c
    chi0 sigma0 sigma1 Ncap den h hden
    Y A (by linarith : 0 < Y) psi1 v1 hUpper
    Bpsi Bgroup hBpsi hBgroup hPsiCap hGrp
    Hprime L Carc hH hL
    ((1/Vs)^2 * (den:ℝ)^2 * (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹)
    hSrc
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAdditiveFromDiscrepancy -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 10000000

/-- Direct invocation of the original discrepancy-to-physical theorem,
then the new exact additive transfer. No assumed physical energy bound.
Source arithmetic grouped cap and explicit arc geometry are retained. -/
theorem eventually_source_original_additive_from_discrepancy434
    (chi Kbump : 𝓢(ℝ,ℂ)) (Bchi : ℝ) (hBchi : 0 < Bchi)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-Bchi) Bchi)
    (j : ℕ) (hj : 2 ≤ j)
    (aexp bexp cexp Carc τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (δ M cband : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hcband : 0 < cband)
    (hSupportK : ∀ z, Kbump z ≠ 0 → |z| ≤ δ)
    (hLipK : ∀ z z', ‖Kbump z-Kbump z'‖ ≤ M*|z-z'|)
    (hLowerK : ∀ t : ℝ, |t| ≤ 1 → cband ≤ ‖(𝓕 (Kbump : ℝ → ℂ)) t‖)
    (hOne : ∀ Y v : ℝ, 0 < Y → v ∈ Set.Icc (Y/(2*A)) (2*A*Y) →
      chi (Real.log (v/Y)) = 1)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ K : ℝ, 0 < K ∧
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (hUpper : ∀ u : ℝ, psi1 u ≠ 0 → u ≤ A) →
      ∀ (Bpsi Bgroup : ℝ), 0 ≤ Bpsi → 0 ≤ Bgroup →
      (∀ n ∈ Finset.Icc 1 Ncap, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi) →
      (∀ n ∈ Finset.Icc 1 Ncap,
        ‖sourcePeeledGroupedPhysicalSum G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1
          n den h hden‖ ≤ Bgroup*(n.divisors.card:ℝ)^3) →
      G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb) → Parity ⊆ G →
      (∀ g, ∀ p ∈ Ts g, p.Prime) → (∀ g, ∀ p ∈ Tb g, p.Prime) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L))) →
      (den:ℝ) ≤ L^Carc → L^Carc ≤ Real.exp (Real.sqrt L) →
      L^Carc < Real.exp (L^aexp) → L^Carc < Real.exp (τ*L) →
      (∀ p ∈ primeSlot, Real.exp (τ*L) ≤ (p:ℝ)) →
      1 ≤ Hprime/L^Carc → Hprime/L^Carc ≤ Y/(8*A) →
      cband^2 * (∫ beta in Set.Icc (-(1/(Hprime/L^Carc))) (1/(Hprime/L^Carc)),
        ‖sourceWeightedPeeledMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
          chi0 sigma0 sigma1 (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
          (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ))‖^2) ≤
        2*(K * (Y * ((1/Vs)^2 * (den:ℝ)^2 *
          (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹) +
          (1/Y) * ((4*((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc) + 16*(Nat.ceil (A*Y):ℝ)*
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
              ((Bpsi*Bgroup)^2*(Nat.ceil (A*Y):ℝ)*
                (1+Real.log (Nat.ceil (A*Y):ℝ))^63)))) +
        2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*((Hprime/L^Carc)/Y)^2 *
          ∑ n ∈ Finset.Icc 1 Ncap, ‖sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1
          den h hden Y psi1 v1 n‖^2) := by
  obtain ⟨K,hK,B,X0,hX0,hOriginal⟩ :=
    eventually_source_original_physical_from_discrepancy434
      chi (𝓕 Kbump) Bchi hBchi hchi j hj
      aexp bexp cexp Carc τ η Cχ C0 q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut epsi A Cpsi Kpsi
      hA hCpsi hKpsi hepsi hFcut haexp hab hb hbc hτ hτη hη
      hCχ hC0 hq0 hq1 hv
  refine ⟨K,hK,B,X0,hX0,?_⟩
  filter_upwards [hOriginal] with L hOriginalL
  intro x hx hLog hL Y Hprime hY hYmax hH hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  intro psi1 hSmooth hSupport v1 hv1 hBudget hden
  intro hUpper Bpsi Bgroup hBpsi hBgroup hPsiCap hGrp
  intro hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin hHband hArcCap
  have hPhys := hOriginalL x hx hLog hL Y Hprime hY hYmax hH hYstrong
    hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
    G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
    F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
    psi1 hSmooth hSupport v1 hv1 hBudget hden
    hUpper Bpsi Bgroup hBpsi hBgroup hPsiCap hGrp
  have hArc := source_original_peeled_physical_arc434
    Ncap qBase S Ts Tb q0 Vs Vsmall Vbig ts tb coef k primeSlot Parity
    (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1 G
    hG hParity hSPrime hTsPrime hTbPrime
    L aexp τ Carc den h hden hDenOriginal hOrigW hOrigSmall hOrigLong
    hRoughOriginal (fun p hp => (hSmall p hp).1) hSlotMin
    chi Kbump Bchi (Hprime/L^Carc) Y A δ M cband psi1 v1
    hBchi hchi hHband (by linarith : 0 < Y) hA hδ hδ1 hM hcband hArcCap
    hSupport hSupportK hLipK hLowerK
    (fun v hvV => hOne Y v (by linarith : 0 < Y) hvV)
  have hScaled := mul_le_mul_of_nonneg_left hPhys (by norm_num : (0:ℝ) ≤ 2)
  apply hArc.trans
  convert add_le_add hScaled (le_refl
    (2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*((Hprime/L^Carc)/Y)^2 *
      ∑ n ∈ Finset.Icc 1 Ncap, ‖sourceOriginalPhysicalEndpointCoefficient434 G Parity S primeSlot
          Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
          (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1
          den h hden Y psi1 v1 n‖^2))) using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalAdditiveUniformOrder -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 12000000

/-- Original additive source discrepancy estimate with grouped coefficient
bound and supported moment discharged; the fixed mark constant Kg is
chosen BEFORE the freely selectable Schwartz decay order j. -/
theorem eventually_source_original_additive_uniform_order434
    (chi Kbump : 𝓢(ℝ,ℂ)) (Bchi : ℝ) (hBchi : 0 < Bchi)
    (hchi : tsupport (chi : ℝ → ℂ) ⊆ Set.Icc (-Bchi) Bchi)
    (aexp bexp cexp Carc τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (δ M cband : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : 0 ≤ M) (hcband : 0 < cband)
    (hSupportK : ∀ z, Kbump z ≠ 0 → |z| ≤ δ)
    (hLipK : ∀ z z', ‖Kbump z-Kbump z'‖ ≤ M*|z-z'|)
    (hLowerK : ∀ t : ℝ, |t| ≤ 1 → cband ≤ ‖(𝓕 (Kbump : ℝ → ℂ)) t‖)
    (hOne : ∀ Y v : ℝ, 0 < Y → v ∈ Set.Icc (Y/(2*A)) (2*A*Y) →
      chi (Real.log (v/Y)) = 1)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ Kg : ℝ, 1 ≤ Kg ∧ ∀ (j : ℕ), 2 ≤ j → ∃ K : ℝ, 0 < K ∧
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (hUpper : ∀ u : ℝ, psi1 u ≠ 0 → u ≤ A) →
      ∀ (Bpsi : ℝ), 0 ≤ Bpsi →
      (∀ n ∈ Finset.Icc 1 Ncap, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi) →
      G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb) → Parity ⊆ G →
      (∀ g, ∀ p ∈ Ts g, p.Prime) → (∀ g, ∀ p ∈ Tb g, p.Prime) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L))) →
      (den:ℝ) ≤ L^Carc → L^Carc ≤ Real.exp (Real.sqrt L) →
      L^Carc < Real.exp (L^aexp) → L^Carc < Real.exp (τ*L) →
      (∀ p ∈ primeSlot, Real.exp (τ*L) ≤ (p:ℝ)) →
      1 ≤ Hprime/L^Carc → Hprime/L^Carc ≤ Y/(8*A) →
      cband^2 * (∫ beta in Set.Icc (-(1/(Hprime/L^Carc))) (1/(Hprime/L^Carc)),
        ‖sourceWeightedPeeledMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
          chi0 sigma0 sigma1 (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
          (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ))‖^2) ≤
        2*(K * (Y * ((1/Vs)^2 * (den:ℝ)^2 *
          (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹) +
          (1/Y) * ((4*((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc) + 16*(Nat.ceil (A*Y):ℝ)*
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
              ((Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1)))^2*(Nat.ceil (A*Y):ℝ)*
                (1+Real.log (Nat.ceil (A*Y):ℝ))^63)))) +
        2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*((Hprime/L^Carc)/Y)^2 *
          ((Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1)))^2*(Nat.ceil (A*Y):ℝ)*
            (1+Real.log (Nat.ceil (A*Y):ℝ))^63)) := by
  obtain ⟨Kg,hKg,hGrouped⟩ := source_original_cut_grouped_uniform_divisor_cube434
    q0 vmin tmax hq0 hq1 hv
  refine ⟨Kg,hKg,?_⟩
  intro j hj
  obtain ⟨K,hK,B,X0,hX0,hOriginal⟩ :=
    eventually_source_original_additive_from_discrepancy434
      chi Kbump Bchi hBchi hchi j hj
      aexp bexp cexp Carc τ η Cχ C0 q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut epsi A Cpsi Kpsi
      hA hCpsi hKpsi δ M cband hδ hδ1 hM hcband
      hSupportK hLipK hLowerK hOne
      hepsi hFcut haexp hab hb hbc hτ hτη hη hCχ hC0 hq0 hq1 hv
  refine ⟨K,hK,B,X0,hX0,?_⟩
  filter_upwards [hOriginal] with L hOriginalL
  intro x hx hLog hL Y Hprime hY hYmax hH hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  intro psi1 hSmooth hSupport v1 hv1 hBudget hden
  intro hUpper Bpsi hBpsi hPsiCap
  intro hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin hHband hArcCap
  let Bg : ℝ := (L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1))
  have hLp : 0 < L := by linarith
  have hVsPos : 0 < Vs := hv.trans_le hVs
  have hBg : 0 ≤ Bg := by dsimp [Bg]; positivity
  have hGrp := hGrouped Ncap qBase S Ts Tb Vs Vsmall Vbig ts tb coef k
    primeSlot Parity alpha c lo hi chi0 sigma0 sigma1 G
    hG hParity hSPrime hTsPrime hTbPrime L aexp τ Carc den h hden
    hDenOriginal hOrigW hOrigSmall hOrigLong hRoughOriginal
    (fun p hp => (hSmall p hp).1) hSlotMin
    hk hVs hts htb hVsmall hVbig hcoef
    (L^ea) C (by positivity) hC hAlpha hcBound
  have hMoment := source_original_marked_supported_moment434
    G Parity S primeSlot Ts Tb q0 Vs Vsmall Vbig ts tb coef k qBase
    (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1 den h hden
    Ncap Y A (by linarith : 0 < Y) psi1 v1 hUpper Bpsi Bg hBpsi hBg hPsiCap hGrp
  have hMain := hOriginalL x hx hLog hL Y Hprime hY hYmax hH hYstrong
    hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
    G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
    F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
    psi1 hSmooth hSupport v1 hv1 hBudget hden
    hUpper Bpsi Bg hBpsi hBg hPsiCap hGrp
    hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin hHband hArcCap
  have hErr := mul_le_mul_of_nonneg_left hMoment
    (by positivity : 0 ≤ 4*δ*(4*δ+1)*(16*A*δ^2*M)^2*((Hprime/L^Carc)/Y)^2)
  have hTwice := mul_le_mul_of_nonneg_left hErr (by norm_num : (0:ℝ) ≤ 2)
  exact hMain.trans (add_le_add le_rfl hTwice)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalSelectedAdditive -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 14000000

/-- No auxiliary kernel assumptions: genuine compact kernels and their
positive Fourier band are selected before every arithmetic parameter.
The group constant also precedes the freely selectable decay order. -/
theorem eventually_source_original_selected_additive434
    (aexp bexp cexp Carc τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ (δ M cband : ℝ), 0 ≤ δ ∧ δ ≤ 1 ∧ 0 ≤ M ∧ 0 < cband ∧
    ∃ Kg : ℝ, 1 ≤ Kg ∧ ∀ (j : ℕ), 2 ≤ j → ∃ K : ℝ, 0 < K ∧
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (hUpper : ∀ u : ℝ, psi1 u ≠ 0 → u ≤ A) →
      ∀ (Bpsi : ℝ), 0 ≤ Bpsi →
      (∀ n ∈ Finset.Icc 1 Ncap, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi) →
      G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb) → Parity ⊆ G →
      (∀ g, ∀ p ∈ Ts g, p.Prime) → (∀ g, ∀ p ∈ Tb g, p.Prime) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L))) →
      (den:ℝ) ≤ L^Carc → L^Carc ≤ Real.exp (Real.sqrt L) →
      L^Carc < Real.exp (L^aexp) → L^Carc < Real.exp (τ*L) →
      (∀ p ∈ primeSlot, Real.exp (τ*L) ≤ (p:ℝ)) →
      1 ≤ Hprime/L^Carc → Hprime/L^Carc ≤ Y/(8*A) →
      cband^2 * (∫ beta in Set.Icc (-(1/(Hprime/L^Carc))) (1/(Hprime/L^Carc)),
        ‖sourceWeightedPeeledMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
          chi0 sigma0 sigma1 (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
          (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ))‖^2) ≤
        2*(K * (Y * ((1/Vs)^2 * (den:ℝ)^2 *
          (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹) +
          (1/Y) * ((4*((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc) + 16*(Nat.ceil (A*Y):ℝ)*
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
              ((Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1)))^2*(Nat.ceil (A*Y):ℝ)*
                (1+Real.log (Nat.ceil (A*Y):ℝ))^63)))) +
        2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*((Hprime/L^Carc)/Y)^2 *
          ((Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1)))^2*(Nat.ceil (A*Y):ℝ)*
            (1+Real.log (Nat.ceil (A*Y):ℝ))^63)) := by
  obtain ⟨chi,Kbump,Bchi,δ,M,cband,hBchi,hδ,hδ1,hM,hcband,
    hchi,hSupportK,hLipK,hLowerK,hOne⟩ := source_selected_arc_kernels434 A hA
  have hMain := eventually_source_original_additive_uniform_order434
    chi Kbump Bchi hBchi hchi
    aexp bexp cexp Carc τ η Cχ C0 q0 vmin
    tmax ea ec s0 cm D s1base vexp fcut epsi A Cpsi Kpsi
    hA hCpsi hKpsi δ M cband hδ.le hδ1 hM hcband
    hSupportK hLipK hLowerK hOne
    hepsi hFcut haexp hab hb hbc hτ hτη hη hCχ hC0 hq0 hq1 hv
  exact ⟨δ,M,cband,hδ.le,hδ1,hM,hcband,hMain⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalFullAdditive -/

section

open MeasureTheory Filter
open scoped BigOperators FourierTransform SchwartzMap ContDiff RealInnerProductSpace
namespace Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option maxHeartbeats 18000000

/-- Original FULL additive endpoint directly from source discrepancy.
All arithmetic coefficients, kernel inputs and square-error estimates
are supplied; the square volume is the true ceil(A Y), not Ncap. -/
theorem eventually_source_original_full_additive434
    (aexp bexp cexp Carc τ η Cχ C0 q0 vmin : ℝ)
    (tmax ea ec s0 cm D s1base vexp fcut epsi : ℕ)
    (A Cpsi : ℝ) (Kpsi : ℕ → ℝ)
    (hA : 1 ≤ A) (hCpsi : 0 ≤ Cpsi) (hKpsi : ∀ j, 0 ≤ Kpsi j)
    (hepsi : 3*Cpsi ≤ (epsi:ℝ)) (hFcut : Cpsi+2 < (fcut:ℝ))
    (haexp : 0 < aexp) (hab : aexp < bexp) (hb : bexp < 1)
    (hbc : bexp < cexp)
    (hτ : 0 < τ) (hτη : τ < η) (hη : η < 1/4)
    (hCχ : 0 < Cχ) (hC0 : 0 ≤ C0)
    (hq0 : 0 < q0) (hq1 : q0 < 1) (hv : 0 < vmin) :
    ∃ Ksq : ℝ, 1 ≤ Ksq ∧ ∃ (δ M cband : ℝ), 0 ≤ δ ∧ δ ≤ 1 ∧ 0 ≤ M ∧ 0 < cband ∧
    ∃ Kg : ℝ, 1 ≤ Kg ∧ ∀ (j : ℕ), 2 ≤ j → ∃ K : ℝ, 0 < K ∧
    ∃ B : ℕ, ∃ X0 : ℝ, 3 ≤ X0 ∧
      ∀ᶠ L : ℝ in atTop,
      ∀ (x : ℝ), X0 ≤ x → L = Real.log x → 3 ≤ L →
      ∀ (Y Hprime : ℝ),
      4 ≤ Y → Y ≤ Real.exp (3*L/2) → 0 < Hprime →
      Real.exp (3*L/4) ≤ Y →
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
        [Fintype β] [DecidableEq β],
      (Fintype.card ι:ℝ) ≤ C0*Real.log L →
      (Fintype.card β:ℝ) ≤ C0*Real.log L →
      ∀ (lo hi Ncap : ℕ) (alpha : ℕ → ℂ),
      (Ncap:ℝ) ≤ x^2 → A*Y ≤ (Ncap:ℝ) →
      (∀ m ∈ Finset.Icc lo hi, ‖alpha m‖ ≤ L^ea) →
      SourceAlphaDiscrepancy L (B:ℝ) x alpha →
      ∀ (G Parity S primeSlot : Finset ℕ)
        (Ts : ι → Finset ℕ) (Tb : β → Finset ℕ)
        (Vs : ℝ) (Vsmall : ι → ℝ) (Vbig : β → ℝ)
        (ts : ι → ℕ) (tb : β → ℕ)
        (coef : (∀ g : β, Fin (tb g) → ℕ) → ℂ) (k qBase den h : ℕ)
        (c : ℕ → ℂ) (chi0 : DirichletCharacter ℂ qBase),
      0 < qBase → 0 < den →
      (qBase:ℝ) ≤ L^cm → (den:ℝ) ≤ L^cm →
      (den:ℝ) ≤ L^Cχ →
      k+1 ≤ tmax → vmin ≤ Vs →
      (∀ j : ι, ts j ≤ tmax) → (∀ j : β, tb j ≤ tmax) →
      (∀ j : ι, vmin ≤ Vsmall j) → (∀ j : β, vmin ≤ Vbig j) →
      (∀ lists, ‖coef lists‖ ≤ 1) →
      ∀ (C : ℝ), 0 ≤ C → C ≤ L^ec → (∀ n, ‖c n‖ ≤ C) →
      ∀ (sigma0 sigma1 : ℝ),
      |sigma0| ≤ L^s0 → |sigma1| ≤ L^s1base →
      ∀ (W : ℝ),
      ((qBase*den:ℕ):ℝ) ≤ W →
      S ⊆ G → (∀ v ∈ S, v.Prime) →
      (∀ v ∈ S, v ≤ Ncap) →
      (∀ p ∈ primeSlot, p ≤ Ncap) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 → SourceRoughAbove m W) →
      (∀ v ∈ G, (v:ℝ) ≤ W) →
      (∀ p ∈ primeSlot, W < (p:ℝ)) →
      ∀ (I : Set ℝ),
      Set.OrdConnected I →
      (∀ s ∈ S, Real.exp (L^aexp) ≤ (s:ℝ) ∧ (s:ℝ) ≤ Real.exp (L^bexp)) →
      (∀ p, p ∈ primeSlot ↔ p.Prime ∧ (p:ℝ) ∈ I) →
      I ⊆ Set.Icc (x^τ) (x^η) →
      ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
        (F1 : Finset ι₁) (F2 : Finset ι₂)
        (p1 : ι₁ → ℕ) (p2 : ι₂ → ℕ) (U1 U2 : ℝ),
      F1.Nonempty → F2.Nonempty →
      (∀ i ∈ F1, 1 ≤ p1 i) → (∀ i ∈ F2, 1 ≤ p2 i) →
      (∀ i ∈ F1, Real.exp (L^cexp) ≤ (p1 i:ℝ)) →
      (∀ i ∈ F2, Real.exp (L^cexp) ≤ (p2 i:ℝ)) →
      0 < U1 → 0 < U2 →
      Real.log (((∏ i ∈ F1, p1 i : ℕ):ℝ)) ≤ Real.log U1+1 →
      Real.log (((∏ i ∈ F2, p2 i : ℕ):ℝ)) ≤ Real.log U2+1 →
      Hprime = U1*U2 →
      ∀ (psi1 : ℝ → ℂ),
      ContDiff ℝ ∞ psi1 →
      (∀ u : ℝ, psi1 u ≠ 0 → 1/A ≤ u ∧ u ≤ A) →
      ∀ (v1 : ℝ), |v1| ≤ L^vexp →
      sourceLogDerivativeBudget Cpsi Kpsi L (fun u => psi1 (Real.exp u)) →
      ∀ (hden : 0 < den),
      (hUpper : ∀ u : ℝ, psi1 u ≠ 0 → u ≤ A) →
      ∀ (Bpsi : ℝ), 0 ≤ Bpsi →
      (∀ n ∈ Finset.Icc 1 Ncap, ‖psi1 ((n:ℝ)/Y)‖ ≤ Bpsi) →
      G = S ∪ ((Finset.univ : Finset ι).biUnion Ts) ∪
        ((Finset.univ : Finset β).biUnion Tb) → Parity ⊆ G →
      (∀ g, ∀ p ∈ Ts g, p.Prime) → (∀ g, ∀ p ∈ Tb g, p.Prime) →
      (∀ m, sourceAlphaDyadicCut alpha lo hi m ≠ 0 →
        SourceRoughAbove m (Real.exp (Real.sqrt L))) →
      (den:ℝ) ≤ L^Carc → L^Carc ≤ Real.exp (Real.sqrt L) →
      L^Carc < Real.exp (L^aexp) → L^Carc < Real.exp (τ*L) →
      (∀ p ∈ primeSlot, Real.exp (τ*L) ≤ (p:ℝ)) →
      2 ≤ Hprime/L^Carc → Hprime/L^Carc ≤ Y/(8*A) →
      (∀ g, ∀ p ∈ S, p ∉ Ts g) → (∀ g, ∀ p ∈ S, p ∉ Tb g) →
      ∀ (Vplus : ℝ), (∑ p ∈ S, (1:ℝ)/(p:ℝ)) ≤ Vplus →
      cband^2 * (∫ beta in Set.Icc (-(1/(Hprime/L^Carc))) (1/(Hprime/L^Carc)),
        ‖sourceWeightedFullMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
          ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
          chi0 sigma0 sigma1 (fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1)
          (((h:ℝ)/(den:ℝ)+(beta:ℝ):ℝ):AddCircle (1:ℝ))‖^2) ≤
      2*(2*(K * (Y * ((1/Vs)^2 * (den:ℝ)^2 *
          (((Ncap.log2+1)^4:ℕ):ℝ)^2 * (L^D)⁻¹) +
          (1/Y) * ((4*((L^(j-2))⁻¹ *
            (L*Y/(Hprime/L^Carc) + 16*(Nat.ceil (A*Y):ℝ)*
              (1+Real.log (Nat.ceil (A*Y):ℝ))))) *
              ((Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1)))^2*(Nat.ceil (A*Y):ℝ)*
                (1+Real.log (Nat.ceil (A*Y):ℝ))^63)))) +
        2*(4*δ*(4*δ+1)*(16*A*δ^2*M)^2*((Hprime/L^Carc)/Y)^2 *
          ((Bpsi*(L^ea*C*(1/Vs)*Kg^(Fintype.card ι+Fintype.card β+1)))^2*(Nat.ceil (A*Y):ℝ)*
            (1+Real.log (Nat.ceil (A*Y):ℝ))^63))) + 2*cband^2*(Bpsi^2*Vplus*(L^ea*C*(Ksq^(Fintype.card ι+Fintype.card β+1)*L*
            (1+2/(vmin*Real.log 2))))^2*
          (Nat.ceil (A*Y):ℝ)*(1+Real.log (Nat.ceil (A*Y):ℝ))^16*
          Real.exp (-(L^aexp))) := by
  obtain ⟨Ksq,hKsq,hSquare⟩ := source_full_weighted_original_group_localized_error434
    q0 vmin tmax hq0 hq1 hv
  obtain ⟨δ,M,cband,hδ,hδ1,hM,hcband,Kg,hKg,hSelected⟩ :=
    eventually_source_original_selected_additive434
      aexp bexp cexp Carc τ η Cχ C0 q0 vmin
      tmax ea ec s0 cm D s1base vexp fcut epsi A Cpsi Kpsi
      hA hCpsi hKpsi hepsi hFcut haexp hab hb hbc hτ hτη hη
      hCχ hC0 hq0 hq1 hv
  refine ⟨Ksq,hKsq,δ,M,cband,hδ,hδ1,hM,hcband,Kg,hKg,?_⟩
  intro j hj
  obtain ⟨K,hK,B,X0,hX0,hOriginal⟩ := hSelected j hj
  refine ⟨K,hK,B,X0,hX0,?_⟩
  filter_upwards [hOriginal] with L hOriginalL
  intro x hx hLog hL Y Hprime hY hYmax hH hYstrong
  intro ι β _ _ _ _ hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
  intro G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
  intro ι₁ ι₂ _ _ F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
  intro psi1 hSmooth hSupport v1 hv1 hBudget hden
  intro hUpper Bpsi hBpsi hPsiCap
  intro hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin hHband hArcCap hDisjS hDisjB Vplus hHarmonic
  have hLp : 0 < L := by linarith
  have hYp : 0 < Y := by linarith
  have hk0 : k ≤ tmax := by omega
  have hPeeled := hOriginalL x hx hLog hL Y Hprime hY hYmax hH hYstrong
    hSmallGroups hBigGroups lo hi Ncap alpha hNcap hCap hAlpha hDisc
    G Parity S primeSlot Ts Tb Vs Vsmall Vbig ts tb coef k qBase den h c chi0
    hBase hden0 hBaseCap hDenCap hDenChar hk0 hVs hts htb hVsmall hVbig hcoef
    C hC hCBudget hcBound sigma0 sigma1 hSigma0 hSigma1 W hModW hSG hSPrime
    hSN hPN hRough hGroup hLong I hI hSmall hSlot hIBand
    F1 F2 p1 p2 U1 U2 hF1 hF2 hp1 hp2 hmin1 hmin2
    hU1 hU2 hcell1 hcell2 hHIdent
    psi1 hSmooth hSupport v1 hv1 hBudget hden
    hUpper Bpsi hBpsi hPsiCap
    hG hParity hTsPrime hTbPrime hRoughOriginal hDenOriginal
    hOrigW hOrigSmall hOrigLong hSlotMin (by linarith) hArcCap
  let Lambda : ℕ → ℂ := fun n => psi1 ((n:ℝ)/Y)*sourcePhase n v1
  have hWeight : ∀ n ∈ Finset.Icc 1 Ncap, ‖Lambda n‖ ≤ Bpsi := by
    intro n hn
    simpa only [Lambda,norm_mul,sourcePhase_norm,mul_one] using hPsiCap n hn
  have hZero := source_smooth_weight_cutoff434 Y A hYp psi1
    (fun n => sourcePhase n v1) hUpper
  have hCut : Nat.ceil (A*Y) ≤ Ncap := Nat.ceil_le.mpr hCap
  have hAY : 1 ≤ A*Y := by nlinarith
  have hNreal : (1:ℝ) ≤ Nat.ceil (A*Y) := hAY.trans (Nat.le_ceil _)
  have hNceil : 1 ≤ Nat.ceil (A*Y) := by exact_mod_cast hNreal
  have hNx : (Nat.ceil (A*Y):ℝ) ≤ x^2 :=
    (Nat.cast_le.mpr hCut).trans hNcap
  have hLogN : Real.log (Nat.ceil (A*Y):ℝ) ≤ 2*L := by
    have hh := Real.log_le_log (by linarith : (0:ℝ) < Nat.ceil (A*Y)) hNx
    simpa only [Real.log_pow,←hLog,Nat.cast_ofNat] using hh
  have hACut := source_original_alpha_cut_pointwise434 alpha lo hi (L^ea)
    (by positivity) hAlpha
  have hError := hSquare S Ts Tb Vs Vsmall Vbig ts tb coef k
    hk hVs hts htb hVsmall hVbig hcoef hSPrime hTsPrime hDisjS hTbPrime hDisjB
    Ncap (Nat.ceil (A*Y)) qBase primeSlot Parity (sourceAlphaDyadicCut alpha lo hi)
    c Lambda chi0 sigma0 sigma1 (L^ea) C Bpsi L aexp 2
    ((h:ℝ)/(den:ℝ)) (Hprime/L^Carc) Vplus
    (by positivity) hC hBpsi hACut hcBound hWeight hNceil hCut hZero
    (fun p hp => (hSmall p hp).1) hHarmonic (by linarith) (by norm_num) hLogN hHband
  let P := sourceWeightedPeeledMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
    ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
    chi0 sigma0 sigma1 Lambda
  let E := sourceWeightedFullPeelingResidualFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
    ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
    chi0 sigma0 sigma1 Lambda
  have hTriangle := source_beta_arc_add_energy_le P E ((h:ℝ)/(den:ℝ)) (Hprime/L^Carc) hHband
  have hSet : {beta : ℝ | |beta| ≤ 1/(Hprime/L^Carc)} =
      Set.Icc (-(1/(Hprime/L^Carc))) (1/(Hprime/L^Carc)) := by
    ext beta; simp only [Set.mem_setOf_eq,Set.mem_Icc,abs_le]
  rw [hSet] at hTriangle hError
  have hScaled := mul_le_mul_of_nonneg_left hTriangle (sq_nonneg cband)
  have hP2 := mul_le_mul_of_nonneg_left hPeeled (by norm_num : (0:ℝ) ≤ 2)
  have hE2 := mul_le_mul_of_nonneg_left hError (by positivity : 0 ≤ 2*cband^2)
  let Full := sourceWeightedFullMarkedFourier Ncap qBase S Ts Tb q0 Vs Vsmall Vbig
    ts tb coef k primeSlot Parity (sourceAlphaDyadicCut alpha lo hi) c
    chi0 sigma0 sigma1 Lambda
  have hFull : Full = P+E := by
    ext theta
    exact source_weighted_full_marked_fourier_eq_peeled_add_error
      Ncap qBase S Ts Tb q0 Vs Vsmall Vbig ts tb coef k primeSlot Parity
      (sourceAlphaDyadicCut alpha lo hi) c chi0 sigma0 sigma1 Lambda theta
  rw [←hFull] at hScaled
  dsimp only [Full,P,E,Lambda] at hScaled hE2
  have hReassoc (u v c : ℝ) :
      c^2*(2*u+2*v) = 2*(c^2*u)+(2*c^2)*v := by ring
  rw [hReassoc] at hScaled
  exact hScaled.trans (add_le_add hP2 hE2)
end Green64Analytic.CorrelationSquare

end

