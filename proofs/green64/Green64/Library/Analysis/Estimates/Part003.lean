module

public import Green64.Library.Weights.Part008
public import Green64.Library.Weights.Part005
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic
public import Green64.Library.Analysis.PrimeNumberTheorem.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part016
public import Mathlib
public import Green64.Library.Sieve.Foundations.ArithmeticSieve
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part007
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Green64.Library.Weights.Part004
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-!
# Analysis / Estimates / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## Standalone.LongPrimeStageB -/

section

-- Flat compilation of unchanged original theorem/proof bodies.

-- BEGIN P1P2CanonicalSource

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open ArithmeticFunction
open scoped Classical

/-- No artificial free natural cutoff in the source M2/P1/P2 bound:
use ceil(3N), and exploit the actual Chebyshev prime-power bound. -/
theorem p1p2_canonical_source_prime_bound
    (hKhale : SourceKhaleZeroFree) :
    ∃ α₀ : ℝ, 0 < α₀ ∧
      ∀ C C₅ : ℝ, 0 < C → 0 ≤ C₅ →
      ∃ L₀ : ℝ, 3 ≤ L₀ ∧
        ∀ L : ℝ, L₀ ≤ L →
          let Q : ℝ := 3*L^C
          let V : ℝ := 3*Real.exp (3*L)
          let D : ℝ := 10.5*Real.log Q +
            61.5*(Real.log V)^(2/3:ℝ) *
              (Real.log (Real.log V))^(1/3:ℝ)
          let δ : ℝ := (100*D)⁻¹
          let H : ℝ := L^C₅
          let right : ℝ := L⁻¹
          ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
            (q:ℝ) ≤ L^C →
          ∀ (η N ε t : ℝ) (j : ℕ) (I : Set ℝ),
            1 < N → N ≤ (Real.exp L)^η →
            0 < ε → ε ≤ 1/4 →
            L^(C₅+3) ≤ |t| → |t| ≤ (Real.exp L)^2 →
            2 ≤ j → Set.OrdConnected I → I ⊆ Set.Icc N (2*N) →
            let B : ℝ :=
              20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
            let R : ℝ :=
              B * Real.exp η * (8*L^2) *
                (-H^(1-(j:ℝ))/(1-(j:ℝ)))
            let M : ℝ :=
              2*H*(B*N^(-δ)*(3*50*L)) +
                2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
                  2*R
            ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
                (fun _ => Classical.propDecidable _)
                ((Finset.range (⌊2*N⌋₊+1)).filter Nat.Prime)),
                sourcePrimeTerm q χ t p‖ ≤
              (M/(2*Real.pi) +
                (2*Real.log (3*N)/N)*(2*ε*N+2) +
                (4*Real.log (4*N))/Real.sqrt N) /
                  Real.log N := by
  obtain ⟨α₀,hα,hMain⟩ := p1p2_source_actual_prime_bound hKhale
  refine ⟨α₀,hα,?_⟩
  intro C C₅ hC hC₅
  obtain ⟨L₀,hL₀,hAll⟩ := hMain C C₅ hC hC₅
  refine ⟨L₀,hL₀,?_⟩
  intro L hL Q V D δ H right q _ χ hq η N ε t j I
    hN hNmax hε hεmax htlo hthi hj hI hIS
  dsimp only
  let Knat : ℕ := ⌈3*N⌉₊
  have hK : 3*N ≤ (Knat:ℝ) := (p1_canonical_truncation N (by linarith)).1
  have hRaw := hAll L hL q χ hq η N ε t j Knat I
    hN hNmax hε hεmax htlo hthi hj hK hI hIS
  dsimp only at hRaw
  have hPow := p1_canonical_prime_power_bound N (by linarith : 1 ≤ N)
  have hden : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hnum :
      2*Real.sqrt (Knat:ℝ)*Real.log (Knat:ℝ)/N ≤
        4*Real.log (4*N)/Real.sqrt N := by
    simpa only [Knat] using hPow
  have hAdd : ∀ a b : ℝ,
      a + b + 2*Real.sqrt (Knat:ℝ)*Real.log (Knat:ℝ)/N ≤
      a + b + 4*Real.log (4*N)/Real.sqrt N := by
    intro a b
    linarith
  exact hRaw.trans <| div_le_div_of_nonneg_right
    (hAdd _ _) hden

end Green64Analytic.LongPrime

-- END P1P2CanonicalSource

-- BEGIN S1ScalePower
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem source_cutoff_epsilon_small (L A : ℝ)
    (hL : 2 ≤ L) (hA : 0 ≤ A) :
    0 < L^(-(A+5)) ∧ L^(-(A+5)) ≤ (1/4:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  constructor
  · exact Real.rpow_pos_of_pos hL0 _
  · have h1 : L^(-(A+5)) ≤ L^(-2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h2 : L^(-2:ℝ) ≤ (2:ℝ)^(-2:ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
    calc
      L^(-(A+5)) ≤ L^(-2:ℝ) := h1
      _ ≤ (2:ℝ)^(-2:ℝ) := h2
      _ = 1/4 := by norm_num

theorem source_cutoff_scale_power (j : ℕ) (L A : ℝ)
    (hL : 2 ≤ L) (hA : 0 ≤ A) :
    ((L^(-(A+5)))⁻¹)^j ≤ L^(((j:ℝ)+1)*(A+5)) := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  calc
    ((L^(-(A+5)))⁻¹)^j = (L^(A+5))^(j:ℝ) := by
      rw [Real.rpow_neg hL0]
      simp
    _ = L^((A+5)*(j:ℝ)) := by
      rw [Real.rpow_mul hL0]
    _ ≤ L^(((j:ℝ)+1)*(A+5)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by
        have hj : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
        nlinarith)

end Green64Analytic.LongPrime

-- END S1ScalePower

-- BEGIN M2SourceCutoffPower

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The source smooth cutoff constant B has only a fixed polynomial
dependence on L after the exact U1 choice ε=L^(-A-5). -/
theorem m2_actual_source_B_polynomial
    (L A : ℝ) (j : ℕ)
    (hL : 2 ≤ L) (hA : 0 ≤ A) :
    20*(8:ℝ)^j *
      ((L^(-(A+5)))⁻¹^j * sourceCutoffDerivConst j) ≤
    (20*(8:ℝ)^j*sourceCutoffDerivConst j) *
      L^(((j:ℝ)+1)*(A+5)) := by
  have hc : 0 ≤ sourceCutoffDerivConst j :=
    (by norm_num : (0:ℝ) ≤ 1).trans
      (sourceCutoffDerivConst_ge_one j)
  have hScale := source_cutoff_scale_power j L A hL hA
  have hmul := mul_le_mul_of_nonneg_left
    hScale (by positivity : 0 ≤ 20*(8:ℝ)^j*sourceCutoffDerivConst j)
  nlinarith [hmul]

end Green64Analytic.LongPrime

-- END M2SourceCutoffPower

-- BEGIN M2TailFactor

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The two actual infinite vertical tails each have the genuine
integrated power denominator 1/(j-1) ≤ 1. -/
theorem m2_actual_tail_factor_le
    (H : ℝ) (j : ℕ) (hH : 0 ≤ H) (hj : 2 ≤ j) :
    0 ≤ -H^(1-(j:ℝ))/(1-(j:ℝ)) ∧
    -H^(1-(j:ℝ))/(1-(j:ℝ)) ≤ H^(1-(j:ℝ)) := by
  have hpow : 0 ≤ H^(1-(j:ℝ)) := Real.rpow_nonneg hH _
  have hjreal : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hden : 1 ≤ (j:ℝ)-1 := by linarith
  have hdenp : 0 < (j:ℝ)-1 := by linarith
  have hform :
      -H^(1-(j:ℝ))/(1-(j:ℝ)) =
        H^(1-(j:ℝ))/((j:ℝ)-1) := by
    rw [show (1:ℝ)-(j:ℝ) = -((j:ℝ)-1) by ring]
    simp only [div_neg, neg_div, neg_neg]
  rw [hform]
  constructor
  · exact div_nonneg hpow hdenp.le
  · apply (div_le_iff₀ hdenp).mpr
    nlinarith [mul_nonneg hpow (sub_nonneg.mpr hden)]

end Green64Analytic.LongPrime

-- END M2TailFactor

-- BEGIN M2Exponent
set_option autoImplicit false
namespace Green64Analytic.LongPrime

theorem m2_decay_exponent_exists
    (A C5 : ℝ) (hA : 0 < A) (hC : A + 7 ≤ C5) :
    ∃ j : ℕ, 2 ≤ j ∧
      1 + (j+1)*(A+5) + C5*(1-j) < -A-3 ∧
      (j+1)*(A+5)+1-C5*j < -A-3 := by
  let j : ℕ := ⌈A+C5+20⌉₊+2
  have hj : A+C5+20 ≤ (j:ℝ) := by
    dsimp [j]
    have h := Nat.le_ceil (A+C5+20)
    push_cast
    linarith
  have hj₂ : 2 ≤ j := by simp [j]
  refine ⟨j,hj₂,?_,?_⟩
  · nlinarith
  · nlinarith

end Green64Analytic.LongPrime

-- END M2Exponent

-- BEGIN M2RightTailPolynomial

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Two right Mellin tails have arbitrarily strong negative log
power after the exact source cutoff and height choices. -/
theorem m2_source_right_tail_polynomial
    (L A C₅ η : ℝ) (j : ℕ)
    (hL : 2 ≤ L) (hA : 0 ≤ A) (hj : 2 ≤ j)
    (hexp : 1+((j:ℝ)+1)*(A+5)+C₅*(1-(j:ℝ)) ≤ -A-3) :
    let ε := L^(-(A+5))
    let H := L^C₅
    let c := 20*(8:ℝ)^j*sourceCutoffDerivConst j
    let B := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
    B*Real.exp η*(8*L^2)*
      (-H^(1-(j:ℝ))/(1-(j:ℝ))) ≤
      (8*Real.exp η*c)*L^(-A-2) := by
  dsimp only
  let ε : ℝ := L^(-(A+5))
  let H : ℝ := L^C₅
  let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let p : ℝ := ((j:ℝ)+1)*(A+5)
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hfac := (m2_actual_tail_factor_le H j hH hj).2
  have hB : B ≤ c*L^p := by
    simpa only [B,c,ε,p] using m2_actual_source_B_polynomial L A j hL hA
  have hconst : 0 ≤ sourceCutoffDerivConst j :=
    (by norm_num : (0:ℝ) ≤ 1).trans (sourceCutoffDerivConst_ge_one j)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hHpow : 0 ≤ H^(1-(j:ℝ)) := Real.rpow_nonneg hH _
  have hr : L^p*L^2*H^(1-(j:ℝ)) =
      L^(p+2+C₅*(1-(j:ℝ))) := by
    change L^p*L^2*(L^C₅)^(1-(j:ℝ)) =
      L^(p+2+C₅*(1-(j:ℝ)))
    rw [← Real.rpow_mul (by linarith : 0 ≤ L) C₅ (1-(j:ℝ))]
    calc
      L^p*L^2*L^(C₅*(1-(j:ℝ))) =
          L^(p+2)*L^(C₅*(1-(j:ℝ))) := by
            rw [Real.rpow_add hLp p 2] <;> simp
      _ = L^(p+2+C₅*(1-(j:ℝ))) := by
            rw [Real.rpow_add hLp (p+2) (C₅*(1-(j:ℝ)))] <;> simp
  have hE : p+2+C₅*(1-(j:ℝ)) ≤ -A-2 := by
    dsimp [p]
    linarith
  have hPow : L^(p+2+C₅*(1-(j:ℝ))) ≤ L^(-A-2) :=
    Real.rpow_le_rpow_of_exponent_le hLone hE
  calc
    B*Real.exp η*(8*L^2)*(-H^(1-(j:ℝ))/(1-(j:ℝ))) ≤
      (c*L^p)*Real.exp η*(8*L^2)*H^(1-(j:ℝ)) := by
        have hnon : 0 ≤ B*Real.exp η*(8*L^2) := by positivity
        have hle1 := mul_le_mul_of_nonneg_left hfac hnon
        have hnon2 : 0 ≤ Real.exp η*(8*L^2)*H^(1-(j:ℝ)) := by positivity
        have hle2 := mul_le_mul_of_nonneg_right hB hnon2
        nlinarith [hle1, hle2]
    _ = (8*Real.exp η*c)*L^(p+2+C₅*(1-(j:ℝ))) := by
      rw [← hr]
      ring
    _ ≤ (8*Real.exp η*c)*L^(-A-2) :=
      mul_le_mul_of_nonneg_left hPow (by positivity)

end Green64Analytic.LongPrime

-- END M2RightTailPolynomial

-- BEGIN M2HorizontalFactor

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Actual horizontal rectangle collar has sufficiently high Mellin
decay in L, not just a formal high-derivative bound. -/
theorem m2_source_horizontal_factor_polynomial
    (L A C₅ : ℝ) (j : ℕ)
    (hL : 2 ≤ L) (hA : 0 ≤ A) :
    let ε := L^(-(A+5))
    let H := L^C₅
    let c := 20*(8:ℝ)^j*sourceCutoffDerivConst j
    let B := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
    B/(1+H)^j ≤ c*L^(((j:ℝ)+1)*(A+5)-C₅*(j:ℝ)) := by
  dsimp only
  let ε : ℝ := L^(-(A+5))
  let H : ℝ := L^C₅
  let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let p : ℝ := ((j:ℝ)+1)*(A+5)
  have hLp : 0 < L := by linarith
  have hHpos : 0 < H := Real.rpow_pos_of_pos hLp _
  have hB : B ≤ c*L^p := by
    simpa only [B,c,ε,p] using m2_actual_source_B_polynomial L A j hL hA
  have hc : 0 ≤ c := by
    dsimp [c]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hP : H^j ≤ (1+H)^j := by
    gcongr
    linarith
  have hHpow : 0 < H^j := pow_pos hHpos _
  have hHplus : 0 < (1+H)^j := pow_pos (by linarith) _
  have hCompare : B/(1+H)^j ≤ (c*L^p)/H^j := by
    apply (div_le_div_iff₀ hHplus hHpow).mpr
    have h1 := mul_le_mul_of_nonneg_right hB hHpow.le
    have h2 := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ c*L^p)
    nlinarith [h1,h2]
  have hHpowId : H^j = L^(C₅*(j:ℝ)) := by
    dsimp [H]
    rw [Real.rpow_mul hLp.le C₅ (j:ℝ)]
    simp only [Real.rpow_natCast]
  have hExp : (c*L^p)/H^j =
      c*L^(p-C₅*(j:ℝ)) := by
    rw [hHpowId, Real.rpow_sub hLp]
    ring
  have htarget : p-C₅*(j:ℝ) =
      ((j:ℝ)+1)*(A+5)-C₅*(j:ℝ) := rfl
  rw [← htarget, ← hExp]
  exact hCompare

end Green64Analytic.LongPrime

-- END M2HorizontalFactor

-- BEGIN M2HorizontalPolynomial

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The true Khale two horizontal rectangle edges decay at an
arbitrarily strong fixed negative power of L. -/
theorem m2_source_horizontal_polynomial
    (L A C₅ η δ N : ℝ) (j : ℕ)
    (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1)
    (hN : 0 < N) (hNmax : N ≤ (Real.exp L)^η)
    (hexp : ((j:ℝ)+1)*(A+5)+1-C₅*(j:ℝ) ≤ -A-3) :
    let ε := L^(-(A+5))
    let H := L^C₅
    let right := L⁻¹
    let c := 20*(8:ℝ)^j*sourceCutoffDerivConst j
    let B := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
    2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) ≤
      (600*Real.exp η*c)*L^(-A-3) := by
  dsimp only
  let ε : ℝ := L^(-(A+5))
  let H : ℝ := L^C₅
  let right : ℝ := L⁻¹
  let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let e : ℝ := ((j:ℝ)+1)*(A+5)-C₅*(j:ℝ)
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hright : 0 ≤ right := by dsimp [right]; positivity
  have hright1 : right ≤ 1 := by
    dsimp [right]
    simpa only [one_div, inv_one] using
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hLone)
  have hrd : right+δ ≤ 2 := by linarith
  have hrd0 : 0 ≤ right+δ := by linarith
  have hc : 0 ≤ c := by
    dsimp [c]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hden : 0 < (1+H)^j := by positivity
  have hFactor : B/(1+H)^j ≤ c*L^e := by
    simpa only [B,H,c,ε,e] using
      m2_source_horizontal_factor_polynomial L A C₅ j hL hA
  have hFactor0 : 0 ≤ B/(1+H)^j := div_nonneg hB hden.le
  have hLpow : 0 ≤ L^e := Real.rpow_nonneg hLp.le _
  have hNpow := m2_right_shift_power_uniform L η N hLp hN hNmax
  have hNpow0 : 0 ≤ N^right := Real.rpow_nonneg hN.le _
  have hExp : 0 < Real.exp η := Real.exp_pos _
  have heq : L^e*L = L^(e+1) := by
    rw [Real.rpow_add hLp]
    simp
  have hE : e+1 ≤ -A-3 := by dsimp [e]; linarith
  have hPow : L^(e+1) ≤ L^(-A-3) :=
    Real.rpow_le_rpow_of_exponent_le hLone hE
  calc
    2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) ≤
        2*2*((B/(1+H)^j)*N^right*(3*50*L)) := by
          gcongr
    _ ≤ 2*2*((c*L^e)*Real.exp η*(3*50*L)) := by
          gcongr
    _ = (600*Real.exp η*c)*L^(e+1) := by
          rw [← heq]
          ring
    _ ≤ (600*Real.exp η*c)*L^(-A-3) :=
          mul_le_mul_of_nonneg_left hPow (by positivity)

end Green64Analytic.LongPrime

-- END M2HorizontalPolynomial

-- BEGIN M2LeftPolynomial

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Genuine shifted left-line contribution after Khale damping.
The input is the separately proved uniform N^(-δ) bound. -/
theorem m2_source_left_line_polynomial
    (L A C₅ δ N : ℝ) (j : ℕ)
    (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hN : 0 < N)
    (hDamp : N^(-δ) ≤
      2*L^(-(C₅+((j:ℝ)+1)*(A+5)+A+5))) :
    let ε := L^(-(A+5))
    let H := L^C₅
    let c := 20*(8:ℝ)^j*sourceCutoffDerivConst j
    let B := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
    2*H*(B*N^(-δ)*(3*50*L)) ≤ 600*c*L^(-A-4) := by
  dsimp only
  let ε : ℝ := L^(-(A+5))
  let H : ℝ := L^C₅
  let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let p : ℝ := ((j:ℝ)+1)*(A+5)
  let S : ℝ := C₅+p+A+5
  have hLp : 0 < L := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hB : B ≤ c*L^p := by
    simpa only [B,c,ε,p] using m2_actual_source_B_polynomial L A j hL hA
  have hDamp' : N^(-δ) ≤ 2*L^(-S) := by
    simpa only [S,p] using hDamp
  have hNpow : 0 ≤ N^(-δ) := Real.rpow_nonneg hN.le _
  have hBase : 0 ≤ B := by
    dsimp [B]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hPr : H*L^p*L^(-S)*L = L^(-A-4) := by
    change L^C₅*L^p*L^(-S)*L = L^(-A-4)
    have hExp : C₅+p-S+1 = -A-4 := by dsimp [S]; ring
    calc
      L^C₅*L^p*L^(-S)*L = L^(C₅+p)*L^(-S)*L := by
        rw [Real.rpow_add hLp C₅ p]
      _ = L^(C₅+p-S)*L := by
        rw [← Real.rpow_add hLp (C₅+p) (-S)]
        congr 1
      _ = L^(C₅+p-S+1) := by
        rw [Real.rpow_add hLp (C₅+p-S) 1]
        simp
      _ = L^(-A-4) := by rw [hExp]
  calc
    2*H*(B*N^(-δ)*(3*50*L)) ≤
        2*H*((c*L^p)*(2*L^(-S))*(3*50*L)) := by
      gcongr
    _ = 600*c*L^(-A-4) := by
      rw [← hPr]
      ring

end Green64Analytic.LongPrime

-- END M2LeftPolynomial

-- BEGIN M2AssembledLogPower

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Full quantitative M2 bound: source-shifted left line, both
horizontal edges and both infinite right-line tails, all with the
same fixed log-power saving. -/
theorem m2_source_full_log_power_estimate
    (L A C₅ η δ N : ℝ) (j : ℕ)
    (hL : 2 ≤ L) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1)
    (hN : 0 < N) (hNmax : N ≤ (Real.exp L)^η)
    (hj : 2 ≤ j)
    (hTailExp : 1+((j:ℝ)+1)*(A+5)+C₅*(1-(j:ℝ)) ≤ -A-3)
    (hHorizontalExp : ((j:ℝ)+1)*(A+5)+1-C₅*(j:ℝ) ≤ -A-3)
    (hDamp : N^(-δ) ≤
      2*L^(-(C₅+((j:ℝ)+1)*(A+5)+A+5))) :
    let ε := L^(-(A+5))
    let H := L^C₅
    let right := L⁻¹
    let c := 20*(8:ℝ)^j*sourceCutoffDerivConst j
    let B := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
    let R := B*Real.exp η*(8*L^2)*
      (-H^(1-(j:ℝ))/(1-(j:ℝ)))
    2*H*(B*N^(-δ)*(3*50*L)) +
      2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
        2*R ≤
      (600*c + 616*Real.exp η*c)*L^(-A-2) := by
  dsimp only
  let ε : ℝ := L^(-(A+5))
  let H : ℝ := L^C₅
  let right : ℝ := L⁻¹
  let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let R : ℝ := B*Real.exp η*(8*L^2)*
    (-H^(1-(j:ℝ))/(1-(j:ℝ)))
  have hleft := m2_source_left_line_polynomial
    L A C₅ δ N j hL hA hδ hN hDamp
  have hhorizontal := m2_source_horizontal_polynomial
    L A C₅ η δ N j hL hA hδ hδmax hN hNmax hHorizontalExp
  have htail := m2_source_right_tail_polynomial
    L A C₅ η j hL hA hj hTailExp
  dsimp only at hleft hhorizontal htail
  have hc : 0 ≤ c := by
    dsimp [c]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hLp : 1 ≤ L := by linarith
  have hpow1 : L^(-A-4) ≤ L^(-A-2) :=
    Real.rpow_le_rpow_of_exponent_le hLp (by linarith)
  have hpow2 : L^(-A-3) ≤ L^(-A-2) :=
    Real.rpow_le_rpow_of_exponent_le hLp (by linarith)
  have hC1 : 600*c*L^(-A-4) ≤ 600*c*L^(-A-2) :=
    mul_le_mul_of_nonneg_left hpow1 (by positivity)
  have hC2 : (600*Real.exp η*c)*L^(-A-3) ≤
      (600*Real.exp η*c)*L^(-A-2) :=
    mul_le_mul_of_nonneg_left hpow2 (by positivity)
  have hC3 := mul_le_mul_of_nonneg_left htail
    (by norm_num : (0:ℝ) ≤ 2)
  change
    2*H*(B*N^(-δ)*(3*50*L)) +
      2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
        2*R ≤
      (600*c + 616*Real.exp η*c)*L^(-A-2)
  have hall :=
    add_le_add (add_le_add (hleft.trans hC1)
      (hhorizontal.trans hC2)) hC3
  nlinarith [hall]

end Green64Analytic.LongPrime

-- END M2AssembledLogPower

-- BEGIN M2TrueSourcePolynomial

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- All three actual Khale contour contributions simultaneously have
an O(L^(-A-2)) majorant on the true short-prime source scale,
without an assumed polynomial prime estimate. -/
theorem m2_true_source_M_polynomial
    (C τ A C₅ η : ℝ) (j : ℕ)
    (hC : 0 < C) (hτ : 0 < τ) (hA : 0 ≤ A) (hC₅ : 0 ≤ C₅)
    (hj : 2 ≤ j)
    (hTailExp : 1+((j:ℝ)+1)*(A+5)+C₅*(1-(j:ℝ)) ≤ -A-3)
    (hHorizontalExp : ((j:ℝ)+1)*(A+5)+1-C₅*(j:ℝ) ≤ -A-3) :
    ∃ L₀ : ℝ, 3 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        ∀ N : ℝ, (Real.exp L)^τ/2 ≤ N →
          N ≤ (Real.exp L)^η →
        let Q : ℝ := 3*L^C
        let V : ℝ := 3*Real.exp (3*L)
        let D : ℝ := 10.5*Real.log Q +
          61.5*(Real.log V)^(2/3:ℝ) *
            (Real.log (Real.log V))^(1/3:ℝ)
        let δ : ℝ := (100*D)⁻¹
        let H : ℝ := L^C₅
        let right : ℝ := L⁻¹
        let ε : ℝ := L^(-(A+5))
        let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
        let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
        let R : ℝ := B*Real.exp η*(8*L^2)*
          (-H^(1-(j:ℝ))/(1-(j:ℝ)))
        2*H*(B*N^(-δ)*(3*50*L)) +
          2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
            2*R ≤ (600*c+616*Real.exp η*c)*L^(-A-2) := by
  let S : ℝ := C₅+((j:ℝ)+1)*(A+5)+A+5
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hS : 0 ≤ S := by dsimp [S]; nlinarith
  obtain ⟨L₀,hL₀,hDamp⟩ :=
    m2_source_damping_superpolynomial C τ S hC.le hτ hS
  refine ⟨L₀,hL₀,?_⟩
  intro L hL N hLow hHigh Q V D δ H right ε c B R
  have hL3 : 3 ≤ L := hL₀.trans hL
  have hNpos : 0 < N := by
    have hp : 0 < (Real.exp L)^τ :=
      Real.rpow_pos_of_pos (Real.exp_pos _) _
    linarith
  have hDone := g2_denominator_ge_one C L hC.le hL3
  change 1 ≤ D at hDone
  have hDpos : 0 < 100*D := by positivity
  have hδpos : 0 ≤ δ := by dsimp [δ]; positivity
  have hδmax : δ ≤ 1 := by
    dsimp [δ]
    have hh : (1:ℝ) ≤ 100*D := by nlinarith
    calc
      (100*D)⁻¹ ≤ (1:ℝ)⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hh)
      _ = 1 := by norm_num
  have hDamp' : N^(-δ) ≤
      2*L^(-(C₅+((j:ℝ)+1)*(A+5)+A+5)) := by
    have h := hDamp L hL N hLow
    simpa only [δ,S] using h
  have hCore :=
    m2_source_full_log_power_estimate L A C₅ η δ N j
      (by linarith) hA hδpos hδmax hNpos hHigh
      hj hTailExp hHorizontalExp hDamp'
  simpa only [ε,H,right,c,B,R] using hCore

end Green64Analytic.LongPrime

-- END M2TrueSourcePolynomial

-- BEGIN P1SourceLogCaps

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The logarithms in the actual collar and prime-power errors are
uniformly at most L on the source N ≤ exp(ηL), η≤1/4. -/
theorem p1_source_log_caps
    (L η N : ℝ)
    (hL : 4 ≤ L) (hη : η ≤ 1/4)
    (hN : 1 ≤ N) (hNmax : N ≤ (Real.exp L)^η) :
    Real.log (3*N) ≤ L ∧ Real.log (4*N) ≤ L := by
  have hLp : 0 < L := by linarith
  have hNp : 0 < N := by linarith
  have hlogN : Real.log N ≤ η*L := by
    have hmax := Real.log_le_log hNp hNmax
    rw [Real.log_rpow (Real.exp_pos L) η, Real.log_exp] at hmax
    exact hmax
  have hlog3 : Real.log (3:ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    norm_num at h
    exact h
  have hlog4 : Real.log (4:ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    norm_num at h
    exact h
  have hηL : η*L ≤ L/4 := by nlinarith
  constructor
  · rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0)
      (ne_of_gt hNp)]
    linarith
  · rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0)
      (ne_of_gt hNp)]
    linarith

end Green64Analytic.LongPrime

-- END P1SourceLogCaps

-- BEGIN P1DampingAllErrors

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Stronger honest powers 1/N and 1/sqrt(N) are dominated
by the source Khale damping N^(-δ) for δ≤1/100. -/
theorem p1_prime_power_collar_damping
    (N δ : ℝ) (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hδmax : δ ≤ 1/100) :
    1/N ≤ N^(-δ) ∧ 1/Real.sqrt N ≤ N^(-δ) := by
  have hNp : 0 < N := by linarith
  have h1 : N^(-1:ℝ) ≤ N^(-δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have h2 : N^(-(1/2:ℝ)) ≤ N^(-δ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  constructor
  · simpa only [Real.rpow_neg_one, one_div] using h1
  · have hsqrt : 1/Real.sqrt N = N^(-(1/2:ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hNp.le]
      simp
    rw [hsqrt]
    exact h2

end Green64Analytic.LongPrime

-- END P1DampingAllErrors

-- BEGIN P1SourceErrorsPolynomial

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Both nonanalytic P1 debts, interval collar and prime powers,
have strong logarithmic saving using the genuine Khale damping
rather than any assumed bound on the prime polynomial. -/
theorem p1_source_sharp_and_prime_power_error
    (L η N A δ : ℝ)
    (hL : 4 ≤ L) (hη : η ≤ 1/4)
    (hN : 1 ≤ N) (hNmax : N ≤ (Real.exp L)^η)
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hDamp : N^(-δ) ≤ 2*L^(-(A+5))) :
    (2*Real.log (3*N)/N)*
      (2*L^(-(A+5))*N+2) +
      (4*Real.log (4*N))/Real.sqrt N ≤
        20*L^(-A-4) := by
  have hLp : 0 < L := by linarith
  have hNp : 0 < N := by linarith
  obtain ⟨hlog3,hlog4⟩ :=
    p1_source_log_caps L η N hL hη hN hNmax
  have hlog3pos : 0 ≤ Real.log (3*N) :=
    Real.log_nonneg (by nlinarith : (1:ℝ) ≤ 3*N)
  have hlog4pos : 0 ≤ Real.log (4*N) :=
    Real.log_nonneg (by nlinarith : (1:ℝ) ≤ 4*N)
  obtain ⟨hdiv,hsqrt⟩ :=
    p1_prime_power_collar_damping N δ hN hδ hδmax
  have hInv : 1/N ≤ 2*L^(-(A+5)) := hdiv.trans hDamp
  have hRoot : 1/Real.sqrt N ≤ 2*L^(-(A+5)) :=
    hsqrt.trans hDamp
  have hε : 0 ≤ L^(-(A+5)) := Real.rpow_nonneg hLp.le _
  have hError : 0 ≤ 2*L^(-(A+5)) := by positivity
  have hpow : L^(-(A+5))*L = L^(-A-4) := by
    have hh : -(A+5)+1 = -A-4 := by ring
    rw [← hh, Real.rpow_add hLp]
    simp
  have hcollar :
      (2*Real.log (3*N)/N)*(2*L^(-(A+5))*N+2) ≤
        12*L^(-A-4) := by
    have hcollEq :
        (2*Real.log (3*N)/N)*(2*L^(-(A+5))*N+2) =
         4*L^(-(A+5))*Real.log (3*N) + 4*Real.log (3*N)/N := by
      field_simp
      ring
    rw [hcollEq]
    have hl1 : L^(-(A+5))*Real.log (3*N) ≤ L^(-A-4) := by
      calc
        _ ≤ L^(-(A+5))*L :=
          mul_le_mul_of_nonneg_left hlog3 hε
        _ = L^(-A-4) := hpow
    have hl2 : Real.log (3*N)/N ≤ 2*L^(-A-4) := by
      calc
        _ ≤ L*(1/N) := by
          have hh := mul_le_mul_of_nonneg_right hlog3
            (by positivity : 0 ≤ N⁻¹)
          simpa only [one_div, div_eq_mul_inv, one_mul] using hh
        _ ≤ L*(2*L^(-(A+5))) := by
          exact mul_le_mul_of_nonneg_left hInv (by linarith)
        _ = 2*L^(-A-4) := by rw [← hpow]; ring
    have hA1 : 4*L^(-(A+5))*Real.log (3*N) ≤ 4*L^(-A-4) := by
      calc
        _ = 4*(L^(-(A+5))*Real.log (3*N)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hl1 (by norm_num)
    have hA2 : 4*Real.log (3*N)/N ≤ 8*L^(-A-4) := by
      calc
        _ = 4*(Real.log (3*N)/N) := by ring
        _ ≤ 4*(2*L^(-A-4)) :=
          mul_le_mul_of_nonneg_left hl2 (by norm_num)
        _ = 8*L^(-A-4) := by ring
    calc
      4*L^(-(A+5))*Real.log (3*N)+4*Real.log (3*N)/N ≤
        4*L^(-A-4)+8*L^(-A-4) := add_le_add hA1 hA2
      _ = 12*L^(-A-4) := by ring
  have hpower :
      (4*Real.log (4*N))/Real.sqrt N ≤ 8*L^(-A-4) := by
    calc
      _ ≤ 4*L*(1/Real.sqrt N) := by
        have hNumer := mul_le_mul_of_nonneg_left hlog4
          (by norm_num : (0:ℝ) ≤ 4)
        have hRootPos : 0 ≤ 1/Real.sqrt N := by positivity
        have hMul := mul_le_mul_of_nonneg_right hNumer hRootPos
        simpa only [one_div, div_eq_mul_inv, one_mul] using hMul
      _ ≤ 4*L*(2*L^(-(A+5))) :=
        mul_le_mul_of_nonneg_left hRoot (by positivity)
      _ = 8*L^(-A-4) := by rw [← hpow]; ring
  linarith

end Green64Analytic.LongPrime

-- END P1SourceErrorsPolynomial

-- BEGIN P1U1NumericClosure

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Final purely quantitative part of source U1: both M2 and sharp
interval/prime-power error savings survive Mellin and P2 normalization. -/
theorem p1p2_numeric_log_power_closure
    (L A C M E : ℝ) (z : ℂ) (N : ℝ)
    (hL : 4 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hLogN : 1 ≤ Real.log N)
    (hMbound : M ≤ C*L^(-A-2))
    (hEbound : E ≤ 20*L^(-A-4))
    (hPrime : ‖z‖ ≤ (M/(2*Real.pi)+E)/Real.log N) :
    ‖z‖ ≤ (C+20)*L^(-A) := by
  have hLone : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hpi : 1 ≤ 2*Real.pi := by
    have hp := Real.pi_gt_three
    linarith
  have hpid : 0 < 2*Real.pi := by linarith
  have hMpi : M/(2*Real.pi) ≤ M := by
    apply (div_le_iff₀ hpid).mpr
    nlinarith [mul_nonneg hM (sub_nonneg.mpr hpi)]
  have hMp : 0 ≤ M/(2*Real.pi) := div_nonneg hM hpid.le
  have hSum : 0 ≤ M/(2*Real.pi)+E := by linarith
  have hlogpos : 0 < Real.log N := by linarith
  have hDiv : (M/(2*Real.pi)+E)/Real.log N ≤
      M/(2*Real.pi)+E := by
    apply (div_le_iff₀ hlogpos).mpr
    nlinarith [mul_nonneg hSum (sub_nonneg.mpr hLogN)]
  have hpowM : L^(-A-2) ≤ L^(-A) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hpowE : L^(-A-4) ≤ L^(-A) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hCpow : C*L^(-A-2) ≤ C*L^(-A) :=
    mul_le_mul_of_nonneg_left hpowM hC
  have hEpow : 20*L^(-A-4) ≤ 20*L^(-A) :=
    mul_le_mul_of_nonneg_left hpowE (by norm_num)
  calc
    ‖z‖ ≤ (M/(2*Real.pi)+E)/Real.log N := hPrime
    _ ≤ M/(2*Real.pi)+E := hDiv
    _ ≤ M+E := by linarith
    _ ≤ C*L^(-A-2)+20*L^(-A-4) :=
      add_le_add hMbound hEbound
    _ ≤ C*L^(-A)+20*L^(-A) :=
      add_le_add hCpow hEpow
    _ = (C+20)*L^(-A) := by ring

end Green64Analytic.LongPrime

-- END P1U1NumericClosure

-- BEGIN P1U1LogParameters

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open scoped Classical

/-- Source-prime upper bound after the complete verified M2 and P1/P2
parameter majorants. No prime polynomial assumption remains. -/
theorem p1p2_literal_source_log_parameters
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (L A η N δ M c t : ℝ) (I : Set ℝ)
    (hL : 4 ≤ L) (hη : η ≤ 1/4) (hA : 0 ≤ A)
    (hN : 1 ≤ N) (hNmax : N ≤ (Real.exp L)^η)
    (hLogN : 1 ≤ Real.log N)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/100)
    (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hDamp : N^(-δ) ≤ 2*L^(-(A+5)))
    (hMbound : M ≤ (600*c+616*Real.exp η*c)*L^(-A-2))
    (hPrime :
      ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
          (fun _ => Classical.propDecidable _)
          ((Finset.range (⌊2*N⌋₊+1)).filter Nat.Prime)),
          sourcePrimeTerm q χ t p‖ ≤
        (M/(2*Real.pi) +
          (2*Real.log (3*N)/N)*(2*L^(-(A+5))*N+2) +
          (4*Real.log (4*N))/Real.sqrt N)/Real.log N) :
      ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
          (fun _ => Classical.propDecidable _)
          ((Finset.range (⌊2*N⌋₊+1)).filter Nat.Prime)),
          sourcePrimeTerm q χ t p‖ ≤
        (600*c+616*Real.exp η*c+20)*L^(-A) := by
  let E : ℝ :=
    (2*Real.log (3*N)/N)*(2*L^(-(A+5))*N+2) +
       (4*Real.log (4*N))/Real.sqrt N
  have hEbound : E ≤ 20*L^(-A-4) :=
    p1_source_sharp_and_prime_power_error L η N A δ
      hL hη hN hNmax hA hδ hδmax hDamp
  have hE : 0 ≤ E := by
    dsimp [E]
    have hlo : 0 ≤ Real.log (3*N) :=
      Real.log_nonneg (by nlinarith : (1:ℝ) ≤ 3*N)
    have hhi : 0 ≤ Real.log (4*N) :=
      Real.log_nonneg (by nlinarith : (1:ℝ) ≤ 4*N)
    have hε : 0 ≤ L^(-(A+5)) := by positivity
    positivity
  have hC : 0 ≤ 600*c+616*Real.exp η*c := by positivity
  have hPrimeEq :
      ‖∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
          (fun _ => Classical.propDecidable _)
          ((Finset.range (⌊2*N⌋₊+1)).filter Nat.Prime)),
          sourcePrimeTerm q χ t p‖ ≤ (M/(2*Real.pi)+E)/Real.log N := by
    have hExpr :
        (M/(2*Real.pi)+E)/Real.log N =
        (M/(2*Real.pi) +
          (2*Real.log (3*N)/N)*(2*L^(-(A+5))*N+2) +
          (4*Real.log (4*N))/Real.sqrt N)/Real.log N := by
      dsimp [E]
      ring
    rw [hExpr]
    exact hPrime
  exact p1p2_numeric_log_power_closure
    L A (600*c+616*Real.exp η*c) M E
      (∑ p ∈ (@Finset.filter ℕ (fun p => (p:ℝ) ∈ I)
        (fun _ => Classical.propDecidable _)
        ((Finset.range (⌊2*N⌋₊+1)).filter Nat.Prime)),
        sourcePrimeTerm q χ t p)
      N hL hC hM hE hLogN hMbound hEbound hPrimeEq

end Green64Analytic.LongPrime

-- END P1U1LogParameters

-- BEGIN P1SourceLogNLower

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Uniformly positive logarithmic normalization on the actual
N≥x^τ/2 range, with a τ-dependent source threshold. -/
theorem p1_source_logN_lower
    (L τ N : ℝ) (hτ : 0 < τ)
    (hL : (1+Real.log 2)/τ ≤ L)
    (hN : (Real.exp L)^τ/2 ≤ N) :
    1 ≤ Real.log N ∧ 1 ≤ N := by
  have hparam : 1+Real.log 2 ≤ τ*L := by
    have hh := (div_le_iff₀ hτ).mp hL
    nlinarith
  have hExpeq : (Real.exp L)^τ = Real.exp (τ*L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _)]
    rw [Real.log_exp]
    congr 1
    ring
  have hBound : Real.exp (1+Real.log 2) ≤ (Real.exp L)^τ := by
    rw [hExpeq]
    exact Real.exp_le_exp.mpr hparam
  have hExp2 : Real.exp (1+Real.log 2) = 2*Real.exp 1 := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    ring
  have hNexp : Real.exp 1 ≤ N := by
    rw [hExp2] at hBound
    linarith
  constructor
  · have hh := Real.log_le_log (Real.exp_pos 1) hNexp
    simpa only [Real.log_exp] using hh
  · have hh : 1 ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    exact hh.trans hNexp

end Green64Analytic.LongPrime

-- END P1SourceLogNLower

-- BEGIN SourceLongPrimeConditional

set_option autoImplicit false
namespace Green64Analytic.LongPrime
open scoped Classical

/-- The literal, unstrengthened U1 follows from exactly the
source zero-free region. It does NOT assert that this external
zero-free region is itself proved in the present Lean development. -/
theorem sourceLongPrimeU1_of_sourceKhaleZeroFree
    (hKhale : SourceKhaleZeroFree) : SourceLongPrimeU1 := by
  unfold SourceLongPrimeU1
  dsimp only
  intro τ η C A hτ hτη hη hC hA
  let C₅ : ℝ := A+7
  have hC₅ : 0 ≤ C₅ := by dsimp [C₅]; linarith
  obtain ⟨j,hj,hTailExp,hHorizontalExp⟩ :=
    m2_decay_exponent_exists A C₅ hA
      (by dsimp [C₅]; linarith)
  obtain ⟨α₀,hα₀,hSourceAll⟩ :=
    p1p2_canonical_source_prime_bound hKhale
  obtain ⟨Lmain,hLmain,hMain⟩ :=
    hSourceAll C C₅ hC hC₅
  obtain ⟨LD,hLD,hPoly⟩ :=
    m2_true_source_M_polynomial C τ A C₅ η j
      hC hτ hA.le hC₅ hj hTailExp.le hHorizontalExp.le
  obtain ⟨LE,hLE,hErr⟩ :=
    m2_source_damping_superpolynomial
      C τ (A+5) hC.le hτ (by linarith)
  let L₀ : ℝ :=
    max 4 (max Lmain (max LD (max LE ((1+Real.log 2)/τ))))
  let B₀ : ℝ := C₅+3
  let c : ℝ := 20*(8:ℝ)^j*sourceCutoffDerivConst j
  let K : ℝ := 600*c+616*Real.exp η*c+20
  let X₀ : ℝ := Real.exp L₀
  have hL₀ : 4 ≤ L₀ := (le_max_left _ _)
  have hLmain₀ : Lmain ≤ L₀ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hLD₀ : LD ≤ L₀ :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hLE₀ : LE ≤ L₀ :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
  have hlog₂₀ : (1+Real.log 2)/τ ≤ L₀ :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
  have hB₀ : 0 < B₀ := by dsimp [B₀,C₅]; linarith
  have hc : 0 < c := by
    dsimp [c]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hK : 0 < K := by
    dsimp [K]
    have hh : 0 < Real.exp η := Real.exp_pos _
    nlinarith
  have hX₀ : 3 ≤ X₀ := by
    dsimp [X₀]
    have hE : (3:ℝ) ≤ Real.exp 4 := by
      have hh := Real.add_one_le_exp (4:ℝ)
      linarith
    exact hE.trans (Real.exp_le_exp.mpr hL₀)
  refine ⟨B₀,K,X₀,hB₀,hK,hX₀,?_⟩
  intro x hx N hNlo hNhi q hq hqmax χ I hI hIS t htlo hthi
  let L : ℝ := Real.log x
  have hX : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hexp : Real.exp L = x := Real.exp_log hX
  have hL : L₀ ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos L₀) hx
    simpa only [X₀, L, Real.log_exp] using hh
  have h4 : 4 ≤ L := hL₀.trans hL
  have hLm : Lmain ≤ L := hLmain₀.trans hL
  have hLd : LD ≤ L := hLD₀.trans hL
  have hLe : LE ≤ L := hLE₀.trans hL
  have hLl : (1+Real.log 2)/τ ≤ L := hlog₂₀.trans hL
  have hNlo' : (Real.exp L)^τ/2 ≤ N := by
    simpa only [hexp] using hNlo
  have hNhi' : N ≤ (Real.exp L)^η := by
    simpa only [hexp] using hNhi
  obtain ⟨hlogN,hNone⟩ :=
    p1_source_logN_lower L τ N hτ hLl hNlo'
  have hNgt : 1 < N := by
    have he : (1:ℝ) < Real.exp 1 := by
      have hh := Real.add_one_le_exp (1:ℝ)
      linarith
    have hh := Real.exp_le_exp.mpr (by norm_num : (0:ℝ) ≤ 1)
    have hln := Real.exp_le_exp.mpr hlogN
    have hp : Real.exp 1 ≤ N := by
      have hpos : 0 < N := by linarith
      have heq : Real.exp (Real.log N) = N := Real.exp_log hpos
      rw [heq] at hln
      exact hln
    exact he.trans_le hp
  let Q : ℝ := 3*L^C
  let V : ℝ := 3*Real.exp (3*L)
  let D : ℝ := 10.5*Real.log Q +
    61.5*(Real.log V)^(2/3:ℝ) *
      (Real.log (Real.log V))^(1/3:ℝ)
  let δ : ℝ := (100*D)⁻¹
  let H : ℝ := L^C₅
  let right : ℝ := L⁻¹
  let ε : ℝ := L^(-(A+5))
  let B : ℝ := 20*(8:ℝ)^j*(ε⁻¹^j*sourceCutoffDerivConst j)
  let R : ℝ := B*Real.exp η*(8*L^2)*
    (-H^(1-(j:ℝ))/(1-(j:ℝ)))
  let M : ℝ :=
    2*H*(B*N^(-δ)*(3*50*L)) +
      2*(right+δ)*((B/(1+H)^j)*N^right*(3*50*L)) +
        2*R
  have hε : 0 < ε ∧ ε ≤ 1/4 := by
    dsimp [ε]
    exact source_cutoff_epsilon_small L A (by linarith) hA.le
  have hqt : (q:ℝ) ≤ L^C := by
    simpa only [L] using hqmax
  have htlower : L^(C₅+3) ≤ |t| := by
    simpa only [B₀] using htlo
  have htupper : |t| ≤ (Real.exp L)^2 := by
    simpa only [hexp] using hthi
  letI : NeZero q := ⟨by omega⟩
  have hActual := hMain L hLm q χ hqt η N ε t j I
    hNgt hNhi' hε.1 hε.2 htlower htupper hj hI hIS
  have hMbound :
      M ≤ (600*c+616*Real.exp η*c)*L^(-A-2) := by
    have hh := hPoly L hLd N hNlo' hNhi'
    simpa only [M,R,B,ε,right,H,δ,D,V,Q,c] using hh
  have hErrDamp : N^(-δ) ≤ 2*L^(-(A+5)) := by
    have hh := hErr L hLe N hNlo'
    simpa only [δ,D,V,Q] using hh
  have hDone := g2_denominator_ge_one C L hC.le (by linarith : 3 ≤ L)
  change 1 ≤ D at hDone
  have hDpos : 0 < D := by linarith
  have hδpos : 0 ≤ δ := by dsimp [δ]; positivity
  have hδmax : δ ≤ 1/100 := by
    dsimp [δ]
    have hh : (0:ℝ) < 100*D := by positivity
    have h1 : (100:ℝ) ≤ 100*D := by linarith
    have hInv : (100*D)⁻¹ ≤ (100:ℝ)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 100) h1)
    simpa using hInv
  have hHpos : 0 ≤ H := by dsimp [H]; positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hconst := sourceCutoffDerivConst_ge_one j
    positivity
  have hR0 : 0 ≤ R := by
    have hTail := (m2_actual_tail_factor_le H j hHpos hj).1
    dsimp [R]
    positivity
  have hRight : 0 ≤ right := by dsimp [right]; positivity
  have hM0 : 0 ≤ M := by
    dsimp [M]
    have hNpos : 0 < N := by linarith
    positivity
  have hActualBound := p1p2_literal_source_log_parameters
    q χ L A η N δ M c t I
    h4 hη.le hA.le hNone hNhi' hlogN
    hδpos hδmax hc.le hM0 hErrDamp hMbound
    (by simpa only [M,R,B,ε,right,H,δ,D,V,Q] using hActual)
  have hPow : K*L^(-A) = K/L^A := by
    rw [Real.rpow_neg (by linarith : 0 ≤ L)]
    ring
  rw [← hPow]
  simpa only [K,c,L,sourcePrimeTerm] using hActualBound

end Green64Analytic.LongPrime

-- END SourceLongPrimeConditional

-- BEGIN KhaleSourceStatement

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Direct transcription of Khale (2022), Theorem 1.1 (1.2).
The imported paper's statement, not a formal Lean proof of that paper. -/
noncomputable def KhalePublished11 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ t : ℝ),
    3 ≤ q → 10 ≤ |t| →
    1 - (10.5*Real.log (q:ℝ) +
      61.5*(Real.log |t|)^(2/3:ℝ) *
        (Real.log (Real.log |t|))^(1/3:ℝ))⁻¹ ≤ σ →
    DirichletCharacter.LFunction χ
      ((σ:ℂ) + (t:ℂ)*Complex.I) ≠ 0

/-- The source paper's real-coordinate statement implies precisely
the premise of the kernel-checked M2 and literal U1 reductions. -/
theorem sourceKhaleZeroFree_of_published11
    (h : KhalePublished11) : SourceKhaleZeroFree := by
  unfold SourceKhaleZeroFree
  dsimp only
  intro q _ χ s hq ht hs
  have hshape : s = ((s.re:ℂ) + (s.im:ℂ)*Complex.I) := by
    apply Complex.ext
    · simp
    · simp
  have hSource := h q χ s.re s.im hq ht
  have hRegion :
      1 - (10.5*Real.log (q:ℝ) +
        61.5*(Real.log |s.im|)^(2/3:ℝ) *
          (Real.log (Real.log |s.im|))^(1/3:ℝ))⁻¹ ≤ s.re := hs
  exact hshape ▸ hSource hRegion

/-- Converse audit: there is no covert strengthening in the source
zero-free region assumption used by the Lean chain. -/
theorem published11_of_sourceKhaleZeroFree
    (h : SourceKhaleZeroFree) : KhalePublished11 := by
  intro q _ χ σ t hq ht hs
  unfold SourceKhaleZeroFree at h
  dsimp only at h
  have hVal := h q χ
    ((σ:ℂ)+(t:ℂ)*Complex.I) hq
  have him : (((σ:ℂ)+(t:ℂ)*Complex.I)).im = t := by simp
  have hre : (((σ:ℂ)+(t:ℂ)*Complex.I)).re = σ := by simp
  exact hVal (by simpa only [him] using ht)
    (by simpa only [him, hre] using hs)

theorem sourceKhaleZeroFree_iff_published11 :
    SourceKhaleZeroFree ↔ KhalePublished11 :=
  ⟨published11_of_sourceKhaleZeroFree,
   sourceKhaleZeroFree_of_published11⟩

end Green64Analytic.LongPrime

-- END KhaleSourceStatement

-- BEGIN KhaleAllModuliLift

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The published q≥3 region implies an all-modulus region of the
same width after replacing q by 3q. This is the actual mechanism in
LongPrimeAnalyticReduction; no separate zeta theorem is required. -/
theorem khale_lift_nonzero_every_modulus
    (h : KhalePublished11)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (ht : 10 ≤ |s.im|)
    (hs : 1-(10.5*Real.log (3*(q:ℝ))+
      61.5*(Real.log |s.im|)^(2/3:ℝ)*
        (Real.log (Real.log |s.im|))^(1/3:ℝ))⁻¹ ≤ s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hKh := sourceKhaleZeroFree_of_published11 h
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  letI : NeZero (3*q) := ⟨by omega⟩
  have hlarge : 3 ≤ 3*q := by omega
  have hdiv : q ∣ 3*q := dvd_mul_left q 3
  have hpole : s ≠ 1 := by
    intro e
    norm_num [e] at ht
  have hregion : 1-(10.5*Real.log ((3*q:ℕ):ℝ)+
      61.5*(Real.log |s.im|)^(2/3:ℝ)*
        (Real.log (Real.log |s.im|))^(1/3:ℝ))⁻¹ ≤ s.re := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
  have hz := hKh (3*q) (DirichletCharacter.changeLevel hdiv χ)
    s hlarge ht hregion
  rw [DirichletCharacter.LFunction_changeLevel hdiv χ
    (Or.inr hpole)] at hz
  exact (mul_ne_zero_iff.mp hz).1

/-- Direct formal bridge from the exact external-source theorem to
the exact, unchanged Lean U1; not an independent proof of Khale 1.1. -/
theorem sourceLongPrimeU1_of_published_Khale11
    (h : KhalePublished11) : SourceLongPrimeU1 :=
  sourceLongPrimeU1_of_sourceKhaleZeroFree
    (sourceKhaleZeroFree_of_published11 h)

end Green64Analytic.LongPrime

-- END KhaleAllModuliLift

-- BEGIN KhaleFidelityAudit

set_option autoImplicit false



-- END KhaleFidelityAudit

-- BEGIN KhaleFromSevenEighths

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The q≥3, |t|≥10 denominator from the published Khale theorem
is strictly greater than 8. -/
theorem khale_denominator_gt_eight
    (q : ℕ) (hq : 3 ≤ q) (t : ℝ) (ht : 10 ≤ |t|) :
    8 < 10.5*Real.log (q:ℝ) +
      61.5*(Real.log |t|)^(2/3:ℝ) *
        (Real.log (Real.log |t|))^(1/3:ℝ) := by
  have hqreal : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqpos : 0 < (q:ℝ) := by linarith
  have he3 : Real.exp 1 < (3:ℝ) :=
    Real.exp_one_lt_d9.trans_le (by norm_num)
  have hqt : Real.exp 1 < (q:ℝ) := he3.trans_le hqreal
  have hqlog : 1 < Real.log (q:ℝ) := by
    have hh := Real.log_lt_log (Real.exp_pos 1) hqt
    simpa only [Real.log_exp] using hh
  have htab : Real.exp 1 < |t| := by
    linarith [Real.exp_one_lt_d9]
  have htlog : 1 < Real.log |t| := by
    have hh := Real.log_lt_log (Real.exp_pos 1) htab
    simpa only [Real.log_exp] using hh
  have hloglog : 0 ≤ Real.log (Real.log |t|) :=
    Real.log_nonneg htlog.le
  have ht1 : 0 ≤ (Real.log |t|)^(2/3:ℝ) :=
    Real.rpow_nonneg (by linarith) _
  have ht2 : 0 ≤ (Real.log (Real.log |t|))^(1/3:ℝ) :=
    Real.rpow_nonneg hloglog _
  have hsecond :
      0 ≤ 61.5*(Real.log |t|)^(2/3:ℝ) *
        (Real.log (Real.log |t|))^(1/3:ℝ) := by positivity
  linarith

/-- A hypothetical kernel-checked uniform 7/8 half-plane theorem
implies the exact published Khale-width nonvanishing region. -/
theorem sourceKhaleZeroFree_of_seven_eighths
    (h7 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℂ), (7/8:ℝ) < s.re →
      ¬ (χ = 1 ∧ s = 1) →
      DirichletCharacter.LFunction χ s ≠ 0) :
    SourceKhaleZeroFree := by
  unfold SourceKhaleZeroFree
  dsimp only
  intro q _ χ s hq ht hs
  let D : ℝ := 10.5*Real.log (q:ℝ) +
    61.5*(Real.log |s.im|)^(2/3:ℝ) *
      (Real.log (Real.log |s.im|))^(1/3:ℝ)
  have hD : 8 < D :=
    khale_denominator_gt_eight q hq s.im ht
  have hDpos : 0 < D := by linarith
  have hInv : D⁻¹ < (1/8:ℝ) := by
    apply (lt_div_iff₀ (by norm_num : (0:ℝ) < 8)).mpr
    have hEq : D⁻¹ * 8 = 8 / D := by ring
    rw [hEq]
    have hOne : (8:ℝ)/D < 1 :=
      (div_lt_iff₀ hDpos).mpr (by linarith)
    exact hOne
  have hRe : (7/8:ℝ) < s.re := by
    have hh : 1-D⁻¹ ≤ s.re := hs
    linarith
  have hpole : ¬ (χ = 1 ∧ s = 1) := by
    rintro ⟨_,hsone⟩
    norm_num [hsone] at ht
  exact h7 q χ s hRe hpole

theorem sourceLongPrimeU1_of_seven_eighths
    (h7 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℂ), (7/8:ℝ) < s.re →
      ¬ (χ = 1 ∧ s = 1) →
      DirichletCharacter.LFunction χ s ≠ 0) :
    SourceLongPrimeU1 :=
  sourceLongPrimeU1_of_sourceKhaleZeroFree
    (sourceKhaleZeroFree_of_seven_eighths h7)

end Green64Analytic.LongPrime

-- END KhaleFromSevenEighths

-- BEGIN OAISevenEighthsContract

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The exact source type of
OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
in openai/math@adc7f1241b42, expressed as a closed proposition.
No axiom is added, nor is the upstream v4.34 proof imported. -/
noncomputable def OAISevenEighthsContract : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    (7 / 8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) →
    DirichletCharacter.LFunction χ s ≠ 0

/-- The exact OAI 7/8 interface implies precisely the unchanged original U1.
This theorem is a kernel-checked *conditional* interface theorem. -/
theorem sourceLongPrimeU1_of_OAI_seven_eighths_contract
    (hOAI : OAISevenEighthsContract) : SourceLongPrimeU1 := by
  apply sourceLongPrimeU1_of_seven_eighths
  intro q _ χ s hre hpole
  exact hOAI χ hre hpole

/-- An independent match of that precise imported-theorem signature to the
Khale paper's original explicit formula, with no strengthening of q or t. -/
theorem khalePublished11_of_OAI_seven_eighths_contract
    (hOAI : OAISevenEighthsContract) : KhalePublished11 :=
  published11_of_sourceKhaleZeroFree
    (sourceKhaleZeroFree_of_seven_eighths
      (fun q _ χ s hre hpole => hOAI χ hre hpole))

end Green64Analytic.LongPrime

-- END OAISevenEighthsContract

-- BEGIN KhaleSmallModuli

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Modulus one has exactly the trivial Dirichlet character. -/
theorem khale_mod_one_character_trivial (χ : DirichletCharacter ℂ 1) :
    χ = 1 := DirichletCharacter.level_one χ

/-- Modulus two also has exactly the trivial Dirichlet character. -/
theorem khale_mod_two_character_trivial (χ : DirichletCharacter ℂ 2) :
    χ = 1 := by
  apply (DirichletCharacter.toUnitHom_inj χ 1).mp
  ext u
  have hu : u = 1 := Subsingleton.elim u 1
  subst u
  simp

end Green64Analytic.LongPrime

-- END KhaleSmallModuli

-- BEGIN KhaleSmallModuliLFunctions

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The exact small-modulus Dirichlet L-functions reduce to zeta. -/
theorem khale_small_modulus_Lfunctions (s : ℂ) (hs : s ≠ 1) :
    (∀ χ : DirichletCharacter ℂ 1,
        DirichletCharacter.LFunction χ s = riemannZeta s) ∧
    (∀ χ : DirichletCharacter ℂ 2,
        DirichletCharacter.LFunction χ s =
          (1-(2:ℂ)^(-s))*riemannZeta s) := by
  constructor
  · intro χ
    exact congrFun (DirichletCharacter.LFunction_modOne_eq (χ := χ)) s
  · intro χ
    rw [khale_mod_two_character_trivial χ]
    have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
      (N := 2) hs
    norm_num [Nat.primeFactors] at h ⊢
    exact h

end Green64Analytic.LongPrime

-- END KhaleSmallModuliLFunctions

-- BEGIN KhaleSmallModuliNonzero

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- The Euler factor distinguishing modulus two from zeta cannot vanish
in the positive half-plane. The remaining issue is the zeta zero-free region. -/
theorem khale_mod_two_euler_factor_ne_zero (s : ℂ) (hs : 0 < s.re) :
    1-(2:ℂ)^(-s) ≠ 0 := by
  have hn : ‖(2:ℂ)^(-s)‖ < 1 := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by simp; linarith)
  intro h
  have hEq : (2:ℂ)^(-s) = 1 := sub_eq_zero.mp h |>.symm
  rw [hEq, norm_one] at hn
  norm_num at hn

end Green64Analytic.LongPrime

-- END KhaleSmallModuliNonzero

-- BEGIN KhaleSmallModuliFromZeta

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Both small-modulus cases follow from zeta nonvanishing in the relevant
point, using the genuinely nonzero modulus-two Euler factor. -/
theorem khale_small_moduli_nonzero_of_zeta
    (s : ℂ) (hs : s ≠ 1) (hRe : 0 < s.re)
    (hz : riemannZeta s ≠ 0) :
    (∀ χ : DirichletCharacter ℂ 1,
      DirichletCharacter.LFunction χ s ≠ 0) ∧
    (∀ χ : DirichletCharacter ℂ 2,
      DirichletCharacter.LFunction χ s ≠ 0) := by
  obtain ⟨hOne,hTwo⟩ := khale_small_modulus_Lfunctions s hs
  constructor
  · intro χ
    rw [hOne χ]
    exact hz
  · intro χ
    rw [hTwo χ]
    exact mul_ne_zero (khale_mod_two_euler_factor_ne_zero s hRe) hz

end Green64Analytic.LongPrime

-- END KhaleSmallModuliFromZeta

-- BEGIN LongPrimeFinalAudit

set_option autoImplicit false



-- END LongPrimeFinalAudit

end

/-! ## Standalone.SourceLongPrimeUnconditional -/

section

set_option autoImplicit false
namespace Green64Analytic.LongPrime

/-- Unconditional literal long-prime U1 via the verified OAI Dirichlet 7/8
statement. This exact source still requires the full OAI module to be built
in this same Lean 4.34.1 environment before it is a kernel receipt. -/
theorem sourceLongPrimeU1_unconditional : SourceLongPrimeU1 := by
  apply sourceLongPrimeU1_of_OAI_seven_eighths_contract
  intro q _ χ s hs hpole
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    χ hs hpole
end Green64Analytic.LongPrime

end

/-! ## SmallBDepth -/

section

set_option maxHeartbeats 300000
open scoped BigOperators
namespace Green64Analytic.SmallB

/-- Source truncation depth h(b)=2*floor(1/(40b)), unchanged. -/
noncomputable def sourceDepth (b : ℝ) : ℕ :=
  2 * Nat.floor (1 / (40*b))

theorem sourceDepth_floor_bounds (q : ℝ) (hq : (5:ℝ)/2 ≤ q) :
    4 ≤ 2 * Nat.floor q ∧
    Even (2 * Nat.floor q) ∧
    2*(q-1) < (2 * Nat.floor q : ℝ) ∧
    (2 * Nat.floor q : ℝ) ≤ 2*q := by
  have hnon : 0 ≤ q := by linarith
  have hfl : (Nat.floor q : ℝ) ≤ q := Nat.floor_le hnon
  have hfu : q < (Nat.floor q : ℝ) + 1 := Nat.lt_floor_add_one q
  have h2 : 2 ≤ Nat.floor q := by
    apply (Nat.le_floor_iff hnon).2
    norm_num at hq ⊢
    linarith
  refine ⟨by omega, ⟨Nat.floor q, by omega⟩, ?_, ?_⟩
  · linarith
  · linarith

theorem sourceDepth_budget (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100) :
    let h := sourceDepth b
    4 ≤ h ∧ Even h ∧
      (1/(40*b)) ≤ (h:ℝ) ∧
      b*(4*(h:ℝ)+2) ≤ 11/50 := by
  let q : ℝ := 1/(40*b)
  have hden : 0 < 40*b := mul_pos (by norm_num) hb
  have hq : (5:ℝ)/2 ≤ q := by
    dsimp [q]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hqb := sourceDepth_floor_bounds q hq
  have hqbound : b*q = 1/40 := by
    dsimp [q]
    field_simp
  have hsm : (1:ℝ)/(40*b) ≤ (sourceDepth b : ℝ) := by
    have hx : q ≤ (2*(Nat.floor q):ℝ) := by
      have hs : (2:ℝ) ≤ q := by linarith
      linarith [hqb.2.2.1]
    simpa only [sourceDepth, q, Nat.cast_mul, Nat.cast_ofNat] using hx
  have hmax : (sourceDepth b : ℝ) ≤ 2*q := by
    simpa only [sourceDepth, Nat.cast_mul, Nat.cast_ofNat] using hqb.2.2.2
  dsimp only
  refine ⟨by simpa only [sourceDepth] using hqb.1,
          by simpa only [sourceDepth] using hqb.2.1,
          hsm, ?_⟩
  have hnon : 0 ≤ b := hb.le
  calc
    b*(4*(sourceDepth b : ℝ)+2) ≤ b*(4*(2*q)+2) := by
      apply mul_le_mul_of_nonneg_left _ hnon
      linarith
    _ = 1/5+2*b := by
      nlinarith [hqbound]
    _ ≤ (11:ℝ)/50 := by nlinarith

end Green64Analytic.SmallB

end

/-! ## SmallBActualSieve -/

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Green64Analytic.SmallB

/-- Exact finite prime alphabet of the source weighted block sieve. -/
noncomputable def roughAlphabet (z : ℝ) : Finset ℕ :=
  (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime

noncomputable def roughEuler (z : ℝ) : ℝ :=
  ∏ p ∈ roughAlphabet z, (1 - (p:ℝ)⁻¹)

/-- Counts all integers in (0,x] free of prime divisors <= x^b.
The harmless mod-1 predicate is kept for definitional replay of
the original finite-AP sieve. -/
noncomputable def roughCount (b x : ℝ) : ℝ :=
  (((Finset.Ioc (⌊(0:ℝ)⌋₊) (⌊x⌋₊)).filter
    (fun n => Nat.ModEq 1 n 0 ∧
       ∀ p ∈ roughAlphabet (x^b), ¬p ∣ n)).card : ℝ)

noncomputable def sieveK : ℝ :=
  (Real.exp (Real.exp 1 * 4) / (1-Real.exp (-1))) /
   Real.exp (-4/(1/2:ℝ))

noncomputable def sieveC : ℝ := sieveK*Real.exp sieveK

theorem sieveK_pos : 0 < sieveK := by
  unfold sieveK
  have h : 0 < 1-Real.exp (-1) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (by norm_num))
  positivity

theorem sieveC_pos : 0 < sieveC := by
  exact mul_pos sieveK_pos (Real.exp_pos _)

theorem roughAlphabet_prime_le (z : ℝ) (hz : 0 ≤ z) (p : ℕ)
    (hp : p ∈ roughAlphabet z) :
    Nat.Prime p ∧ (p:ℝ) ≤ z := by
  have hp' : p ∈ Finset.range (⌊z⌋₊+1) ∧ Nat.Prime p := by
    simpa only [roughAlphabet, Finset.mem_filter] using hp
  have hp_le : p ≤ ⌊z⌋₊ := by
    have hmem := Finset.mem_range.mp hp'.1
    omega
  have hc : (p:ℝ) ≤ (⌊z⌋₊:ℝ) := by exact_mod_cast hp_le
  exact ⟨hp'.2, hc.trans (Nat.floor_le hz)⟩

/-- Exact nonnegative rough-count estimate from the full, unchanged
source theorem `finite_prime_sieve`; no candidate claim premise. -/
theorem actual_rough_sieve_abs (b x : ℝ)
    (hb : 0 < b) (hsmall : b ≤ 1/100) (hx : 1 < x) :
    |roughCount b x - x*roughEuler (x^b)| ≤
      x*roughEuler (x^b)*sieveC*Real.exp (-(sourceDepth b:ℝ)) +
        2*(x^b)^(4*(sourceDepth b:ℝ)+2) := by
  have hz : 1 < x^b := Real.one_lt_rpow hx hb
  have hbud := sourceDepth_budget b hb hsmall
  have hraw :=
    Green64Analytic.SieveContinuation.finite_prime_sieve
      (sourceDepth b) (roughAlphabet (x^b)) (x^b)
      0 x 1 0 hz (by omega : 2 ≤ sourceDepth b)
      hbud.2.1 (by norm_num : (0:ℝ) ≤ 0) (by linarith : (0:ℝ) ≤ x)
      (by norm_num : 0 < (1:ℕ))
      (fun p hp => roughAlphabet_prime_le (x^b) (le_trans (by norm_num) hz.le) p hp)
      (fun p hp => by simp)
  simpa only [roughCount, roughEuler, sieveK, sieveC,
    Nat.floor_zero, Nat.cast_one, sub_zero, div_one,
    one_mul, Nat.zero_eq, zero_add] using hraw

theorem actual_rough_sieve_upper (b x : ℝ)
    (hb : 0 < b) (hsmall : b ≤ 1/100) (hx : 1 < x) :
    roughCount b x ≤
      x * roughEuler (x^b) *
        (1+sieveC*Real.exp (-(sourceDepth b:ℝ))) +
        2*(x^b)^(4*(sourceDepth b:ℝ)+2) := by
  have habs := actual_rough_sieve_abs b x hb hsmall hx
  have hu := (le_abs_self (roughCount b x - x*roughEuler (x^b))).trans habs
  calc
    roughCount b x ≤ x*roughEuler (x^b) +
      (x*roughEuler (x^b)*sieveC*Real.exp (-(sourceDepth b:ℝ)) +
        2*(x^b)^(4*(sourceDepth b:ℝ)+2)) := by linarith only [hu]
    _ = _ := by ring

end Green64Analytic.SmallB

end

/-! ## SmallBTail -/

section

set_option maxHeartbeats 700000
open Filter Topology Real
namespace Green64Analytic.SmallB

theorem source_error_exponent_pos (b : ℝ) (hb : 0 < b)
    (hsmall : b ≤ 1/100) :
    0 < 1 - b * (4 * (sourceDepth b : ℝ) + 2) := by
  have h := (sourceDepth_budget b hb hsmall).2.2.2
  linarith

theorem log_div_power_tendsto_zero (r : ℝ) (hr : 0 < r) :
    Tendsto (fun x : ℝ => Real.log x / x ^ r) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero

/-- Exact source divisor level vanishes after normalization,
so it costs no asymptotic room when b is fixed before x. -/
theorem source_sieve_remainder_tendsto_zero
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100) :
    Tendsto (fun x : ℝ =>
      2 * Real.log x * ((x ^ b) ^ (4*(sourceDepth b:ℝ)+2)) / x)
      atTop (𝓝 0) := by
  let e : ℝ := b*(4*(sourceDepth b:ℝ)+2)
  have he : 0 < 1-e := source_error_exponent_pos b hb hsmall
  have hlog := log_div_power_tendsto_zero (1-e) he
  have heq : (fun x : ℝ =>
      2 * Real.log x * ((x ^ b) ^ (4*(sourceDepth b:ℝ)+2)) / x) =ᶠ[atTop]
      (fun x : ℝ => 2 * (Real.log x / x ^ (1-e))) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hk : (x ^ b) ^ (4*(sourceDepth b:ℝ)+2) / x =
        (x ^ (1-e))⁻¹ := by
      have hh : (x ^ b) ^ (4*(sourceDepth b:ℝ)+2) / x = x ^ (e-1) := by
        rw [← Real.rpow_mul hx.le]
        dsimp [e]
        rw [Real.rpow_sub hx, Real.rpow_one]
      rw [hh, show e-1 = -(1-e) by ring, Real.rpow_neg hx.le]
    calc
      _ = 2 * Real.log x *
          ((x ^ b) ^ (4*(sourceDepth b:ℝ)+2) / x) := by ring
      _ = 2 * Real.log x * (x ^ (1-e))⁻¹ := by rw [hk]
      _ = 2 * (Real.log x / x^(1-e)) := by ring
  have hlim : Tendsto (fun x : ℝ => 2 * (Real.log x / x ^ (1-e)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hlog)
  exact hlim.congr' heq.symm

end Green64Analytic.SmallB

end

/-! ## SmallBLimitBridge -/

section

set_option maxHeartbeats 700000
open Filter Topology Real
namespace Green64Analytic.SmallB

/-- No liminf oracle: its exact eventual lower-approximation property
is combined with an independently convergent upper majorant. -/
theorem eventual_liminf_le_of_majorant
    (f g : ℝ → ℝ) (A B : ℝ)
    (hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, A ≤ f x + ε)
    (hMajor : ∀ᶠ x in atTop, f x ≤ g x)
    (hTend : Tendsto g atTop (𝓝 B)) :
    A ≤ B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hB : B < B+ε/2 := by linarith
  have hevent : ∀ᶠ x in atTop, g x < B+ε/2 :=
    hTend.eventually (isOpen_Iio.mem_nhds hB)
  obtain ⟨x,hx⟩ := ((hLower (ε/2) hε2).and (hMajor.and hevent)).exists
  rcases hx with ⟨hlo, hmaj, hhi⟩
  linarith

/-- Abstract exact result for sieve-like normalized inputs. -/
theorem small_b_majorant_from_limits
    (b m K : ℝ) (hb : 0 < b) (hm : 0 ≤ m) (hK : 0 ≤ K)
    (hsmall : b ≤ 1/100)
    (R V : ℝ → ℝ) (D : ℝ)
    (hMertens : Tendsto (fun x : ℝ => (Real.log x) * V x)
      atTop (𝓝 (m/b)))
    (hRoughLower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop, D ≤ (Real.log x)*R x/x + ε)
    (hSieve : ∀ᶠ x : ℝ in atTop,
      R x ≤ x * V x * (1+K*Real.exp (-(sourceDepth b : ℝ))) +
        2*((x^b)^(4*(sourceDepth b:ℝ)+2))) :
    D ≤ (m/b)*(1+K*Real.exp (-(sourceDepth b:ℝ))) := by
  have _ := hm
  have _ := hK
  let C : ℝ := 1+K*Real.exp (-(sourceDepth b:ℝ))
  let f : ℝ → ℝ := fun x => (Real.log x)*R x/x
  let g : ℝ → ℝ := fun x => (Real.log x)*V x*C +
    2*Real.log x*((x^b)^(4*(sourceDepth b:ℝ)+2))/x
  have hcomp : ∀ᶠ x : ℝ in atTop, f x ≤ g x := by
    filter_upwards [eventually_gt_atTop (1:ℝ),hSieve] with x hx hs
    have hx0 : 0 < x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hc : 0 ≤ Real.log x / x := div_nonneg hlog hx0.le
    have hmaj := mul_le_mul_of_nonneg_left hs hc
    calc
      f x = (Real.log x / x)*R x := by dsimp [f]; ring
      _ ≤ (Real.log x / x) *
        (x * V x * C + 2*((x^b)^(4*(sourceDepth b:ℝ)+2))) := hmaj
      _ = g x := by
        dsimp [g]
        field_simp
  have hMain : Tendsto (fun x : ℝ => (Real.log x)*V x*C)
      atTop (𝓝 ((m/b)*C)) := hMertens.mul_const C
  have hTail := source_sieve_remainder_tendsto_zero b hb hsmall
  have hG : Tendsto g atTop (𝓝 ((m/b)*C)) := by
    have hh := hMain.add hTail
    simpa only [g, add_zero] using hh
  exact eventual_liminf_le_of_majorant f g D ((m/b)*C)
    hRoughLower hcomp hG

/-- Convert an exact depth-decay bound to absolute exponential
precision in 1/b, with constants chosen before b and before x. -/
theorem source_depth_exp_absorbed
    (b K : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100)
    (hK : 0 ≤ K) :
    1+K*Real.exp (-(sourceDepth b:ℝ)) ≤
      1+K*Real.exp (-(1/(40*b))) := by
  have hh := (sourceDepth_budget b hb hsmall).2.2.1
  have hmul : K*Real.exp (-(sourceDepth b:ℝ)) ≤
      K*Real.exp (-(1/(40*b))) := by
    apply mul_le_mul_of_nonneg_left _ hK
    apply Real.exp_le_exp.mpr
    linarith
  linarith

/-- Absolute source constants: b0=1/100, c=1/40 and C=K.
The difficult PNT/Mertens + ordered-rough lower comparisons are shown,
not hidden, as the only analytic theorem premises. -/
theorem exponential_small_b_from_limits
    (b K m D : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100)
    (hK : 0 ≤ K) (hm : 0 < m)
    (R V : ℝ → ℝ)
    (hMertens : Tendsto (fun x : ℝ => (Real.log x)*V x)
      atTop (𝓝 (m/b)))
    (hRoughLower : ∀ ε : ℝ, 0 < ε →
       ∀ᶠ x : ℝ in atTop, D ≤ Real.log x * R x/x + ε)
    (hSieve : ∀ᶠ x : ℝ in atTop,
      R x ≤ x * V x *
        (1+K*Real.exp (-(sourceDepth b : ℝ))) +
        2*((x^b)^(4*(sourceDepth b:ℝ)+2))) :
    D ≤ (m/b)*(1+K*Real.exp (-(1/(40*b)))) := by
  have hmain := small_b_majorant_from_limits b m K hb hm.le hK
      hsmall R V D hMertens hRoughLower hSieve
  have hfactor := source_depth_exp_absorbed b K hb hsmall hK
  exact hmain.trans (mul_le_mul_of_nonneg_left hfactor
     (div_nonneg hm.le hb.le))

end Green64Analytic.SmallB

end

/-! ## SmallBDensity -/

section

set_option maxHeartbeats 1000000
open Filter Topology Real
namespace Green64Analytic.SmallB

/-- Exact literal source (n+2)-prime simplex coefficient with factorial. -/
noncomputable def sourceSimplexTerm (n : ℕ) (γ w : ℝ) : ℝ :=
  (∫ t in {t : Fin (n+1) → ℝ |
      (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w-γ},
      (∏ i : Fin (n+1), (t i)⁻¹) *
        (w-∑ i, t i)⁻¹) / ((n+2).factorial : ℝ)

noncomputable def sourceDensity (γ w : ℝ) : ℝ :=
  1/w + ∑' n : ℕ, sourceSimplexTerm n γ w

theorem sourceDensity_one_prime_lower (γ w : ℝ) (hγ : 0 < γ) :
    1/w ≤ sourceDensity γ w := by
  simpa only [sourceDensity,sourceSimplexTerm] using
    (Green64Analytic.ReciprocalSimplex.density_one_prime_lower γ w hγ)

/-- The *actual* bounded finite-prime sieve theorem is already a
Lean theorem, not an analytic premise. -/
theorem source_rough_upper_eventual (b : ℝ)
    (hb : 0 < b) (hsmall : b ≤ 1/100) :
    ∀ᶠ x : ℝ in atTop,
      roughCount b x ≤
        x * roughEuler (x^b) *
         (1+sieveC*Real.exp (-(sourceDepth b:ℝ))) +
        2*(x^b)^(4*(sourceDepth b:ℝ)+2) := by
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  exact actual_rough_sieve_upper b x hb hsmall hx

/-- Quantified small-b bound with an EXPLICIT absolute exponential
error, derived from the ACTUAL source finite sieve. Only the precisely
displayed classical-Mertens and ordered-list/rough-count lower comparison
remain external theorem parameters; neither presupposes the desired bound. -/
theorem source_small_b_exp_bound
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1/100)
    (hMertens :
      Tendsto (fun x : ℝ => Real.log x * roughEuler (x^b))
        atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/b)))
    (hRoughLower : ∀ ε : ℝ, 0 < ε →
       ∀ᶠ x : ℝ in atTop,
         sourceDensity b 1 ≤
           Real.log x * roughCount b x / x + ε) :
    sourceDensity b 1 ≤
      Real.exp (-Real.eulerMascheroniConstant)/b *
        (1+sieveC*Real.exp (-(1/(40*b)))) := by
  exact exponential_small_b_from_limits
    b sieveC (Real.exp (-Real.eulerMascheroniConstant))
    (sourceDensity b 1) hb hsmall
    sieveC_pos.le (Real.exp_pos _)
    (roughCount b) (fun x => roughEuler (x^b))
    hMertens hRoughLower (source_rough_upper_eventual b hb hsmall)

end Green64Analytic.SmallB

end

/-! ## SourceRealMertens -/

section

set_option maxHeartbeats 2000000
open Filter Topology
open scoped BigOperators

namespace Green64Analytic.SmallB

/-- The literal natural-prime alphabet (including p = 2) agrees
exactly with Chen's natural-cutoff Euler product, for every real z. -/
theorem roughEuler_eq_chen (z : ℝ) :
    roughEuler z = Chen.primeEulerProduct ⌊z⌋₊ := by
  rw [Chen.primeEulerProduct_eq_Ioc]
  unfold roughEuler roughAlphabet
  apply Finset.prod_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hlt, hp⟩
      have hle : p ≤ ⌊z⌋₊ := by omega
      exact ⟨⟨hp.pos, hle⟩, hp⟩
    · rintro ⟨⟨_, hle⟩, hp⟩
      exact ⟨by omega, hp⟩
  · intro p hp
    simp only [one_div]

/-- The real-x logarithmic floor cutoff has precisely the exponent b. -/
theorem log_real_power_floor_ratio (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ =>
       Real.log (⌊x ^ b⌋₊ : ℝ) / Real.log x)
       atTop (𝓝 b) := by
  have hpow : Tendsto (fun x : ℝ => x ^ b) atTop atTop :=
    tendsto_rpow_atTop hb
  have hratio : Tendsto (fun x : ℝ =>
      (⌊x ^ b⌋₊ : ℝ) / (x ^ b)) atTop (𝓝 1) := by
    simpa only [Function.comp_def] using
      tendsto_nat_floor_div_atTop.comp hpow
  have hlogratio : Tendsto (fun x : ℝ =>
      Real.log ((⌊x ^ b⌋₊ : ℝ) / (x ^ b))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using hratio.log one_ne_zero
  have hsmall := hlogratio.div_atTop Real.tendsto_log_atTop
  have hlim := (tendsto_const_nhds (x := b)).add hsmall
  simp only [add_zero] at hlim
  apply hlim.congr'
  have hfloor : Tendsto (fun x : ℝ => (⌊x ^ b⌋₊ : ℕ)) atTop atTop :=
    tendsto_nat_floor_atTop.comp hpow
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    hfloor.eventually (eventually_ge_atTop 2)] with x hx hy
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : (0 : ℝ) < (⌊x ^ b⌋₊ : ℝ) := by
    exact_mod_cast (show 0 < ⌊x ^ b⌋₊ by omega)
  have hlogx : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  rw [Real.log_div (ne_of_gt hypos)
        (ne_of_gt (Real.rpow_pos_of_pos hxpos b)),
      Real.log_rpow hxpos]
  field_simp
  ring

/-- Third Mertens theorem with the exact *real x*, floor(x^b)
cutoff, literal source Euler product and Euler's constant. -/
theorem real_roughEuler_mertens (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.log x * roughEuler (x ^ b))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / b)) := by
  have hpow : Tendsto (fun x : ℝ => x ^ b) atTop atTop :=
    tendsto_rpow_atTop hb
  have hfloor : Tendsto (fun x : ℝ => (⌊x ^ b⌋₊ : ℕ)) atTop atTop :=
    tendsto_nat_floor_atTop.comp hpow
  have hprod := Chen.primeEulerProduct_mul_log_tendsto.comp hfloor
  have hratio := log_real_power_floor_ratio b hb

  have hlim := hprod.div hratio (ne_of_gt hb)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    hfloor.eventually (eventually_ge_atTop 2)] with x hx hy
  have hlogx : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  have hlogy : Real.log (⌊x ^ b⌋₊ : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (show 1 < ⌊x ^ b⌋₊ by omega)
  rw [roughEuler_eq_chen]
  change (Chen.primeEulerProduct ⌊x ^ b⌋₊ *
      Real.log (⌊x ^ b⌋₊ : ℝ)) /
        (Real.log (⌊x ^ b⌋₊ : ℝ) / Real.log x) =
      Real.log x * Chen.primeEulerProduct ⌊x ^ b⌋₊
  field_simp

/-- Remove the Mertens premise from the exact SmallB bound; the
rough-count lower comparison remains an explicit dependency. -/
theorem source_small_b_exp_bound_of_rough_lower
    (b : ℝ) (hb : 0 < b) (hsmall : b ≤ 1 / 100)
    (hRoughLower : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        sourceDensity b 1 ≤ Real.log x * roughCount b x / x + ε) :
    sourceDensity b 1 ≤
      Real.exp (-Real.eulerMascheroniConstant) / b *
        (1 + sieveC * Real.exp (-(1 / (40 * b)))) := by
  exact source_small_b_exp_bound b hb hsmall
    (real_roughEuler_mertens b hb) hRoughLower

end Green64Analytic.SmallB

end

/-! ## LiteralDensityScaling -/

section

open MeasureTheory Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.SmallB
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Exact positive dilation of a complete source-simplex term. Every
coordinate and the dependent last coordinate are scaled; the Jacobian
leaves exactly one inverse physical exponent. -/
theorem b647_source_simplex_rescale434 (n : ℕ) (b w : ℝ) (hw : 0 < w) :
    sourceSimplexTerm n b w = w⁻¹ * sourceSimplexTerm n (b / w) 1 := by
  let T : Set (Fin (n+1) → ℝ) :=
    {t | (∀ i, b ≤ t i) ∧ ∑ i, t i ≤ w-b}
  let U : Set (Fin (n+1) → ℝ) :=
    {z | (∀ i, b/w ≤ z i) ∧ ∑ i, z i ≤ 1-b/w}
  let f : (Fin (n+1) → ℝ) → ℝ :=
    fun t => (∏ i, (t i)⁻¹) * (w-∑ i, t i)⁻¹
  let g : (Fin (n+1) → ℝ) → ℝ :=
    fun z => (∏ i, (z i)⁻¹) * (1-∑ i, z i)⁻¹
  have hT : MeasurableSet T := by dsimp [T]; measurability
  have hU : MeasurableSet U := by dsimp [U]; measurability
  have hf : Measurable f := by dsimp [f]; measurability
  have hpre (z : Fin (n+1) → ℝ) :
      (fun i => w*z i) ∈ T ↔ z ∈ U := by
    change ((∀ i, b ≤ w*z i) ∧ (∑ i, w*z i) ≤ w-b) ↔
      ((∀ i, b/w ≤ z i) ∧ (∑ i, z i) ≤ 1-b/w)
    rw [← Finset.mul_sum]
    have he : w-b = w*(1-b/w) := by field_simp
    rw [he]
    constructor
    · intro h
      refine ⟨fun i => ?_, (mul_le_mul_iff_of_pos_left hw).mp h.2⟩
      exact (div_le_iff₀ hw).mpr (by simpa only [mul_comm] using h.1 i)
    · intro h
      refine ⟨fun i => ?_, (mul_le_mul_iff_of_pos_left hw).mpr h.2⟩
      simpa only [mul_comm] using (div_le_iff₀ hw).mp (h.1 i)
  have hker (z : Fin (n+1) → ℝ) :
      f (fun i => w*z i) = (w⁻¹)^(n+2)*g z := by
    dsimp [f,g]
    rw [← Finset.mul_sum]
    rw [show w-w*(∑ i, z i) = w*(1-∑ i, z i) by ring]
    simp only [mul_inv_rev, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    ring
  have he := Green64Analytic.ReciprocalSimplex.affine_integral
    (n+1) w (0 : Fin (n+1) → ℝ) (T.indicator f) hw (hf.indicator hT)
  rw [integral_indicator hT] at he
  have hfun :
      (fun z : Fin (n+1) → ℝ => T.indicator f (0 + w • z)) =
      (fun z => (w⁻¹)^(n+2)*U.indicator g z) := by
    funext z
    have hz0 : (0 : Fin (n+1) → ℝ) + w • z = (fun i => w*z i) := by
      ext i
      simp
    rw [hz0]
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hpre z).mpr hz)]
      exact hker z
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (mt (hpre z).mp hz), mul_zero]
  rw [hfun, integral_const_mul, integral_indicator hU] at he
  have hp : w^(n+1)*(w⁻¹)^(n+2) = w⁻¹ := by
    calc
      _ = (w^(n+1)*(w⁻¹)^(n+1))*w⁻¹ := by rw [pow_succ]; ring
      _ = w⁻¹ := by rw [← mul_pow, mul_inv_cancel₀ hw.ne', one_pow, one_mul]
  unfold sourceSimplexTerm
  change (∫ t in T, f t) / ((n+2).factorial : ℝ) =
    w⁻¹*((∫ z in U, g z) / ((n+2).factorial : ℝ))
  rw [he]
  calc
    _ = (w^(n+1)*(w⁻¹)^(n+2))*
        ((∫ z in U, g z) / ((n+2).factorial : ℝ)) := by ring
    _ = _ := by rw [hp]

/-- The full literal density, including its one-prime term and every
factorial-weighted simplex length, has degree minus one. -/
theorem b647_source_density_rescale434 (b w : ℝ) (hw : 0 < w) :
    sourceDensity b w = w⁻¹ * sourceDensity (b/w) 1 := by
  have hs : (∑' n : ℕ, sourceSimplexTerm n b w) =
      w⁻¹ * ∑' n : ℕ, sourceSimplexTerm n (b/w) 1 := by
    calc
      _ = ∑' n : ℕ, w⁻¹ * sourceSimplexTerm n (b/w) 1 :=
        tsum_congr (fun n => b647_source_simplex_rescale434 n b w hw)
      _ = _ := tsum_mul_left
  simp only [sourceDensity, hs, one_div_one]
  ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## RoughCountSemantics -/

section

set_option maxHeartbeats 650000
open Filter Topology Real
namespace Green64Analytic.SmallB

/-- The finite alphabet is exactly the set of natural primes <=z,
with no artificial squarefree restriction on the surviving integers. -/
theorem roughAlphabet_iff (z : ℝ) (hz : 0 ≤ z) (p : ℕ) :
    p ∈ roughAlphabet z ↔ Nat.Prime p ∧ (p:ℝ) ≤ z := by
  constructor
  · exact roughAlphabet_prime_le z hz p
  · intro hp
    have hfloor : p ≤ ⌊z⌋₊ := Nat.le_floor hp.2
    simp only [roughAlphabet, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega,hp.1⟩

theorem modeq_one_all (n : ℕ) : Nat.ModEq 1 n 0 := by
  change n % 1 = 0 % 1
  omega

/-- The mod-1 AP syntax is precisely the unrestricted count of
natural integers in (0,x] having NO prime factor <=x^b.
Repeated factors of primes >x^b are allowed. -/
theorem roughCount_is_actual (b x : ℝ) :
    roughCount b x =
     (((Finset.Ioc 0 ⌊x⌋₊).filter
       (fun n => ∀ p ∈ roughAlphabet (x^b), ¬ p ∣ n)).card : ℝ) := by
  unfold roughCount
  simp only [Nat.floor_zero]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ))
  apply Finset.filter_congr
  intro n hn
  simp only [Nat.ModEq]
  have h : n % 1 = 0 := by omega
  simp [h]

end Green64Analytic.SmallB

end

/-! ## SmallHaarTorus -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]

/-- Exactly the original finite small-prime residue torus
    ∏_{p∈P_small} Z/pZ (not a fake single residue coordinate). -/
abbrev SmallTorus := (p : P) → ZMod (modulus p)

/-- Translate EVERY prime coordinate by the same integer step. -/
def translate (step : ℤ) (y : SmallTorus modulus) : SmallTorus modulus :=
  fun p => y p + (step : ZMod (modulus p))

theorem translate_zero (y : SmallTorus modulus) :
    translate modulus 0 y = y := by
  funext p
  simp [translate]

theorem translate_neg (step : ℤ) (y : SmallTorus modulus) :
    translate modulus (-step) (translate modulus step y) = y := by
  funext p
  simp [translate]

theorem translate_back (step : ℤ) (y : SmallTorus modulus) :
    translate modulus step (translate modulus (-step) y) = y := by
  funext p
  simp [translate]

/-- Haar translations are *permutations* of the actual full finite torus. -/
def translationEquiv (step : ℤ) :
    SmallTorus modulus ≃ SmallTorus modulus where
  toFun := translate modulus step
  invFun := translate modulus (-step)
  left_inv := translate_neg modulus step
  right_inv := translate_back modulus step

instance : Nonempty (SmallTorus modulus) :=
  ⟨fun _ => 0⟩

/-- Haar probability of any coordinate point = 1/|Y|. -/
noncomputable def haarAtomMass : ℝ :=
  (1:ℝ) / (Fintype.card (SmallTorus modulus) : ℝ)

theorem haarAtomMass_positive :
    0 < haarAtomMass modulus := by
  unfold haarAtomMass
  positivity

/-- Integrating over the real small-prime Haar torus is a uniform
    finite average. This is the *unique* translation-invariant
    probability on this finite abelian group. -/
noncomputable def haarIntegral (F : SmallTorus modulus → ℂ) : ℂ :=
  ∑ y : SmallTorus modulus, (haarAtomMass modulus : ℂ) * F y

theorem haarIntegral_one :
    haarIntegral modulus (fun _ => (1:ℂ)) = 1 := by
  unfold haarIntegral
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (SmallTorus modulus) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (⟨fun _ => 0⟩ : Nonempty (SmallTorus modulus))).ne'
  have hmass : ((haarAtomMass modulus : ℝ) : ℂ) =
      1 / (Fintype.card (SmallTorus modulus) : ℂ) := by
    simp [haarAtomMass]
  rw [hmass]
  field_simp [hcard]

/-- The fundamental Haar transport equality, with NO missing factor
    1/p on some coordinates and without changing the source measure. -/
theorem haarIntegral_translate (step : ℤ)
    (F : SmallTorus modulus → ℂ) :
    haarIntegral modulus (fun y => F (translate modulus step y)) =
      haarIntegral modulus F := by
  unfold haarIntegral
  have hf :=
    Equiv.sum_comp (translationEquiv modulus step)
      (fun y => (haarAtomMass modulus : ℂ) * F y)
  simpa [translationEquiv] using hf

theorem haarIntegral_translate_to (step : ℤ)
    (F : SmallTorus modulus → ℂ) :
    haarIntegral modulus F =
      haarIntegral modulus (fun y => F (translate modulus (-step) y)) := by
  exact (haarIntegral_translate modulus (-step) F).symm

/-- Empty small-prime torus still has one coordinate and unit Haar mass. -/
theorem haarAtomMass_empty
    (emptyModuli : Fin 0 → ℕ) [∀ p, NeZero (emptyModuli p)] :
    haarAtomMass emptyModuli = 1 := by
  classical
  have hcard : Fintype.card (SmallTorus emptyModuli) = 1 := by
    haveI : Subsingleton (SmallTorus emptyModuli) := ⟨fun a b => by
      funext p
      exact p.elim0⟩
    exact Fintype.card_ofSubsingleton (fun _ => 0)
  simp [haarAtomMass,hcard]

end Green64SmallHaar

end

/-! ## SmallPhysicalStates -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- The exact small-prime zero-coordinate set at one Haar residue y. -/
noncomputable def zeroCoordSet (y : SmallTorus modulus) : Finset P :=
  Finset.univ.filter (fun p => y p = 0)

noncomputable def omega (y : SmallTorus modulus) : ℕ :=
  (zeroCoordSet modulus y).card

/-- A small physical state at y: an ORDERED list of M numerical small
prime labels, distinct within its group, each marking a zero
coordinate at the same Haar residue vector y. This is the original
source Hilbert small-state carrier, not a set of all zero coordinates. -/
def SmallState :=
  { x : SmallTorus modulus × (Fin M → P) //
      Function.Injective x.2 ∧ (∀ j : Fin M, x.1 (x.2 j) = 0) }

noncomputable instance : Fintype (SmallState modulus M) := by
  classical
  unfold SmallState
  infer_instance

noncomputable def residues (x : SmallState modulus M) : SmallTorus modulus :=
  x.val.1

noncomputable def marks (x : SmallState modulus M) : Fin M → P :=
  x.val.2

theorem marks_injective (x : SmallState modulus M) :
    Function.Injective (marks modulus M x) := x.property.1

theorem marked_zero (x : SmallState modulus M) (j : Fin M) :
    residues modulus M x (marks modulus M x j) = 0 := x.property.2 j

/-- The physical state has omega_g(y) >= M because its M ordered
active marks are genuinely distinct zero coordinates, which ensures
that q^((omega_g-M)/2) has a NONNEGATIVE real exponent. -/
theorem omega_ge_M (x : SmallState modulus M) :
    M ≤ omega modulus (residues modulus M x) := by
  have hsubset :
      (Finset.univ : Finset (Fin M)).image (marks modulus M x) ⊆
        zeroCoordSet modulus (residues modulus M x) := by
    intro p hp
    obtain ⟨j,hj,hp⟩ := Finset.mem_image.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hp]
    exact marked_zero modulus M x j
  have hcard :
      ((Finset.univ : Finset (Fin M)).image (marks modulus M x)).card = M := by
    rw [Finset.card_image_of_injective _ (marks_injective modulus M x)]
    simp
  have hle := Finset.card_le_card hsubset
  simpa only [hcard,omega] using hle

/-- The exact source power q^((omega_g(y)-M)/2), written as
(sqrt q)^(omega-M). This is equivalent for q>=0; use the sqrt
representation to keep exponent natural and avoid artificial
negative powers on invalid mark states (they do not exist). -/
noncomputable def endpointDamping (q : ℝ)
    (x : SmallState modulus M) : ℝ :=
  (Real.sqrt q) ^ (omega modulus (residues modulus M x) - M)

/-- This exactly matches the published q^((omega_g(y)-M)/2)
small endpoint factor, including the source omega count. -/
theorem endpointDamping_eq_source_rpow (q : ℝ) (hq : 0 ≤ q)
    (x : SmallState modulus M) :
    endpointDamping modulus M q x =
      q ^ (((omega modulus (residues modulus M x) - M : ℕ) : ℝ) / 2) := by
  unfold endpointDamping
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul_natCast hq (1/2)]
  congr 1
  ring

theorem endpointDamping_nonneg (q : ℝ)
    (x : SmallState modulus M) :
    0 ≤ endpointDamping modulus M q x := by
  unfold endpointDamping
  positivity

theorem endpointDamping_le_one (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (x : SmallState modulus M) :
    endpointDamping modulus M q x ≤ 1 := by
  unfold endpointDamping
  have hh : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  have hle : Real.sqrt q ≤ 1 := by
    nlinarith [Real.sq_sqrt hq0]
  exact pow_le_one₀ hh hle

/-- The actual finite small-state scalar mass is Haar atom 1/|Y|
times the source's independent physical mark mass V_g^(-M).
It is constant per ordered valid mark-list state at fixed y. -/
noncomputable def stateMass (V : ℝ) : ℝ :=
  haarAtomMass modulus * (1 / (V ^ M))

theorem stateMass_positive (V : ℝ) (hV : 0 < V) :
    0 < stateMass modulus M V := by
  unfold stateMass
  exact mul_pos (haarAtomMass_positive modulus)
    (one_div_pos.mpr (pow_pos hV M))

theorem stateMass_same (V : ℝ)
    (x z : SmallState modulus M) :
    stateMass modulus M V = stateMass modulus M V := rfl

/-- The empty-mark case M=0 has one ordered mark list at every y,
so small state mass is exactly Haar mass (not an extra M! factor). -/
theorem stateMass_zero_marks (V : ℝ) :
    stateMass modulus 0 V = haarAtomMass modulus := by
  simp [stateMass]

end Green64SmallHaar

end

/-! ## SmallPhysicalEdge -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- Shared marks at exactly the same canonical pattern slots. The
source and target permutations are still separate external choices;
we do NOT cancel either permutation factorial term-by-term. -/
def sameShared (shared : Finset (Fin M))
    (x z : SmallState modulus M) : Prop :=
  ∀ j ∈ shared, marks modulus M x j = marks modulus M z j

theorem sameShared_symm (shared : Finset (Fin M))
    (x z : SmallState modulus M) :
    sameShared modulus M shared x z ↔
      sameShared modulus M shared z x := by
  constructor
  · intro h j hj
    exact (h j hj).symm
  · intro h j hj
    exact (h j hj).symm

/-- The REAL physical small-prime E_i transition: translate ALL
small-residue Haar coordinates by Delta, and require the chosen shared
active labels to agree in their canonical slots. -/
def edgeAllowed (shared : Finset (Fin M)) (step : ℤ)
    (x z : SmallState modulus M) : Prop :=
  residues modulus M z = translate modulus step (residues modulus M x) ∧
    sameShared modulus M shared x z

/-- Translating by -Delta and swapping endpoints is the EXACT reverse
physical small-state edge. The allowed relation is not assumed to be
symmetric at a fixed positive Delta. -/
theorem edgeAllowed_reverse (shared : Finset (Fin M))
    (step : ℤ) (x z : SmallState modulus M) :
    edgeAllowed modulus M shared step x z ↔
      edgeAllowed modulus M shared (-step) z x := by
  constructor
  · rintro ⟨ht,hs⟩
    constructor
    · rw [ht,translate_neg]
    · exact (sameShared_symm modulus M shared x z).mp hs
  · rintro ⟨ht,hs⟩
    constructor
    · rw [ht,translate_back]
    · exact (sameShared_symm modulus M shared x z).mpr hs

/-- The shared prime really must divide the displacement Delta,
because its residue vanishes at both ends. This is the precise
small-coordinate analogue of original source shared congruence. -/
theorem shared_prime_divides_step
    (shared : Finset (Fin M)) (step : ℤ)
    (x z : SmallState modulus M)
    (h : edgeAllowed modulus M shared step x z)
    (j : Fin M) (hj : j ∈ shared) :
    (modulus (marks modulus M x j) : ℤ) ∣ step := by
  have hs := h.2 j hj
  have hx := marked_zero modulus M x j
  have hz := marked_zero modulus M z j
  have hz' : residues modulus M z (marks modulus M x j) = 0 := by
    rw [hs]
    exact hz
  have ht := congrFun h.1 (marks modulus M x j)
  simp only [translate] at ht
  rw [hz', hx,zero_add] at ht
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd step
     (modulus (marks modulus M x j))).mp ht.symm

/-- Exactly t=M-|shared| unshared target active slots. -/
def unsharedSlots (shared : Finset (Fin M)) : ℕ :=
  M - shared.card

theorem shared_plus_unshared (shared : Finset (Fin M)) :
    shared.card + unsharedSlots M shared = M := by
  unfold unsharedSlots
  have h : shared.card ≤ M := by
    simpa using Finset.card_le_univ shared
  omega

/-- The source small target sum charges V_g^{-t} for the t unshared
target slots; endpoint damping is q^((omega(y)-M)/2) at BOTH
the true small-residue source and translated target positions. -/
noncomputable def edgeScalar (q V : ℝ)
    (shared : Finset (Fin M))
    (x z : SmallState modulus M) : ℝ :=
  (1 / (V ^ (unsharedSlots M shared))) *
    endpointDamping modulus M q x *
    endpointDamping modulus M q z

theorem edgeScalar_symmetric (q V : ℝ)
    (shared : Finset (Fin M))
    (x z : SmallState modulus M) :
    edgeScalar modulus M q V shared x z =
      edgeScalar modulus M q V shared z x := by
  unfold edgeScalar
  ring

theorem edgeScalar_nonneg (q V : ℝ) (hV : 0 < V)
    (shared : Finset (Fin M))
    (x z : SmallState modulus M) :
    0 ≤ edgeScalar modulus M q V shared x z := by
  unfold edgeScalar
  exact mul_nonneg
    (mul_nonneg (le_of_lt (one_div_pos.mpr (pow_pos hV _)))
      (endpointDamping_nonneg modulus M q x))
    (endpointDamping_nonneg modulus M q z)

/-- Forward *physical* small-group edge kernel for ONE sampled
shared pattern and oriented source step, including its complex
multiplier K. The reversal uses -Delta and conj(K). -/
noncomputable def edgeKernel
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (x z : SmallState modulus M) : ℂ :=
  if edgeAllowed modulus M shared step x z then
    K * (edgeScalar modulus M q V shared x z : ℂ)
  else 0

/-- A direct per-pair proof of true physical small-kernel time
reversal, including the complex conjugation of K. -/
theorem edgeKernel_reverse
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (x z : SmallState modulus M) :
    edgeKernel modulus M q V shared step K x z =
      star (edgeKernel modulus M q V shared (-step) (star K) z x) := by
  by_cases h : edgeAllowed modulus M shared step x z
  · have hr := (edgeAllowed_reverse modulus M shared step x z).mp h
    simp only [edgeKernel,h,hr,if_true,star_mul,star_star]
    rw [edgeScalar_symmetric modulus M q V shared z x]
    rw [Complex.star_def, Complex.conj_ofReal]
    ring
  · have hr : ¬ edgeAllowed modulus M shared (-step) z x := by
      intro hh
      exact h ((edgeAllowed_reverse modulus M shared step x z).mpr hh)
    simp [edgeKernel,h,hr]

/-- The EXACT source joint small measure for each allowed edge is
Haar(y)*V^{-M}*V^{-t} times its two q endpoint factors, hence
Haar(y)*V^{-(M+t)}*endpointDamping(y)*endpointDamping(y+Delta).
No spurious factorial or residue 1/p is introduced. -/
theorem joint_small_normalization (q V : ℝ)
    (shared : Finset (Fin M))
    (x z : SmallState modulus M) :
    stateMass modulus M V * edgeScalar modulus M q V shared x z =
      haarAtomMass modulus *
        (1 / V ^ (M + unsharedSlots M shared)) *
        endpointDamping modulus M q x *
        endpointDamping modulus M q z := by
  unfold stateMass edgeScalar
  rw [pow_add]
  ring

/-- Reversing an edge preserves the *complete* physical small
source/target joint measure V^{-M-t}; the Haar masses agree by
translation-invariance, and endpoint damping swaps symmetrically. -/
theorem small_joint_detailed_balance
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (x z : SmallState modulus M) :
    (stateMass modulus M V : ℂ) *
        edgeKernel modulus M q V shared step K x z =
      (stateMass modulus M V : ℂ) *
        star (edgeKernel modulus M q V shared (-step) (star K) z x) := by
  rw [edgeKernel_reverse]

end Green64SmallHaar

end

/-! ## SmallHaarHilbert -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- The actual finite Hilbert inner-product sum on the source
small-prime Haar coordinate torus and ordered valid M-mark states.
Every state has Haar(y) * V^{-M} mass; no extra endpoint factorial
or counting-residue weight is secretly introduced. -/
noncomputable def smallInner (V : ℝ)
    (F G : SmallState modulus M → ℂ) : ℂ :=
  ∑ x : SmallState modulus M,
    (stateMass modulus M V : ℂ) * star (F x) * G x

/-- A true fixed-pattern small physical E edge row action: the input
state is y and source ordered marks, targets run over every valid
ordered M-mark list at y+Delta; the target normalization V^{-t}
and both small endpoint q factors reside in the actual kernel. -/
noncomputable def smallEdgeAct
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (G : SmallState modulus M → ℂ)
    (x : SmallState modulus M) : ℂ :=
  ∑ z : SmallState modulus M,
    edgeKernel modulus M q V shared step K x z * G z

/-- This is a genuine FINITE Hilbert adjoint, not just a formal
property of an arbitrary function. Reverse orientation -Delta,
conjugate the complex multiplier K, swap the ordered mark lists,
and retain the original V^{-M-t} joint physical measure. -/
theorem smallEdgeAct_adjoint
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (F G : SmallState modulus M → ℂ) :
    smallInner modulus M V F
        (smallEdgeAct modulus M q V shared step K G) =
      smallInner modulus M V
        (smallEdgeAct modulus M q V shared (-step) (star K) F) G := by
  let W : ℂ := (stateMass modulus M V : ℂ)
  let A : SmallState modulus M → SmallState modulus M → ℂ :=
    edgeKernel modulus M q V shared step K
  let B : SmallState modulus M → SmallState modulus M → ℂ :=
    edgeKernel modulus M q V shared (-step) (star K)
  have hpair (x z : SmallState modulus M) :
      W * star (F x) * (A x z * G z) =
      W * star (B z x * F x) * G z := by
    have hker := edgeKernel_reverse modulus M q V shared step K x z
    change A x z = star (B z x) at hker
    rw [hker,star_mul]
    ring
  have hleft :
      smallInner modulus M V F
          (smallEdgeAct modulus M q V shared step K G) =
        ∑ x : SmallState modulus M,
          ∑ z : SmallState modulus M,
            W * star (F x) * (A x z * G z) := by
    unfold smallInner smallEdgeAct
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  have hright :
      smallInner modulus M V
          (smallEdgeAct modulus M q V shared (-step) (star K) F) G =
        ∑ z : SmallState modulus M,
          ∑ x : SmallState modulus M,
            W * star (B z x * F x) * G z := by
    unfold smallInner smallEdgeAct
    apply Finset.sum_congr rfl
    intro z hz
    rw [star_sum]
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
  calc
    smallInner modulus M V F
        (smallEdgeAct modulus M q V shared step K G) =
      ∑ x : SmallState modulus M,
          ∑ z : SmallState modulus M,
            W * star (F x) * (A x z * G z) := hleft
    _ = ∑ z : SmallState modulus M,
          ∑ x : SmallState modulus M,
            W * star (F x) * (A x z * G z) :=
      Finset.sum_comm
    _ = ∑ z : SmallState modulus M,
          ∑ x : SmallState modulus M,
            W * star (B z x * F x) * G z := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair x z
    _ = smallInner modulus M V
          (smallEdgeAct modulus M q V shared (-step) (star K) F) G :=
        hright.symm

/-- The finite small Hilbert edge adjoint can be checked for *any*
complex functions; no symmetric-big-group Fock or independent
source Fourier hypothesis is required. -/
theorem smallEdgeAct_reverse_pairing
    (q V : ℝ) (shared : Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (F G : SmallState modulus M → ℂ) :
    smallInner modulus M V
        (smallEdgeAct modulus M q V shared (-step) (star K) F) G =
      smallInner modulus M V F
        (smallEdgeAct modulus M q V shared step K G) :=
  (smallEdgeAct_adjoint modulus M q V shared step K F G).symm

end Green64SmallHaar

end

/-! ## SmallMarksCount -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- All numerical small primes whose Haar coordinate is zero at y. -/
abbrev ZeroLabel (y : SmallTorus modulus) :=
  { p : P // y p = 0 }

/-- An ordered M-element DISTINCT mark list drawn only from the
small-prime zeros at one specified Haar coordinate y. -/
def MarksAt (y : SmallTorus modulus) :=
  { marks : Fin M → P // Function.Injective marks ∧
     ∀ j : Fin M, y (marks j) = 0 }

noncomputable instance (y : SmallTorus modulus) :
    Fintype (MarksAt modulus M y) := by
  classical
  unfold MarksAt
  infer_instance

/-- An exact equivalence (not a quotient or set-valued approximation):
ordered distinct M-marks are embeddings of Fin M into the full
zero-coordinate label fibre. -/
def marksAtEquivEmbedding (y : SmallTorus modulus) :
    MarksAt modulus M y ≃ (Fin M ↪ ZeroLabel modulus y) where
  toFun a :=
    { toFun := fun j => ⟨a.val j, a.property.2 j⟩
      inj' := by
        intro i j hij
        apply a.property.1
        exact congrArg Subtype.val hij }
  invFun e :=
    ⟨fun j => (e j).val,
      ⟨by
        intro i j hij
        apply e.injective
        exact Subtype.ext hij,
       fun j => (e j).property⟩⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    apply Function.Embedding.ext
    intro j
    apply Subtype.ext
    rfl

theorem zeroLabel_count (y : SmallTorus modulus) :
    Fintype.card (ZeroLabel modulus y) = omega modulus y := by
  unfold ZeroLabel omega zeroCoordSet
  rw [Fintype.card_subtype]

/-- EXACT number of admissible physical ordered M-mark states at y:
ω_g(y) falling-factorial M, with no independent-vs-identical
prime confusion and NO spurious M! factor. This is the small-group
combinatorial count used in the original physical row bounds. -/
theorem marksAt_card (y : SmallTorus modulus) :
    Fintype.card (MarksAt modulus M y) =
      (omega modulus y).descFactorial M := by
  calc
    Fintype.card (MarksAt modulus M y) =
      Fintype.card (Fin M ↪ ZeroLabel modulus y) :=
      Fintype.card_congr (marksAtEquivEmbedding modulus M y)
    _ = (Fintype.card (ZeroLabel modulus y)).descFactorial
      (Fintype.card (Fin M)) :=
        Fintype.card_embedding_eq
    _ = (omega modulus y).descFactorial M := by
      rw [zeroLabel_count]
      simp

/-- The empty ordered small-mark list is unique at every y, and the
source cardinal count gives (ω)_0 = 1 even if ω=0. -/
theorem marksAt_card_zero (y : SmallTorus modulus) :
    Fintype.card (MarksAt modulus 0 y) = 1 := by
  rw [marksAt_card]
  simp

/-- The source's physical small state at y with M marks has TOTAL
mark-weight (ω(y))_M / V^M. This is exact finite counting with
V^{-M} assigned to each ordered admissible mark list. -/
theorem small_mark_mass_at_y (y : SmallTorus modulus) (V : ℝ) :
    (∑ a : MarksAt modulus M y, (1:ℝ)/(V^M)) =
      ((omega modulus y).descFactorial M : ℝ) / (V^M) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [marksAt_card]
  ring

end Green64SmallHaar

end

/-! ## SmallJointMeasure -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p, NeZero (modulus p)]
variable (M : ℕ)

/-- An exact source small physical state is a Haar point followed by
an ordered injective mark list selected from the zeros of that point.
This equivalence DOES NOT collapse the mark list into a distinct-value
set, hence retains source mark multiplicities and permutations. -/
def smallStateSigmaEquiv :
    SmallState modulus M ≃
      Σ y : SmallTorus modulus, MarksAt modulus M y where
  toFun x := ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
  invFun x := ⟨⟨x.1, x.2.val⟩, x.2.property⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    cases x with
    | mk y a =>
      rfl

/-- Build an actual physical small state at a specified Haar residue y
from any ordered list of M distinct zero-coordinate marks at y. -/
noncomputable def stateFrom
    (y : SmallTorus modulus) (a : MarksAt modulus M y) :
    SmallState modulus M :=
  ⟨⟨y, a.val⟩, a.property⟩

/-- EXACT disintegration of the finite small-group L² mass into
Haar probability on y and V^{-M} counting mass on each valid
ordered mark list at that y. This is the literal source small
Hilbert measure from §Hilbert, not an abstract weight redefinition. -/
theorem small_state_mass_disintegration
    (V : ℝ) (F : SmallState modulus M → ℂ) :
    (∑ x : SmallState modulus M,
        (stateMass modulus M V : ℂ) * F x) =
      ∑ y : SmallTorus modulus,
        (haarAtomMass modulus : ℂ) *
          (∑ a : MarksAt modulus M y,
            (((1:ℝ)/(V^M):ℝ):ℂ) * F (stateFrom modulus M y a)) := by
  have hsum :=
    Fintype.sum_equiv (smallStateSigmaEquiv modulus M)
      (fun x : SmallState modulus M =>
        (stateMass modulus M V : ℂ) * F x)
      (fun x : Σ y : SmallTorus modulus, MarksAt modulus M y =>
        (stateMass modulus M V : ℂ) *
          F (stateFrom modulus M x.1 x.2))
      (by intro x; rfl)
  rw [hsum]
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  unfold stateMass
  simp only [Complex.ofReal_mul]
  ring

/-- The Haar-averaged physical total mass over all small M-mark states
is exactly the expectation of (omega(y))_M / V^M. This is a
nontrivial normalization check for the source Hilbert measure;
the total mass need not be 1 when there are M active marks. -/
theorem small_state_total_mass
    (V : ℝ) :
    (∑ x : SmallState modulus M, (stateMass modulus M V : ℂ)) =
      ∑ y : SmallTorus modulus,
        (haarAtomMass modulus : ℂ) *
          ((((omega modulus y).descFactorial M : ℝ) / V^M) : ℂ) := by
  have hs := small_state_mass_disintegration modulus M V
    (fun _ => (1:ℂ))
  simp only [mul_one] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro y hy
  have hcount :
      (∑ a : MarksAt modulus M y,
        (((1:ℝ)/(V^M):ℝ):ℂ)) =
      ((((omega modulus y).descFactorial M : ℝ)/V^M):ℂ) := by
    exact_mod_cast small_mark_mass_at_y modulus M y V
  rw [hcount]

/-- For M=0 there is precisely one admissible ordered mark list at
each Haar residue, hence the full small physical Hilbert state mass
is one, independently of V. -/
theorem small_state_total_mass_zero_marks (V : ℝ) :
    (∑ x : SmallState modulus 0,
      (stateMass modulus 0 V : ℂ)) = 1 := by
  rw [small_state_total_mass]
  simpa [haarIntegral] using (haarIntegral_one modulus)

end Green64SmallHaar

end

/-! ## SmallHaarGroups -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Type) [∀ g, Fintype (P g)]
variable [∀ g, DecidableEq (P g)]
variable (modulus : (g : G) → P g → ℕ)
variable [∀ g, ∀ p, NeZero (modulus g p)]
variable (M : ℕ)

/-- True finite tensor of all small-prime group physical states. Each
group has its own residue torus and M ordered distinct zero-mark labels.
There is NO fictitious single factorial across different groups. -/
abbrev GroupState := (g : G) → SmallState (modulus g) M

noncomputable instance : Fintype (GroupState P modulus M) := by
  classical
  unfold GroupState
  infer_instance

/-- One integer displacement Delta is applied to *every* small
residue coordinate in every group, just as in the physical source. -/
def groupEdgeAllowed
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ)
    (x z : GroupState P modulus M) : Prop :=
  ∀ g, edgeAllowed (modulus g) M (shared g) step (x g) (z g)

theorem groupEdgeAllowed_reverse
    (shared : (g : G) → Finset (Fin M)) (step : ℤ)
    (x z : GroupState P modulus M) :
    groupEdgeAllowed P modulus M shared step x z ↔
      groupEdgeAllowed P modulus M shared (-step) z x := by
  constructor
  · intro h g
    exact (edgeAllowed_reverse (modulus g) M (shared g) step (x g) (z g)).mp (h g)
  · intro h g
    exact (edgeAllowed_reverse (modulus g) M (shared g) step (x g) (z g)).mpr (h g)

/-- Product of actual independent small group physical masses.
Each factor is Haar(y_g) * V_g^-M; no factorial across groups. -/
noncomputable def groupStateMass (V : G → ℝ) : ℝ :=
  ∏ g : G, stateMass (modulus g) M (V g)

/-- Tensor of all source small groups' q endpoint damping and
V_g^-t target normalization. -/
noncomputable def groupEdgeScalar
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (x z : GroupState P modulus M) : ℝ :=
  ∏ g : G, edgeScalar (modulus g) M q (V g)
    (shared g) (x g) (z g)

theorem groupEdgeScalar_symmetric
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (x z : GroupState P modulus M) :
    groupEdgeScalar P modulus M q V shared x z =
      groupEdgeScalar P modulus M q V shared z x := by
  unfold groupEdgeScalar
  apply Finset.prod_congr rfl
  intro g hg
  exact edgeScalar_symmetric (modulus g) M q (V g) (shared g) (x g) (z g)

/-- The source global complex small-operator multiplier K is charged
ONCE for the entire pattern, not once per small group. -/
noncomputable def groupEdgeKernel
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (x z : GroupState P modulus M) : ℂ :=
  if groupEdgeAllowed P modulus M shared step x z then
    K * (groupEdgeScalar P modulus M q V shared x z : ℂ)
  else 0

theorem groupEdgeKernel_reverse
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (x z : GroupState P modulus M) :
    groupEdgeKernel P modulus M q V shared step K x z =
      star (groupEdgeKernel P modulus M q V shared (-step) (star K) z x) := by
  by_cases h : groupEdgeAllowed P modulus M shared step x z
  · have hr := (groupEdgeAllowed_reverse P modulus M shared step x z).mp h
    simp only [groupEdgeKernel,h,hr,if_true,star_mul,star_star]
    rw [groupEdgeScalar_symmetric P modulus M q V shared z x]
    rw [Complex.star_def,Complex.conj_ofReal]
    ring
  · have hr : ¬ groupEdgeAllowed P modulus M shared (-step) z x := by
      intro hh
      exact h ((groupEdgeAllowed_reverse P modulus M shared step x z).mpr hh)
    simp [groupEdgeKernel,h,hr]

/-- **Source-exact** multi-small-group joint measure: product over g
of Haar probability, V_g^(-M-t_g), and the two q endpoint factors.
No extra cross-group factorial is present, and reversing x,z
does not change any of the physical joint normalizations. -/
theorem groupJointSmallNormalization
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (x z : GroupState P modulus M) :
    groupStateMass P modulus M V *
      groupEdgeScalar P modulus M q V shared x z =
    ∏ g : G,
      (haarAtomMass (modulus g) *
       (1 / (V g) ^ (M + unsharedSlots M (shared g))) *
       endpointDamping (modulus g) M q (x g) *
       endpointDamping (modulus g) M q (z g)) := by
  unfold groupStateMass groupEdgeScalar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  exact joint_small_normalization (modulus g) M q (V g)
    (shared g) (x g) (z g)

/-- The full finite small-group physical joint measure respects the
source adjoint's orientation reversal, including an arbitrary
complex multiplier K with the right conjugate. -/
theorem groupJointDetailedBalance
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (x z : GroupState P modulus M) :
    (groupStateMass P modulus M V : ℂ) *
      groupEdgeKernel P modulus M q V shared step K x z =
    (groupStateMass P modulus M V : ℂ) *
      star (groupEdgeKernel P modulus M q V shared (-step) (star K) z x) := by
  rw [groupEdgeKernel_reverse]

end Green64SmallHaar

end

/-! ## GroupSmallHilbert -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Type) [∀ g, Fintype (P g)]
variable [∀ g, DecidableEq (P g)]
variable (modulus : (g : G) → P g → ℕ)
variable [∀ g, ∀ p, NeZero (modulus g p)]
variable (M : ℕ)

/-- The finite Hilbert small-torus/mark tensor inner product using
the TRUE product Haar probability and independent V_g^-M
small-state masses. These are not big-group Fock sector weights. -/
noncomputable def groupSmallInner (V : G → ℝ)
    (F H : GroupState P modulus M → ℂ) : ℂ :=
  ∑ x : GroupState P modulus M,
    (groupStateMass P modulus M V : ℂ) * star (F x) * H x

/-- The actual finite physical E step for ALL small groups with one
sampled pattern family, one common Delta, and ONE complex multiplier K. -/
noncomputable def groupSmallEdgeAct
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (H : GroupState P modulus M → ℂ)
    (x : GroupState P modulus M) : ℂ :=
  ∑ z : GroupState P modulus M,
    groupEdgeKernel P modulus M q V shared step K x z * H z

/-- TRUE finite weighted Hilbert adjoint of the combined small-group
physical E kernel. Reversal swaps all endpoint mark lists and translates
every Haar coordinate by -Delta, while complex K is conjugated and
the exact source measure ∏_g V_g^{-M-t_g} is retained. -/
theorem groupSmallEdgeAct_adjoint
    (q : ℝ) (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (step : ℤ) (K : ℂ)
    (F H : GroupState P modulus M → ℂ) :
    groupSmallInner P modulus M V F
        (groupSmallEdgeAct P modulus M q V shared step K H) =
      groupSmallInner P modulus M V
        (groupSmallEdgeAct P modulus M q V shared (-step) (star K) F)
          H := by
  let W : ℂ := (groupStateMass P modulus M V : ℂ)
  let A : GroupState P modulus M → GroupState P modulus M → ℂ :=
    groupEdgeKernel P modulus M q V shared step K
  let B : GroupState P modulus M → GroupState P modulus M → ℂ :=
    groupEdgeKernel P modulus M q V shared (-step) (star K)
  have hpair (x z : GroupState P modulus M) :
      W * star (F x) * (A x z * H z) =
      W * star (B z x * F x) * H z := by
    have hker := groupEdgeKernel_reverse P modulus M q V shared step K x z
    change A x z = star (B z x) at hker
    rw [hker,star_mul]
    ring
  have hleft :
      groupSmallInner P modulus M V F
          (groupSmallEdgeAct P modulus M q V shared step K H) =
        ∑ x : GroupState P modulus M,
          ∑ z : GroupState P modulus M,
            W * star (F x) * (A x z * H z) := by
    unfold groupSmallInner groupSmallEdgeAct
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  have hright :
      groupSmallInner P modulus M V
        (groupSmallEdgeAct P modulus M q V shared (-step) (star K) F) H =
        ∑ z : GroupState P modulus M,
          ∑ x : GroupState P modulus M,
            W * star (B z x * F x) * H z := by
    unfold groupSmallInner groupSmallEdgeAct
    apply Finset.sum_congr rfl
    intro z hz
    rw [star_sum]
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
  calc
    groupSmallInner P modulus M V F
      (groupSmallEdgeAct P modulus M q V shared step K H) =
        ∑ x : GroupState P modulus M,
          ∑ z : GroupState P modulus M,
            W * star (F x) * (A x z * H z) := hleft
    _ = ∑ z : GroupState P modulus M,
          ∑ x : GroupState P modulus M,
            W * star (F x) * (A x z * H z) :=
          Finset.sum_comm
    _ = ∑ z : GroupState P modulus M,
          ∑ x : GroupState P modulus M,
            W * star (B z x * F x) * H z := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair x z
    _ = groupSmallInner P modulus M V
        (groupSmallEdgeAct P modulus M q V shared (-step) (star K) F) H :=
          hright.symm

/-- The exact original q exponent can be read from every group of
the physical E kernel, not an unspecified damping multiplier. -/
theorem groupEdgeScalar_eq_source_rpow (q : ℝ) (hq : 0 ≤ q)
    (V : G → ℝ)
    (shared : (g : G) → Finset (Fin M))
    (x z : GroupState P modulus M) :
    groupEdgeScalar P modulus M q V shared x z =
      ∏ g : G,
        (1 / (V g ^ (unsharedSlots M (shared g)))) *
        (q ^ (((omega (modulus g) (residues (modulus g) M (x g)) - M : ℕ) : ℝ)/2)) *
        (q ^ (((omega (modulus g) (residues (modulus g) M (z g)) - M : ℕ) : ℝ)/2)) := by
  unfold groupEdgeScalar
  apply Finset.prod_congr rfl
  intro g hg
  unfold edgeScalar
  rw [endpointDamping_eq_source_rpow (modulus g) M q hq (x g),
      endpointDamping_eq_source_rpow (modulus g) M q hq (z g)]

end Green64SmallHaar

end

/-! ## GroupHaarTorus -/

section

open Classical
open scoped BigOperators

namespace Green64SmallHaar

variable {G : Type} [Fintype G] [DecidableEq G]
variable (P : G → Type) [∀ g, Fintype (P g)]
variable [∀ g, DecidableEq (P g)]
variable (modulus : (g : G) → P g → ℕ)
variable [∀ g, ∀ p, NeZero (modulus g p)]

/-- The exact original TOTAL small Haar torus
Y_S = ∏_{g∈small groups} ∏_{p∈P_g} Z/pZ. -/
abbrev GroupTorus :=
  (g : G) → SmallTorus (modulus g)

noncomputable instance : Fintype (GroupTorus P modulus) := by
  classical
  unfold GroupTorus
  infer_instance

instance : Nonempty (GroupTorus P modulus) :=
  ⟨fun g p => 0⟩

/-- The entire group collection is shifted by ONE integer Delta,
applied to each actual modular residue. -/
def groupTranslate (step : ℤ)
    (y : GroupTorus P modulus) : GroupTorus P modulus :=
  fun g => translate (modulus g) step (y g)

def groupTranslateEquiv (step : ℤ) :
    GroupTorus P modulus ≃ GroupTorus P modulus where
  toFun := groupTranslate P modulus step
  invFun := groupTranslate P modulus (-step)
  left_inv := by
    intro y
    funext g
    exact translate_neg (modulus g) step (y g)
  right_inv := by
    intro y
    funext g
    exact translate_back (modulus g) step (y g)

/-- Product of the TRUE per-group Haar probability atoms. -/
noncomputable def groupHaarMass : ℝ :=
  ∏ g : G, haarAtomMass (modulus g)

theorem groupHaarMass_positive :
    0 < groupHaarMass P modulus := by
  unfold groupHaarMass
  apply Finset.prod_pos
  intro g hg
  exact haarAtomMass_positive (modulus g)

/-- The independent-group Haar mass equals the unique uniform mass
on the ENTIRE finite torus. This rules out an extra factor p, 1/p
or factorial from tensoring small groups. -/
theorem groupHaarMass_eq_card :
    groupHaarMass P modulus =
      1 / (Fintype.card (GroupTorus P modulus) : ℝ) := by
  unfold groupHaarMass haarAtomMass
  have hcard : Fintype.card (GroupTorus P modulus) =
      ∏ g : G, Fintype.card (SmallTorus (modulus g)) := by
    exact Fintype.card_pi
  rw [hcard]
  push_cast
  simp only [one_div, Finset.prod_inv_distrib]

/-- Exact true Haar average on every small-prime residue coordinate
of every group, not just a row coefficient name. -/
noncomputable def groupHaarIntegral
    (F : GroupTorus P modulus → ℂ) : ℂ :=
  ∑ y : GroupTorus P modulus, (groupHaarMass P modulus : ℂ) * F y

theorem groupHaarIntegral_one :
    groupHaarIntegral P modulus (fun _ => (1:ℂ)) = 1 := by
  unfold groupHaarIntegral
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [groupHaarMass_eq_card]
  have hn : (Fintype.card (GroupTorus P modulus) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr
      (⟨fun g p => 0⟩ : Nonempty (GroupTorus P modulus))).ne'
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  field_simp [hn]

/-- Physical translation of the FULL finite small-prime torus
preserves the product Haar probability exactly. -/
theorem groupHaarIntegral_translate (step : ℤ)
    (F : GroupTorus P modulus → ℂ) :
    groupHaarIntegral P modulus
      (fun y => F (groupTranslate P modulus step y)) =
        groupHaarIntegral P modulus F := by
  unfold groupHaarIntegral
  have he := Equiv.sum_comp (groupTranslateEquiv P modulus step)
     (fun y => (groupHaarMass P modulus : ℂ) * F y)
  simpa [groupTranslateEquiv] using he

end Green64SmallHaar

end

/-! ## MemoryCleanFrozenResidueFourier -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Exact residual torus after freezing ALL genuine BIG prime labels
and ORIGINAL indexed OLD memory sector lengths. Repetitions remain
as separate coordinates with independent counting residue variables. -/
abbrev memoryFrozenResidueGroup
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g) :=
  Green64SmallHaar.GroupTorus SP smallMod ×
    ((g : BG) → (i : Fin (sizes g)) → ZMod (bigMod g (prime g i)))

/-- A single physical integer displacement affects EVERY SMALL Haar
coordinate and EVERY indexed BIG memory residue. -/
def memoryFrozenResidueShift
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (step : ℤ) :
    memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime :=
  (fun g p => (step : ZMod (smallMod g p)),
   fun g i => (step : ZMod (bigMod g (prime g i))))

/-- The actual simultaneous physical clean translation is group
addition by the above frozen-prime displacement. -/
theorem memory_frozen_residue_actual_translate
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (step : ℤ)
    (x : memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime) :
    x + memoryFrozenResidueShift SP smallMod BP bigMod sizes prime step =
    (Green64SmallHaar.groupTranslate SP smallMod step x.1,
      fun g i => x.2 g i +
        (step : ZMod (bigMod g (prime g i)))) := rfl
/-- All characters of the ORIGINAL full SMALL×BIG frozen residue
group form a complete basis, including repeated prime labels. -/
theorem memory_frozen_residue_full_fourier_expansion
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (f : memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime → ℂ) :
    (∑ ψ : AddChar (memoryFrozenResidueGroup SP smallMod
        BP bigMod sizes prime) ℂ,
       ((AddChar.complexBasis
          (memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime)).repr f ψ) •
       (ψ : memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime → ℂ)) =
    f := by
  simpa only [AddChar.complexBasis_apply] using
    (AddChar.complexBasis (memoryFrozenResidueGroup SP smallMod
      BP bigMod sizes prime)).sum_repr f

/-- Every frequency sees the exact physical clean displacement as
a scalar phase of modulus ONE. -/
theorem memory_frozen_residue_full_fourier_eigen
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (step : ℤ)
    (ψ : AddChar (memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime) ℂ)
    (x : memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime) :
    ψ (x + memoryFrozenResidueShift SP smallMod BP bigMod
       sizes prime step) =
      ψ x * ψ (memoryFrozenResidueShift SP smallMod BP bigMod
       sizes prime step) := AddChar.map_add_eq_mul ψ _ _
end Green64FullPhysicalE

end

end

/-! ## MemoryCleanFrozenFourierShift -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- Every frozen physical SMALL×BIG Fourier mode sees exactly
one unit-modulus scalar of the true output-frozen residue shift. -/
theorem memory_frozen_full_fourier_phase_norm_one
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (step : ℤ)
    (ψ : AddChar (memoryFrozenResidueGroup SP smallMod BP bigMod
        sizes prime) ℂ) :
    ‖ψ (memoryFrozenResidueShift SP smallMod BP bigMod
       sizes prime step)‖ = 1 := ψ.norm_apply _

/-- Complete Fourier expansion of the ACTUAL simultaneous residue
translation (SMALL Haar and BIG counting residues). It does not
replace the existing physical active-prime transition. -/
theorem memory_frozen_full_residue_fourier_shift_formula
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (step : ℤ)
    (f : memoryFrozenResidueGroup SP smallMod BP bigMod
        sizes prime → ℂ)
    (x : memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime) :
    let G := memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime
    let δ := memoryFrozenResidueShift SP smallMod BP bigMod sizes prime step
    f (x + δ) =
      ∑ ψ : AddChar G ℂ,
        (AddChar.complexBasis G).repr f ψ * ψ x * ψ δ := by
  dsimp only
  let G := memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime
  let δ := memoryFrozenResidueShift SP smallMod BP bigMod sizes prime step
  have h := congrFun (memory_frozen_residue_full_fourier_expansion
      SP smallMod BP bigMod sizes prime f) (x + δ)
  calc
    f (x + δ) =
      ∑ ψ : AddChar G ℂ,
        (AddChar.complexBasis G).repr f ψ * ψ (x + δ) := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
    _ = ∑ ψ : AddChar G ℂ,
        (AddChar.complexBasis G).repr f ψ * ψ x * ψ δ := by
      apply Finset.sum_congr rfl; intro ψ _
      rw [AddChar.map_add_eq_mul]
      ring
end Green64FullPhysicalE

end

end

/-! ## MemoryCleanFrozenAngle -/

section

open Classical
open scoped BigOperators
noncomputable section
namespace Green64FullPhysicalE
set_option maxHeartbeats 0

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]

/-- A genuine integer physical displacement is the integer multiple
of the ONE-step displacement, in all SMALL/BIG residue coordinates. -/
theorem memory_frozen_residue_shift_int_multiple
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (step : ℤ) :
    memoryFrozenResidueShift SP smallMod BP bigMod sizes prime step =
      step • memoryFrozenResidueShift SP smallMod BP bigMod sizes prime 1 := by
  apply Prod.ext
  · funext g p
    simp [memoryFrozenResidueShift]
  · funext g i
    simp [memoryFrozenResidueShift]
/-- For the real source residue product, each Fourier mode is an
exponential character of the SAME original integer displacement.
The angle is fixed once the memory prime list and mode are frozen. -/
theorem memory_frozen_residue_character_real_angle
    (sizes : BG → ℕ)
    (prime : (g : BG) → Fin (sizes g) → BP g)
    (ψ : AddChar (memoryFrozenResidueGroup SP smallMod BP bigMod
      sizes prime) ℂ) :
    ∃ θ : ℝ, ∀ step : ℤ,
      ψ (memoryFrozenResidueShift SP smallMod BP bigMod sizes prime step) =
        Complex.exp (((step : ℝ) * θ : ℝ) * Complex.I) := by
  let a := ψ (memoryFrozenResidueShift SP smallMod BP bigMod sizes prime 1)
  have hn : ‖a‖ = 1 := ψ.norm_apply _
  obtain ⟨θ,hθ⟩ := (Complex.norm_eq_one_iff a).mp hn
  refine ⟨θ, ?_⟩
  intro step
  rw [memory_frozen_residue_shift_int_multiple]
  rw [AddChar.map_zsmul_eq_zpow]
  change a ^ step = _
  rw [← hθ, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring
end Green64FullPhysicalE

end

end

