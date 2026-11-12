module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic
public import Green64.Library.Sieve.Foundations.ExactMertens
public import Mathlib

@[expose] public section

/-!
# Weights / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## ElementaryRates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Fixed coefficients are absorbed by any strictly larger positive-scale
power. This lemma never changes the source moment exponent. -/
theorem b638_eventually_const_power434 (C a b : ℝ) (hab : a<b) :
    ∀ᶠ L : ℝ in atTop, C*L^a ≤ L^b := by
  have hc : ∀ᶠ L : ℝ in atTop, C ≤ L^(b-a) :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop C)
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with L hc hL
  calc
    _ ≤ L^(b-a)*L^a := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le _)
    _ = _ := by rw [←Real.rpow_add hL]; congr 1; ring

/-- A complete eventual log-power estimate with the constant chosen before L. -/
theorem b638_eventually_log_power434 (C a b : ℝ) (hC : 0≤C) (hab : a<b) :
    ∀ᶠ L : ℝ in atTop, C*L^a*Real.log L ≤ L^b := by
  let d : ℝ := (b-a)/2
  have hd : 0<d := by dsimp [d]; linarith
  have hc : ∀ᶠ L : ℝ in atTop, C/d ≤ L^d :=
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop (C/d))
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with L hc hL
  have hl := Real.log_le_rpow_div hL.le hd
  calc
    _ ≤ C*L^a*(L^d/d) :=
      mul_le_mul_of_nonneg_left hl (mul_nonneg hC (Real.rpow_nonneg hL.le _))
    _ = (C/d)*L^a*L^d := by ring
    _ ≤ L^d*L^a*L^d := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le _))
        (Real.rpow_nonneg hL.le _)
    _ = L^b := by
      rw [←Real.rpow_add hL,←Real.rpow_add hL]
      congr 1
      dsimp [d]
      ring

/-- Polynomial quantities are dominated by the ACTUAL prime lower
exponential scale; no restriction to a cofinal subsequence is used. -/
theorem b638_eventually_poly_exp434 (C a b : ℝ) (hC : 0<C) (hb : 0<b) :
    ∀ᶠ L : ℝ in atTop, C*L^a ≤ Real.exp (L^b) := by
  let D : ℝ := max 0 (Real.log C)+max 0 a
  have hD : 0≤D := add_nonneg (le_max_left _ _) (le_max_left _ _)
  filter_upwards [b638_eventually_log_power434 D 0 b hD hb,
    eventually_ge_atTop (Real.exp 1)] with L hh hL
  have hLp : 0<L := (Real.exp_pos _).trans_le hL
  have hl : 1≤Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    simpa only [Real.log_exp] using h
  have h1 : Real.log C ≤ max 0 (Real.log C)*Real.log L := by
    have hm := mul_le_mul_of_nonneg_left hl (le_max_left 0 (Real.log C))
    nlinarith [le_max_right 0 (Real.log C)]
  have h2 : a*Real.log L ≤ max 0 a*Real.log L :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hbnd : Real.log C+a*Real.log L ≤ L^b := by
    simp only [Real.rpow_zero,mul_one] at hh
    dsimp [D] at hh
    nlinarith
  calc
    _ = Real.exp (Real.log C+a*Real.log L) := by
      rw [Real.exp_add,Real.exp_log hC,Real.rpow_def_of_pos hLp]
      congr 1
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hbnd

/-- The literal source N=2 ceil(L^.52), and the chosen finite Bonferroni
order K=ceil(L^.55). The larger sieve order still has K L^.4=o(L). -/
theorem b638_moment_and_order434 (L : ℝ) (hL : 1≤L) :
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    let K := Nat.ceil (L^(11/20:ℝ))
    1≤N ∧ (N:ℝ) ≤ 4*L^(13/25:ℝ) ∧
    ((N+1:ℕ):ℝ) ≤ 5*L^(13/25:ℝ) ∧
    2*L^(11/20:ℝ) ≤ ((2*K+1:ℕ):ℝ) ∧
    ((2*K+1:ℕ):ℝ) ≤ 5*L^(11/20:ℝ) ∧
    ((2*K+2:ℕ):ℝ) ≤ 6*L^(11/20:ℝ) := by
  dsimp only
  have hn1 := Real.one_le_rpow hL (by norm_num : (0:ℝ)≤13/25)
  have hk1 := Real.one_le_rpow hL (by norm_num : (0:ℝ)≤11/20)
  have hnlo := Nat.le_ceil (L^(13/25:ℝ))
  have hklo := Nat.le_ceil (L^(11/20:ℝ))
  have hnhi := (Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hL) (13/25:ℝ))).le
  have hkhi := (Nat.ceil_lt_add_one (Real.rpow_nonneg (zero_le_one.trans hL) (11/20:ℝ))).le
  have hn : 1 ≤ 2*Nat.ceil (L^(13/25:ℝ)) := by
    have hr : (1:ℝ) ≤ (2*Nat.ceil (L^(13/25:ℝ)):ℕ) := by push_cast; linarith
    exact_mod_cast hr
  refine ⟨hn,?_,?_,?_,?_,?_⟩ <;> push_cast <;> linarith
end Green64Analytic.SourceBlockSieve

end

end

/-! ## RelativeCRTRates -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Both COMPLETE terms in the relative physical CRT bound are smaller
than exp(-A*N*log L), with N the original 2 ceil(L^.52). Constants precede
L and the finite path; no desired saving is assumed. The auxiliary
Bonferroni order is ceil(L^.55), still strictly below the exponential
counting threshold because .55+.4<1. -/
theorem b638_eventually_relative_CRT_rate434
    (C Cq A gamma : ℝ) (hC : 0≤C) (hCq : 0≤Cq)
    (hA : 0≤A) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    let K := Nat.ceil (L^(11/20:ℝ))
    1≤L ∧ 5*L^(13/25:ℝ) ≤ Real.exp (L^(1/10:ℝ))/2 ∧
    ∀ lam U Q H : ℝ,
      0≤lam → lam ≤ C*((N+1:ℕ):ℝ)*Real.log L →
      1≤U → U ≤ 1+((N+1:ℕ):ℝ)*Real.exp (L^(2/5:ℝ)) →
      0≤Q → Q ≤ Real.exp (Cq*((N+1:ℕ):ℝ)*Real.log L*L^(2/5:ℝ)) →
      Real.exp (gamma*L) ≤ H →
      Real.exp (4*lam)/(2:ℝ)^(2*K+1) +
        (Q/H)*2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1)*Real.exp (2*lam) ≤
          Real.exp (-A*(N:ℝ)*Real.log L) := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let D1 : ℝ := (20*C+4*A+1)/(Real.log 2)
  let D2 : ℝ := (5*Cq+11+10*C+4*A+1)/gamma
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    b638_eventually_log_power434 1 0 (1/100) (by norm_num) (by norm_num),
    b638_eventually_poly_exp434 10 (13/25) (1/10) (by norm_num) (by norm_num),
    b638_eventually_poly_exp434 6 (13/25) (2/5) (by norm_num) (by norm_num),
    b638_eventually_poly_exp434 (12*Real.exp 1) (11/20) (2/5) (by positivity) (by norm_num),
    b638_eventually_const_power434 D1 (53/100) (11/20) (by norm_num),
    b638_eventually_const_power434 D2 (19/20) 1 (by norm_num)]
    with L hLarge hLog hHalf hUscale hPref hTailRate hCountRate
  dsimp only
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  let K := Nat.ceil (L^(11/20:ℝ))
  have hL : 1≤L := (Real.one_le_exp (by norm_num)).trans hLarge
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hl : 0≤Real.log L := Real.log_nonneg hL
  simp only [Real.rpow_zero,one_mul] at hLog
  have hn := b638_moment_and_order434 L hL
  change 1≤N ∧ (N:ℝ) ≤ 4*L^(13/25:ℝ) ∧
    ((N+1:ℕ):ℝ) ≤ 5*L^(13/25:ℝ) ∧
    2*L^(11/20:ℝ) ≤ ((2*K+1:ℕ):ℝ) ∧
    ((2*K+1:ℕ):ℝ) ≤ 5*L^(11/20:ℝ) ∧
    ((2*K+2:ℕ):ℝ) ≤ 6*L^(11/20:ℝ) at hn
  refine ⟨hL,by linarith,?_⟩
  intro lam U Q H hlam0 hlam hU1 hU hQ0 hQ hH
  have hHp : 0<H := (Real.exp_pos _).trans_le hH
  have hNlog : (N:ℝ)*Real.log L ≤ 4*L^(53/100:ℝ) := by
    calc
      _ ≤ (4*L^(13/25:ℝ))*L^(1/100:ℝ) :=
        mul_le_mul hn.2.1 hLog hl (by positivity)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hLp]; norm_num
  have hVlog : ((N+1:ℕ):ℝ)*Real.log L ≤ 5*L^(53/100:ℝ) := by
    calc
      _ ≤ (5*L^(13/25:ℝ))*L^(1/100:ℝ) :=
        mul_le_mul hn.2.2.1 hLog hl (by positivity)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hLp]; norm_num
  have hlam53 : lam ≤ 5*C*L^(53/100:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hVlog hC
    nlinarith only [hh,hlam]
  have hTarget53 : A*(N:ℝ)*Real.log L ≤ 4*A*L^(53/100:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hNlog hA
    nlinarith only [hh]
  have h5395 : L^(53/100:ℝ) ≤ L^(19/20:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h4095 : L^(2/5:ℝ) ≤ L^(19/20:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hlam95 : lam ≤ 5*C*L^(19/20:ℝ) :=
    hlam53.trans (mul_le_mul_of_nonneg_left h5395 (by positivity))
  have hTarget95 : A*(N:ℝ)*Real.log L ≤ 4*A*L^(19/20:ℝ) :=
    hTarget53.trans (mul_le_mul_of_nonneg_left h5395 (by positivity))
  have hlog253 : Real.log 2 ≤ L^(53/100:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    exact (show Real.log 2 ≤ 1 by linarith).trans (Real.one_le_rpow hL (by norm_num))
  have hlog295 := hlog253.trans h5395
  have hTailCoef : (20*C+4*A+1)*L^(53/100:ℝ) ≤ Real.log 2*L^(11/20:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hTailRate hlog2.le
    dsimp [D1] at hh
    have he : ((20*C+4*A+1)/Real.log 2)*L^(53/100:ℝ)*Real.log 2 =
        (20*C+4*A+1)*L^(53/100:ℝ) := by field_simp
    rw [he] at hh
    nlinarith only [hh]
  have hTailExponent : 4*lam+A*(N:ℝ)*Real.log L+Real.log 2 ≤
      ((2*K+1:ℕ):ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hn.2.2.2.1 hlog2.le
    have hp : 0≤Real.log 2*L^(11/20:ℝ) := by positivity
    nlinarith only [hlam53,hTarget53,hlog253,hTailCoef,hh,hp]
  have hTail : Real.exp (4*lam)/(2:ℝ)^(2*K+1) ≤
      Real.exp (-A*(N:ℝ)*Real.log L-Real.log 2) := by
    have hpow : (2:ℝ)^(2*K+1) = Real.exp (((2*K+1:ℕ):ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [hpow,←Real.exp_sub]
    exact Real.exp_le_exp.mpr (by linarith)
  have hP1 : 1 ≤ L^(13/25:ℝ)*Real.exp (L^(2/5:ℝ)) := by
    apply one_le_mul_of_one_le_of_one_le
    · exact Real.one_le_rpow hL (by norm_num)
    · exact Real.one_le_exp (Real.rpow_nonneg hLp.le _)
  have hUexp : U ≤ Real.exp (2*L^(2/5:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hn.2.2.1 (Real.exp_nonneg (L^(2/5:ℝ)))
    calc
      U ≤ 6*L^(13/25:ℝ)*Real.exp (L^(2/5:ℝ)) := by nlinarith only [hU,hh,hP1]
      _ ≤ Real.exp (L^(2/5:ℝ))*Real.exp (L^(2/5:ℝ)) :=
        mul_le_mul_of_nonneg_right hUscale (Real.exp_nonneg _)
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hUpow : U^(2*K+1) ≤ Real.exp (10*L^(19/20:ℝ)) := by
    calc
      _ ≤ (Real.exp (2*L^(2/5:ℝ)))^(2*K+1) :=
        pow_le_pow_left₀ (by linarith) hUexp _
      _ = Real.exp (((2*K+1:ℕ):ℝ)*(2*L^(2/5:ℝ))) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (5*L^(11/20:ℝ))*(2*L^(2/5:ℝ)) :=
            mul_le_mul_of_nonneg_right hn.2.2.2.2.1 (by positivity)
          _ = _ := by
            have he : L^(11/20:ℝ)*L^(2/5:ℝ)=L^(19/20:ℝ) := by rw [←Real.rpow_add hLp]; norm_num
            nlinarith only [he]
  have hCountPref : 2*((2*K+2:ℕ):ℝ)*Real.exp 1 ≤ Real.exp (L^(2/5:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hn.2.2.2.2.2 (Real.exp_nonneg 1)
    have hh' : 2*((2*K+2:ℕ):ℝ)*Real.exp 1 ≤ (12*Real.exp 1)*L^(11/20:ℝ) := by
      nlinarith only [hh]
    exact hh'.trans hPref
  have hCount : 2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1) ≤
      Real.exp (11*L^(19/20:ℝ)) := by
    calc
      _ ≤ Real.exp (L^(2/5:ℝ))*Real.exp (10*L^(19/20:ℝ)) :=
        mul_le_mul hCountPref hUpow (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (L^(2/5:ℝ)+10*L^(19/20:ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hQBudget : Cq*((N+1:ℕ):ℝ)*Real.log L*L^(2/5:ℝ) ≤
      5*Cq*L^(19/20:ℝ) := by
    calc
      _ ≤ (5*Cq*L^(53/100:ℝ))*L^(2/5:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLp.le _)
        have hh := mul_le_mul_of_nonneg_left hVlog hCq
        nlinarith only [hh]
      _ = 5*Cq*L^(93/100:ℝ) := by rw [mul_assoc,←Real.rpow_add hLp]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (by positivity)
  have hQ95 := hQ.trans (Real.exp_le_exp.mpr hQBudget)
  have hQH : Q/H ≤ Real.exp (5*Cq*L^(19/20:ℝ)-gamma*L) := by
    apply (div_le_iff₀ hHp).mpr
    have hh := mul_le_mul_of_nonneg_left hH
      (Real.exp_nonneg (5*Cq*L^(19/20:ℝ)-gamma*L))
    rw [←Real.exp_add] at hh
    have he : 5*Cq*L^(19/20:ℝ)-gamma*L+gamma*L=5*Cq*L^(19/20:ℝ) := by ring
    rw [he] at hh
    exact hQ95.trans hh
  have hCountCoef : (5*Cq+11+10*C+4*A+1)*L^(19/20:ℝ) ≤ gamma*L := by
    have hh := mul_le_mul_of_nonneg_right hCountRate hgamma.le
    dsimp [D2] at hh
    rw [Real.rpow_one] at hh
    have he : ((5*Cq+11+10*C+4*A+1)/gamma)*L^(19/20:ℝ)*gamma =
        (5*Cq+11+10*C+4*A+1)*L^(19/20:ℝ) := by field_simp
    rw [he] at hh
    nlinarith only [hh]
  have hCRT : (Q/H)*2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1)*Real.exp (2*lam) ≤
      Real.exp (-A*(N:ℝ)*Real.log L-Real.log 2) := by
    have hh := mul_le_mul hQH hCount (by positivity) (Real.exp_nonneg _)
    have hh' := mul_le_mul hh (Real.exp_le_exp.mpr (show 2*lam≤10*C*L^(19/20:ℝ) by linarith))
      (Real.exp_nonneg _) (by positivity)
    calc
      _ ≤ (Real.exp (5*Cq*L^(19/20:ℝ)-gamma*L)*Real.exp (11*L^(19/20:ℝ)))*
          Real.exp (10*C*L^(19/20:ℝ)) := by
        convert hh' using 1
        ring
      _ = Real.exp ((5*Cq+11+10*C)*L^(19/20:ℝ)-gamma*L) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hCountCoef,hTarget95,hlog295])
  have heps : Real.exp (-A*(N:ℝ)*Real.log L-Real.log 2)+
      Real.exp (-A*(N:ℝ)*Real.log L-Real.log 2) = Real.exp (-A*(N:ℝ)*Real.log L) := by
    rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)]
    ring
  exact (add_le_add hTail hCRT).trans_eq heps
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ExactEulerProduct -/

section

open Filter Finset
open scoped Classical

namespace Chen

/-- Euler's prime product at a natural cutoff. -/
noncomputable def primeEulerProduct (y : ℕ) : ℝ :=
  ∏ p ∈ y.primesLE, (1 - (1 : ℝ) / p)

theorem primeEulerProduct_eq_Ioc (y : ℕ) :
    primeEulerProduct y = ∏ p ∈ Ioc 0 y with p.Prime, (1 - (1 : ℝ) / p) := by
  apply prod_congr
  · ext p
    simp only [Nat.mem_primesLE, mem_filter, mem_Ioc]
    exact ⟨fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  · intro p _; rfl

/-- Mertens' third theorem with its exact exponential remainder, obtained
from the locally included proof. -/
theorem primeEulerProduct_eq (y : ℕ) (hy : 1 < y) :
    primeEulerProduct y = Real.exp (-Real.eulerMascheroniConstant) *
      Real.exp (Mertens.E₃ y) / Real.log y := by
  rw [primeEulerProduct_eq_Ioc]
  simpa only [Nat.floor_natCast] using
    Mertens.prod_one_minus_div_prime_eq (x := (y : ℝ)) (by exact_mod_cast hy)

/-- The normalization used in the one-dimensional sieve product. -/
theorem primeEulerProduct_mul_log_tendsto :
    Tendsto (fun y : ℕ => primeEulerProduct y * Real.log y) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hE : Tendsto Mertens.E₃ atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have hlim := (tendsto_const_nhds (x := Real.exp (-Real.eulerMascheroniConstant))).mul
    ((hE.comp tendsto_natCast_atTop_atTop).rexp)
  simp only [Real.exp_zero, mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with y hy
  have hlog : Real.log (y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < y by omega)))
  rw [primeEulerProduct_eq y (by omega), div_mul_cancel₀ _ hlog]
  rfl

end Chen

end

/-! ## PositiveSpectralMoment -/

section

open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
namespace Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Exact diagonal action of every natural power of a positive operator.
No normalization of the argument vector is imposed. -/
theorem b649_positive_power_coordinates434
    (B : E →ₗ[ℂ] E) (hB : B.IsPositive) (R : ℕ) (f : E)
    (i : Fin (Module.finrank ℂ E)) :
    (hB.isSymmetric.eigenvectorBasis rfl).repr ((B^R) f) i =
      (hB.isSymmetric.eigenvalues rfl i : ℂ)^R *
        (hB.isSymmetric.eigenvectorBasis rfl).repr f i := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [pow_succ', Module.End.mul_apply,
      hB.isSymmetric.eigenvectorBasis_apply_self_apply rfl, ih, pow_succ']
    simp only [RCLike.ofReal_eq_complex_ofReal, mul_assoc]

/-- The literal quadratic moment, with the actual coordinates of f and
all nonnegative eigenvalues. No equal-norm or orthogonality premise on
any later physical root vectors is hidden in this identity. -/
theorem b649_positive_power_spectral_moment434
    (B : E →ₗ[ℂ] E) (hB : B.IsPositive) (R : ℕ) (f : E) :
    (inner ℂ f ((B^R) f)).re =
      ∑ i : Fin (Module.finrank ℂ E),
        ‖inner ℂ (hB.isSymmetric.eigenvectorBasis rfl i) f‖^2 *
          (hB.isSymmetric.eigenvalues rfl i)^R := by
  let v := hB.isSymmetric.eigenvectorBasis (rfl : Module.finrank ℂ E = _)
  rw [← v.sum_inner_mul_inner f ((B^R) f), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc := b649_positive_power_coordinates434 B hB R f i
  have hi : inner ℂ (v i) ((B^R) f) =
      (hB.isSymmetric.eigenvalues rfl i : ℂ)^R * inner ℂ (v i) f := by
    simpa only [OrthonormalBasis.repr_apply_apply, v] using hc
  rw [hi, ← inner_conj_symm f (v i)]
  calc
    _ = (((hB.isSymmetric.eigenvalues rfl i : ℂ)^R) *
        ((starRingEnd ℂ) (inner ℂ (v i) f) * inner ℂ (v i) f)).re := by
      congr 1
      ring
    _ = _ := by
      rw [Complex.conj_mul']
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact mul_comm _ _

/-- Every natural power is genuinely positive; no spectral bound is a premise. -/
theorem b649_positive_power434
    (B : E →ₗ[ℂ] E) (hB : B.IsPositive) (R : ℕ) : (B^R).IsPositive := by
  refine ⟨hB.isSymmetric.pow R, fun f => ?_⟩
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ f ((B^R) f)).re
  rw [b649_positive_power_spectral_moment434 B hB R f]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (sq_nonneg _) (pow_nonneg (hB.nonneg_eigenvalues rfl i) R)
end Green64Analytic.SpectralEndpoint

end

end

