module

public import Green64.Library.Weights.Part051
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Green64.Library.Correlation.Part038
public import Green64.Library.Correlation.Part039
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part014
public import Green64.Library.Weights.Part018
public import Green64.Library.Analysis.Estimates.Part002
public import Green64.Library.Weights.Part015

@[expose] public section

/-!
# Weights / Part052

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalLocalArcBetaDyads -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- In the ORIGINAL proof's physical dyad pair
X_A∈[U,2U], X_B∈[V,2V], Dirichlet approximation yields
|beta| *Hprime ≤ 2S/r for Hprime=U*V and denominator r≥1.
The GENUINE local GLOBAL cell cap then implies
2π|beta| *Rcell ≤ 192*S, uniformly in the ACTUAL retained
indices (jA,jB), without any coarse global
exp((m_A+m_B)*L^d) loss. -/
theorem source_original_local_arc_beta_dyadic_cost434
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V S beta : ℝ) (r : ℕ)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hXA : (XA:ℝ) ≤ 2*U)
    (hXB : (XB:ℝ) ≤ 2*V)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hW : hA+hB ≤ 1)
    (hS : 0 ≤ S)
    (hr : 0 < r)
    (hDir : |beta| *(U*V) ≤ 2*S/(r:ℝ)) :
    2*Real.pi*|beta| *
      Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) ≤
      192*S := by
  let w : ℝ := hA+hB
  let R : ℝ :=
    Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hexp : 0 ≤ Real.exp w := (Real.exp_pos _).le
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hPi : 0 ≤ 2*Real.pi := by positivity
  have hPiMax : 2*Real.pi ≤ 8 := by
    nlinarith [Real.pi_lt_four]
  have hExpBound : Real.exp w ≤ 3 :=
    (Real.exp_le_exp.mpr hW).trans
      (le_of_lt Real.exp_one_lt_three)
  have hDyad : R ≤ 4*Real.exp w*(U*V) :=
    source_original_two_global_local_cell_dyad_cap434
      hA hB jA jB XA XB U V hXAp hXBp hU hV hXA hXB
      hCellA hCellB
  have hDir2 : 2*S/(r:ℝ) ≤ 2*S := by
    apply (div_le_self (by linarith : 0 ≤ 2*S) hr1)
  have hBetaUV : |beta| *(U*V) ≤ 2*S :=
    hDir.trans hDir2
  have hScale :
      |beta| *R ≤ 24*S := by
    calc
      _ ≤ |beta| *(4*Real.exp w*(U*V)) :=
        mul_le_mul_of_nonneg_left hDyad (abs_nonneg _)
      _ = (4*Real.exp w)*(|beta| *(U*V)) := by ring
      _ ≤ (4*Real.exp w)*(2*S) :=
        mul_le_mul_of_nonneg_left hBetaUV (by positivity)
      _ ≤ (4*3)*(2*S) := by
        gcongr
      _ = 24*S := by ring
  have hScaleNN : 0 ≤ 24*S := by positivity
  calc
    _ = (2*Real.pi)*(|beta| *R) := by
      dsimp [R]
      ring
    _ ≤ (2*Real.pi)*(24*S) :=
      mul_le_mul_of_nonneg_left hScale hPi
    _ ≤ 8*(24*S) :=
      mul_le_mul_of_nonneg_right hPiMax hScaleNN
    _ = 192*S := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLocalArcBetaPower -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- The actual SOURCE03 Dirichlet approximation with dyad
scale Hprime=U*V and polynomial S<=L^Cs satisfies the
exact local major-arc beta condition
2π|beta| *Rcell <= L^C4
for ALL retained log-cell indices on a dyad, once
C4>=Cs+1 and L>=192. No coarse global prime-product
scale condition is assumed or needed. -/
theorem source_original_local_arc_beta_uniform_log_power434
    (Cs C4 : ℕ)
    (hA hB : ℝ) (jA jB : ℤ) (XA XB : ℕ)
    (U V S beta L : ℝ) (r : ℕ)
    (hL : 192 ≤ L)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hXA : (XA:ℝ) ≤ 2*U)
    (hXB : (XB:ℝ) ≤ 2*V)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hWidth : hA+hB ≤ 1)
    (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hr : 0 < r)
    (hDir : |beta| *(U*V) ≤ 2*S/(r:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ)) :
    2*Real.pi*|beta| *
      Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) ≤
      L^C4 := by
  have hRaw := source_original_local_arc_beta_dyadic_cost434
    hA hB jA jB XA XB U V S beta r
    hXAp hXBp hU hV hXA hXB
    hCellA hCellB hWidth hS hr hDir
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hScaleNN : 0 ≤ L^Cs := pow_nonneg hLp.le _
  have hConstant : 192*S ≤ L^((Cs:ℝ)+1) := by
    calc
      _ ≤ L*S :=
        mul_le_mul_of_nonneg_right hL hS
      _ ≤ L*(L^Cs) :=
        mul_le_mul_of_nonneg_left hSscale hLp.le
      _ = L^((Cs:ℝ)+1) := by
        conv_rhs => rw [Real.rpow_add hLp]
        simp only [Real.rpow_one, Real.rpow_natCast]
        ring
  have hMonotone : L^((Cs:ℝ)+1) ≤ L^C4 := by
    convert Real.rpow_le_rpow_of_exponent_le hLone hC4 using 1
    rw [Real.rpow_natCast]
  exact hRaw.trans (hConstant.trans hMonotone)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLocalArcMellinLoss -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- TRUE LOCAL original SOURCE03 primitive two-frame
beta/Mellin perturbation saving on EVERY dyadic pair.
Dirichlet's original |beta| *U*V<=2*S/r and
target GLOBAL-cell membership yield the scale Rcell
automatically, so NO global exp(m L^d) scale comparison
hypothesis occurs. Uniform for all |zeta|<=L^C4.
The actual Q^4 primitive-frame loss is absorbed by
the mesh hA+hB<=L^(-(B+4Cq+C4)); S<=L^Cs
with C4>=Cs+1. -/
theorem source_original_local_arc_wide_mellin_loss434
    (Q Cq Cs C4 : ℕ)
    (L B ζ beta hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V S : ℝ) (r : ℕ)
    (hL : 192 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hA+hB ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hXA : (XA:ℝ) ≤ 2*U)
    (hXB : (XB:ℝ) ≤ 2*V)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hr : 0 < r)
    (hDir : |beta| *(U*V) ≤ 2*S/(r:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ)) :
    ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2) *
      ((|ζ|+2*Real.pi*|beta| *
        Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)) *
         (hA+hB)) ≤ 2*L^(-B) := by
  have hBeta := source_original_local_arc_beta_uniform_log_power434
    Cs C4 hA hB jA jB XA XB U V S beta L r
    hL hXAp hXBp hU hV hXA hXB
    hCellA hCellB hWidth1 hS hSscale hr hDir hC4
  have hOne : 1 ≤ L := by linarith
  have hR : 0 ≤ Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) :=
    (Real.exp_pos _).le
  exact source_original_wide_mellin_two_char_loss_absorb434
    Q Cq C4 L B ζ beta
    (Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB))
    hA hB hOne hQ hR
    (add_nonneg hhA.le hhB.le) hWidth hZeta hBeta
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalLocalArcFullBudget -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact original source03 LOCAL dyadic major-arc
comparison error budget: combine the genuine rational
denominator r≤Q cost and true two-primitive-character
Mellin/irrational-beta phase within the actual matched
GLOBAL cells. For |ζ|≤L^C4, |beta|UV≤2S/r,
S≤L^Cs, Q≤L^Cq, and hA+hB≤L^(-(B+4Cq+C4)),
the fully quantitative coefficient is
<= (3K/Vmin+2)L^-B.
Crucially no global Rglobal/Hprime comparability
assumption survives. -/
theorem source_original_local_arc_full_log_power_budget434
    (Q Cq Cs C4 r : ℕ) (L B K Vmin ζ beta : ℝ)
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V S : ℝ)
    (hL : 192 ≤ L) (hQ : (Q:ℝ) ≤ L^Cq)
    (hrQ : r ≤ Q) (hr : 0 < r)
    (hK : 0 ≤ K) (hVmin : 0 < Vmin)
    (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hA+hB ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hXA : (XA:ℝ) ≤ 2*U)
    (hXB : (XB:ℝ) ≤ 2*V)
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hDir : |beta| *(U*V) ≤ 2*S/(r:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ)) :
    let δ : ℝ := (K/Vmin)*L^(-(B+(Cq:ℝ)))
    let Rcell : ℝ :=
      Real.exp (((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB)
    let omega : ℝ := (|ζ|+2*Real.pi*|beta| *Rcell)*(hA+hB)
    ((δ+δ+δ*δ)*(r:ℝ)+
      ((Fintype.card (sourceOriginalPrimitiveFamily434 Q):ℝ)^2)*omega) ≤
        (3*(K/Vmin)+2)*L^(-B) := by
  have hRational :=
    source_original_major_rational_denominator_loss_absorb434
      Q Cq r L B K Vmin (by linarith : 1 ≤ L)
      hQ hrQ hK hVmin hDeltaLe
  have hSlow := source_original_local_arc_wide_mellin_loss434
      Q Cq Cs C4 L B ζ beta hA hB jA jB
      XA XB U V S r hL hQ
      hhA hhB hWidth hWidth1 hZeta
      hXAp hXBp hU hV hXA hXB
      hCellA hCellB hS hSscale hr hDir hC4
  dsimp only at hRational
  dsimp only
  calc
    _ ≤ 3*(K/Vmin)*L^(-B)+2*L^(-B) :=
      add_le_add hRational hSlow
    _ = (3*(K/Vmin)+2)*L^(-B) := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueMovingCellBetaDyad -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Source03's ACTUAL SAME-active-cell local beta bound.
When XA,XB are in their original active GLOBAL product cells
jA,jB, and the true product-dyad lower scales U,V do not
exceed XA,XB, the dyad-product scale is at most
3*Hcell where Hcell=exp(jA*hA+jB*hB), provided hA+hB<=1.
No independent source/target phase factorization, no
coarse exp((#A+#B)*L^d) radius assumption. -/
theorem source_original_true_same_cell_dyad_product_cap434
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V : ℝ)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUX : U ≤ (XA:ℝ)) (hVX : V ≤ (XB:ℝ))
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hWidth : hA+hB ≤ 1) :
    U*V ≤ 3*Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB) := by
  have hpA : (0:ℝ) < (XA:ℝ) := by exact_mod_cast hXAp
  have hpB : (0:ℝ) < (XB:ℝ) := by exact_mod_cast hXBp
  have hXAupper : (XA:ℝ) ≤
      Real.exp (((jA:ℝ)+1)*hA) := by
    calc
      (XA:ℝ) = Real.exp (Real.log (XA:ℝ)) :=
        (Real.exp_log hpA).symm
      _ ≤ Real.exp (((jA:ℝ)+1)*hA) :=
        Real.exp_le_exp.mpr hCellA.2.le
  have hXBupper : (XB:ℝ) ≤
      Real.exp (((jB:ℝ)+1)*hB) := by
    calc
      (XB:ℝ) = Real.exp (Real.log (XB:ℝ)) :=
        (Real.exp_log hpB).symm
      _ ≤ Real.exp (((jB:ℝ)+1)*hB) :=
        Real.exp_le_exp.mpr hCellB.2.le
  have hAU : U ≤ Real.exp (((jA:ℝ)+1)*hA) :=
    hUX.trans hXAupper
  have hBV : V ≤ Real.exp (((jB:ℝ)+1)*hB) :=
    hVX.trans hXBupper
  have hUV :
      U*V ≤ Real.exp (((jA:ℝ)+1)*hA) *
         Real.exp (((jB:ℝ)+1)*hB) :=
    mul_le_mul hAU hBV hV (Real.exp_pos _).le
  have hExpEq :
      Real.exp (((jA:ℝ)+1)*hA) *
        Real.exp (((jB:ℝ)+1)*hB) =
      Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB) *
        Real.exp (hA+hB) := by
    calc
      _ = Real.exp (
        ((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) :=
          (Real.exp_add _ _).symm
      _ = Real.exp (
        ((jA:ℝ)*hA+(jB:ℝ)*hB)+(hA+hB)) := by
          congr 1
          ring
      _ = _ := Real.exp_add _ _
  have hExpWidth : Real.exp (hA+hB) ≤ 3 :=
    (Real.exp_le_exp.mpr hWidth).trans
      (le_of_lt Real.exp_one_lt_three)
  calc
    U*V ≤ Real.exp (((jA:ℝ)+1)*hA) *
        Real.exp (((jB:ℝ)+1)*hB) := hUV
    _ = Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB) *
        Real.exp (hA+hB) := hExpEq
    _ ≤ Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB)*3 :=
      mul_le_mul_of_nonneg_left hExpWidth
        (Real.exp_pos _).le
    _ = _ := by ring

/-- The true moving-major arc radius
|beta| <= L^Carc/Hcell, at the SAME SOURCE03 active
product cells which contain XA,XB, gives a dyadic
phase budget |beta| *U*V <= 3 L^Carc.
It does NOT assert membership of every active cell in
the same arc, or an original RAW-vs-Knu estimate. -/
theorem source_original_true_moving_cell_beta_budget434
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V L Carc beta : ℝ)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUX : U ≤ (XA:ℝ)) (hVX : V ≤ (XB:ℝ))
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hWidth : hA+hB ≤ 1)
    (hArc : |beta| ≤
      L^Carc/Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB)) :
    |beta| *(U*V) ≤ 3*L^Carc := by
  let Hcell : ℝ := Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB)
  have hHpos : 0 < Hcell := Real.exp_pos _
  have hBeta :
      |beta| *Hcell ≤ L^Carc := by
    have hh := mul_le_mul_of_nonneg_right hArc hHpos.le
    have hcancel : (L^Carc/Hcell)*Hcell = L^Carc := by
      field_simp [ne_of_gt hHpos]
    exact hh.trans_eq hcancel
  have hProduct :=
    source_original_true_same_cell_dyad_product_cap434
      hA hB jA jB XA XB U V hXAp hXBp hU hV
      hUX hVX hCellA hCellB hWidth
  calc
    |beta| *(U*V) ≤ |beta| *(3*Hcell) :=
      mul_le_mul_of_nonneg_left hProduct (abs_nonneg beta)
    _ = 3*(|beta| *Hcell) := by ring
    _ ≤ 3*L^Carc :=
      mul_le_mul_of_nonneg_left hBeta (by norm_num)

/-- With an explicit polynomial major budget S, the
SAME moving cell's radius delivers EXACTLY the C196
Dirichlet hypothesis |beta| U V <= 2 S / r.
A budget S large enough for 3 r L^Carc <= 2 S
is a visible input; compatibility with the original
fixed exponent Cs must be proved by the later
parameter schedule. -/
theorem source_original_true_moving_cell_beta_C196_dir434
    (hA hB : ℝ) (jA jB : ℤ)
    (XA XB : ℕ) (U V L Carc beta S : ℝ) (r : ℕ)
    (hXAp : 0 < XA) (hXBp : 0 < XB)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUX : U ≤ (XA:ℝ)) (hVX : V ≤ (XB:ℝ))
    (hCellA : sourceOriginalLiteralLogCell434 hA jA XA)
    (hCellB : sourceOriginalLiteralLogCell434 hB jB XB)
    (hWidth : hA+hB ≤ 1)
    (hArc : |beta| ≤
      L^Carc/Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB))
    (hr : 0 < r) (hS : 3*(r:ℝ)*L^Carc ≤ 2*S) :
    |beta| *(U*V) ≤ 2*S/(r:ℝ) := by
  have hLocal :=
    source_original_true_moving_cell_beta_budget434
      hA hB jA jB XA XB U V L Carc beta
      hXAp hXBp hU hV hUX hVX
      hCellA hCellB hWidth hArc
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hC : 3*L^Carc ≤ 2*S/(r:ℝ) := by
    apply (le_div_iff₀ hrpos).mpr
    nlinarith [hS]
  exact hLocal.trans hC
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueGlobalOwnCutoffScale -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Exact SOURCE03 half-open GLOBAL product-cell index determines
the true exponential upper cutoff for an integer prime-product.
The bound is for the ORIGINAL width h, not an artificial
log(2) substitute. -/
theorem source_original_true_global_cell_index_upper434
    (h : ℝ) (hh : 0 < h) (j : ℤ) (n : ℕ) (hn : 0 < n)
    (hj : sourceOriginalLiteralLogCellIndex434 h n = j) :
    (n:ℝ) < Real.exp (((j:ℝ)+1)*h) := by
  have hCell := source_original_literal_log_cell_index_mem434
    h hh n
  rw [hj] at hCell
  have hp : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  calc
    (n:ℝ) = Real.exp (Real.log (n:ℝ)) :=
      (Real.exp_log hp).symm
    _ < Real.exp (((j:ℝ)+1)*h) :=
      Real.exp_lt_exp.mpr hCell.2

/-- The two EXACT ORIGINAL global log-cell exponential
upper cutoffs (including the one-cell shift) have product
at most 3 Hcell = 3 exp(j_A h_A+j_B h_B)
whenever the original widths obey h_A+h_B<=1.
This is stronger than bounding both sides separately by 3,
which would incorrectly pay a factor 9 in C196 hDir. -/
theorem source_original_true_global_pair_upper_C196_cap434
    (hA hB : ℝ) (jA jB : ℤ)
    (hWidth : hA+hB ≤ 1) :
    Real.exp (((jA:ℝ)+1)*hA) *
      Real.exp (((jB:ℝ)+1)*hB) ≤
    3*(Real.exp ((jA:ℝ)*hA) *
       Real.exp ((jB:ℝ)*hB)) := by
  have hExpEq :
      Real.exp (((jA:ℝ)+1)*hA) *
        Real.exp (((jB:ℝ)+1)*hB) =
      Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB) *
        Real.exp (hA+hB) := by
    calc
      _ = Real.exp (
        ((jA:ℝ)+1)*hA+((jB:ℝ)+1)*hB) :=
          (Real.exp_add _ _).symm
      _ = Real.exp (
        ((jA:ℝ)*hA+(jB:ℝ)*hB)+(hA+hB)) := by
          congr 1
          ring
      _ = _ := Real.exp_add _ _
  have hExpWidth : Real.exp (hA+hB) ≤ 3 :=
    (Real.exp_le_exp.mpr hWidth).trans
      (le_of_lt Real.exp_one_lt_three)
  calc
    _ = Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB) *
         Real.exp (hA+hB) := hExpEq
    _ ≤ Real.exp ((jA:ℝ)*hA+(jB:ℝ)*hB) * 3 :=
      mul_le_mul_of_nonneg_left hExpWidth
        (Real.exp_pos _).le
    _ = 3*(Real.exp ((jA:ℝ)*hA) *
         Real.exp ((jB:ℝ)*hB)) := by
      rw [Real.exp_add]
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualPrimitiveKnuCellMatching -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- ORIGINAL source03 primitive one-GLOBAL Dirichlet comparison
kernel is ZERO if its auxiliary D prime-product and true output
X prime-product are in DIFFERENT authentic half-open logarithmic
cells. True primitive conductor family and active cell masses are
unchanged; this is an exact arithmetic support theorem, not a
magnitude or an assumed C6 spectral saving. -/
theorem source_original_true_primitive_global_kernel_cell_mismatch_zero434
    (Q : ℕ) (active : Finset ℤ) (h : ℝ) (hh : 0 < h)
    (mass : ℤ → ℝ) (D X : ℕ)
    (hMismatch : sourceOriginalLiteralLogCellIndex434 h D ≠
                 sourceOriginalLiteralLogCellIndex434 h X) :
    sourceOriginalActualPrimitiveGlobalKernel434
      Q active h mass D X = 0 := by
  classical
  unfold sourceOriginalActualPrimitiveGlobalKernel434
    sourceOriginalCharacterCellKernel434
  apply Finset.sum_eq_zero
  intro j hj
  have hOff : ¬(sourceOriginalLiteralLogCell434 h j D ∧
                sourceOriginalLiteralLogCell434 h j X) := by
    intro hBoth
    have hD := (source_original_literal_log_cell_iff_index434
      h hh D j).mp hBoth.1
    have hX := (source_original_literal_log_cell_iff_index434
      h hh X j).mp hBoth.2
    exact hMismatch (hD.symm.trans hX)
  simp only [if_neg hOff]

/-- The TRUE signed SOURCE03 two-independent-GLOBAL primitive
Knu comparison is zero unless BOTH source/target original
integer output products have the SAME log cells as their
corresponding auxiliary inputs. No assumption about characters,
numbers of source groups, or output-value factorization. -/
theorem source_original_true_primitive_Knu_cell_mismatch_zero434
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ)
    (hMismatch :
      sourceOriginalLiteralLogCellIndex434 hA DA ≠
        sourceOriginalLiteralLogCellIndex434 hA XA ∨
      sourceOriginalLiteralLogCellIndex434 hB DB ≠
        sourceOriginalLiteralLogCellIndex434 hB XB) :
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r = 0 := by
  rcases hMismatch with hAoff | hBoff
  · unfold sourceOriginalActualPrimitiveComparisonKernel434
    rw [source_original_true_primitive_global_kernel_cell_mismatch_zero434
      Q JA hA hhA massA DA XA hAoff]
    simp
  · unfold sourceOriginalActualPrimitiveComparisonKernel434
    rw [source_original_true_primitive_global_kernel_cell_mismatch_zero434
      Q JB hB hhB massB DB XB hBoff]
    simp

/-- Nonzero original SOURCE03 comparison forces BOTH its
actual auxiliary D_A,D_B products and physical X_A,X_B products
into matching GLOBAL cells. This closes the exact support step
needed to synchronize original moving own arcs and input dyads;
it does not itself deliver the C6 logarithmic minor saving. -/
theorem source_original_true_primitive_Knu_nonzero_cells_match434
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ)
    (hNonzero : sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r ≠ 0) :
    sourceOriginalLiteralLogCellIndex434 hA DA =
        sourceOriginalLiteralLogCellIndex434 hA XA ∧
    sourceOriginalLiteralLogCellIndex434 hB DB =
        sourceOriginalLiteralLogCellIndex434 hB XB := by
  constructor
  · by_contra hDiff
    exact hNonzero
      (source_original_true_primitive_Knu_cell_mismatch_zero434
        Q JA JB hA hB hhA hhB massA massB
        DA XA DB XB r (Or.inl hDiff))
  · by_contra hDiff
    exact hNonzero
      (source_original_true_primitive_Knu_cell_mismatch_zero434
        Q JA JB hA hB hhA hhB massA massB
        DA XA DB XB r (Or.inr hDiff))

/-- If the TRUE SOURCE03 signed Knu primitive comparison kernel
at the actual selected output GLOBAL cells (jA,jB) is nonzero,
both true auxiliary input prime products D_A,D_B share precisely
those two ORIGINAL log cells. Their combined scale therefore obeys
the genuine C196 3*Hcell upper cap (not a fake 9*Hcell or an
assumed common arc). This is arithmetic SUPPORT only, not a
minor-arc C6 saving. -/
theorem source_original_true_primitive_Knu_input_own_cell_C196_cap434
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ)
    (hDA : 0 < DA) (hDB : 0 < DB)
    (jA jB : ℤ)
    (hXA : sourceOriginalLiteralLogCellIndex434 hA XA = jA)
    (hXB : sourceOriginalLiteralLogCellIndex434 hB XB = jB)
    (hWidth : hA+hB ≤ 1)
    (hNonzero : sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r ≠ 0) :
    sourceOriginalLiteralLogCellIndex434 hA DA = jA ∧
    sourceOriginalLiteralLogCellIndex434 hB DB = jB ∧
    (DA:ℝ)*(DB:ℝ) ≤
      3*(Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB)) := by
  obtain ⟨hCellA,hCellB⟩ :=
    source_original_true_primitive_Knu_nonzero_cells_match434
      Q JA JB hA hB hhA hhB massA massB
      DA XA DB XB r hNonzero
  have hDAindex : sourceOriginalLiteralLogCellIndex434 hA DA = jA :=
    hCellA.trans hXA
  have hDBindex : sourceOriginalLiteralLogCellIndex434 hB DB = jB :=
    hCellB.trans hXB
  have hUpA : (DA:ℝ) ≤ Real.exp (((jA:ℝ)+1)*hA) :=
    le_of_lt (source_original_true_global_cell_index_upper434
      hA hhA jA DA hDA hDAindex)
  have hUpB : (DB:ℝ) ≤ Real.exp (((jB:ℝ)+1)*hB) :=
    le_of_lt (source_original_true_global_cell_index_upper434
      hB hhB jB DB hDB hDBindex)
  have hDAge : (0:ℝ) ≤ DA := Nat.cast_nonneg _
  have hExpGe : (0:ℝ) ≤ Real.exp (((jA:ℝ)+1)*hA) :=
    (Real.exp_pos _).le
  have hProdCap : (DA:ℝ)*(DB:ℝ) ≤
      Real.exp (((jA:ℝ)+1)*hA) *
        Real.exp (((jB:ℝ)+1)*hB) :=
    mul_le_mul hUpA hUpB (Nat.cast_nonneg _) hExpGe
  exact ⟨hDAindex,hDBindex,hProdCap.trans
    (source_original_true_global_pair_upper_C196_cap434
      hA hB jA jB hWidth)⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePrimitiveKnuMatchedDyadC196 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- ORIGINAL SOURCE03 primitive Knu's NONZERO auxiliary input
pair DA,DB is contained in one of just TWO TRUE dyads per
ACTUAL selected OUTPUT GLOBAL cell (jA,jB). The integer
dyad origins are ceil(exp(jh)) or twice that number, and
are never smaller than the genuine original cell lower
scale. The comparison's exact input-output cell matching is
deduced from the unchanged primitive character kernel itself.
This provides the four genuine C6 input rectangles attached
to ONE output pair, not a synthetic dyad family. -/
theorem source_original_true_primitive_Knu_matched_two_dyads434
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (massA massB : ℤ → ℝ)
    (DA XA DB XB r : ℕ)
    (hDA : 0 < DA) (hDB : 0 < DB)
    (jA jB : ℤ)
    (hXA : sourceOriginalLiteralLogCellIndex434 hA XA = jA)
    (hXB : sourceOriginalLiteralLogCellIndex434 hB XB = jB)
    (hWidth : hA+hB ≤ 1)
    (hNonzero : sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB DA XA DB XB r ≠ 0) :
    ∃ M N : ℕ,
      (M = Nat.ceil (Real.exp ((jA:ℝ)*hA)) ∨
       M = 2*Nat.ceil (Real.exp ((jA:ℝ)*hA))) ∧
      (N = Nat.ceil (Real.exp ((jB:ℝ)*hB)) ∨
       N = 2*Nat.ceil (Real.exp ((jB:ℝ)*hB))) ∧
      0 < M ∧ 0 < N ∧
      Real.exp ((jA:ℝ)*hA) ≤ (M:ℝ) ∧
      Real.exp ((jB:ℝ)*hB) ≤ (N:ℝ) ∧
      DA ∈ Finset.Ico M (2*M) ∧
      DB ∈ Finset.Ico N (2*N) ∧
      (DA:ℝ)*(DB:ℝ) ≤
        3*(Real.exp ((jA:ℝ)*hA)*Real.exp ((jB:ℝ)*hB)) := by
  classical
  obtain ⟨hMatchA,hMatchB,hCap⟩ :=
    source_original_true_primitive_Knu_input_own_cell_C196_cap434
      Q JA JB hA hB hhA hhB massA massB
      DA XA DB XB r hDA hDB jA jB hXA hXB hWidth hNonzero
  have hCellA : sourceOriginalLiteralLogCell434 hA jA DA :=
    (source_original_literal_log_cell_iff_index434
      hA hhA DA jA).mpr hMatchA.symm
  have hCellB : sourceOriginalLiteralLogCell434 hB jB DB :=
    (source_original_literal_log_cell_iff_index434
      hB hhB DB jB).mpr hMatchB.symm
  obtain ⟨M,hMpos,hMchoice,hMscale,hMlo,hMhi⟩ :=
    source_original_actual_log_cell_two_integer_dyads434
      hA hhA1 jA DA hDA hCellA
  obtain ⟨N,hNpos,hNchoice,hNscale,hNlo,hNhi⟩ :=
    source_original_actual_log_cell_two_integer_dyads434
      hB hhB1 jB DB hDB hCellB
  refine ⟨M,N,hMchoice,hNchoice,hMpos,hNpos,
    hMscale,hNscale,?_,?_,hCap⟩
  · exact Finset.mem_Ico.mpr ⟨hMlo,hMhi⟩
  · exact Finset.mem_Ico.mpr ⟨hNlo,hNhi⟩
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTruePrimitiveKnuFourDyadSupport -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The ORIGINAL primitive SOURCE03 Knu auxiliary sum at fixed
selected output products XA/XB is EXACTLY four true dyadic
rectangles, two per genuine output GLOBAL log cell.
The source's full complex physical weighting and Fourier
phase may be arbitrary functions of the ACTUAL auxiliary
prime-label state X. Crucially, ZERO primitive-kernel terms
need no dyad membership; every NONZERO comparison term
belongs to EXACTLY ONE of four rectangles via certified
true input/output GLOBAL cell matching. -/
theorem source_original_true_primitive_Knu_four_matched_dyads434
    {X : Type} [Fintype X]
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (massA massB : ℤ → ℝ)
    (XA XB r : ℕ) (jA jB : ℤ)
    (hXA : sourceOriginalLiteralLogCellIndex434 hA XA = jA)
    (hXB : sourceOriginalLiteralLogCellIndex434 hB XB = jB)
    (hWidth : hA+hB ≤ 1)
    (DA DB : X → ℕ)
    (hDA : ∀ x, 0 < DA x) (hDB : ∀ x, 0 < DB x)
    (w phase : X → ℂ) :
    let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let F : X → ℂ := fun x =>
      w x*sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB (DA x) XA (DB x) XB r *
        phase x
    let A0 : X → Prop := fun x => DA x ∈ Finset.Ico M0 (2*M0)
    let A1 : X → Prop := fun x => DA x ∈ Finset.Ico (2*M0) (4*M0)
    let B0 : X → Prop := fun x => DB x ∈ Finset.Ico N0 (2*N0)
    let B1 : X → Prop := fun x => DB x ∈ Finset.Ico (2*N0) (4*N0)
    (∑ x : X, F x) =
      (∑ x : X, if A0 x ∧ B0 x then F x else 0) +
      (∑ x : X, if A0 x ∧ B1 x then F x else 0) +
      (∑ x : X, if A1 x ∧ B0 x then F x else 0) +
      (∑ x : X, if A1 x ∧ B1 x then F x else 0) := by
  classical
  let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let F : X → ℂ := fun x =>
    w x*sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB (DA x) XA (DB x) XB r *
      phase x
  let A0 : X → Prop := fun x => DA x ∈ Finset.Ico M0 (2*M0)
  let A1 : X → Prop := fun x => DA x ∈ Finset.Ico (2*M0) (4*M0)
  let B0 : X → Prop := fun x => DB x ∈ Finset.Ico N0 (2*N0)
  let B1 : X → Prop := fun x => DB x ∈ Finset.Ico (2*N0) (4*N0)
  have hMatched (x : X) (hx : F x ≠ 0) :
      (A0 x ∨ A1 x) ∧ (B0 x ∨ B1 x) := by
    have hK : sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB
          (DA x) XA (DB x) XB r ≠ 0 := by
      intro hzero
      apply hx
      simp [F,hzero]
    obtain ⟨M,N,hMchoice,hNchoice,hMp,hNp,hMs,hNs,
      hMA,hNB,hCap⟩ :=
      source_original_true_primitive_Knu_matched_two_dyads434
        Q JA JB hA hB hhA hhB hhA1 hhB1 massA massB
        (DA x) XA (DB x) XB r (hDA x) (hDB x)
        jA jB hXA hXB hWidth hK
    constructor
    · rcases hMchoice with hm | hm
      · left
        simpa only [A0,M0,hm] using hMA
      · right
        rw [hm] at hMA
        change DA x ∈ Finset.Ico (2*M0) (4*M0)
        obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hMA
        exact Finset.mem_Ico.mpr (by constructor <;> omega)
    · rcases hNchoice with hn | hn
      · left
        simpa only [B0,N0,hn] using hNB
      · right
        rw [hn] at hNB
        change DB x ∈ Finset.Ico (2*N0) (4*N0)
        obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hNB
        exact Finset.mem_Ico.mpr (by constructor <;> omega)
  have hADisjoint (x : X) : ¬(A0 x ∧ A1 x) := by
    rintro ⟨hx,hy⟩
    have hx' := (Finset.mem_Ico.mp hx).2
    have hy' := (Finset.mem_Ico.mp hy).1
    omega
  have hBDisjoint (x : X) : ¬(B0 x ∧ B1 x) := by
    rintro ⟨hx,hy⟩
    have hx' := (Finset.mem_Ico.mp hx).2
    have hy' := (Finset.mem_Ico.mp hy).1
    omega
  change (∑ x : X, F x) =
    (∑ x : X, if A0 x ∧ B0 x then F x else 0) +
    (∑ x : X, if A0 x ∧ B1 x then F x else 0) +
    (∑ x : X, if A1 x ∧ B0 x then F x else 0) +
    (∑ x : X, if A1 x ∧ B1 x then F x else 0)
  convert source_original_finite_four_matched_dyad_masks434
    F A0 A1 B0 B1 (fun x hx => (hMatched x hx).1)
    (fun x hx => (hMatched x hx).2)
    hADisjoint hBDisjoint using 1
  congr 1
  · congr 1
    · congr 1
      · apply Finset.sum_congr rfl
        intro x hx
        by_cases h : A0 x ∧ B0 x <;> simp [h]
      · apply Finset.sum_congr rfl
        intro x hx
        by_cases h : A0 x ∧ B1 x <;> simp [h]
    · apply Finset.sum_congr rfl
      intro x hx
      by_cases h : A1 x ∧ B0 x <;> simp [h]
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases h : A1 x ∧ B1 x <;> simp [h]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueKnuFixedOutputFourDyadOperator -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- TRUE primitive SOURCE03 comparison Knu at every attainable
OUTPUT product nA,nB in one selected original global log-cell
pair is exactly four matched INPUT dyadic rectangles.
All input labels X, original primitive kernel, harmonic weights,
actual -k theta phase, and potential Mellin twists are retained.
The four rectangles are the TWO genuine source03 windows on EACH
side, not a partition over exponentially many arbitrary dyads.
No analytic saving is assumed or asserted. -/
theorem source_original_true_Knu_fixed_output_four_dyad_operator434
    {X : Type} [Fintype X]
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (massA massB : ℤ → ℝ) (r : ℕ)
    (jA jB : ℤ) (hWidth : hA+hB ≤ 1)
    (TA TB : Finset ℕ)
    (hTA : ∀ nA∈TA,
      sourceOriginalLiteralLogCellIndex434 hA nA = jA)
    (hTB : ∀ nB∈TB,
      sourceOriginalLiteralLogCellIndex434 hB nB = jB)
    (DA DB : X → ℕ)
    (hDA : ∀ x, 0 < DA x) (hDB : ∀ x, 0 < DB x)
    (w phase : X → ℂ)
    (aCoeff bCoeff : ℕ → ℂ) :
    let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let F : ℕ → ℕ → X → ℂ := fun nA nB x =>
      w x*sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB (DA x) nA (DB x) nB r *
        phase x
    let A0 : X → Prop := fun x => DA x ∈ Finset.Ico M0 (2*M0)
    let A1 : X → Prop := fun x => DA x ∈ Finset.Ico (2*M0) (4*M0)
    let B0 : X → Prop := fun x => DB x ∈ Finset.Ico N0 (2*N0)
    let B1 : X → Prop := fun x => DB x ∈ Finset.Ico (2*N0) (4*N0)
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ x : X, F nA nB x)) =
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B0 x then F nA nB x else 0)) +
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B1 x then F nA nB x else 0)) +
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B0 x then F nA nB x else 0)) +
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B1 x then F nA nB x else 0)) := by
  classical
  let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let F : ℕ → ℕ → X → ℂ := fun nA nB x =>
    w x*sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB (DA x) nA (DB x) nB r *
      phase x
  let A0 : X → Prop := fun x => DA x ∈ Finset.Ico M0 (2*M0)
  let A1 : X → Prop := fun x => DA x ∈ Finset.Ico (2*M0) (4*M0)
  let B0 : X → Prop := fun x => DB x ∈ Finset.Ico N0 (2*N0)
  let B1 : X → Prop := fun x => DB x ∈ Finset.Ico (2*N0) (4*N0)
  have hAt (nA : ℕ) (hnA : nA∈TA)
      (nB : ℕ) (hnB : nB∈TB) :
      (∑ x : X, F nA nB x) =
      (∑ x : X, if A0 x ∧ B0 x then F nA nB x else 0) +
      (∑ x : X, if A0 x ∧ B1 x then F nA nB x else 0) +
      (∑ x : X, if A1 x ∧ B0 x then F nA nB x else 0) +
      (∑ x : X, if A1 x ∧ B1 x then F nA nB x else 0) := by
    have hRaw := source_original_true_primitive_Knu_four_matched_dyads434
      Q JA JB hA hB hhA hhB hhA1 hhB1 massA massB
      nA nB r jA jB (hTA nA hnA) (hTB nB hnB) hWidth
      DA DB hDA hDB w phase
    simpa only [F,M0,N0,A0,A1,B0,B1] using hRaw
  change (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ x : X, F nA nB x)) =
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B0 x then F nA nB x else 0)) +
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B1 x then F nA nB x else 0)) +
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B0 x then F nA nB x else 0)) +
    (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B1 x then F nA nB x else 0))
  calc
    _ = ∑ nA∈TA, ∑ nB∈TB,
      (aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B0 x then F nA nB x else 0) +
       aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B1 x then F nA nB x else 0) +
       aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B0 x then F nA nB x else 0) +
       aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B1 x then F nA nB x else 0)) := by
      apply Finset.sum_congr rfl
      intro nA hnA
      apply Finset.sum_congr rfl
      intro nB hnB
      rw [hAt nA hnA nB hnB]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueKnuFourMatchedOutputSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- TRUE original SOURCE03 primitive Knu output operator, for ALL
original selected outputs in one fixed genuine active GLOBAL
cell pair. FOUR independently matched input rectangles suffice;
four genuine local squared weighted-L2 C6 bounds imply full
selected output saving at exactly 16 times their common budget,
without a factor from the size of the prime tuples, atom fibres,
output cardinalities, or all dyads. The per-rectangle C6 bounds
remain EXPLICIT inputs, not a hidden spectral saving hypothesis. -/
theorem source_original_true_Knu_four_matched_output_saving434
    {X : Type} [Fintype X]
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (massA massB : ℤ → ℝ) (r : ℕ)
    (jA jB : ℤ) (hWidth : hA+hB ≤ 1)
    (TA TB : Finset ℕ)
    (hTA : ∀ nA∈TA,
      sourceOriginalLiteralLogCellIndex434 hA nA = jA)
    (hTB : ∀ nB∈TB,
      sourceOriginalLiteralLogCellIndex434 hB nB = jB)
    (DA DB : X → ℕ)
    (hDA : ∀ x, 0 < DA x) (hDB : ∀ x, 0 < DB x)
    (w phase : X → ℂ)
    (aCoeff bCoeff : ℕ → ℂ)
    (EA EB saving : ℝ)
    (hEA : 0 ≤ EA) (hEB : 0 ≤ EB)
    (hSaving : 0 ≤ saving) :
    let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let F : ℕ → ℕ → X → ℂ := fun nA nB x =>
      w x*sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB (DA x) nA (DB x) nB r *
        phase x
    let A0 : X → Prop := fun x => DA x ∈ Finset.Ico M0 (2*M0)
    let A1 : X → Prop := fun x => DA x ∈ Finset.Ico (2*M0) (4*M0)
    let B0 : X → Prop := fun x => DB x ∈ Finset.Ico N0 (2*N0)
    let B1 : X → Prop := fun x => DB x ∈ Finset.Ico (2*N0) (4*N0)

    let full : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ x : X, F nA nB x)
    let z00 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B0 x then F nA nB x else 0))
    let z01 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A0 x ∧ B1 x then F nA nB x else 0))
    let z10 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B0 x then F nA nB x else 0))
    let z11 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ x : X, if A1 x ∧ B1 x then F nA nB x else 0))
    (‖z00‖^2 ≤ saving*EA*EB) →
    (‖z01‖^2 ≤ saving*EA*EB) →
    (‖z10‖^2 ≤ saving*EA*EB) →
    (‖z11‖^2 ≤ saving*EA*EB) →
    ‖full‖^2 ≤ 16*(saving*EA*EB) := by
  classical
  dsimp only
  intro h00 h01 h10 h11
  let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let F : ℕ → ℕ → X → ℂ := fun nA nB x =>
    w x*sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB (DA x) nA (DB x) nB r *
      phase x
  let A0 : X → Prop := fun x => DA x ∈ Finset.Ico M0 (2*M0)
  let A1 : X → Prop := fun x => DA x ∈ Finset.Ico (2*M0) (4*M0)
  let B0 : X → Prop := fun x => DB x ∈ Finset.Ico N0 (2*N0)
  let B1 : X → Prop := fun x => DB x ∈ Finset.Ico (2*N0) (4*N0)
  let full : ℂ := ∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*(∑ x : X, F nA nB x)
  let z00 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*
      (∑ x : X, if A0 x ∧ B0 x then F nA nB x else 0))
  let z01 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*
      (∑ x : X, if A0 x ∧ B1 x then F nA nB x else 0))
  let z10 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*
      (∑ x : X, if A1 x ∧ B0 x then F nA nB x else 0))
  let z11 : ℂ := (∑ nA∈TA, ∑ nB∈TB,
    aCoeff nA*bCoeff nB*
      (∑ x : X, if A1 x ∧ B1 x then F nA nB x else 0))
  have hExact := source_original_true_Knu_fixed_output_four_dyad_operator434
    Q JA JB hA hB hhA hhB hhA1 hhB1 massA massB r
    jA jB hWidth TA TB hTA hTB DA DB hDA hDB
    w phase aCoeff bCoeff
  have hSum : full = z00+z01+z10+z11 := by
    simpa only [full,z00,z01,z10,z11] using hExact
  have hTotalSaving : 0 ≤ saving*EA*EB :=
    mul_nonneg (mul_nonneg hSaving hEA) hEB
  calc
    ‖full‖^2 = ‖z00+z01+z10+z11‖^2 :=
      congrArg (fun v : ℂ => ‖v‖^2) hSum
    _ ≤ 16*(saving*EA*EB) :=
      source_original_finite_four_matched_operator_saving434
        z00 z01 z10 z11 (saving*EA*EB)
        hTotalSaving h00 h01 h10 h11
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueKnuPhysicalFourMatchedOutputSaving -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The ORIGINAL source03 primitive signed comparison Knu,
with TRUE harmonic labelled BIG input prime tuples,
ACTUAL selected output integer-product atoms at the active
jA/jB GLOBAL cells and exact -kθ Fourier/Mellin input phase,
is supported in only FOUR genuine input dyadic rectangles.
If these four TRUE physical inverse-atom weighted-L2 C6 bounds
hold, the complete selected-output operator loses exactly
factor 16 in its squared norm. Nonnegative inverse-atom
energies are DERIVED from authentic source03 prime measures,
never assumed or replaced by a uniform counting law.
The per-rectangle analytic C6 bounds are EXPLICIT inputs. -/
theorem source_original_true_Knu_physical_four_matched_saving434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (hVbig : ∀ g : β, d.Vbig g =
      ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (m : ℕ) (A B : Finset (β × Fin m))
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
    (hhA1 : hA ≤ 1) (hhB1 : hB ≤ 1)
    (massA massB : ℤ → ℝ)
    (jA jB : ℤ) (hWidth : hA+hB ≤ 1)
    (theta ζ : ℝ) (k : ℤ)
    (aCoeff bCoeff : ℕ → ℂ)
    (saving : ℝ) (hSaving : 0 ≤ saving) :
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 hA n=jA)
    let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 hB n=jB)
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SB v.2
    let w : X → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ) *
      (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
    let phase : X → ℂ := fun v =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
    let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
    let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
      w v*sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB
        (DA v) nA (DB v) nB (A.card+B.card) * phase v
    let A0 : X → Prop := fun v => DA v ∈ Finset.Ico M0 (2*M0)
    let A1 : X → Prop := fun v => DA v ∈ Finset.Ico (2*M0) (4*M0)
    let B0 : X → Prop := fun v => DB v ∈ Finset.Ico N0 (2*N0)
    let B1 : X → Prop := fun v => DB v ∈ Finset.Ico (2*N0) (4*N0)
    let E00 : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ v : X, if A0 v ∧ B0 v then F nA nB v else 0)
    let E01 : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ v : X, if A0 v ∧ B1 v then F nA nB v else 0)
    let E10 : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ v : X, if A1 v ∧ B0 v then F nA nB v else 0)
    let E11 : ℂ := ∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*
        (∑ v : X, if A1 v ∧ B1 v then F nA nB v else 0)
    let EA : ℝ := ∑ n∈TA,
      ‖aCoeff n‖^2 /
        sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n∈TB,
      ‖bCoeff n‖^2 /
        sourceOriginalPhysicalProductAtom434 SB muB n
    (‖E00‖^2 ≤ saving*EA*EB) →
    (‖E01‖^2 ≤ saving*EA*EB) →
    (‖E10‖^2 ≤ saving*EA*EB) →
    (‖E11‖^2 ≤ saving*EA*EB) →
    ‖(∑ nA∈TA, ∑ nB∈TB,
      aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v))‖^2 ≤
        16*(saving*EA*EB) := by
  classical
  dsimp only
  intro h00 h01 h10 h11
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 hA n=jA)
  let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 hB n=jB)
  let X := SourceOriginalGramPrimeTuple434 SA ×
    SourceOriginalGramPrimeTuple434 SB
  let DA : X → ℕ := fun v => sourceOriginalGramPrimeProduct434 SA v.1
  let DB : X → ℕ := fun v => sourceOriginalGramPrimeProduct434 SB v.2
  let w : X → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SA muA v.1:ℂ) *
    (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)
  let phase : X → ℂ := fun v =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((DA v*DB v:ℕ):ℤ)) *
    sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
  let M0 := Nat.ceil (Real.exp ((jA:ℝ)*hA))
  let N0 := Nat.ceil (Real.exp ((jB:ℝ)*hB))
  let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
    w v*sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB
      (DA v) nA (DB v) nB (A.card+B.card) * phase v
  let A0 : X → Prop := fun v => DA v ∈ Finset.Ico M0 (2*M0)
  let A1 : X → Prop := fun v => DA v ∈ Finset.Ico (2*M0) (4*M0)
  let B0 : X → Prop := fun v => DB v ∈ Finset.Ico N0 (2*N0)
  let B1 : X → Prop := fun v => DB v ∈ Finset.Ico (2*N0) (4*N0)
  let EA : ℝ := ∑ n∈TA,
    ‖aCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n∈TB,
    ‖bCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SB muB n
  have hAtoms := source_original_true_nu_selected_atom_probability434
    cfg x L Y Hprime d hVbig m A B
  have hAtomA (n : ℕ) (hn : n∈TA) :
      0 < sourceOriginalPhysicalProductAtom434 SA muA n :=
    hAtoms.1 n (Finset.mem_filter.mp hn).1
  have hAtomB (n : ℕ) (hn : n∈TB) :
      0 < sourceOriginalPhysicalProductAtom434 SB muB n :=
    hAtoms.2.1 n (Finset.mem_filter.mp hn).1
  have hEA : 0 ≤ EA := by
    dsimp only [EA]
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (sq_nonneg _) (hAtomA n hn).le
  have hEB : 0 ≤ EB := by
    dsimp only [EB]
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (sq_nonneg _) (hAtomB n hn).le
  have hCellA (n : ℕ) (hn : n∈TA) :
      sourceOriginalLiteralLogCellIndex434 hA n = jA :=
    (Finset.mem_filter.mp hn).2
  have hCellB (n : ℕ) (hn : n∈TB) :
      sourceOriginalLiteralLogCellIndex434 hB n = jB :=
    (Finset.mem_filter.mp hn).2
  have hDA (v : X) : 0 < DA v :=
    source_original_gram_physical_prime_product_pos434 SA
      (fun z p hp => d.hTbPrime z.val.1 p hp) v.1
  have hDB (v : X) : 0 < DB v :=
    source_original_gram_physical_prime_product_pos434 SB
      (fun z p hp => d.hTbPrime z.val.1 p hp) v.2
  have hBound := source_original_true_Knu_four_matched_output_saving434
    Q JA JB hA hB hhA hhB hhA1 hhB1 massA massB
    (A.card+B.card) jA jB hWidth
    TA TB hCellA hCellB DA DB hDA hDB
    w phase aCoeff bCoeff EA EB saving hEA hEB hSaving
    h00 h01 h10 h11
  simpa only [SA,SB,muA,muB,TA,TB,X,DA,DB,w,phase,
    M0,N0,F,A0,A1,B0,B1,EA,EB] using hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueKnuMatchedRectangleMellinFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- A genuine SOURCE03 primitive-Knu matched input RECTANGLE,
with original independently labelled harmonic tuples, coupled
Dirichlet characters and authentic Fourier/Mellin oscillation,
is EXACTLY the weighted SOURCE03 C6 two-sided prime-tuple
bilinear kernel with input windows M+range M, N+range N.
No factorization of the jointly dependent arithmetic kernel
or weakening of output prime-atom information is introduced. -/
theorem source_original_true_Knu_rectangle_mellin_fubini434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434) (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (m : ℕ) (A B : Finset (β × Fin m))
    (Q : ℕ) (JA JB : Finset ℤ)
    (hA hB : ℝ) (massA massB : ℤ → ℝ)
    (XA XB : ℕ) (theta ζ : ℝ) (k : ℤ)
    (M N : ℕ) :
    let SA : A → Finset ℕ := fun z => d.Tb z.val.1
    let SB : B → Finset ℕ := fun z => d.Tb z.val.1
    let muA : A → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : B → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v => sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v => sourceOriginalGramPrimeProduct434 SB v.2
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ := fun v =>
      (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let AW := (Finset.range M).image (fun i => M+i)
    let BW := (Finset.range N).image (fun j => N+j)
    let coupled : X → ℂ := fun v =>
      sourceOriginalActualPrimitiveComparisonKernel434
        Q JA JB hA hB massA massB (DA v) XA (DB v) XB
        (A.card+B.card) *
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    (∑ v : X,
      if DA v ∈ Finset.Ico M (2*M) ∧
         DB v ∈ Finset.Ico N (2*N)
      then wA v.1*wB v.2*coupled v else 0) =
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun a => if sourceOriginalGramPrimeProduct434 SA a ∈ AW
        then (1:ℂ) else 0)
      (fun b => if sourceOriginalGramPrimeProduct434 SB b ∈ BW
        then (1:ℂ) else 0) coupled := by
  classical
  dsimp only
  let SA : A → Finset ℕ := fun z => d.Tb z.val.1
  let SB : B → Finset ℕ := fun z => d.Tb z.val.1
  let muA : A → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : B → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let X := SourceOriginalGramPrimeTuple434 SA ×
    SourceOriginalGramPrimeTuple434 SB
  let DA : X → ℕ := fun v => sourceOriginalGramPrimeProduct434 SA v.1
  let DB : X → ℕ := fun v => sourceOriginalGramPrimeProduct434 SB v.2
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ := fun v =>
    (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  let coupled : X → ℂ := fun v =>
    sourceOriginalActualPrimitiveComparisonKernel434
      Q JA JB hA hB massA massB (DA v) XA (DB v) XB
      (A.card+B.card) *
    Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((DA v*DB v:ℕ):ℤ)) *
    sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
  exact source_original_finite_ico_mask_bilinear434
    wA wB (fun a => sourceOriginalGramPrimeProduct434 SA a)
    (fun b => sourceOriginalGramPrimeProduct434 SB b)
    M N coupled
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueKnuFullFourMatchedOwnMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 25000000

/-- Genuine ORIGINAL SOURCE03 full primitive Knu auxiliary
Fourier/Mellin operator on each actual output jA/jB GLOBAL cell,
for arbitrary selected inverse-harmonic-atom L2 coefficients.
Outside the OWN moving major arc of the actual FIVE-index
source mode, ALL FOUR true input dyad C6 spectral estimates
are proved arithmetically. Exact finite rectangle Fubini
identifies them with the FULL primitive comparison kernel:
  squared norm <= 16 * (Qchar^4 xi^-4)^2 *125*L^-Bsave
                  * E_selectedA * E_selectedB.
No output cardinality or artificial full-mode cell count, no
assumed per-rectangle analytic savings, all real Fourier/Mellin
phases and original source prime groups preserved. This is
ONE selected original mode; ν/four-sign global proof open. -/
theorem eventually_source_original_true_Knu_FULL_four_matched_CELL_mellin_operator434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (JA JB : Finset ℤ) (massA massB : ℤ → ℝ)
    (hMassA : ∀ j ∈ JA, xi ≤ massA j)
    (hMassB : ∀ j ∈ JB, xi ≤ massB j)
    (hTotalA : (∑ j ∈ JA, massA j) ≤ 1)
    (hTotalB : (∑ j ∈ JB, massB j) ≤ 1)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z))
    (hWidth : hAvar z.1+hBvar z.1 ≤ 1),
    let SA : z.1.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : z.1.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1)
    let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
      (fun n => sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1)
    let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
    let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
    let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
    let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
      fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
    let Hwin : ℕ → ℕ → ℕ → ℕ → ℂ := fun M N XA XB =>
      sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
        (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈
          (Finset.range M).image (fun i => M+i) then (1:ℂ) else 0)
        (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈
          (Finset.range N).image (fun j => N+j) then (1:ℂ) else 0)
        (fun v =>
          sourceOriginalActualPrimitiveComparisonKernel434
            Qchar JA JB (hAvar z.1) (hBvar z.1)
            massA massB
            (sourceOriginalGramPrimeProduct434 SA v.1) XA
            (sourceOriginalGramPrimeProduct434 SB v.2) XB
            (z.1.1.card+z.1.2.card) *
          Green64SourceC6.integerPhase (-(k:ℝ)*theta)
            (((sourceOriginalGramPrimeProduct434 SA v.1 *
               sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
          sourceOriginalPureMellinPhase434 ζ
            (sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2))
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    let budget : ℝ :=
      (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))
    let X := SourceOriginalGramPrimeTuple434 SA ×
      SourceOriginalGramPrimeTuple434 SB
    let DA : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SA v.1
    let DB : X → ℕ := fun v =>
      sourceOriginalGramPrimeProduct434 SB v.2
    let w : X → ℂ := fun v => wA v.1*wB v.2
    let phase : X → ℂ := fun v =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta)
        (((DA v*DB v:ℕ):ℤ)) *
      sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
    let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
      w v*sourceOriginalActualPrimitiveComparisonKernel434
        Qchar JA JB (hAvar z.1) (hBvar z.1)
        massA massB (DA v) nA (DB v) nB
        (z.1.1.card+z.1.2.card) * phase v
    ‖(∑ nA ∈ TA, ∑ nB ∈ TB,
      aCoeff nA*bCoeff nB*(∑ v : X, F nA nB v))‖^2 ≤
        16*(budget*EA*EB) := by
  have hFour :=
    eventually_source_original_true_five_index_Knu_FOUR_matched_CELL_mellin_operator434
      cfg D Bsave hD C hExponent hSaving Aarc hAarc hArc
  filter_upwards [hFour,eventually_ge_atTop (4:ℝ)]
    with L hFourL hL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff theta k hk hOutside hWidth
  classical
  let SA : z.1.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : z.1.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : z.1.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : z.1.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TA := (sourceOriginalPhysicalProductAtomSupport434 SA).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1)
  let TB := (sourceOriginalPhysicalProductAtomSupport434 SB).filter
    (fun n => sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1)
  let M0 := Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1))
  let N0 := Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1))
  let wA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  let Hwin : ℕ → ℕ → ℕ → ℕ → ℂ := fun M N XA XB =>
    sourceOriginalFiniteTwoSidedMinorBilinear434 wA wB
      (fun v => if sourceOriginalGramPrimeProduct434 SA v ∈
        (Finset.range M).image (fun i => M+i) then (1:ℂ) else 0)
      (fun v => if sourceOriginalGramPrimeProduct434 SB v ∈
        (Finset.range N).image (fun j => N+j) then (1:ℂ) else 0)
      (fun v =>
        sourceOriginalActualPrimitiveComparisonKernel434
          Qchar JA JB (hAvar z.1) (hBvar z.1)
          massA massB
          (sourceOriginalGramPrimeProduct434 SA v.1) XA
          (sourceOriginalGramPrimeProduct434 SB v.2) XB
          (z.1.1.card+z.1.2.card) *
        Green64SourceC6.integerPhase (-(k:ℝ)*theta)
          (((sourceOriginalGramPrimeProduct434 SA v.1 *
             sourceOriginalGramPrimeProduct434 SB v.2):ℕ):ℤ) *
        sourceOriginalPureMellinPhase434 ζ
          (sourceOriginalGramPrimeProduct434 SA v.1 *
           sourceOriginalGramPrimeProduct434 SB v.2))
  let EA : ℝ := ∑ n ∈ TA,
    ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n ∈ TB,
    ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
  let budget : ℝ :=
    (((Qchar:ℝ)^4)*(xi⁻¹)^4)^2*(125*L^(-Bsave))

  let X := SourceOriginalGramPrimeTuple434 SA ×
    SourceOriginalGramPrimeTuple434 SB
  let DA : X → ℕ := fun v =>
    sourceOriginalGramPrimeProduct434 SA v.1
  let DB : X → ℕ := fun v =>
    sourceOriginalGramPrimeProduct434 SB v.2
  let w : X → ℂ := fun v => wA v.1*wB v.2
  let phase : X → ℂ := fun v =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta)
      (((DA v*DB v:ℕ):ℤ)) *
    sourceOriginalPureMellinPhase434 ζ (DA v*DB v)
  let F : ℕ → ℕ → X → ℂ := fun nA nB v =>
    w v*sourceOriginalActualPrimitiveComparisonKernel434
      Qchar JA JB (hAvar z.1) (hBvar z.1)
      massA massB (DA v) nA (DB v) nB
      (z.1.1.card+z.1.2.card) * phase v
  obtain ⟨h00,h01,h10,h11⟩ := hFourL
    x Y Hprime d sep hVbig
    blockA blockB hDisjoint m Qchar hm hTbLower
    hAvar hBvar hhA hhB xi hxi z hz
    JA JB massA massB hMassA hMassB hTotalA hTotalB
    ζ aCoeff bCoeff theta k hk hOutside
  have hRect (M N nA nB : ℕ) :
      (∑ v : X,
        if DA v ∈ Finset.Ico M (2*M) ∧
           DB v ∈ Finset.Ico N (2*N)
        then F nA nB v else 0) = Hwin M N nA nB := by
    have hh := source_original_true_Knu_rectangle_mellin_fubini434
      cfg x L Y Hprime d m z.1.1 z.1.2 Qchar JA JB
      (hAvar z.1) (hBvar z.1) massA massB
      nA nB theta ζ k M N
    change
      (∑ v : X,
        if DA v ∈ Finset.Ico M (2*M) ∧
           DB v ∈ Finset.Ico N (2*N)
        then wA v.1*wB v.2*
          (sourceOriginalActualPrimitiveComparisonKernel434
            Qchar JA JB (hAvar z.1) (hBvar z.1)
            massA massB (DA v) nA (DB v) nB
            (z.1.1.card+z.1.2.card) *
           Green64SourceC6.integerPhase (-(k:ℝ)*theta)
             (((DA v*DB v:ℕ):ℤ)) *
           sourceOriginalPureMellinPhase434 ζ (DA v*DB v))
        else 0) = Hwin M N nA nB at hh
    calc
      _ = (∑ v : X,
          if DA v ∈ Finset.Ico M (2*M) ∧
             DB v ∈ Finset.Ico N (2*N)
          then wA v.1*wB v.2*
            (sourceOriginalActualPrimitiveComparisonKernel434
              Qchar JA JB (hAvar z.1) (hBvar z.1)
              massA massB (DA v) nA (DB v) nB
              (z.1.1.card+z.1.2.card) *
             Green64SourceC6.integerPhase (-(k:ℝ)*theta)
               (((DA v*DB v:ℕ):ℤ)) *
             sourceOriginalPureMellinPhase434 ζ (DA v*DB v))
          else 0) := by
            apply Finset.sum_congr rfl
            intro v hv
            by_cases h : DA v ∈ Finset.Ico M (2*M) ∧
                DB v ∈ Finset.Ico N (2*N)
            · simp only [if_pos h]
              dsimp only [F,w,phase]
              ring
            · simp only [if_neg h]
      _ = Hwin M N nA nB := hh
  have hOutput (M N : ℕ) :
      (∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*
          (∑ v : X,
            if DA v ∈ Finset.Ico M (2*M) ∧
               DB v ∈ Finset.Ico N (2*N)
            then F nA nB v else 0)) =
      (∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*Hwin M N nA nB) := by
    apply Finset.sum_congr rfl
    intro nA hnA
    apply Finset.sum_congr rfl
    intro nB hnB
    rw [hRect M N nA nB]
  have hLocal00 :
      ‖(∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*
          (∑ v : X,
            if DA v ∈ Finset.Ico M0 (2*M0) ∧
               DB v ∈ Finset.Ico N0 (2*N0)
            then F nA nB v else 0))‖^2 ≤
        budget*EA*EB := by
    rw [hOutput M0 N0]
    exact h00
  have hLocal01 :
      ‖(∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*
          (∑ v : X,
            if DA v ∈ Finset.Ico M0 (2*M0) ∧
               DB v ∈ Finset.Ico (2*N0) (2*(2*N0))
            then F nA nB v else 0))‖^2 ≤
        budget*EA*EB := by
    rw [hOutput M0 (2*N0)]
    exact h01
  have hLocal10 :
      ‖(∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*
          (∑ v : X,
            if DA v ∈ Finset.Ico (2*M0) (2*(2*M0)) ∧
               DB v ∈ Finset.Ico N0 (2*N0)
            then F nA nB v else 0))‖^2 ≤
        budget*EA*EB := by
    rw [hOutput (2*M0) N0]
    exact h10
  have hLocal11 :
      ‖(∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*
          (∑ v : X,
            if DA v ∈ Finset.Ico (2*M0) (2*(2*M0)) ∧
               DB v ∈ Finset.Ico (2*N0) (2*(2*N0))
            then F nA nB v else 0))‖^2 ≤
        budget*EA*EB := by
    rw [hOutput (2*M0) (2*N0)]
    exact h11
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m := (Finset.mem_sigma.mp hz).1
  have hAA := hhA z.1 hν
  have hBB := hhB z.1 hν
  have hBudgetNN : 0 ≤ budget := by
    dsimp only [budget]
    have hLpos : 0 < L := by linarith
    positivity
  have hDoubleM : 2*(2*M0) = 4*M0 := by omega
  have hDoubleN : 2*(2*N0) = 4*N0 := by omega
  have hLocal01' := hLocal01
  simp only [hDoubleN] at hLocal01'
  have hLocal10' := hLocal10
  simp only [hDoubleM] at hLocal10'
  have hLocal11' := hLocal11
  simp only [hDoubleM,hDoubleN] at hLocal11'
  have hFull := source_original_true_Knu_physical_four_matched_saving434
    cfg x L Y Hprime d hVbig m z.1.1 z.1.2
    Qchar JA JB (hAvar z.1) (hBvar z.1)
    hAA.1 hBB.1 hAA.2 hBB.2 massA massB
    z.2.1.1 z.2.2.1 hWidth theta ζ k
    aCoeff bCoeff budget hBudgetNN
    hLocal00 hLocal01' hLocal10' hLocal11'
  simpa only [SA,SB,muA,muB,TA,TB,X,DA,DB,wA,wB,w,phase,
    F,M0,N0,EA,EB,budget] using hFull
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualGlobalDyadicAlignment -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Choose a genuine logarithmic source mesh aligned with dyadic windows:
h = log(2)/N. Coarsening is EXACT integer division, including endpoints. -/
theorem source_original_dyadic_aligned_log_index434
    (N : ℕ) (hN : 0 < N) (n : ℕ) :
    sourceOriginalLiteralLogCellIndex434 (Real.log 2) n =
      sourceOriginalLiteralLogCellIndex434 (Real.log 2/(N:ℝ)) n / (N:ℤ) := by
  unfold sourceOriginalLiteralLogCellIndex434
  rw [← Int.floor_div_natCast]
  congr 1
  have hnR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Coarse log(2) cells are exactly the ORIGINAL integer dyadic windows. -/
theorem source_original_log_two_cell_iff_dyad434
    (n b : ℕ) (hn : 0 < n) :
    sourceOriginalLiteralLogCellIndex434 (Real.log 2) n = (b:ℤ) ↔
      n ∈ Finset.Ico (2^b) (2^(b+1)) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hp : (0:ℝ) < (2:ℝ)^b := by positivity
  have hq : (0:ℝ) < (2:ℝ)^(b+1) := by positivity
  rw [eq_comm, ← source_original_literal_log_cell_iff_index434
    (Real.log 2) hlog n (b:ℤ)]
  simp only [sourceOriginalLiteralLogCell434, Int.cast_natCast]
  rw [← Nat.cast_add_one]
  rw [← Real.log_pow (2:ℝ) b, ← Real.log_pow (2:ℝ) (b+1),
    Real.log_le_log_iff hp hnR, Real.log_lt_log_iff hnR hq,
    Finset.mem_Ico]
  norm_cast

/-- The actual GLOBAL primitive kernel for the aligned fine mesh has
no coupling between DIFFERENT coarse dyadic windows, however small h is.
This removes any need to charge the fine-cell-pair count in a C6 split. -/
theorem source_original_actual_GLOBAL_aligned_dyad_support434
    (Q : ℕ) (active : Finset ℤ) (mass : ℤ → ℝ)
    (N : ℕ) (hN : 0 < N) (D X b : ℕ)
    (hD : 0 < D) (hX : 0 < X)
    (hNonzero : sourceOriginalActualPrimitiveGlobalKernel434
      Q active (Real.log 2/(N:ℝ)) mass D X ≠ 0) :
    (D ∈ Finset.Ico (2^b) (2^(b+1))) ↔
      X ∈ Finset.Ico (2^b) (2^(b+1)) := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hnR : (0:ℝ) < N := by exact_mod_cast hN
  have hFine :
      sourceOriginalLiteralLogCellIndex434 (Real.log 2/(N:ℝ)) D =
      sourceOriginalLiteralLogCellIndex434 (Real.log 2/(N:ℝ)) X := by
    by_contra hDiff
    exact hNonzero
      (source_original_true_primitive_global_kernel_cell_mismatch_zero434
        Q active (Real.log 2/(N:ℝ)) (div_pos hlog hnR) mass D X hDiff)
  have hCoarse :
      sourceOriginalLiteralLogCellIndex434 (Real.log 2) D =
      sourceOriginalLiteralLogCellIndex434 (Real.log 2) X := by
    rw [source_original_dyadic_aligned_log_index434 N hN D,
      source_original_dyadic_aligned_log_index434 N hN X, hFine]
  rw [← source_original_log_two_cell_iff_dyad434 D b hD,
    ← source_original_log_two_cell_iff_dyad434 X b hX, hCoarse]

/-- Exact commutation of the literal physical GLOBAL action with an
original coarse dyadic projection. All retained fine cells are still
inside the action and their true probability denominators are unchanged. -/
theorem source_original_actual_GLOBAL_commutes_dyad434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (hPositive : ∀ i p, p ∈ S i → 0 < p)
    (active : Finset ℤ) (Q N : ℕ) (hN : 0 < N)
    (b : ℕ) (f : SourceOriginalGramPrimeTuple434 S → ℂ)
    (p : SourceOriginalGramPrimeTuple434 S) :
    sourceOriginalActualGlobalAction434 S mu (Real.log 2/(N:ℝ)) active Q
      (fun q => if sourceOriginalGramPrimeProduct434 S q ∈
        Finset.Ico (2^b) (2^(b+1)) then f q else 0) p =
    if sourceOriginalGramPrimeProduct434 S p ∈ Finset.Ico (2^b) (2^(b+1))
    then sourceOriginalActualGlobalAction434 S mu (Real.log 2/(N:ℝ))
      active Q f p else 0 := by
  classical
  have hProd (q : SourceOriginalGramPrimeTuple434 S) :
      0 < sourceOriginalGramPrimeProduct434 S q :=
    Finset.prod_pos (fun i _ => hPositive i (q i).val (q i).property)
  have hRight :
      (if sourceOriginalGramPrimeProduct434 S p ∈ Finset.Ico (2^b) (2^(b+1))
       then sourceOriginalActualGlobalAction434 S mu (Real.log 2/(N:ℝ)) active Q f p
       else 0) =
      ∑ q : SourceOriginalGramPrimeTuple434 S,
        if sourceOriginalGramPrimeProduct434 S p ∈ Finset.Ico (2^b) (2^(b+1))
        then (sourceOriginalGramPrimeMass434 S mu q:ℂ) *
          sourceOriginalActualPrimitiveGlobalKernel434 Q active (Real.log 2/(N:ℝ))
            (sourceOriginalRealGramCellMass434 S mu (Real.log 2/(N:ℝ)))
            (sourceOriginalGramPrimeProduct434 S p)
            (sourceOriginalGramPrimeProduct434 S q) * f q
        else 0 := by
    by_cases hp : sourceOriginalGramPrimeProduct434 S p ∈ Finset.Ico (2^b) (2^(b+1))
    · simp only [hp,ite_true,sourceOriginalActualGlobalAction434]
    · simp [hp]
  rw [hRight]
  unfold sourceOriginalActualGlobalAction434
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : sourceOriginalActualPrimitiveGlobalKernel434
      Q active (Real.log 2/(N:ℝ))
      (sourceOriginalRealGramCellMass434 S mu (Real.log 2/(N:ℝ)))
      (sourceOriginalGramPrimeProduct434 S p)
      (sourceOriginalGramPrimeProduct434 S q) = 0
  · simp [hz]
  · have hs := source_original_actual_GLOBAL_aligned_dyad_support434
      Q active (sourceOriginalRealGramCellMass434 S mu (Real.log 2/(N:ℝ)))
      N hN (sourceOriginalGramPrimeProduct434 S p)
      (sourceOriginalGramPrimeProduct434 S q) b (hProd p) (hProd q) hz
    by_cases hp : sourceOriginalGramPrimeProduct434 S p ∈
        Finset.Ico (2^b) (2^(b+1))
    · simp [hp,hs.mp hp]
    · have hq' : sourceOriginalGramPrimeProduct434 S q ∉
          Finset.Ico (2^b) (2^(b+1)) := fun h => hp (hs.mpr h)
      simp [hp,hq']
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalActualCoarseDyadWitness -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false

/-- Every actual coarse candidate has a positive physical tuple witness
and a NATURAL dyadic index. No artificial cells or extra ranges are added. -/
theorem source_original_actual_coarse_candidate_witness434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (hPositive : ∀ i p, p ∈ S i → 0 < p)
    (j : ℤ) (hj : j ∈ sourceOriginalCandidateLogCells434 S (Real.log 2)) :
    ∃ b : ℕ, (b:ℤ)=j ∧ ∃ v : SourceOriginalGramPrimeTuple434 S,
      sourceOriginalGramPrimeProduct434 S v ∈
        Finset.Ico (2^b) (2^(b+1)) := by
  classical
  obtain ⟨a,ha,haj⟩ := Finset.mem_image.mp hj
  let v : SourceOriginalGramPrimeTuple434 S :=
    fun i => ⟨a i,(Fintype.mem_piFinset.mp ha) i⟩
  have hprod : 0 < sourceOriginalGramPrimeProduct434 S v :=
    Finset.prod_pos (fun i _ => hPositive i (v i).val (v i).property)
  have hindex : sourceOriginalLiteralLogCellIndex434 (Real.log 2)
      (sourceOriginalGramPrimeProduct434 S v)=j := haj
  have hj0 : 0 ≤ j := by
    rw [← hindex]
    unfold sourceOriginalLiteralLogCellIndex434
    apply Int.floor_nonneg.mpr
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast hprod
    · exact (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hcast : (j.toNat:ℤ)=j := Int.toNat_of_nonneg hj0
  refine ⟨j.toNat,hcast,v,?_⟩
  apply (source_original_log_two_cell_iff_dyad434 _ _ hprod).mp
  rw [hcast]
  exact hindex

/-- Both genuine endpoint outputs stay positive, including empty selected
products. The original free-slot labels and their multiplicities are kept. -/
theorem source_original_actual_free_outputs_positive434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ)
    (hPositive : ∀ g p, p ∈ P g → 0 < p)
    (v : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν)) :
    0 < sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
      (fun g i => (v g i).val) ∧
    0 < sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
      (fun g i => (v g i).val) := by
  constructor
  · unfold sourceOriginalProbeFreeSourceX434
    apply Finset.prod_pos
    intro z hz
    exact hPositive _ _ (v _ _).property
  · unfold sourceOriginalProbeFreeTargetX434
    apply Finset.prod_pos
    intro z hz
    exact hPositive _ _ (v _ _).property
end Green64Analytic.CorrelationSquare

end

