module

public import Green64.Library.Weights.Part030
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Correlation / GlobalRootScalar

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalGlobalRootScalar -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem rpow_nat (L t : ℝ) (hL : 0<L) (n : ℕ) :
    (L^t)^n=L^(t*(n:ℝ)) := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hL.le]

private theorem exp_nat (t : ℝ) (n : ℕ) :
    (Real.exp t)^n=Real.exp (t*(n:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,ih,←Real.exp_add]; congr 1; push_cast; ring

/-- Uniform per-rank scalar estimate with the exact moving rank split.
All hypotheses here are numerical interfaces, discharged in source assembly. -/
theorem source_original_global_root_SCALAR_RANK434
    (L e Cv Cb K c P b a delta : ℝ) (A N r : ℕ)
    (hL : 2≤L) (hP : 0≤P) (hb : 0≤b) (ha : 0≤a) (hd : 0≤delta)
    (hA : (A:ℝ)≤L^4) (hK : 0≤K) (hCv : Cv≤(N:ℝ))
    (hPb : P≤L^((Cv+2)*(N:ℝ)))
    (hbb : b≤L^K) (hab : a≤L^Cb)
    (hcut : (8+2*K)*L^(-c/2)≤1)
    (hcoin : (A:ℝ)^2*delta≤Real.exp (-(L^c)/2))
    (hhigh : 2*(e+Cb+Cv+4)*Real.log L≤L^(c/2)) :
    (A:ℝ)^(2*r)*min
      (P*(L^(-(e+Cv+5)))^N*b^(2*r)) (P*a^N*delta^r) ≤
    L^(-(e+2)*(N:ℝ)) := by
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1≤L := le_trans (by norm_num) hL
  have hl : 0≤Real.log L := Real.log_nonneg hL1
  have hN : (0:ℝ)≤N := Nat.cast_nonneg _
  have hr : (0:ℝ)≤ r := Nat.cast_nonneg _
  by_cases hlow : r < Nat.ceil ((N:ℝ)*L^(-c/2))
  · have hrl : (r:ℝ)<(N:ℝ)*L^(-c/2) := (Nat.lt_ceil).mp hlow
    have hcost : (8+2*K)*(r:ℝ)≤(N:ℝ) := by
      have hk0 : 0≤8+2*K := by linarith
      have h1 := mul_le_mul_of_nonneg_left hrl.le hk0
      have h2 := mul_le_mul_of_nonneg_left hcut hN
      nlinarith
    have hcount : (A:ℝ)^(2*r) ≤ L^(8*(r:ℝ)) := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg A : (0:ℝ)≤A) hA (2*r)
      have he : (L^4)^(2*r)=L^(8*(r:ℝ)) := by
        rw [←Real.rpow_natCast L 4]
        norm_num only [Nat.cast_ofNat]
        rw [rpow_nat L 4 hLp]
        push_cast
        congr 1
        ring
      exact he ▸ h
    calc
      _ ≤ (A:ℝ)^(2*r)*(P*(L^(-(e+Cv+5)))^N*b^(2*r)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ L^(8*(r:ℝ))*(L^((Cv+2)*(N:ℝ))*(L^(-(e+Cv+5)))^N*(L^K)^(2*r)) := by
        apply mul_le_mul hcount
        · exact mul_le_mul (mul_le_mul_of_nonneg_right hPb (by positivity))
            (pow_le_pow_left₀ hb hbb _) (pow_nonneg hb _) (by positivity)
        · positivity
        · positivity
      _ = L^((Cv+2)*(N:ℝ)-(e+Cv+5)*(N:ℝ)+(8+2*K)*(r:ℝ)) := by
        rw [rpow_nat L (-(e+Cv+5)) hLp,rpow_nat L K hLp]
        rw [←Real.rpow_add hLp,←Real.rpow_add hLp,←Real.rpow_add hLp]
        push_cast
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (by nlinarith)
  · have hrl : (N:ℝ)*L^(-c/2)≤(r:ℝ) := by
      exact (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_of_not_gt hlow)
    have hmul : L^(-c/2)*L^c=L^(c/2) := by
      rw [←Real.rpow_add hLp]
      congr 1
      ring
    have hrank : (N:ℝ)*L^(c/2) ≤ (r:ℝ)*L^c := by
      have h := mul_le_mul_of_nonneg_right hrl (Real.rpow_nonneg hLp.le c)
      simpa only [mul_assoc,hmul] using h
    have hdecay : ((A:ℝ)^2*delta)^r ≤ Real.exp (-(L^c)/2*(r:ℝ)) := by
      calc
        _ ≤ (Real.exp (-(L^c)/2))^r :=
          pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hd) hcoin r
        _ = _ := exp_nat _ r
    calc
      _ ≤ (A:ℝ)^(2*r)*(P*a^N*delta^r) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg (Nat.cast_nonneg _) _)
      _ = P*a^N*((A:ℝ)^2*delta)^r := by rw [mul_pow,←pow_mul]; ring
      _ ≤ L^((Cv+2)*(N:ℝ))*(L^Cb)^N*Real.exp (-(L^c)/2*(r:ℝ)) := by
        apply mul_le_mul
        · exact mul_le_mul hPb (pow_le_pow_left₀ ha hab _) (pow_nonneg ha _) (by positivity)
        · exact hdecay
        · positivity
        · positivity
      _ = Real.exp (((Cv+2)*(N:ℝ)+Cb*(N:ℝ))*Real.log L-(L^c)/2*(r:ℝ)) := by
        rw [rpow_nat L Cb hLp,←Real.rpow_add hLp,Real.rpow_def_of_pos hLp,←Real.exp_add]
        congr 1
        ring
      _ ≤ L^(-(e+2)*(N:ℝ)) := by
        conv_rhs => rw [Real.rpow_def_of_pos hLp]
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left hhigh hN
        nlinarith

/-- Finite forest aggregation after the scalar rank estimate.
The source parameter assembly must establish its numerical interfaces. -/
theorem source_original_global_root_SCALAR_FOREST434
    (L e Cv Cb K c P b a delta : ℝ) (A N : ℕ)
    (hL : 2≤L) (hN : 5≤N) (he : 0≤e)
    (hP : 0≤P) (hb : 0≤b) (ha : 0≤a) (hd : 0≤delta)
    (hA : (A:ℝ)≤L^4) (hK : 0≤K) (hCv : Cv≤(N:ℝ))
    (hPb : P≤L^((Cv+2)*(N:ℝ)))
    (hbb : b≤L^K) (hab : a≤L^Cb)
    (hcut : (8+2*K)*L^(-c/2)≤1)
    (hcoin : (A:ℝ)^2*delta≤Real.exp (-(L^c)/2))
    (hhigh : 2*(e+Cb+Cv+4)*Real.log L≤L^(c/2))
    (F : SourceOriginalRootForest434 A → ℂ)
    (hLow : ∀ p,‖F p‖≤P*(L^(-(e+Cv+5)))^N*b^(2*sourceOriginalRootForestRank434 p))
    (hHigh : ∀ p,‖F p‖≤P*a^N*delta^(sourceOriginalRootForestRank434 p)) :
    ‖∑ p,F p‖≤L^(-e*(N:ℝ)) := by
  have hLp : 0<L := lt_of_lt_of_le (by norm_num) hL
  have hL1 : 1≤L := le_trans (by norm_num) hL
  have hA1 : ((A+1:ℕ):ℝ)≤L^5 := by
    have h4 : 1≤L^4 := one_le_pow₀ hL1
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hL (pow_nonneg hLp.le 4)]
  have hcount : ((A+1:ℕ):ℝ)≤L^(N:ℝ) := by
    apply hA1.trans
    rw [←Real.rpow_natCast L 5]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by exact_mod_cast hN)
  calc
    _ ≤ ∑ r ∈ Finset.range (A+1),(A:ℝ)^(2*r)*min
        (P*(L^(-(e+Cv+5)))^N*b^(2*r)) (P*a^N*delta^r) :=
      source_original_global_root_FOREST_TWO_BANKS434 A F P (L^(-(e+Cv+5))) b a delta
        hP (by positivity) hb ha hd N hLow hHigh
    _ ≤ ∑ _r ∈ Finset.range (A+1),L^(-(e+2)*(N:ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact source_original_global_root_SCALAR_RANK434 L e Cv Cb K c P b a delta A N r
        hL hP hb ha hd hA hK hCv hPb hbb hab hcut hcoin hhigh
    _ = ((A+1:ℕ):ℝ)*L^(-(e+2)*(N:ℝ)) := by simp
    _ ≤ L^(N:ℝ)*L^(-(e+2)*(N:ℝ)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ _ := by
      rw [←Real.rpow_add hLp]
      apply Real.rpow_le_rpow_of_exponent_le hL1
      nlinarith [(Nat.cast_nonneg N : (0:ℝ)≤N)]
end Green64Analytic.CorrelationSquare

end

end

