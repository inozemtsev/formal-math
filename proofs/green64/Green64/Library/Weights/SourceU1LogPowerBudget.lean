module

public import Green64.Library.Analysis.Estimates.Part006
public import Mathlib

@[expose] public section

/-!
# Weights / SourceU1LogPowerBudget

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceU1LogPowerBudget -/

section

namespace Green64Analytic.LongPrime

private theorem source_log_Y_budget_434
    (L Y : ℝ) (hL : 3 ≤ L) (hY : 1 ≤ Y)
    (hYupper : Y ≤ Real.exp (2*L)) :
    0 ≤ 1+Real.log (4*Y) ∧
    1+Real.log (4*Y) ≤ 4*L := by
  have hPos : 0 ≤ Real.log (4*Y) :=
    Real.log_nonneg (by linarith)
  have hExp : 4 ≤ Real.exp L := by
    have h := Real.add_one_le_exp L
    linarith
  have hProd : 4*Y ≤ Real.exp (3*L) := by
    calc
      4*Y ≤ Real.exp L * Real.exp (2*L) := by gcongr
      _ = Real.exp (3*L) := by
        rw [← Real.exp_add]
        ring_nf
  have hLog : Real.log (4*Y) ≤ Real.log (Real.exp (3*L)) :=
    Real.log_le_log (by positivity) hProd
  rw [Real.log_exp] at hLog
  constructor <;> linarith

/-- An *explicit* source-scale log-power budget. Given polynomial-size
alpha and physical coefficients and certified U1 saving of degree
a+c+D+4, the large-time integral costs at most L^(-D), for
L larger than the fixed U1/mark constant. No desired estimate is
assumed in lieu of a proof. -/
theorem source_U1_arbitrary_log_power_numeric
    (L Y A C Kmark Ku : ℝ) (a c D : ℕ)
    (hL : 3 ≤ L) (hY : 1 ≤ Y)
    (hYupper : Y ≤ Real.exp (2*L))
    (hA : 0 ≤ A) (hC : 0 ≤ C)

    (hAle : A ≤ L^a) (hCle : C ≤ L^c)
    (hKm : 0 ≤ Kmark) (hKu : 0 ≤ Ku)
    (hthreshold : 10752*256*(Kmark*Ku)^2 ≤ L) :
    (Ku/L^(a+c+D+4))^2 *
       (10752*(A*C*Kmark)^2 * (1+Real.log (4*Y))^4)
       ≤ 1/L^D := by
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hKpos : 0 ≤ Kmark*Ku := mul_nonneg hKm hKu
  have hLog := (source_log_Y_budget_434 L Y hL hY hYupper)
  have hAB : A*C*Kmark ≤ L^a * L^c * Kmark := by gcongr
  have hCoeffPos : 0 ≤ A*C*Kmark := by positivity
  have hUpper : 10752*(A*C*Kmark)^2*
       (1+Real.log (4*Y))^4 ≤
       10752*(L^a*L^c*Kmark)^2*(4*L)^4 := by
    gcongr
    · exact hLog.1
    · exact hLog.2
  have hPower : L^(a+c+D+4)=L^a*L^c*L^D*L^4 := by
    rw [show a+c+D+4=a+(c+(D+4)) by omega,
      pow_add,pow_add,pow_add]
    ring
  have hDenom : L^(2*D+4)=L^D*L^D*L^4 := by
    rw [show 2*D+4=D+(D+4) by omega, pow_add, pow_add]
    ring
  have hConst :
      (Ku/L^(a+c+D+4))^2 *
        (10752*(L^a*L^c*Kmark)^2*(4*L)^4) =
      (10752*256*(Kmark*Ku)^2)/L^(2*D+4) := by
    rw [hPower, hDenom]
    field_simp
    ring
  have hPowDom : L ≤ L^(D+4) := by
    calc
      L = L^1 := by ring
      _ ≤ L^(D+4) := by
        apply pow_le_pow_right₀ hLone
        omega
  have hDiv :
      (10752*256*(Kmark*Ku)^2)/L^(2*D+4) ≤ 1/L^D := by
    apply (div_le_div_iff₀ (pow_pos hLpos _) (pow_pos hLpos _)).mpr
    rw [hDenom]
    have hDpos : 0 < L^D := pow_pos hLpos _
    have hD4pos : 0 < L^4 := pow_pos hLpos _
    have hBig : 10752*256*(Kmark*Ku)^2 ≤ L^(D+4) :=
      hthreshold.trans hPowDom
    rw [pow_add] at hBig
    nlinarith [mul_pos hDpos hD4pos]
  calc
    _ ≤ (Ku/L^(a+c+D+4))^2 *
         (10752*(L^a*L^c*Kmark)^2*(4*L)^4) :=
      mul_le_mul_of_nonneg_left hUpper (sq_nonneg _)
    _ = (10752*256*(Kmark*Ku)^2)/L^(2*D+4) := hConst
    _ ≤ 1/L^D := hDiv
end Green64Analytic.LongPrime

end

