module

public import Green64.Library.Correlation.Part002

@[expose] public section

/-!
# Analysis / Estimates / SourceLowFrequencyFourFactorIntegral

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceLowFrequencyFourFactorIntegral -/

section

open MeasureTheory

namespace Green64Analytic.CorrelationMellin

noncomputable def sourceFourFactorAt
    (small long residual : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 t : ℝ) : ℂ :=
  (∑ p ∈ small, bs p * (p:ℂ)⁻¹ * sourcePhase p t) *
  (∑ p ∈ long, bp p * (p:ℂ)⁻¹ * sourcePhase p (sigma1+t)) *
  ((∑ m ∈ Finset.Icc a b,
     alpha m * chi m * (m:ℂ)⁻¹ * sourcePhase m (sigma0+t)) *
   (∑ r ∈ residual, d r * (r:ℂ)⁻¹ * sourcePhase r t))

private theorem source_reciprocal_poly_continuous
    (s : Finset ℕ) (a : ℕ → ℂ) (shift : ℝ) :
    Continuous (fun t : ℝ =>
      ∑ n ∈ s, a n * (n:ℂ)⁻¹ * sourcePhase n (shift+t)) := by
  apply continuous_finset_sum
  intro n hn
  exact continuous_const.mul (sourcePhase_continuous n shift)
private theorem sourceFourFactorAt_continuous
    (small long residual : Finset ℕ) (a b : ℕ)
    (alpha bs bp d : ℕ → ℂ) {q : ℕ}
    (chi : DirichletCharacter ℂ q) (sigma0 sigma1 : ℝ) :
    Continuous (fun t => sourceFourFactorAt small long residual a b
      alpha bs bp d chi sigma0 sigma1 t) := by
  unfold sourceFourFactorAt
  have hsmall := source_reciprocal_poly_continuous small bs 0
  have hlong := source_reciprocal_poly_continuous long bp sigma1
  have hres := source_reciprocal_poly_continuous residual d 0
  have ha := source_reciprocal_poly_continuous
    (Finset.Icc a b) (fun m => alpha m * chi m) sigma0
  convert (hsmall.mul hlong).mul (ha.mul hres) using 1
  funext t
  simp only [Pi.mul_apply, zero_add, mul_assoc]

/-- Source four-factor low-frequency REAL Mellin mean square, assuming
exactly the original universal alpha discrepancy and no U1. -/
theorem source_fourfactor_low_frequency_integral
    (L B x T : ℝ) (hL : 0 < L) (hT : 0 ≤ T)
    (alpha : ℕ → ℂ) (hdisc : SourceAlphaDiscrepancy L B x alpha)
    (q : ℕ) (chi : DirichletCharacter ℂ q)
    (a b : ℕ) (hq : (q:ℝ) ≤ L^B)
    (ha : 1 ≤ a) (hb : (b:ℝ) ≤ x^2)
    (sigma0 sigma1 : ℝ) (hfreq : T + |sigma0| ≤ L^B)
    (P Pprime R0 : ℕ) (small long residual : Finset ℕ)
    (bs bp d : ℕ → ℂ) (Cs Cl D : ℝ)
    (hP : 1 ≤ P) (hPprime : 1 ≤ Pprime) (hR0 : 1 ≤ R0)
    (hCs : 0 ≤ Cs) (hCl : 0 ≤ Cl) (hD : 0 ≤ D)
    (hSmall : small ⊆ Finset.Icc P (2*P))
    (hLong : long ⊆ Finset.Icc Pprime (2*Pprime))
    (hResidual : residual ⊆ Finset.Icc R0 (2*R0))
    (hbs : ∀ p ∈ small, ‖bs p‖ ≤ Cs)
    (hbp : ∀ p ∈ long, ‖bp p‖ ≤ Cl)
    (hd : ∀ r ∈ residual, ‖d r‖ ≤ D) :
    (∫ t in Set.Icc (-T) T,
      ‖sourceFourFactorAt small long residual a b
        alpha bs bp d chi sigma0 sigma1 t‖^2) ≤
      2*T*((2*Cs)*(2*Cl)*(L^(-B)*(2*D)))^2 := by
  let F : ℝ → ℂ := fun t => sourceFourFactorAt small long residual
    a b alpha bs bp d chi sigma0 sigma1 t
  let C : ℝ := (2*Cs)*(2*Cl)*(L^(-B)*(2*D))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpt (t : ℝ) (ht : t ∈ Set.Icc (-T) T) : ‖F t‖ ≤ C := by
    have htb := Set.mem_Icc.mp ht
    have htAbs : |t| ≤ T := abs_le.mpr ⟨by linarith, htb.2⟩
    have htf : |t+sigma0| ≤ L^B := by
      calc
        _ ≤ |t| + |sigma0| := abs_add_le t sigma0
        _ ≤ T + |sigma0| := by gcongr
        _ ≤ L^B := hfreq

    simpa [F, C, sourceFourFactorAt] using
      (source_fourfactor_low_frequency_pointwise
        L B x hL alpha hdisc q chi a b hq ha hb
        sigma0 sigma1 t htf P Pprime R0 small long residual
        bs bp d Cs Cl D hP hPprime hR0 hCs hCl hD
        hSmall hLong hResidual hbs hbp hd)
  have hcont : Continuous F := by
    exact sourceFourFactorAt_continuous small long residual a b
      alpha bs bp d chi sigma0 sigma1
  exact source_pointwise_to_interval_square_energy
    F T C hT hC hcont hpt
end Green64Analytic.CorrelationMellin

end

