module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondOuterPhase (h y : Fin 6 → ℝ) : ℂ :=
  logPhase (h 0) (y 0) * logPhase (h 1) (y 1) *
    logPhase (h 2) (y 2) * logPhase (h 3) (y 3)

def childLogTest (ω : ℝ → ℂ) (h : ℝ) (y : ℝ) : ℂ :=
  ω y * logPhase h (Real.log y)

lemma second_mode_split (y : Fin 6 → ℝ) (t : Frequency) (u : Fin 6 → ℝ) :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

lemma secondOuterPhase_norm (h y : Fin 6 → ℝ) : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,logPhase_norm,mul_one]

lemma second_fresh_scale {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N) (X : ℝ) :
    primeProductNorm p (V ∪ N)/(primeProductNorm p V*X) = primeProductNorm p N/X := by
  rw [primeProductNorm_union p V N hVN]
  field_simp [(primeProductNorm_pos p hp V).ne']

theorem actual_second_columns_separated {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (X : ℝ) (h₁ h₂ : ℝ) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X)) * ω₂ (primeProductNorm p M/X)) *
        logPhase h₁ (Real.log (primeProductNorm p N/X)) *
        logPhase h₂ (Real.log (primeProductNorm p M/X))) =
    star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
      slots₁ lists₁ a₁ (childLogTest ω₁ (-h₁)) (primeProductNorm p x.overlap*X)) *
      canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
      slots₂ lists₂ a₂ (childLogTest ω₂ h₂) (primeProductNorm p x.overlap*X) := by
  rw [← secondChildKernelPair_separated_marked]
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint x.overlap N := by
    apply Finset.disjoint_left.mpr
    intro i hi hiN
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 hi
  have hVM : Disjoint x.overlap M := by
    apply Finset.disjoint_left.mpr
    intro i hi hiM
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hM) hiM)).2 hi
  dsimp only
  rw [second_fresh_scale p hp x.overlap N hVN,second_fresh_scale p hp x.overlap M hVM]
  simp only [secondActualCoefficient,childLogTest,secondChildColumn,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondFreshAssembly -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) : ℂ :=
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  secondOuterPhase h
    (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
  star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ lists₁ a₁ (childLogTest ω₁ (-h 4)) (primeProductNorm p x.overlap*X₀)) *
  canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
    slots₂ lists₂ a₂ (childLogTest ω₂ (h 5)) (primeProductNorm p x.overlap*X₀)

theorem actual_second_full_mode_columns (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2) =
      secondSeparatedPair p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  let O := secondOuterPhase h (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀)
  calc
    _ = O * (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
          logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
          logPhase (h 5) (Real.log (primeProductNorm p M/X₀))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hm : pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2 =
          O * logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
            logPhase (h 5) (Real.log (primeProductNorm p M/X₀)) := by
        rw [second_mode_split]
        simp [secondOuterPhase,secondRelativeLog,secondRelativeNorm,secondActualNorms,O,h]
      rw [hm]
      ring
    _ = _ := by
      rw [actual_second_columns_separated]
      simp only [secondSeparatedPair,h,O,mul_assoc]

theorem actualSecondFreshRows_integral {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), fullProfileDensity g b₁ b₂ b₃ v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← full_density_finite_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondDensityAssembly -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondFreshRows_integral_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

theorem actualSecondFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondGenerator -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondUnitFrequency (u v : Eisˣ) (k : Eis) : Eis := ((u^4*v:Eisˣ):Eis)*k

lemma secondUnitFrequency_injective (u v : Eisˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (Units.ne_zero (u^4*v)) hab

lemma secondUnitFrequency_norm (u v : Eisˣ) (k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding k‖ :=
  GaussGeneratorTransport.norm_eisEmbedding_unit_mul (u^4*v) k

lemma secondUnitFrequency_neg (u v : Eisˣ) (k : Eis) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : Eis →* ℂ) (m label d e k : Eis)
    (L D E : Ideal Eis) (u v : Eisˣ)
    (hl : label = (u:Eis)*primaryGenerator L)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m (primaryGenerator L)
        (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:Eis)^4*((v:Eis)*(primaryGenerator D*primaryGenerator E)*k) =
    primaryGenerator D*primaryGenerator E*(((u:Eis)^4*(v:Eis))*k)
  ring

theorem secondCanonical_row_norm (D E : Ideal Eis) (u v : Eisˣ) (d e k : Eis)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E)) :
    ‖ConcreteTraceCRT.eisEmbedding
      (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*k)‖ := by
  rw [hd]
  have hl : primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k =
      ((u^4*v:Eisˣ):Eis)*(primaryGenerator D*primaryGenerator E*k) := by
    unfold secondUnitFrequency
    ring
  rw [hl,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  have hr : (v:Eis)*(primaryGenerator D*primaryGenerator E)*k =
      (v:Eis)*(primaryGenerator D*primaryGenerator E*k) := by ring
  rw [hr,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryGenerator L ∧
      d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSourceProfile -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def expansionProfileData (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (A₁ A₂ : Finset ι) (x : SecondExpansionData ι) : SecondProfileData ι where
  common := x.sourceCommon
  overlap := x.overlap
  extractedLeft := A₁ ∪ x.sourceCommon
  extractedRight := A₂ ∪ x.sourceCommon
  rayLeft := secondRayMinus Ψ z
  rayRight := secondRayPlus Ψ z
  puncture := m
  quotient := secondExpansionQuotient p x
  oldLabel := c
  oldDivisor := d
  divisor := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  frequency := x.frequency

def expansionProfileWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (Y : ℝ) (x : SecondExpansionData ι) : ℂ :=
  (Y : ℂ) * (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

theorem secondExpansionSource_marked_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    ∑ x ∈ source, expansionProfileWeight p hp hcop hg Ψ m c d z Y x *
      actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  have he := hE x hx
  have hc := weighted_secondRayChild_congr_off_common p hp hcop hg hinj hpr
    x.sourceCommon x.divisor he F x.overlap Ψ Ψ m c d x.frequency z
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ (x.sourceCommon ∪ U)) *
        W₁ (primeProductNorm p (x.sourceCommon ∪ U)/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ (x.sourceCommon ∪ U)) *
        W₂ (primeProductNorm p (x.sourceCommon ∪ U)/X)) Φ Y)
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ ((A₁ ∪ x.sourceCommon) ∪ U) *
        W₁ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ ((A₂ ∪ x.sourceCommon) ∪ U) *
        W₂ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X)) Φ Y)
    (by
      intro S T hGS hGT
      simp only [secondSourcePairKernel,primeProductNorm_union p x.sourceCommon S hGS,
        primeProductNorm_union p x.sourceCommon T hGT,Finset.union_assoc])
  dsimp only at hc
  rw [← secondExpansionQuotient_of_subset p x he] at hc
  rw [hc]
  simp only [expansionProfileWeight,actualSecondProfileRow,expansionProfileData,
    secondSourceCommonCoefficient,Complex.ofReal_pow]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSourceTuples -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure SecondOriginalSource (ι : Type*) (Jo Jn : ℕ) where
  q0 : Ideal Eis
  quotient : Ideal Eis
  J : Ideal Eis
  C : Ideal Eis
  s : Ideal Eis
  b1 : Ideal Eis
  A1 : Ideal Eis
  A2 : Ideal Eis
  dK : Ideal Eis
  J2 : Ideal Eis
  b2 : Ideal Eis
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def originalSecondTuple {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) : SecondTuple Jo Jn where
  outer := ⟨x.q0,x.quotient,sourceIdeal p (x.common \ x.divisor)⟩
  core := ![x.J,x.C,sourceIdeal p x.divisor,x.s,x.b1,x.A1,x.A2,x.dK]
  commonResidual := sourceIdeal p x.overlap
  cubeResidual := x.J2
  secondCube := x.b2
  extractedCommon := sourceIdeal p x.common
  frequency := secondUnitFrequency u v x.frequency
  oldAssigned := x.oldAssigned
  newAssigned := fun i => sourcePrime p (x.newAssigned i)

structure SecondOriginalValid {Jo Jn : ℕ} (x : SecondOriginalSource ι Jo Jn) : Prop where
  j_split : x.s*x.J2 = x.J
  b_split : x.b1*x.b2 = x.q0^2*x.J2^2*x.s
  a1 : x.A1 ∣ (x.b1*x.b2).radical
  a2 : x.A2 ∣ (x.b1*x.b2).radical
  first_divisor : x.dK ∣ x.C*(x.b1*x.b2).radical
  first_generator : primaryGenerator x.dK ≠ 0
  second_subset : x.divisor ⊆ x.common
  old_support : ∀ i, (x.oldAssigned i).val ∣ x.q0*x.J*x.C*x.quotient
  new_support : ∀ i, x.newAssigned i ∈ x.common ∪ x.overlap

theorem originalSecondTuple_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) (hx : SecondOriginalValid x) :
    Valid (originalSecondTuple p u v x)
      (secondChild (originalSecondTuple p u v x)).1
      (secondChild (originalSecondTuple p u v x)).2.1
      (secondChild (originalSecondTuple p u v x)).2.2 := by
  have hproduct : sourceIdeal p x.divisor * sourceIdeal p (x.common \ x.divisor) =
      sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common \ x.divisor)
      (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
      Finset.union_sdiff_of_subset hx.second_subset]
  refine ⟨rfl,rfl,hx.j_split,hx.b_split,hx.a1,hx.a2,hx.first_divisor,?_,hx.first_generator,?_,rfl,?_,?_⟩
  · exact hproduct
  · change primaryGenerator (sourceIdeal p x.divisor) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · intro i
    apply (hx.old_support i).trans
    change x.q0*x.J*x.C*x.quotient ∣
      x.q0*(x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*x.quotient
    refine ⟨sourceIdeal p x.divisor*sourceIdeal p x.overlap,?_⟩
    ring
  · intro i
    change (sourcePrime p (x.newAssigned i)).val ∣
      (x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*sourceIdeal p (x.common \ x.divisor)
    have hslot : (sourcePrime p (x.newAssigned i)).val ∣
        sourceIdeal p x.common*sourceIdeal p x.overlap := by
      rcases Finset.mem_union.mp (hx.new_support i) with hi|hi
      · exact dvd_mul_of_dvd_left (source_prime_dvd p x.common _ hi) _
      · exact dvd_mul_of_dvd_right (source_prime_dvd p x.overlap _ hi) _
    apply hslot.trans
    refine ⟨x.J*x.C,?_⟩
    rw [←hproduct]
    ring

theorem originalSecondTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) :
    Function.Injective (originalSecondTuple (Jo:=Jo) (Jn:=Jn) p u v) := by
  intro x y hxy
  have hi := sourceIdeal_injective p hinj
  have hcore (i : Fin 8) := congrArg (fun z : SecondTuple Jo Jn => z.core i) hxy
  apply SecondOriginalSource.ext
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.q0) hxy
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.quotient) hxy
  · exact hcore 0
  · exact hcore 1
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hcore 7
  · exact congrArg SecondTuple.cubeResidual hxy
  · exact congrArg SecondTuple.secondCube hxy
  · exact hi (congrArg SecondTuple.extractedCommon hxy)
  · exact hi (hcore 2)
  · exact hi (congrArg SecondTuple.commonResidual hxy)
  · exact secondUnitFrequency_injective u v (congrArg SecondTuple.frequency hxy)
  · exact congrArg SecondTuple.oldAssigned hxy
  · funext i
    apply hinj
    exact congrArg (fun z : SecondTuple Jo Jn => (z.newAssigned i).val) hxy

theorem original_second_source_fiber_bound (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (SecondOriginalSource ι Jo Jn))
    (hs : ∀ x ∈ source, SecondOriginalValid x)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let S := source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))
  have hv : ∀ y ∈ S.image (originalSecondTuple p u v), Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    have hh := originalSecondTuple_valid p hp hpr u v x (hs x hxs)
    simpa only [he] using hh
  have hb := valid_tuple_card_le_slot_cap (S.image (originalSecondTuple p u v))
    γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_of_injective S (originalSecondTuple_injective p hinj u v)] at hb
  exact hb

theorem originalSecondTuple_row_norm {Jo Jn : ℕ} (u v : Eisˣ)
    (x : SecondOriginalSource ι Jo Jn) (d e : Eis)
    (hde : d*e = (v:Eis)*(primaryGenerator x.dK*primaryGenerator (sourceIdeal p x.divisor))) :
    ‖ConcreteTraceCRT.eisEmbedding (secondChild (originalSecondTuple p u v x)).2.2‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*x.frequency)‖ := by
  exact secondCanonical_row_norm x.dK (sourceIdeal p x.divisor) u v d e x.frequency hde

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CubeSource -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

lemma sourceIdeal_isRadical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (S : Finset ι) :
    (sourceIdeal p S).IsRadical := by
  change (Ideal.span {∏ i ∈ S,p i}).IsRadical
  rw [FiniteGaussPhase.span_finset_prod]
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _ _ => by simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Ideal.mul_eq_inf_of_isCoprime]
    · exact (inferInstance : (Ideal.span {p a}).IsPrime).isRadical.inf ih
    · apply IsCoprime.prod_right
      intro b hb
      exact hcop (fun he => ha (he.symm ▸ hb))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

theorem cubeSupport_dvd_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p B ∣
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  apply Ideal.dvd_iff_le.mpr
  apply (sourceIdeal_isRadical p hcop B).radical_le_iff.mpr
  apply Ideal.dvd_iff_le.mp
  rw [Ideal.span_singleton_mul_span_singleton,←primeProduct_add]
  exact cubeRadical_span_dvd_product p B _ hv

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_cubeSupport (B : Finset ι) (ε : ι → Bool) :
    Ideal.span {aLabel p B ε} ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  unfold aLabel primeProduct
  change (∏ i ∈ B,p i^bit (ε i)) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases hh : ε i <;> simp [bit]

theorem firstMask_dvd_cube_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B C D : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p D ∣ sourceIdeal p C *
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  have hd := InverseInitialArithmetic.sourceIdeal_dvd p D (C∪B) hD
  rw [sourceIdeal_union p C B hCB] at hd
  exact hd.trans (mul_dvd_mul_left _ (cubeSupport_dvd_radical p hcop B v₁ v₂ hv))

def cubeSecondSource {Jo Jn : ℕ} (B C D G E V : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι) :
    SecondOriginalSource ι Jo Jn where
  q0 := Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  quotient := t
  J := Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  C := sourceIdeal p C
  s := Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)}
  b1 := Ideal.span {primeProduct p B v₁}
  A1 := Ideal.span {aLabel p B ε₁}
  A2 := Ideal.span {aLabel p B ε₂}
  dK := sourceIdeal p D
  J2 := Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  common := G
  divisor := E
  overlap := V
  frequency := k
  oldAssigned := oldAssigned
  newAssigned := newAssigned

theorem cubeSecondSource_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣
      Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} *
      Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂} * sourceIdeal p C * t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) := by
  constructor
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} = _
    rw [Ideal.span_singleton_mul_span_singleton,←jLabel_eq_squarefree_mul_j2]
    rfl
  · have hb := congrArg (fun a : Eis => (Ideal.span {a} : Ideal Eis))
      (cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv)
    simpa only [cubeSecondSource,pow_two,←Ideal.span_singleton_mul_span_singleton] using hb
  · exact (aLabel_dvd_cubeSupport p B ε₁).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact (aLabel_dvd_cubeSupport p B ε₂).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact firstMask_dvd_cube_radical p hcop B C D hCB hD v₁ v₂ hv
  · change primaryGenerator (sourceIdeal p D) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · exact hE
  · exact hold
  · exact hnew

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem oldSlot_dvd_reconstructed_support
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (P t : Ideal Eis)
    (hP : P ∣ sourceIdeal p B*sourceIdeal p C*t) :
    P ∣ Ideal.span {b0Label p B v ε₁ ε₂}*
      Ideal.span {jLabel p B v ε₁ ε₂}*sourceIdeal p C*t := by
  have hb := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv)
  change sourceIdeal p B ∣ Ideal.span {jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂} at hb
  rw [←Ideal.span_singleton_mul_span_singleton,mul_comm (Ideal.span {jLabel p B v ε₁ ε₂})] at hb
  exact hP.trans (mul_dvd_mul_right (mul_dvd_mul_right hb _) _)

theorem cubeSecondSource_valid_original_slots (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣ sourceIdeal p B*sourceIdeal p C*t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) :=
  cubeSecondSource_valid p hp hpr hcop B C D G E V hCB hD hE v₁ v₂ ε₁ ε₂ hv t k
    oldAssigned newAssigned
    (fun i => oldSlot_dvd_reconstructed_support p B C _ ε₁ ε₂ hv _ t (hold i)) hnew

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CubeSupportNorm -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀ i,p i≠0)

include hp in
theorem cube_whole_support_norm (b : CubeCoordinates ι) :
    primeProductNorm p b.support≤
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2*
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 := by
  have hd := cubeRadical_span_dvd_product p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.support_pos
  have hne : (Ideal.span {primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i)}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hn := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd))
  have he : (Ideal.absNorm (sourceIdeal p b.support):ℝ)=primeProductNorm p b.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈b.support,p i)).symm
  have hh : primeProductNorm p b.support≤
      ‖eisEmbedding (primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i))‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,←he]
    exact_mod_cast hn
  simpa only [primeProduct_add,map_mul,norm_mul,mul_pow] using hh

include hp in
theorem cube_whole_support_dyad (b : CubeCoordinates ι) (B : ℝ) (hB : 0≤B)
    (hl : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hr : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p b.support≤B^2 :=
  (cube_whole_support_norm p hp b).trans ((mul_le_mul hl hr (sq_nonneg _) hB).trans_eq (pow_two B).symm)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstMarkedZeroSource -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_marked_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (coeff:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ)
      (extra₁ extra₂ : CubeCoordinates ι→Finset ι)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖coeff b D I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,coeff b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W K‖≤
      C*B^(1+ε)*L*F*Γ*((B^2*L)^ε)^2*(G₁*G₂ * |K| * ‖paperRadialFourier W 0‖) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_variable_first_zero_bound ε hε
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cz*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    test₁ test₂ extra₁ extra₂ slots lists a W Γ G₁ G₂ L K B F
    hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff hslots ha
    he₁ he₂ htest₁ htest₂ hs₁ hs₂
  have hB0 : 0≤B := le_trans zero_le_one hB
  have hextra (extra : CubeCoordinates ι→Finset ι) (he : ∀b∈bs,extra b⊆b.support)
      (b : CubeCoordinates ι) (hb : b∈bs) : primeProductNorm p (extra b)≤B^2 :=
    (primeProductNorm_mono p hp (he b hb)).trans (cube_whole_support_dyad p hp b B hB0 (hb₁ b hb) (hb₂ b hb))
  have ht₁ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₁ b∪U)*test₁ b U‖≤Cm*(B^2*L)^ε*G₁ :=
    hmark p hp hcop slots lists a hslots ha (extra₁ b) (test₁ b) (B^2) G₁ L
      (sq_nonneg _) hG₁ hL.le (hextra extra₁ he₁ b hb) (htest₁ b hb) (hs₁ b hb)
  have ht₂ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₂ b∪U)*test₂ b U‖≤Cm*(B^2*L)^ε*G₂ :=
    hmark p hp hcop slots lists a hslots ha (extra₂ b) (test₂ b) (B^2) G₂ L
      (sq_nonneg _) hG₂ hL.le (hextra extra₂ he₂ b hb) (htest₂ b hb) (hs₂ b hb)
  have hh := hzero p hp hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W
    Γ (Cm*(B^2*L)^ε*G₁) (Cm*(B^2*L)^ε*G₂) L K B F
    hΓ (by positivity) (by positivity) hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff ht₁ ht₂
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2)
  exact hh.trans_eq (by ring)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstTailAggregation -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstLocalPhysicalTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (T:Finset ι→Finset O) (D:Finset ι):ℂ :=
  ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
    (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) W (fun _=>1) (fun _=>1) 1 1 K
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

theorem cube_tail_support_test (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K L:ℝ) (T:Finset ι→Finset O)
    (hs:∀U,H₁ U≠0→primeProductNorm p U≤L) (hC:¬primeProductNorm p C≤L) :
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T=0 := by
  have hz (U:Finset ι):H₁ ((b.rightDivisor∪C)∪U)=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans (hs _ h))
  have hcoef (U:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ U=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_first_tail_from_local (ε:ℝ) (hε:0<ε) :
    ∃Ctail:ℝ,0<Ctail ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (K B L F Γ E:ℝ)
      (T:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→Finset O),
      1≤B → 0<L → 1≤F → 0≤Γ → 0≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀C∈boundedPrimeSupports p (pool\b.support) L,∀I∈labels,
        ∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I) D‖≤E) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I)‖≤
        Ctail*B^(4+ε)*L^2*F*Γ*E := by
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨Cb*128^3,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W K B L F Γ E T
    hB hL hF hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hs hlocal
  have hBp:0<B:=zero_lt_one.trans_le hB
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hBp.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cube_whole_support_dyad p hp b B hBp.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels):
      ‖z b C I‖≤128*(L*B^2)*E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C
      Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)).trans
    calc
      _≤∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,E:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D)
          (hlocal b hb C hC I hI D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul E)
      _= ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*E:=by simp
      _≤_:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B L hBp hL hCB
        (hb₁ b hb) (hb₂ b hb) (Finset.mem_filter.mp hC).2) hE
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*L)*(128*F)*Γ*(128*(L*B^2)*E):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from cube_tail_support_test p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _
        (H₁ b) (H₂ b) W K L (T b C I) (hs b hb) hn,mul_zero]
    rw [heq]
    calc
      _≤∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,Γ*(128*(L*B^2)*E):=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro C hC
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I hI) (norm_nonneg _) hΓ
      _= ((boundedPrimeSupports p (pool\b.support) L).card:ℝ)*(labels.card:ℝ)*Γ*(128*(L*B^2)*E):=by simp;ring
      _≤_:=by gcongr;exact boundedPrimeSupports_card_positive p hp hinj _ _ hL
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _≤∑b∈bs,(128*L)*(128*F)*Γ*(128*(L*B^2)*E):=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hcommon)
    _= (bs.card:ℝ)*((128*L)*(128*F)*Γ*(128*(L*B^2)*E)):=by simp
    _≤(Cb*B^(1+ε)*B)*((128*L)*(128*F)*Γ*(128*(L*B^2)*E)):=by gcongr
    _= _:=by
      have he:B^(1+ε)*B*B^2=B^(4+ε):=by
        calc
          _=B^(1+ε)*B^(1:ℝ)*B^(2:ℝ):=by rw [Real.rpow_one,Real.rpow_two]
          _=B^((1+ε)+1+2):=by rw [←Real.rpow_add hBp,←Real.rpow_add hBp]
          _= _:=by congr 1;ring
      calc
        _=(Cb*128^3)*(B^(1+ε)*B*B^2)*L^2*F*Γ*E:=by ring
        _= _:=by rw [he]

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstRapidPhysicalTail -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_rapid_physical_tail (ε:ℝ) (hε:0<ε)
    (Mmax Fmax eta tau saving:ℝ) (hMm:0≤Mmax) (hFm:0≤Fmax)
    (heta:0≤eta) (htau:0<tau) :
    ∃ (s:Finset (ℕ×ℕ)) (Ct Cm:ℝ),0<Ct ∧ 0<Cm ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι) (C D extra₁ extra₂:Finset ι)
      (f:Ideal O) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (test₁ test₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (E G₁ G₂ Z M r ell V B j:ℝ) (delta:Finset ι→ℝ),
      b.Admissible → Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      f≠0 → 0≤E → 0≤G₁ → 0≤G₂ → 1≤Z → 0≤M → M≤Mmax →
      0≤ell → 0≤V → -eta≤ r → r+3*ell+V≤Fmax →
      primeProductNorm p C≤Z^(r+eta) →
      primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖test₁ U‖≤G₁) → (∀U,‖test₂ U‖≤G₂) →
      (∀U,test₁ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀U,test₂ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f:ℝ)≤Z^(V+eta) → primeProductNorm p D≤Z^(delta D+eta) →
      Z^(B-eta)≤primeProductNorm p C →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2 →
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W (Z^M)
        (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent
          b.rightExponent b.leftBit b.rightBit f)
          (Z^(firstPhysicalHeight M r ell V (delta D) B j+12*eta+tau))) D‖≤
      65536*(Cm*(E*Z^(r+eta))^ε*G₁)*(Cm*(E*Z^(r+eta))^ε*G₂)*
        (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=choose_actual_first_tail_order Mmax Fmax eta tau saving hMm hFm heta htau
  obtain ⟨s,Ct,Cm,hCt,hCm,htail⟩:=first_whole_cube_canonical_tail ε hε order
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C D extra₁ extra₂ f Ψ₁ Ψ₂ m₁ m₂ slots lists a
    test₁ test₂ W E G₁ G₂ Z M r ell V B j delta hb hCB hD hf hE hG₁ hG₂ hZ hM hMmax
    hell hV hr hwhole hC he₁ he₂ hΨ₁ hΨ₂ hslots ha ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlocal:=htail p hp hinj hcop hg hc pool b hb C D hCB f hf Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V
    (delta D) B j eta tau hG₁ hG₂ hz ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  dsimp only at hlocal
  apply hlocal.trans
  exact horder p hp b C D hCB hD Z M r ell V
    (Cm*(E*Z^(r+eta))^ε*G₁) (Cm*(E*Z^(r+eta))^ε*G₂)
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hM hMmax hell hV hr hwhole (by positivity) (by positivity) (by positivity) hb₁ hb₂ hC

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstFullRapidTail -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def firstExactPhysicalCutoff {ι:Type*} [DecidableEq ι] (p:ι→O)
    (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O) (Z M r ell V eta tau:ℝ) (D:Finset ι):Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (Z^(firstPhysicalHeight M r ell V (Real.logb Z (primeProductNorm p D))
      (Real.logb Z (primeProductNorm p C))
      (Real.logb Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau))

theorem full_first_whole_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
    (hMm:0≤Mmax) (hFm:0≤Fmax) (heta:0≤eta) (htau:0<tau) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (weights:σ→ι→ℂ)
      (extra₁ extra₂:CubeCoordinates ι→Finset ι)
      (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (Z M r ell V Γ G₁ G₂:ℝ),
      1<Z → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤ r → r+3*ell+V≤Fmax →
      0≤Γ → 0≤G₁ → 0≤G₂ →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta)) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
          (firstExactPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*65536*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
    hadm hb₁ hb₂ hI0 hIF ha hslots hw he₁ he₂ ht₁ ht₂ hs₁ hs₂
  have hz:0<Z:=zero_lt_one.trans hZ
  let B:=Z^(ell+eta)
  let L:=Z^(r+eta)
  let E:=65536*(Cm*(B^2*L)*G₁)*(Cm*(B^2*L)*G₂)*
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving')
  have hB:1≤B:=Real.one_le_rpow hZ.le (by linarith)
  have hL:0<L:=Real.rpow_pos_of_pos hz _
  have hE:0≤E:=by dsimp [E,B,L];positivity
  have hextra (extra:CubeCoordinates ι→Finset ι) (he:∀b∈bs,extra b⊆b.support)
      (b:CubeCoordinates ι) (hb:b∈bs):primeProductNorm p (extra b)≤B^2:=
    (primeProductNorm_mono p hp (he b hb)).trans
      (cube_whole_support_dyad p hp b B (zero_le_one.trans hB) (hb₁ b hb) (hb₂ b hb))
  have hlocal (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels)
      (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
        (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
        (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
        (firstExactPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:0<x):x≤Z^(Real.logb Z x+eta):=by
      conv_lhs=>rw [←Real.rpow_logb hz (ne_of_gt hZ) hx]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hlower (x:ℝ) (hx:0<x):Z^(Real.logb Z x-eta)≤x:=by
      conv_rhs=>rw [←Real.rpow_logb hz (ne_of_gt hZ) hx]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hjpos:0<‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (Real.logb Z (primeProductNorm p C))
      (Real.logb Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>Real.logb Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_pos p hp D)) (hlower _ (primeProductNorm_pos p hp C)) (hlower _ hjpos)
    simpa only [firstLocalPhysicalTail,firstExactPhysicalCutoff,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstExactPhysicalCutoff p b C I Z M r ell V eta tau)
    hB hL (Real.one_le_rpow hZ.le (by linarith)) hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2) hlocal
  apply he.trans
  have hexp:B^9*L^4*Z^(V+eta)*Z^(-saving')≤Z^(-saving):=by
    dsimp [B,L]
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [saving']
    norm_num
    linarith
  have hm:=mul_le_mul_of_nonneg_left hexp
    (show 0≤Ca*65536*Cm^2*Ct*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) from by positivity)
  convert hm using 1
  · dsimp only [E]
    norm_num
    ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedZeroEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_reopened_marked_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (W:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Γ G L K B F:ℝ),
      0≤Γ → 0≤G → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ u‖≤1) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖W (primeProductNorm p U)‖≤G) →
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤L) →
      ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ K)‖≤
      C*B^(1+ε)*L*F*Γ^2*((B^2*L)^ε)^2*(G^2*|K| *‖paperRadialFourier Φ 0‖) := by
  obtain ⟨C,hC,he⟩ := full_marked_first_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G L K B F
    hΓ hG hL hB hF hΨ hQ hn hFlabels hβ hslots ha hW hs
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hcoeff := reopenedPairCoefficient_bound Q labels β Γ hΓ hβ
  have hh := he p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (fun _ U=>W (primeProductNorm p U))
    (fun _ U=>W (primeProductNorm p U))
    (fun b=>b.rightExponent.support) (fun b=>b.leftExponent.support)
    slots lists a Φ (Γ^2) G G L K B F (sq_nonneg _) hG hG hL hB hF hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun b hb'=> (hb b hb').1) (fun b hb'=> (hb b hb').2)
    hn hFlabels (fun b hb C hC I hI=>hcoeff b hb C I hI) hslots ha
    (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hs) (fun _ _=>hs)
  simpa only [reopenedPhysicalSourceSum,Finset.union_comm,pow_two] using hh

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.OriginalZeroPhysical -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_first_zero_physical (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
      (Z M r ell V eta Γ G:ℝ),1<Z→0≤ell+eta→0≤V+eta→0≤Γ→0≤G→
      (∀u,‖Ψ u‖≤1)→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀U,‖W (primeProductNorm p U)‖≤G)→
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta))→
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ (Z^M))‖≤
        C*Γ^2*G^2*‖paperRadialFourier Φ 0‖*Z^(M-ell+3*eta+ε*(5*ell+2*r+7*eta)):=by
  obtain ⟨C,hC,he⟩:=original_reopened_marked_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Z M r ell V eta Γ G
    hZ hell hV hΓ hG hΨ hQ hn hlabels hβ hslots ha hW hs
  have hz:0<Z:=zero_lt_one.trans hZ
  have hb:=he p hp hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G
    (Z^(r+eta)) (Z^M) (Z^(ell+eta)) (Z^(V+eta)) hΓ hG
    (Real.rpow_pos_of_pos hz _) (Real.one_le_rpow hZ.le hell) (Real.one_le_rpow hZ.le hV)
    hΨ hQ hn hlabels hβ hslots ha hW hs
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hz.le _)).trans
  apply le_of_eq
  rw [abs_of_pos (Real.rpow_pos_of_pos hz M)]
  have hp2 (x:ℝ):(Z^x)^2=Z^(2*x):=by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
  rw [hp2,←Real.rpow_add hz,←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,hp2]
  calc
    _=(C*Γ^2*G^2*‖paperRadialFourier Φ 0‖)*
      (Z^(-r-2*ell-V)*Z^((ell+eta)*(1+ε))*Z^(r+eta)*Z^(V+eta)*
        Z^(2*((2*(ell+eta)+(r+eta))*ε))*Z^M):=by ring
    _=_:=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSourceEncoding -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_injective)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure MarkedSecondSource (ι : Type*) (Jo Jn : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  second : SecondExpansionData ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def markedSecondOriginal {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : SecondOriginalSource ι Jo Jn :=
  cubeSecondSource p x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.quotient x.second.frequency x.oldAssigned x.newAssigned

theorem markedSecondOriginal_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} :
    Set.InjOn (markedSecondOriginal (Jo:=Jo) (Jn:=Jn) p) {x | x.cube.Admissible} := by
  intro x hx y hy hxy
  have hc : x.cube = y.cube := by
    apply cubeDivisorKey_injective_on_product p hp hinj hx hy
    · simpa only [markedSecondOriginal,cubeSecondSource,cubeProductIdeal] using
        congrArg (fun z : SecondOriginalSource ι Jo Jn => z.b1*z.b2) hxy
    · funext i
      fin_cases i
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.b1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A2 hxy
  apply MarkedSecondSource.ext hc
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.C hxy)
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.dK hxy)
  · apply SecondExpansionData.ext
    · exact congrArg SecondOriginalSource.common hxy
    · exact congrArg SecondOriginalSource.divisor hxy
    · exact congrArg SecondOriginalSource.overlap hxy
    · exact congrArg SecondOriginalSource.frequency hxy
  · exact congrArg SecondOriginalSource.quotient hxy
  · exact congrArg SecondOriginalSource.oldAssigned hxy
  · exact congrArg SecondOriginalSource.newAssigned hxy

theorem markedSecondTuple_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : Eisˣ) :
    Set.InjOn (fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x))
      {x | x.cube.Admissible} := by
  intro x hx y hy he
  exact markedSecondOriginal_injOn p hp hinj hx hy
    (originalSecondTuple_injective p hinj u v he)

theorem markedSecondOriginal_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap) :
    SecondOriginalValid (markedSecondOriginal p x) :=
  cubeSecondSource_valid_original_slots p hp hpr hcop x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap hCB hD hE
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.cube.support_pos
    x.quotient x.second.frequency x.oldAssigned x.newAssigned hold hnew

theorem actual_marked_second_source_fiber (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (ha : ∀ x ∈ source, x.cube.Admissible)
    (hCB : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support)
    (hD : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v (markedSecondOriginal p x)) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let encode := fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x)
  let S := source.filter (fun x => secondChild (encode x) = (γ,f,k))
  have hvalid : ∀ x ∈ source,
      Valid (encode x) (secondChild (encode x)).1 (secondChild (encode x)).2.1 (secondChild (encode x)).2.2 := by
    intro x hx
    exact originalSecondTuple_valid p hp hpr u v (markedSecondOriginal p x)
      (markedSecondOriginal_valid p hp hpr hcop x (hCB x hx) (hD x hx) (hE x hx) (hold x hx) (hnew x hx))
  have hv : ∀ y ∈ S.image encode, Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using hvalid x hxs
  have hi : Set.InjOn encode (S : Set (MarkedSecondSource ι Jo Jn)) := by
    intro x hx y hy he
    exact markedSecondTuple_injOn p hp hinj u v
      (ha x (Finset.mem_filter.mp hx).1) (ha y (Finset.mem_filter.mp hy).1) he
  have hb := valid_tuple_card_le_slot_cap (S.image encode) γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_iff.mpr hi] at hb
  exact hb

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondFixedFamily -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_drop_puncture (Ψ : Eis →* ℂ) (m d f k : Eis)
    (hd : d ∣ m*f) (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*d) f k H S =
      secondChildColumn p hp hcop hg Ψ m f k H S := by
  by_cases hz : ∃ i ∈ S, d ∈ Ideal.span {p i}
  · obtain ⟨i,hi,hdI⟩ := hz
    have hr : m*f ∈ Ideal.span {p i} := by
      obtain ⟨a,ha⟩ := hd
      rw [ha]
      exact Ideal.mul_mem_right _ _ hdI
    have hl : (m*d)*f ∈ Ideal.span {p i} := by
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdI)
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ (m*d) f k H S i hi hl,
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k H S i hi hr]
  · have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S d = 1 := by
      simp only [rowCoprimeMask,ite_eq_right hz]
    simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg S,hm,mul_one]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_drop_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m d f k : Eis) (hd : d ∣ m*f)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*d) f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_drop_puncture p hp hcop hg Ψ m d f k hd]

theorem canonicalMarkedSplit_original_lists (F V A : Finset ι) (Ψ : Eis →* ℂ)
    (m r c d e k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hA : ∀ i ∈ A, (m*r)*(c*e*∏ j ∈ V,p j) ∈ Ideal.span {p i}) :
    canonicalMarkedSplit p hp hcop hg F V A Ψ m r c d e k slots lists a W X =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*r)
          (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) := by
  unfold canonicalMarkedSplit
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ (m*r)
    (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) hA]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_first_divisor_dvd_child
    (B C D V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (m r e : Eis) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) D ∣
      ((m*b0Label p B v ε₁ ε₂)*r)*
        (((∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂)*e*∏ i ∈ V,p i) := by
  have hd := poisson_mask_generator_dvd p D (C∪B) hD
  rw [Finset.prod_union hCB] at hd
  have hb := cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv
  change (∏ i ∈ B,p i) ∣ jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂ at hb
  apply (hd.trans (mul_dvd_mul_left (∏ i ∈ C,p i) hb)).trans
  refine ⟨m*r*e*∏ i ∈ V,p i,?_⟩
  ring

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_extracted_support_killed
    (B C G E V A : Finset ι) (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) (m : Eis) :
    ∀ i ∈ A,
      ((m*b0Label p B v ε₁ ε₂)*secondMaskQuotient p E G hEG)*
        (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*
          primeSubsetGenerator (fun j => Ideal.span {p j}) E*∏ j ∈ V,p j) ∈ Ideal.span {p i} := by
  let r := secondMaskQuotient p E G hEG
  let e := primeSubsetGenerator (fun j => Ideal.span {p j}) E
  let T := ((m*b0Label p B v ε₁ ε₂)*r)*
    (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*e*∏ j ∈ V,p j)
  have hb : (∏ j ∈ B,p j) ∣ T := by
    apply (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv).trans
    refine ⟨m*r*(∏ j ∈ C,p j)*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hc : (∏ j ∈ C,p j) ∣ T := by
    refine ⟨m*b0Label p B v ε₁ ε₂*r*jLabel p B v ε₁ ε₂*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hg' : (∏ j ∈ G,p j) ∣ T := by
    rw [secondMaskQuotient_spec p E G hEG]
    refine ⟨m*b0Label p B v ε₁ ε₂*(∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂*∏ j ∈ V,p j,?_⟩
    dsimp [T,r,e]
    ring
  intro i hi
  apply Ideal.mem_span_singleton.mpr
  change p i ∣ T
  rcases Finset.mem_union.mp (hA hi) with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.dvd_prod_of_mem p hi).trans hb
    · exact (Finset.dvd_prod_of_mem p hi).trans hc
  · exact (Finset.dvd_prod_of_mem p hi).trans hg'

theorem actual_second_split_fixed_family
    (F B C D G E V A : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (Ψ : Eis →* ℂ) (m k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
    canonicalMarkedSplit p hp hcop hg F V A Ψ
      (m*b0Label p B v ε₁ ε₂*d) r c d e k slots lists a W (primeProductNorm p V*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ ((m*b0Label p B v ε₁ ε₂)*r)
          (c*e*∏ i ∈ V,p i) (d*e*k) (slots\J) lists a W X := by
  dsimp only
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
  have hd := actual_first_divisor_dvd_child p B C D V hCB hD v ε₁ ε₂ hv m r e
  have hk := actual_second_extracted_support_killed p B C G E V A hEG hA v ε₁ ε₂ hv m
  have hm : (m*b0Label p B v ε₁ ε₂*d)*r = ((m*b0Label p B v ε₁ ε₂)*r)*d := by ring
  have hX : primeProductNorm p V*X/primeProductNorm p V = X := by
    field_simp [(primeProductNorm_pos p hp V).ne']
  unfold canonicalMarkedSplit
  rw [show m*b0Label p B v ε₁ ε₂*primeSubsetGenerator (fun i => Ideal.span {p i}) D *
      secondMaskQuotient p E G hEG = ((m*b0Label p B v ε₁ ε₂)*r)*d from hm]
  rw [hX]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_drop_puncture p hp hcop hg F Ψ _ d _ _ hd]
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ _ _ _ (slots\J) lists a W X hk]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondVaryingDensity -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondVaryingFreshRows_integral_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

theorem actualSecondVaryingFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondWeights -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSignedSourceWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap

theorem expansionProfileWeight_eq_signed (Ψ : Eis →* ℂ) (m c d : Eis)
    (z : SecondRayIndex) (Y : ℝ) (x : SecondExpansionData ι) :
    expansionProfileWeight p hp hcop hg Ψ m c d z Y x =
      (Y : ℂ)*secondRayCoefficient z*secondSignedSourceWeight p hp hcop hg Ψ m c d z x := by
  simp only [expansionProfileWeight,secondSignedSourceWeight,secondTotalWeight]
  ring

theorem secondSignedSourceWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) :
    ‖secondSignedSourceWeight p hp hcop hg Ψ m c d z x‖ ≤ 1 := by
  have hinput : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d x.sourceCommon).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one
    (∏ i ∈ x.divisor,Ideal.span {p i})
  have hcommon := secondCommonWeight_norm_le p hp hcop hg hinj hc
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency) x.overlap
  have hc1 : ‖secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap‖ ≤ 1 := by
    apply hcommon.trans
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((secondRayMinus_norm_le Ψ z _).trans (hΨ _))).trans
      ((secondRayPlus_norm_le Ψ z _).trans (hΨ _))
  simp only [secondSignedSourceWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖))]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hinput).trans hμ)).trans hc1

theorem secondExpansionSource_signed_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x ∈ source, secondSignedSourceWeight p hp hcop hg Ψ m c d z x *
        actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [secondExpansionSource_marked_profile p hp hcop hg hinj hpr (hE := hE)]
  simp only [expansionProfileWeight_eq_signed,Finset.mul_sum,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.TripleMass -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def tripleDivisorWeight (K : ℕ) (γ : OuterTriple) : ℝ :=
  ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
    ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
    ((idealDivisors γ.residual).card : ℝ)^(2*K)

lemma tripleDivisorWeight_nonneg (K : ℕ) (γ : OuterTriple) :
    0 ≤ tripleDivisorWeight K γ := by unfold tripleDivisorWeight; positivity

theorem ideal_divisor_power_small (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal Eis, I ≠ 0 →
      ((idealDivisors I).card : ℝ)^j ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  have hj : 0 < (j+1 : ℝ) := by positivity
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/(j+1)) (div_pos hε hj)
  refine ⟨C^(j+1), by positivity, ?_⟩
  intro I hI
  have hcard : (1 : ℝ) ≤ (idealDivisors I).card := by
    exact_mod_cast InverseInitialFibers.divisor_card_pos I hI
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^(j+1) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(Ideal.absNorm I : ℝ)^(ε/(j+1)))^(j+1) :=
      pow_le_pow_left₀ (by positivity) (hb I hI) _
    _ = C^(j+1)*(Ideal.absNorm I : ℝ)^ε := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      field_simp

theorem tripleDivisorWeight_small (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : OuterTriple,
      γ.q0 ≠ 0 → γ.quotient ≠ 0 → γ.residual ≠ 0 →
      tripleDivisorWeight K γ ≤
        C*((Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient*Ideal.absNorm γ.residual)^ε := by
  obtain ⟨Cq,hCq,hq⟩ := ideal_divisor_power_small (5+2*K) ε hε
  obtain ⟨Ct,hCt,ht⟩ := ideal_divisor_power_small (2*K) ε hε
  refine ⟨Cq*Ct*Ct, by positivity, ?_⟩
  intro γ hq0 ht0 hr0
  unfold tripleDivisorWeight
  calc
    _ ≤ (Cq*(Ideal.absNorm γ.q0 : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.quotient : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.residual : ℝ)^ε) := by
      gcongr
      · exact hq γ.q0 hq0
      · exact ht γ.quotient ht0
      · exact ht γ.residual hr0
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient)
        (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      ring

theorem outerTriple_card (Γ : Finset OuterTriple) (B T R : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hzero : ∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hnorm : ∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) :
    (Γ.card : ℝ) ≤ 128^3*B*T*R := by
  let f : OuterTriple → Ideal Eis × Ideal Eis × Ideal Eis := fun γ => (γ.q0,γ.quotient,γ.residual)
  have hf : Function.Injective f := by
    intro γ δ h
    exact OuterTriple.ext (congrArg Prod.fst h)
      (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)
  have hc := DescentFiberCost.fixed_triple_count (Γ.image f) B T R hB hT hR
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hzero γ hγ)
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hnorm γ hγ)
  simpa only [Finset.card_image_of_injective _ hf] using hc

theorem triple_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      1 ≤ B → 1 ≤ T → 1 ≤ R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := tripleDivisorWeight_small K ε hε
  refine ⟨128^3*C, by positivity, ?_⟩
  intro Γ B T R hB hT hR hz hn
  have hpos : 0 < B*T*R := by positivity
  have hw : ∀ γ ∈ Γ, tripleDivisorWeight K γ ≤ C*(B*T*R)^ε := by
    intro γ hγ
    obtain ⟨hq,ht,hr⟩ := hz γ hγ
    apply (hb γ hq ht hr).trans
    gcongr
    · exact (hn γ hγ).1
    · exact (hn γ hγ).2.1
    · exact (hn γ hγ).2.2
  have hs : (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤
      (128^3*B*T*R)*(C*(B*T*R)^ε) := by
    calc
      _ ≤ ∑ _γ ∈ Γ, C*(B*T*R)^ε := Finset.sum_le_sum hw
      _ = (Γ.card : ℝ)*(C*(B*T*R)^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (outerTriple_card Γ B T R hB hT hR hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)).trans_eq
  field_simp

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondCauchy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

theorem second_weighted_count {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  have hF := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw F
  have hG := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw G
  apply (DescentWeightedCauchy.weighted_cauchy (originalSource source oldLists newLists keep)
    w (F ∘ secondChild) (G ∘ secondChild)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem second_weighted_count_of_child_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows G γ ≤ E) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ)
      (hP : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  apply (second_weighted_count source oldLists newLists keep hvalid labels rows hf houter hchild K ho hn w hw F G).trans
  calc
    _ ≤ Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) *
      Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

theorem secondCanonicalPolynomial_actual_columns {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ puncture slots lists a W X c =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist (Ψ c.1) (puncture c.1)
          (primaryGenerator c.2.1) c.2.2) (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W c.1 (FirstPassCubeLabels.primeProductNorm p U / X)) :=
  finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualSecondEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers IdealMobiusDivisorSum
open InverseInitialArithmetic (sourceIdeal sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondChild {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) : SecondChild :=
  secondChild (originalSecondTuple p u v (markedSecondOriginal p x))

def actualSecondTriples {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset OuterTriple :=
  source.image (fun x => (actualSecondChild p u v x).1)

theorem actualSecondChild_nonzero (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0) :
    (actualSecondChild p u v x).2.1 ≠ 0 ∧
    (actualSecondChild p u v x).1.q0 ≠ 0 ∧
    (actualSecondChild p u v x).1.quotient ≠ 0 ∧
    (actualSecondChild p u v x).1.residual ≠ 0 := by
  have hj : Ideal.span {(jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hb : Ideal.span {(b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  change _ ≠ 0 ∧ _ ≠ 0 ∧ x.quotient ≠ 0 ∧ _ ≠ 0
  refine ⟨?_,hb,ht,sourceIdeal_ne_zero p hp _⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)) (sourceIdeal_ne_zero p hp _)

structure ActualSecondSourceConditions {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Prop where
  admissible : ∀ x ∈ source, x.cube.Admissible
  common_disjoint : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support
  first_divisor : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support
  second_divisor : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon
  old_support : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient
  new_support : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap
  quotient_nonzero : ∀ x ∈ source, x.quotient ≠ 0

theorem actual_second_fiber_weight (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (c : SecondChild)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) :
    ∑ x ∈ source with actualSecondChild p u v x = c, w x ≤ secondDivisorWeight K c := by
  by_cases he : (source.filter (fun x => actualSecondChild p u v x = c)).Nonempty
  · obtain ⟨x,hx⟩ := he
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hf,hq,ht,hr⟩ := actualSecondChild_nonzero p hp u v x (hs.quotient_nonzero x hx)
    rw [he] at hf hq ht hr
    have hcard := actual_marked_second_source_fiber p hp hpr hcop hinj u v source
      hs.admissible hs.common_disjoint hs.first_divisor hs.second_divisor hs.old_support hs.new_support
      c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
    calc
      _ ≤ ∑ _x ∈ source with actualSecondChild p u v _x = c, (1 : ℝ) :=
        Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
      _ = ((source.filter (fun x => actualSecondChild p u v x = c)).card : ℝ) := by simp
      _ ≤ _ := by
        dsimp only [secondDivisorWeight,actualSecondChild]
        exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.sum_empty]
    unfold secondDivisorWeight
    positivity

theorem actual_second_energy_projection (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : SecondChild → ℂ) :
    ∑ x ∈ source, w x * ‖F (actualSecondChild p u v x)‖^2 ≤
      ∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ := by
  have hm : ∀ x ∈ source, actualSecondChild p u v x ∈
      actualSecondTriples p u v source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,Finset.mem_product.mpr (hchild x hx)⟩
  have hb := fiber_energy_bound source (actualSecondTriples p u v source ×ˢ (labels ×ˢ rows))
    (actualSecondChild p u v) w (secondDivisorWeight K) (fun c => ‖F c‖^2) hm
    (fun _ _ => sq_nonneg _) (fun c _ => actual_second_fiber_weight p hp hpr hcop hinj u v source hs c K ho hn w hw)
  apply hb.trans_eq
  simp only [Finset.sum_product,secondDivisorWeight,tripleDivisorWeight,secondLabelEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem actual_second_weighted_count (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x * F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  apply (DescentWeightedCauchy.weighted_cauchy source w (F ∘ actualSecondChild p u v)
    (G ∘ actualSecondChild p u v)).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw F))
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondCanonicalChild -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem primaryGenerator_primeProduct
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (S : Finset ι) (v : ι → ℕ) :
    primaryGenerator (Ideal.span {primeProduct p S v}) = primeProduct p S v := by
  apply primaryGenerator_span _ (primeProduct_ne_zero p hp S v)
  unfold primeProduct
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have hpow : ConcretePrimeRowBridge.goodLambda^2 ∣ p i^v i-1 := by
      simpa only [one_pow] using (hpr i).trans (sub_dvd_pow_sub_pow (p i) 1 (v i))
    have he : p i^v i*(∏ j ∈ S,p j^v j)-1 =
        (p i^v i-1)*(∏ j ∈ S,p j^v j)+((∏ j ∈ S,p j^v j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hpow _) ih

def actualSecondPuncture (m : Eis) (γ : OuterTriple) : Eis :=
  (m*primaryGenerator γ.q0)*primaryGenerator γ.residual

def actualSecondRawLabel {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  ((∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * ∏ i ∈ x.second.overlap,p i

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_mask_span (F : Finset ι) (Ψ : Eis →* ℂ)
    (m₁ m₂ f k : Eis) (he : Ideal.span {m₁}=Ideal.span {m₂})
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m₁ f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m₂ f k slots lists a W X :=
  fixedChildRow_congr_mask_span p hp hcop hg F Ψ he _ f k

theorem actual_second_puncture_span
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) :
    Ideal.span {((m*b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
      secondExpansionQuotient p x.second)} =
    Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} := by
  change Ideal.span {(m*b0Label p _ _ _ _)*secondExpansionQuotient p x.second} =
    Ideal.span {((m*primaryGenerator (Ideal.span {b0Label p _ _ _ _}))*
      primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor)))}
  rw [show primaryGenerator (Ideal.span {(b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr,secondExpansionQuotient_of_subset p x.second hE]
  simp only [←Ideal.span_singleton_mul_span_singleton,secondMaskQuotient_span,
    FiniteGaussPhase.span_finset_prod]

theorem actual_second_generator_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    ∃ u v : Eisˣ,
      actualSecondRawLabel p x = (u:Eis)*primaryGenerator (actualSecondChild p u v x).2.1 ∧
      primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor =
        (v:Eis)*(primaryGenerator (sourceIdeal p x.firstDivisor)*primaryGenerator (sourceIdeal p x.second.divisor)) := by
  let L := (markedSecondOriginal p x).J * sourceIdeal p x.firstCommon *
    sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap
  have hs (S : Finset ι) : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) S} = sourceIdeal p S := by
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,sourceIdeal]
    exact (FiniteGaussPhase.span_finset_prod S p).symm
  have hl : Ideal.span {actualSecondRawLabel p x} = L := by
    unfold actualSecondRawLabel L
    simp only [←Ideal.span_singleton_mul_span_singleton,hs,sourceIdeal,markedSecondOriginal,cubeSecondSource]
    ring
  have hgp (S : Finset ι) : primaryGenerator (sourceIdeal p S) ≠ 0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hL : primaryGenerator L ≠ 0 := by
    dsimp only [L]
    rw [primaryGenerator_mul,primaryGenerator_mul,primaryGenerator_mul]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (hgp _)) (hgp _)) (hgp _)
    change primaryGenerator (Ideal.span {jLabel p _ _ _ _}) ≠ 0
    rw [show primaryGenerator (Ideal.span {(jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}) =
      jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _]
    exact primeProduct_ne_zero p hp _ _
  obtain ⟨u,v,hu,hv⟩ := exists_second_generator_sectors (actualSecondRawLabel p x)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor)
    L (sourceIdeal p x.firstDivisor) (sourceIdeal p x.second.divisor)
    hl (hs _) (hs _) hL (hgp _) (hgp _)
  exact ⟨u,v,hu,hv⟩

theorem actual_second_canonical_child
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      ((m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)*secondExpansionQuotient p x.second)
      (actualSecondRawLabel p x)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * k)
      slots lists a W X =
    secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
      slots lists a (fun _ => W) X
      (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hu,hv⟩ := actual_second_generator_sectors p hp hpr x
  refine ⟨u,v,?_⟩
  intro F Ψ m k slots lists a W X
  rw [secondCanonical_generator_transport p hp hcop hg F Ψ _ _ _ _ _ _ _ _ u v hu hv]
  exact finiteCanonicalMarkedRow_mask_span p hp hcop hg F Ψ _ _ _ _
    (actual_second_puncture_span p hp hpr x hE u v m) slots lists a W X

end
end SevenEighths.InverseMoment

end OAI

end

