module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstModeChild -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstModeCubeCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
    (firstColumnMode true C y t) d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
    (firstColumnMode false C y t) d

theorem firstModeCubeCoefficient_eq (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative C y t d =
      cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y (-t) d := by
  have ht (u : ℝ) : logPhase (-t) (-u) = logPhase t u := by
    unfold logPhase
    congr 1
    push_cast
    ring
  have hm : firstColumnMode true C y t = logTwistMinus C (fun _ => 1) y (-t) := by
    funext S
    simp only [firstColumnMode,logTwistMinus,ite_true,one_mul,ht]
  have hp' : firstColumnMode false C y t = logTwistPlus C (fun _ => 1) y (-t) := by
    funext S
    simp only [firstColumnMode,logTwistPlus,Bool.false_eq_true,ite_false,one_mul,ht]
  cases negative <;>
    simp only [firstModeCubeCoefficient,cubeLogCoefficient,Bool.false_eq_true,ite_false,ite_true,hm,hp']

omit [DecidableEq σ] in
theorem actual_first_mode_marked_input
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (negative : Bool) (χ : RayCharacter)
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : Eis) :
    rayIdealRow p hg F
      (firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U)*H U)) c f)
        y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
        firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
          (fun U => primeMark slots lists a (A ∪ U)*H U) (fun _ => 1) y c d r (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂) := by
  rw [firstModeCubeCoefficient_eq,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  congr 1
  exact marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun _ => 1) y c d (-t) _

theorem actual_first_mode_priority_input
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (negative : Bool) (χ : RayCharacter)
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : Eis) :
    rayIdealRow p hg F
      (firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U)*H U)) c f)
        y t d) negative χ D h =
    beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
      ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
        ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
          firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U*H U)
            (fun _ => 1) y c d r (-t) (h*f^2*dilationLabel p B v ε₁ ε₂) := by
  rw [actual_first_mode_marked_input p hp hcop hg hinj hc hpr F D B A v ε₁ ε₂ hv]
  simp_rw [firstCoreInputRow_marked_priority]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
local notation "lambda" => ConcretePrimeRowBridge.goodLambda
theorem full_rayIdealRow_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    Continuous (fun t => rayIdealRow p hg F (C t) negative χ D h) := by
  simp only [rayIdealRow, ConcretePrimeRowBridge.conjugateIdealRowSum,
    ConcretePrimeRowBridge.mobiusIdealColumn]
  fun_prop

theorem full_rayIdealRow_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖rayIdealRow p hg F (C t) negative χ D h‖ ≤ M := by
  let P := fun i => Ideal.span {p i}
  let s := supportIdealFamily P (F \ D)
  let T := fun (t : Frequency × (Fin 9 → ℝ)) (I : Ideal O) =>
    ConcretePrimeRowBridge.mobiusIdealColumn
      (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
        else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C t (D ∪ recoveredSupport P (F \ D) I)) I *
      star (ConcretePrimeRowBridge.idealSexticRow s (supportIdealFamily_pos P (F \ D))
        (supportIdealFamily_good P hg (F \ D)) I h)
  refine ⟨∑ I ∈ s, ‖T 0 I‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  change ‖∑ I ∈ s, T t I‖ ≤ _
  apply (norm_sum_le s (T t)).trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  simp only [T, ConcretePrimeRowBridge.mobiusIdealColumn, norm_mul, hC]

theorem full_rayIdealEnergy_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => rayIdealEnergy p hg F (C t) negative h) := by
  unfold rayIdealEnergy
  apply continuous_finsetSum _
  intro r hr
  apply continuous_finsetSum _
  intro D hD
  exact continuous_const.mul ((full_rayIdealRow_continuous p hg F C hC negative _ D h).norm.pow 2)

theorem full_rayIdealEnergy_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, rayIdealEnergy p hg F (C t) negative h ≤ M := by
  choose M hM hbound using fun (r : RayCharacter × RayCharacter) (D : Finset ι) =>
    full_rayIdealRow_uniform_bound p hg F C hC negative (if negative then r.1 else r.2) D h
  refine ⟨∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ * (M r D)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound r D t) 2)
    (norm_nonneg _)

theorem full_integrable_rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : (Frequency × (Fin 9 → ℝ)) → ℂ) (hb : Integrable b) :
    Integrable (fun t : Frequency × (Fin 9 → ℝ) => ‖b t‖ * rayIdealEnergy p hg F (C t) negative h) volume := by
  obtain ⟨M, hM, hbnd⟩ := full_rayIdealEnergy_uniform_bound p hg F C hn negative h
  apply hb.norm.mul_bdd (c := M)
  · exact (full_rayIdealEnergy_continuous p hg F C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (rayIdealEnergy_nonneg p hg F (C t) negative h)]
      exact hbnd t)

theorem full_cube_integral_norm_le_energy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : (Frequency × (Fin 9 → ℝ)) → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : (Frequency × (Fin 9 → ℝ)) → ℂ)
    (hb : Integrable b) (hbc : Continuous b) (a : ℂ) :
    ‖∫ t : Frequency × (Fin 9 → ℝ), b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by
  let E₁ := fun t => rayIdealEnergy p hg F (C₁ t) true h
  let E₂ := fun t => rayIdealEnergy p hg F (C₂ t) false h
  let w := fun t : Frequency × (Fin 9 → ℝ) => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => rayIdealEnergy_nonneg p hg F (C₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => rayIdealEnergy_nonneg p hg F (C₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume := by
    convert (full_integrable_rayIdealEnergy p hg F C₁ hc₁ hn₁ true h b hb).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₁]
    ring
  have i₂ : Integrable (fun t => w t * E₂ t) volume := by
    convert (full_integrable_rayIdealEnergy p hg F C₂ hc₂ hn₂ false h b hb).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₂]
    ring
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (((hbc.norm.mul_const ‖a‖).mul
      (full_rayIdealEnergy_continuous p hg F C₁ hc₁ true h)))
  have hg' : Continuous g :=
    Real.continuous_sqrt.comp (((hbc.norm.mul_const ‖a‖).mul
      (full_rayIdealEnergy_continuous p hg F C₂ hc₂ false h)))
  have hfsq (t : Frequency × (Fin 9 → ℝ)) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : Frequency × (Fin 9 → ℝ)) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : Frequency × (Fin 9 → ℝ)) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : Frequency × (Fin 9 → ℝ), b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      ∫ t : Frequency × (Fin 9 → ℝ), f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (idealPairReindex_norm_le p hg F (C₁ t) (C₂ t) h) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : Frequency × (Fin 9 → ℝ), f t * g t) ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), w t * E₁ t) * Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : Frequency × (Fin 9 → ℝ), f t * g t) ≤
      Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), f t ^ 2) * Real.sqrt (∫ t : Frequency × (Fin 9 → ℝ), g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstActualEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation FourierBridge ActualEisensteinCubic FirstPassCubeLabels
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstModeEnergyCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis)
    (z : Frequency × (Fin 9 → ℝ)) : Finset ι → ℂ :=
  firstModeCubeCoefficient p hp hcop hg B v ε₁ ε₂ negative C y
    (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)) d

theorem firstModeEnergyCoefficient_continuous (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis) (S : Finset ι) :
    Continuous (fun z => firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ negative C y d z S) := by
  simp only [firstModeEnergyCoefficient,firstModeCubeCoefficient_eq]
  apply (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y d S).comp
  unfold profileHeight
  fun_prop

theorem firstModeEnergyCoefficient_norm (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (y : Finset ι → ℝ) (d : Eis)
    (z : Frequency × (Fin 9 → ℝ)) (S : Finset ι) :
    ‖firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ negative C y d z S‖ =
      ‖firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ negative C y d 0 S‖ := by
  simp only [firstModeEnergyCoefficient,firstModeCubeCoefficient_eq]
  exact (norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y _ d S).trans
    (norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ negative C (fun _ => 1) y _ d S).symm

theorem firstOuterPhase_norm (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) :
    ‖firstOuterPhase h a‖ = 1 := by
  simp [firstOuterPhase,norm_prod,logPhase_norm]

theorem actual_first_common_energy (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
      firstModeIdealRows p hp hcop hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z‖ ≤
    Real.sqrt (∫ z : Frequency × (Fin 9 → ℝ), ‖fullProfileDensity g b₁ b₂ b₃ z‖ *
      ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      rayIdealEnergy p hg F (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d z) true h) *
    Real.sqrt (∫ z : Frequency × (Fin 9 → ℝ), ‖fullProfileDensity g b₁ b₂ b₃ z‖ *
      ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      rayIdealEnergy p hg F (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d z) false h) := by
  let b := fun z : Frequency × (Fin 9 → ℝ) => fullProfileDensity g b₁ b₂ b₃ z *
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a
  have hphase : Continuous (fun z : Frequency × (Fin 9 → ℝ) =>
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a) := by
    unfold firstOuterPhase profileHeight logPhase
    fun_prop
  have hb : Integrable b := (full_density_integrable g b₁ b₂ b₃).mul_bdd
    hphase.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => (firstOuterPhase_norm _ _).le))
  have hbc : Continuous b := by
    apply Continuous.mul _ hphase
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  have hbn (z : Frequency × (Fin 9 → ℝ)) : ‖b z‖ = ‖fullProfileDensity g b₁ b₂ b₃ z‖ := by
    simp only [b,norm_mul,firstOuterPhase_norm,mul_one]
  have hh := full_cube_integral_norm_le_energy p hg F
    (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d)
    (firstModeEnergyCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d)
    (firstModeEnergyCoefficient_norm p hp hcop hg B v ε₁ ε₂ true C₁ y₁ d)
    (firstModeEnergyCoefficient_norm p hp hcop hg B v ε₁ ε₂ false C₂ y₂ d)
    h b hb hbc (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [hbn] at hh
  convert hh using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstModeIdealRows,firstModeEnergyCoefficient,firstModeCubeCoefficient,
    Bool.false_eq_true,ite_false,ite_true,b]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCoupledReindex -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic CoprimeMobiusExtension
open RayFourExpansion MixedCrossSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_coprime_coupled_reindex {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
        (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
      ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
        H (D ∪ U) (D ∪ V) *
          star (supportMobius P U * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg U h)) *
            (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← prime_product_moebius P hprime hinj D]
  change supportMobius P D * _ = _
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hdV : Disjoint D V := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
  have hmu (S T : Finset ι) (hd : Disjoint S T) :
      supportMobius P (S ∪ T) = supportMobius P S * supportMobius P T := by
    simp only [supportMobius,prime_product_moebius P hprime hinj,
      Finset.card_union_of_disjoint hd,pow_add]
  have hrow (S T : Finset ι) (hd : Disjoint S T) :
      finiteSquarefreeRow P hg (S ∪ T) h =
        finiteSquarefreeRow P hg S h * finiteSquarefreeRow P hg T h := Finset.prod_union hd
  rw [hmu D U hdU,hmu D V hdV,hrow D U hdU,hrow D V hdV]
  simp only [star_mul,star_star,star_supportMobius]
  have hm := supportMobius_sq P hprime hinj D
  have hz := finiteSquarefreeRow_self_pair P hg D h
  calc
    _ = (supportMobius P D * supportMobius P D) *
        (star (finiteSquarefreeRow P hg D h)*finiteSquarefreeRow P hg D h) *
        (H (D ∪ U) (D ∪ V) *
          (supportMobius P U * star (C₁ (D ∪ U)) * finiteSquarefreeRow P hg U h) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h))) := by ring
    _ = _ := by rw [hm,hz]; ring

theorem first_quadratic_coupled_reindex {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (B : Finset ι)
    (C₁ C₂ : Finset ι → ℂ) (H : Finset ι → Finset ι → ℂ) (h : Eis) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      H S T * quadraticCrossPhase p hg S T *
        star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h)) *
        (supportMobius (fun i => Ideal.span {p i}) T * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
          H (D ∪ U) (D ∪ V) *
          star (supportMobius (fun i => Ideal.span {p i}) U *
            (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
          (supportMobius (fun i => Ideal.span {p i}) V *
            (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h)) := by
  let P := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i j hij
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hij)
  have hprime (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let T := fun (r : RayCharacter × RayCharacter) (S V : Finset ι) => if Disjoint S V then
    H S V * star (supportMobius P S * (star (supportRay p r.1 S)*C₁ S) * star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P V * (supportRay p r.2 V*C₂ V) * star (finiteSquarefreeRow P hg V h)) else 0
  have he (S V : Finset ι) :
      (if Disjoint S V then H S V * quadraticCrossPhase p hg S V *
        star (supportMobius P S*C₁ S*star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P V*C₂ V*star (finiteSquarefreeRow P hg V h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
    by_cases hd : Disjoint S V
    · rw [ite_eq_left hd,quadraticCrossPhase_character_expansion p hp hcop hg hc S V hd]
      simp only [Fintype.sum_prod_type,T,ite_eq_left hd,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay,star_mul,star_star]
      ring
    · simp [T,hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ V ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2*T r S V := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun V hV => he S V)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ V ∈ B.powerset, T r S V := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ V ∈ B.powerset, crossCoeff r.1 r.2*T r S V := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact first_coprime_coupled_reindex P hprime hinj hg B _ _ H h

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCommonProfile -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem firstNormProfile_common_support (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C D R T H X₁ X₂ K : ℝ) (hT : 0 ≤ T) :
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K ![A₁,A₂,C,D,R,1,H,T*X₁,T*X₂] =
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K ![A₁,A₂,C,D,R,T,H,X₁,X₂] := by
  have hroot : Real.sqrt (T*X₁)*Real.sqrt (T*X₂) =
      T*Real.sqrt X₁*Real.sqrt X₂ := by
    rw [Real.sqrt_mul hT,Real.sqrt_mul hT]
    calc
      _ = (Real.sqrt T)^2*Real.sqrt X₁*Real.sqrt X₂ := by ring
      _ = _ := by rw [Real.sq_sqrt hT]
  unfold firstNormProfile
  simp only [Finset.prod_const_one,one_mul,Matrix.cons_val_zero,
    Fin.isValue,]
  change W₁ (A₁*C*1*(T*X₁))*W₂ (A₂*C*1*(T*X₂))*
      EisensteinSchwartzPoisson.paperRadialFourier Φ (K*H/(D*R*1^2*(T*X₁)*(T*X₂))) /
        ((D:ℂ)*(Real.sqrt R:ℂ)*(1:ℂ)*(Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ)) =
    W₁ (A₁*C*T*X₁)*W₂ (A₂*C*T*X₂)*
      EisensteinSchwartzPoisson.paperRadialFourier Φ (K*H/(D*R*T^2*X₁*X₂)) /
        ((D:ℂ)*(Real.sqrt R:ℂ)*(T:ℂ)*(Real.sqrt X₁:ℂ)*(Real.sqrt X₂:ℂ))
  simp only [mul_one,one_pow]
  rw [show A₁*C*(T*X₁) = A₁*C*T*X₁ from by ring,
    show A₂*C*(T*X₂) = A₂*C*T*X₂ from by ring,
    show K*H/(D*R*(T*X₁)*(T*X₂)) = K*H/(D*R*T^2*X₁*X₂) from by ring]
  have hc : (Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ) =
      (T:ℂ)*(Real.sqrt X₁:ℂ)*(Real.sqrt X₂:ℂ) := by exact_mod_cast hroot
  rw [show (D:ℂ)*(Real.sqrt R:ℂ)*(Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ) =
    (D:ℂ)*(Real.sqrt R:ℂ)*((Real.sqrt (T*X₁):ℂ)*(Real.sqrt (T*X₂):ℂ)) from by ring,hc]
  ring

theorem firstNormProfile_actual_common {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (D U V : Finset ι)
    (hDU : Disjoint D U) (hDV : Disjoint D V)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C E R H K : ℝ) :
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,E,R,1,H,primeProductNorm p (D∪U),primeProductNorm p (D∪V)] =
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,E,R,primeProductNorm p D,H,primeProductNorm p U,primeProductNorm p V] := by
  rw [primeProductNorm_union p D U hDU,primeProductNorm_union p D V hDV]
  exact firstNormProfile_common_support W₁ W₂ Φ A₁ A₂ C E R _ H _ _ K
    (primeProductNorm_pos p hp D).le

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCoupledRayColumns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        H (D ∪ U) (D ∪ V) *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h))

theorem actual_first_gauss_coupled_reindex
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (d h : Eis) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      H N P * threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstCoupledRayColumns p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d) H h := by
  rw [firstCoupledRayColumns, ← first_quadratic_coupled_reindex p hp hinj hg hc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [threeGaussRowFactor_eq_ray_columns p hp hcop hg hc hpr N P B hd
      (hFB.mono_left (Finset.mem_powerset.mp hN)) (hFB.mono_left (Finset.mem_powerset.mp hP))]
    ring
  · simp [hd]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCommon -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonCoefficient (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D U V : Finset ι) (h : Eis) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) U *
    (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
  (supportMobius (fun i => Ideal.span {p i}) V *
    (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h))

def firstPhysicalCommonRows (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D *
      rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
          ![A₁,A₂,C,‖eisEmbedding d‖^2,R,primeProductNorm p D,
            ‖eisEmbedding h‖^2,primeProductNorm p U,primeProductNorm p V] *
          firstCommonCoefficient p hg C₁ C₂ r D U V h

theorem actual_first_physical_common
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C K : ℝ) (d h : Eis) :
    (‖eisEmbedding d‖^2 : ℂ)⁻¹ *
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ Φ
          (fun y => W₁ (A₁*C*Real.exp y)) (fun y => W₂ (A₂*C*Real.exp y)) 1 1 K d h else 0) =
    (K:ℂ) * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstPhysicalCommonRows p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d)
        W₁ W₂ Φ A₁ A₂ C (primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)) K d h := by
  let R := primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)
  let H := fun N P : Finset ι => firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
    ![A₁,A₂,C,‖eisEmbedding d‖^2,R,1,‖eisEmbedding h‖^2,primeProductNorm p N,primeProductNorm p P]
  calc
    _ = (K:ℂ) * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        H N P*threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : Disjoint N P
      · simp only [hd,ite_true]
        simpa only [H,R,mul_assoc] using canonicalPairMode_whole_profile p hp hcop hg
          N P B hd (hFB.mono_left (Finset.mem_powerset.mp hN))
          (hFB.mono_left (Finset.mem_powerset.mp hP)) v ε₁ ε₂ C₁ C₂ W₁ W₂ Φ A₁ A₂ C K d h
      · simp [hd]
    _ = _ := by
      rw [actual_first_gauss_coupled_reindex p hp hcop hg hinj hc hpr F B hFB]
      rw [mul_assoc]
      apply congrArg (fun z : ℂ => (K:ℂ)*(cubeBaseFactor p hp hg B v ε₁ ε₂ d h*z))
      unfold firstCoupledRayColumns firstPhysicalCommonRows
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg (fun z : ℂ => crossCoeff r.1 r.2*z)
      apply Finset.sum_congr rfl
      intro D hD
      apply congrArg (fun z : ℂ => supportMobius (fun i => Ideal.span {p i}) D *
        rowCoprimeMask (fun i => Ideal.span {p i}) D h*z)
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      have hDU : Disjoint D U := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
      have hDV : Disjoint D V := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
      dsimp only [H]
      rw [firstNormProfile_actual_common p hp D U V hDU hDV]
      simp only [firstCommonCoefficient,R,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCanonicalPhysical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_residual_mul_test (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H test : Finset ι→ℂ) (N : Finset ι) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>H U*test U) N =
      canonicalCubeResidual p hg b C negative Ψ m f H N *
        test (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) := by
  simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn]
  ring

theorem actual_first_kernel_window_transport
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ A₁ A₂ : Finset ι→ℂ) (V₁ V₂ : ℝ→ℂ)
    (hC₁ : ∀ N∈F.powerset,C₁ N=A₁ N*star (V₁ (columnLog p 1 N)))
    (hC₂ : ∀ N∈F.powerset,C₂ N=A₂ N*V₂ (columnLog p 1 N))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 K d h =
    ∑ N∈F.powerset,∑ Q∈F.powerset,if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ A₁ A₂ W V₁ V₂ 1 1 K d h else 0 := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro Q hQ
  by_cases hd : Disjoint N Q
  · simp only [hd,ite_true,canonicalPairMode,threeGaussRowFactor,hC₁ N hN,hC₂ Q hQ,star_mul,star_star]
    ring
  · simp only [hd,ite_false]

theorem canonical_first_kernel_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) :
    let F := pool\(b.support∪C)
    let A₁ := ‖eisEmbedding (aLabel p b.support b.rightBit)‖^2
    let A₂ := ‖eisEmbedding (aLabel p b.support b.leftBit)‖^2
    let B₁ := canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁
    let B₂ := canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂
    (‖eisEmbedding d‖^2:ℂ)⁻¹ * actualFirstKernel p hp hcop hg F b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>H₁ U*W₁ (primeProductNorm p U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>H₂ U*W₂ (primeProductNorm p U)))
      Φ (fun _=>1) (fun _=>1) 1 1 K d h =
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
      firstPhysicalCommonRows p hg F
        (cubeMinusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit B₁ d)
        (cubePlusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit B₂ d)
        (fun x=>star (W₁ x)) W₂ Φ A₁ A₂ (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h := by
  intro F A₁ A₂ B₁ B₂
  have hdis : Disjoint F (b.support∪C) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  have hwindow (negative : Bool) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (W : ℝ→ℂ)
      (N : Finset ι) (hN : N∈F.powerset) :
      canonicalCubeResidual p hg b C negative Ψ m f (fun U=>H U*W (primeProductNorm p U)) N =
      canonicalCubeResidual p hg b C negative Ψ m f H N *
        W (‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
          primeProductNorm p C*Real.exp (columnLog p 1 N)) := by
    rw [canonical_residual_mul_test p hg, cube_whole_column_norm p b hb C N hC
      (hdis.mono_left (Finset.mem_powerset.mp hN)) negative]
    simp only [columnLog,div_one,Real.exp_log (primeProductNorm_pos p hp N)]
  rw [actual_first_kernel_window_transport p hp hcop hg F b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit _ _ B₁ B₂
    (fun y=>star (W₁ (A₁*primeProductNorm p C*Real.exp y)))
    (fun y=>W₂ (A₂*primeProductNorm p C*Real.exp y))
    (fun N hN=>by simpa only [star_star,ite_true,A₁,B₁] using hwindow true Ψ₁ m₁ H₁ W₁ N hN)
    (fun N hN=>by simpa only [Bool.false_eq_true,ite_false,A₂,B₂] using hwindow false Ψ₂ m₂ H₂ W₂ N hN)]
  exact actual_first_physical_common p hp hcop hg hinj hc hpr F b.support
    (hdis.mono_right Finset.subset_union_left) _ _ _ B₁ B₂
    (fun x=>star (W₁ x)) W₂ Φ A₁ A₂ (primeProductNorm p C) K d h

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCommonMeasure -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation MeasureTheory
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev FirstCommonIndex (ι : Type*) :=
  (RayCharacter × RayCharacter) × (Σ _ : Finset ι, Finset ι × Finset ι)

def firstCommonIndices {ι : Type*} [DecidableEq ι] (F : Finset ι) : Finset (FirstCommonIndex ι) :=
  Finset.univ ×ˢ F.powerset.sigma (fun D => (F\D).powerset ×ˢ (F\D).powerset)

def firstCommonNorms {ι : Type*} (p : ι → Eis) (A₁ A₂ C R : ℝ) (d h : Eis)
    (j : FirstCommonIndex ι) : Fin 9 → ℝ :=
  ![A₁,A₂,C,‖eisEmbedding d‖^2,R,primeProductNorm p j.2.1,
    ‖eisEmbedding h‖^2,primeProductNorm p j.2.2.1,primeProductNorm p j.2.2.2]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonWeight (C₁ C₂ : Finset ι → ℂ) (h : Eis) (j : FirstCommonIndex ι) : ℂ :=
  crossCoeff j.1.1 j.1.2 * supportMobius (fun i => Ideal.span {p i}) j.2.1 *
    rowCoprimeMask (fun i => Ideal.span {p i}) j.2.1 h *
    firstCommonCoefficient p hg C₁ C₂ j.1 j.2.1 j.2.2.1 j.2.2.2 h

theorem firstPhysicalCommonRows_indexed (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    ∑ j ∈ firstCommonIndices F, firstCommonWeight p hg C₁ C₂ h j *
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j) := by
  simp only [firstPhysicalCommonRows,firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonNorms,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  ring

theorem firstPhysicalCommonRows_integral (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis)
    (s : Fin 9 → ℝ) (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ firstCommonIndices F,
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K
        (firstCommonNorms p A₁ A₂ C R d h j) =
      (firstRootScale s:ℂ)⁻¹ *
        (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
        ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) :
    firstPhysicalCommonRows p hg F C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹ * ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
      ∑ j ∈ firstCommonIndices F,firstCommonWeight p hg C₁ C₂ h j *
        (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 := by
  rw [firstPhysicalCommonRows_indexed]
  calc
    _ = (firstRootScale s:ℂ)⁻¹ * ∑ j ∈ firstCommonIndices F,
        (firstCommonWeight p hg C₁ C₂ h j *
          (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8))) *
        ∫ z : Frequency × (Fin 9 → ℝ),fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j hj]
      ring
    _ = _ := by
      rw [full_density_finite_sum]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCommonColumns -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonColumn (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg (F\D)
    (fun U => (if negative then star (supportRay p χ (D∪U)) else supportRay p χ (D∪U)) *
      C (D∪U) * (if negative then star (ω (primeProductNorm p U/X)*
        logPhase t (Real.log (primeProductNorm p U/X))) else
        ω (primeProductNorm p U/X)*logPhase t (Real.log (primeProductNorm p U/X)))) h

theorem firstCommonColumn_pair (F D : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (ω₁ ω₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ : ℝ) (h : Eis) :
    (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
      firstCommonCoefficient p hg C₁ C₂ r D U V h *
        (ω₁ (primeProductNorm p U/X₁)*ω₂ (primeProductNorm p V/X₂)) *
        logPhase t₁ (Real.log (primeProductNorm p U/X₁)) *
        logPhase t₂ (Real.log (primeProductNorm p V/X₂))) =
    star (firstCommonColumn p hg F D C₁ true r.1 ω₁ X₁ t₁ h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ X₂ t₂ h := by
  simp only [firstCommonColumn,supportConjugateSum,star_sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  simp only [firstCommonCoefficient,Bool.false_eq_true,ite_false,ite_true,star_mul,star_star]
  ring

def firstCommonOuterLog (A₁ A₂ C R : ℝ) (d h : Eis) (D : Finset ι) (s : Fin 9 → ℝ) : Fin 7 → ℝ :=
  ![Real.log (A₁/s 0),Real.log (A₂/s 1),Real.log (C/s 2),Real.log (‖eisEmbedding d‖^2/s 3),
    Real.log (R/s 4),Real.log (primeProductNorm p D/s 5),Real.log (‖eisEmbedding h‖^2/s 6)]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem first_common_source_mode (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (j : FirstCommonIndex ι) (z : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
      (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2)
      (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s) *
    logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (Real.log (primeProductNorm p j.2.2.1/s 7)) *
    logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
  have hy : firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s =
      firstCoordinates (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s)
        (Real.log (primeProductNorm p j.2.2.1/s 7))
        (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
    funext i
    fin_cases i <;> rfl
  rw [hy,first_mode_split]

def firstCommonSeparatedRow (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h

theorem first_common_modes_eq_columns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ j ∈ firstCommonIndices F,firstCommonWeight p hg C₁ C₂ h j *
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
      pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
        (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) =
    firstCommonSeparatedRow p hg F C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonSeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  calc
    _ = crossCoeff r.1 r.2 *
        (supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
          firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s)) *
        (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
          firstCommonCoefficient p hg C₁ C₂ r D U V h *
            (ω₁ (primeProductNorm p U/s 7)*ω₂ (primeProductNorm p V/s 8)) *
            logPhase (H 7) (Real.log (primeProductNorm p U/s 7)) *
            logPhase (H 8) (Real.log (primeProductNorm p V/s 8))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      rw [first_common_source_mode]
      dsimp only [H]
      ring
    _ = _ := by
      rw [firstCommonColumn_pair]
      dsimp only [H]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstBlocks -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstBlockedPhysicalRows (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ j ∈ firstCommonIndices F, selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j *
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j)

def firstBlockedSeparatedRow (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, selector D * supportMobius (fun i => Ideal.span {p i}) D *
      rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h

theorem first_block_modes_eq_columns (F : Finset ι) (selector : Finset ι → ℂ) (C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ j ∈ firstCommonIndices F,(selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j) *
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
      pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
        (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) =
    firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstBlockedSeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  calc
    _ = crossCoeff r.1 r.2 *
        (selector D * supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
          firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s)) *
        (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
          firstCommonCoefficient p hg C₁ C₂ r D U V h *
            (ω₁ (primeProductNorm p U/s 7)*ω₂ (primeProductNorm p V/s 8)) *
            logPhase (H 7) (Real.log (primeProductNorm p U/s 7)) *
            logPhase (H 8) (Real.log (primeProductNorm p V/s 8))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      rw [first_common_source_mode]
      dsimp only [H]
      ring
    _ = _ := by
      rw [firstCommonColumn_pair]
      dsimp only [H]
      ring

theorem first_blocks_reconstruct {κ : Type*} (blocks : Finset κ)
    (F : Finset ι) (selector : κ → Finset ι → ℂ)
    (hpartition : ∀ D ∈ F.powerset, ∑ a ∈ blocks, selector a D = 1)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) :
    (∑ a ∈ blocks, firstBlockedPhysicalRows p hg F (selector a) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h) =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  unfold firstBlockedPhysicalRows
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hDj : j.2.1 ∈ F.powerset := (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1
  rw [← Finset.sum_mul, ← Finset.sum_mul, hpartition j.2.1 hDj, one_mul]

def firstCommonBlockSelector {κ : Type*} [DecidableEq κ]
    (label : Finset ι → κ) (a : κ) (D : Finset ι) : ℂ :=
  if label D = a then 1 else 0

theorem first_source_blocks_reconstruct {κ : Type*} [DecidableEq κ]
    (F : Finset ι) (label : Finset ι → κ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) :
    (∑ a ∈ F.powerset.image label,
      firstBlockedPhysicalRows p hg F (firstCommonBlockSelector label a)
        C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h) =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  apply first_blocks_reconstruct
  intro D hD
  have hm : label D ∈ F.powerset.image label := Finset.mem_image_of_mem label hD
  simp [firstCommonBlockSelector,hm]

theorem first_block_nonzero_label {κ : Type*} [DecidableEq κ]
    (label : Finset ι → κ) (a : κ) (C₁ C₂ : Finset ι → ℂ) (h : Eis)
    (j : FirstCommonIndex ι)
    (hn : firstCommonBlockSelector label a j.2.1 * firstCommonWeight p hg C₁ C₂ h j ≠ 0) :
    label j.2.1 = a := by
  by_contra he
  simp [firstCommonBlockSelector,he] at hn

theorem first_block_normalized_density (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (normalization : ℂ)
    (he : ∀ j ∈ firstCommonIndices F,
      selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
        (firstCommonNorms p A₁ A₂ C R d h j) =
      (firstRootScale s:ℂ)⁻¹ *
        (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8)) *
        ∫ z : Frequency × (Fin 9 → ℝ),density z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) :
    normalization * firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹ * ∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp_rw [← first_block_modes_eq_columns]
  rw [← density_finite_sum _ density hDensity]
  simp only [firstBlockedPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j = 0
  · simp only [hz,zero_mul,mul_zero]
  · calc
      _ = (selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j) *
          (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
            (firstCommonNorms p A₁ A₂ C R d h j)) := by ring
      _ = _ := by rw [he j hj hz]; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstBlockEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstBlockOuterWeight (selector : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) : ℂ :=
  crossCoeff r.1 r.2 * selector D * supportMobius (fun i => Ideal.span {p i}) D *
    rowCoprimeMask (fun i => Ideal.span {p i}) D h

def firstBlockEnergy (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖firstBlockOuterWeight p selector r D h‖ *
      ‖firstCommonColumn p hg F D C negative (if negative then r.1 else r.2) ω X t h‖^2

theorem firstBlockEnergy_nonneg (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : Eis) :
    0 ≤ firstBlockEnergy p hg F selector C negative ω X t h := by
  unfold firstBlockEnergy
  positivity

theorem first_block_energy (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstBlockEnergy p hg F selector C₁ true ω₁ (s 7) (H 7) h) *
      Real.sqrt (firstBlockEnergy p hg F selector C₂ false ω₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let w := fun j : (RayCharacter × RayCharacter) × Finset ι =>
    firstBlockOuterWeight p selector j.1 j.2 h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h j.2 s)
  have hn (j : (RayCharacter × RayCharacter) × Finset ι) :
      ‖w j‖ = ‖firstBlockOuterWeight p selector j.1 j.2 h‖ := by
    simp only [w,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset) w
    (fun j => firstCommonColumn p hg F j.2 C₂ false j.1.2 ω₂ (s 8) (H 8) h)
    (fun j => firstCommonColumn p hg F j.2 C₁ true j.1.1 ω₁ (s 7) (H 7) h)
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      w (r,D) * firstCommonColumn p hg F D C₂ false r.2 ω₂ (s 8) (H 8) h *
        star (firstCommonColumn p hg F D C₁ true r.1 ω₁ (s 7) (H 7) h)) =
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
    simp only [firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [w,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  change ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    Real.sqrt (firstBlockEnergy p hg F selector C₂ false ω₂ (s 8) (H 8) h) *
    Real.sqrt (firstBlockEnergy p hg F selector C₁ true ω₁ (s 7) (H 7) h) at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_block_integral_of_energy (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstBlockEnergy p hg F selector C₁ true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstBlockEnergy p hg F selector C₂ false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_block_energy p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have h := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact h.trans_eq (by rw [← sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),B*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul B)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCommonChild -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic FourierBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp in
theorem firstCommonColumn_eq_rayIdealRow
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (h : Eis) :
    firstCommonColumn p hg F D C negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
    rayIdealRow p hg F
      (fun S => C S * if negative then
        star (ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
          logPhase t (columnLog p (primeProductNorm p D*X) S)) else
        ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
          logPhase t (columnLog p (primeProductNorm p D*X) S)) negative χ D h := by
  rw [rayIdealRow_eq_supportRow p hinj hg F D
    (fun S => C S * if negative then
      star (ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
        logPhase t (columnLog p (primeProductNorm p D*X) S)) else
      ω (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
        logPhase t (columnLog p (primeProductNorm p D*X) S)) negative χ h]
  simp only [firstCommonColumn,supportConjugateSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hy : columnLog p (primeProductNorm p D*X) (D∪U) =
      Real.log (primeProductNorm p U/X) := by
    unfold columnLog
    rw [primeProductNorm_union p D U hdU,mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']
  have hR : supportRay p χ (D∪U) = supportRay p χ D*supportRay p χ U := by
    rw [supportRay,Finset.prod_union hdU,rayCharacter_mul]
    rfl
  rw [hy,Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),hR]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,star_mul] <;> ring

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

def firstBareCubeCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (d : Eis) : Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C d

theorem firstBareCubeCoefficient_window (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    (fun S => firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative C d S *
      if negative then star (V (y S)*logPhase t (y S)) else V (y S)*logPhase t (y S)) =
    cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y (-t) d := by
  funext S
  have ht : logPhase (-t) (-(y S)) = logPhase t (y S) := by
    unfold logPhase
    congr 1
    push_cast
    ring
  cases negative <;>
    simp only [firstBareCubeCoefficient,cubeLogCoefficient,cubeMinusCoefficient,cubePlusCoefficient,
      firstPassColumnMinus,firstPassColumnPlus,logTwistMinus,logTwistPlus,
      Bool.false_eq_true,ite_false,ite_true,ht] <;> ring

theorem firstCommonColumn_original_labels
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) d) negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
        dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_eq_rayIdealRow p hp hg hinj F D _ negative χ ω X t hX h,
    firstBareCubeCoefficient_window p hp hg hcop B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f)
      (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) t d,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  rfl

theorem firstCommonColumn_marked_priority {σ : Type*} [DecidableEq σ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U)) c f) d)
      negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
        ∑ r : FirstCoreIndex,firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
          ∑ J ∈ slots.powerset,primeMark J lists a (A∪D) *
            firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
              (fun U => primeMark (slots\J) (fun i => lists i\(A∪D)) a U*H U)
              (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t)
              (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U))
    ω X t hX c d f h]
  rw [marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun u => ω (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) c d (-t)]
  simp_rw [firstCoreInputRow_marked_priority]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstFamilyEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFamilySeparatedRow (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  ∑ x∈source,w x*firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x)
    ω₁ ω₂ (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z

def firstFamilyEnergy (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) : ℝ :=
  ∑ x∈source,‖w x‖*firstBlockEnergy p hg F (selector x) (C x) negative ω X t (h x)

theorem firstFamilyEnergy_nonneg (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) :
    0 ≤ firstFamilyEnergy p hg source F selector C w negative ω X t h :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _)
    (firstBlockEnergy_nonneg p hg F (selector x) (C x) negative ω X t (h x)))

theorem first_family_cauchy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7) (H 7) h)*
      Real.sqrt (firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let weight (j : κ × (RayCharacter × RayCharacter) × Finset ι) : ℂ :=
    w j.1*firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)*
      firstOuterPhase H (firstCommonOuterLog p (A₁ j.1) (A₂ j.1) (C j.1) (R j.1)
        (d j.1) (h j.1) j.2.2 s)
  have hn (j : κ × (RayCharacter × RayCharacter) × Finset ι) :
      ‖weight j‖ = ‖w j.1‖*‖firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)‖ := by
    simp only [weight,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    (source ×ˢ ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)) weight
    (fun j => firstCommonColumn p hg F j.2.2 (C₂ j.1) false j.2.1.2 ω₂ (s 8) (H 8) (h j.1))
    (fun j => firstCommonColumn p hg F j.2.2 (C₁ j.1) true j.2.1.1 ω₁ (s 7) (H 7) (h j.1))
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      weight (x,r,D)*firstCommonColumn p hg F D (C₂ x) false r.2 ω₂ (s 8) (H 8) (h x)*
        star (firstCommonColumn p hg F D (C₁ x) true r.1 ω₁ (s 7) (H 7) (h x))) =
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
    simp only [firstFamilySeparatedRow,firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [weight,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  have hleft : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₁ x) true r.1 ω₁ (s 7) (H 7) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7) (H 7) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,ite_true]
  have hright : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₂ x) false r.2 ω₂ (s 8) (H 8) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8) (H 8) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,Bool.false_eq_true,ite_false]
  rw [hleft,hright] at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_family_integral_of_energy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact hh.trans_eq (by rw [←sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),B*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul B)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstFreshEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_fresh_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B,0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
      (ω : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ source,Squarefree x.1) →
      (∀ x ∈ source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z ∈ rows,z ≠ 0) → (∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x ∈ source,‖w x‖ ≤ M) →
      (∑ x ∈ source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1)) d)
        negative χ ω X t x.2‖^2) ≤
      M*K*Y^ε * ∑ z ∈ rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
        (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := SquarefreeDivisorBound.first_element_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C ω X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply le_trans _ (hpush source rows (dilationLabel p B v ε₁ ε₂) w
    (dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
      (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)) M Y hM hY hs hmap hrows hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ C ω X t hX c d (ConcretePrimeRowBridge.idealGenerator x.1) x.2]
  simp only [norm_mul]
  have hr0 : ‖supportRay p χ D‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one χ _
  have hr : ‖if negative then star (supportRay p χ D) else supportRay p χ D‖ ≤ 1 := by
    cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,norm_star]
      using hr0
  have hb := beforeDilationLabel_norm_le_one (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂
    negative c d (ConcretePrimeRowBridge.idealGenerator x.1) D
  calc
    _ ≤ ‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d
        (ConcretePrimeRowBridge.idealGenerator x.1) D‖ *
        ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (x.2*(ConcretePrimeRowBridge.idealGenerator x.1)^2*dilationLabel p B v ε₁ ε₂)‖ :=
      mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hb

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOldEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem firstBlockOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (selector : Finset ι → ℂ) (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) :
    ‖firstBlockOuterWeight p selector r D h‖ ≤ ‖crossCoeff r.1 r.2‖*‖selector D‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hm : ‖supportMobius (fun i => Ideal.span {p i}) D‖ = 1 := by
    have hs := congrArg norm (supportMobius_sq _ hprime hinj D)
    simp only [norm_mul,norm_one] at hs
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) D)]
  have hc : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [firstBlockOuterWeight,norm_mul,hm,mul_one]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc

def firstOldLabelCoefficient (hp : ∀ i,p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (c d : Eis) (f : Ideal Eis) : Finset ι → ℂ :=
  firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
    (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator f)) d

theorem first_block_old_label_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ j∈B,0 < v j) → ∀ (negative : Bool) (C : Finset ι → ℂ)
      (ω : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * firstBlockEnergy p hg F selector
        (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
        negative ω X t x.2) ≤
      M*K*Y^ε * ∑ r : RayCharacter × RayCharacter, ∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖) *
          ∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => ω (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F B selector v ε₁ ε₂ hv negative C ω X t hX c d
    source rows w M Y hM hY hs hmap hrows hnorm hw
  calc
    _ = ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,∑ x∈source,
        ‖w x‖*‖firstBlockOuterWeight p selector r D x.2‖*
          ‖firstCommonColumn p hg F D
            (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
            negative (if negative then r.1 else r.2) ω X t x.2‖^2 := by
      simp only [firstBlockEnergy,Finset.mul_sum,← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          (M*K*Y^ε*∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => ω (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ x∈source,
            ‖w x‖*‖firstCommonColumn p hg F D
              (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
              negative (if negative then r.1 else r.2) ω X t x.2‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          have hh := mul_le_mul_of_nonneg_left
            (firstBlockOuterWeight_norm_le p hinj selector r D x.2) (norm_nonneg (w x))
          exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
            (if negative then r.1 else r.2) C ω X t hX c d source rows w M Y
              hM hY hs hmap hrows hnorm hw) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring_nf

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstRetainedPhysical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCubePhysicalMode (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) : ℂ :=
  (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
    firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (cubeMinusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁) d)
      (cubePlusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) d)
      (fun x=>star (W₁ x)) W₂ Φ
      (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (primeProductNorm p C)
      (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h

theorem canonical_retained_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (T : Finset ι→Finset O) :
    canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K T =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
        ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂
          W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  unfold canonicalCubeDualFinite
  apply congrArg
  apply Finset.sum_congr rfl
  intro D hD
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have he := canonical_first_kernel_physical p hp hcop hg hinj hc hpr pool b hb C hC
    Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h
  change (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)‖^2:ℂ)⁻¹ * _ =
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K _ h at he
  rw [←Complex.ofReal_pow,primeSubsetGenerator_norm_eq_productNorm] at he
  rw [div_eq_mul_inv,mul_assoc,he]

theorem canonical_first_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (f : Ideal O) (hf : f≠0) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (R : Finset ι→ℝ)
    (hR : ∀ D,0≤R D) :
    let fgen := ConcretePrimeRowBridge.idealGenerator f
    let H₁' := fun U=>H₁ U*W₁ (primeProductNorm p U)
    let H₂' := fun U=>H₂ U*W₂ (primeProductNorm p U)
    let T := fun D=>childFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D)
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K =
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K +
      (canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ fgen *
        ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
          ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁ H₂
            W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h) +
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K T := by
  intro fgen H₁' H₂' T
  rw [canonicalCubeBeforePoisson_split p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K hK T]
  · rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  · intro D hD
    apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ f hf) _ _).mpr
    simpa only [mul_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0)] using hR D

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstToSecond -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFreshSecondPoisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) : ℂ :=
  ∑ G ∈ (F\D).powerset, ∑ U ∈ ((F\D)\G).powerset, ∑ V ∈ ((F\D)\G).powerset,
    if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
      (m*b0Label p B v ε₁ ε₂) (c*jLabel p B v ε₁ ε₂) d
      (firstCoreTest H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
      maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0

theorem firstFreshSecondPoisson_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) (hY : 0 < Y) :
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y =
    ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
      if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
        ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
        (firstCoreTest H (fun u => ω (Real.exp u))
          (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
        maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  unfold firstFreshSecondPoisson
  rw [← firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y hY]
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y]
  simp_rw [inputConjugateRow_fixed_pool p hg hinj F D]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F
    (firstCoreTwist negative χ Ψ r) ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i)
    (c*jLabel p B v ε₁ ε₂) d
    (firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D) rowMajorant Y hY

theorem first_fresh_core_energy_to_second
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis) (t : ℝ)
    (rows : Finset Eis) (Y : ℝ) (hY : 0 < Y)
    (hrows : ∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y)
    (hΨ : ‖Ψ (∏ i∈D,p i)‖ ≤ 1) :
    (∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) ≤
    (32*512) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y).re := by
  calc
    _ ≤ ∑ z∈rows,(32*512) * ∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
            (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact dilatedCoreRow_sq_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d (-t) z hΨ
    _ = (32*512) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
        ∑ z∈rows,‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact firstCoreInputRow_finite_le_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d r (-t) rows Y hY hrows

theorem first_fresh_old_labels_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) →
      ∀ (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), (∀ j∈B,0 < v j) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis),
      ‖Ψ (∏ i∈D,p i)‖ ≤ 1 → ∀ (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H)
            c (ConcretePrimeRowBridge.idealGenerator x.1)) d)
        negative χ ω X t x.2‖^2) ≤
      M*K*Y^ε * ((32*512)*∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F D B v ε₁ ε₂ hv negative χ Ψ m hΨ H ω X t hX
    c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ
    (multiplicativeCoreColumn p Ψ m H) ω X t hX c d source rows w M Y hM hY.le
      hs hmap hrows hnorm hw).trans
  exact mul_le_mul_of_nonneg_left
    (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative χ
      Ψ m H ω X c d t rows Y hY hnorm hΨ) (by positivity)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstFamilyToSecond -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_family_original_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) →
      ∀ (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ i∈B,0 < v i) → ∀ (negative : Bool) (Ψ : Eis →* ℂ) (m : Eis),
      (∀ a,‖Ψ a‖ ≤ 1) → ∀ (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x∈rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      firstFamilyEnergy p hg source F (fun _ => selector)
        (fun x => firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m H) c d x.1) w negative ω X t Prod.snd ≤
      M*K*Y^ε * ((32*512)*
        ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
          (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H ω X c d core t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_block_old_label_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B selector v ε₁ ε₂ hv negative Ψ m hΨ
    H ω X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  have h := hpush p hp hinj hcop hg F B selector v ε₁ ε₂ hv negative
    (multiplicativeCoreColumn p Ψ m H) ω X t hX c d source rows w M Y hM hY.le
    hs hmap hrows hnorm hw
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ((32*512)*∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H ω X c d core t Y).re) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left
        (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative
          (if negative then r.1 else r.2) Ψ m H ω X c d t rows Y hY hnorm (hΨ _)) (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro core hcore
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstCanonicalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def retainedCubeWeight (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) : ℂ :=
  a x * canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1) *
    cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2

theorem retainedCubeWeight_norm
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) :
    ‖retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a x‖≤‖a x‖ := by
  simp only [retainedCubeWeight,norm_mul]
  calc
    _ ≤ ‖a x‖*1*1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _) (norm_nonneg _))
        (cubeBaseFactor_norm_le_one p hp hcop hg hc _ _ _ _ _ _)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

include hp in
theorem retained_physical_row_support (b : CubeCoordinates ι) (x : Ideal O×O) (hx : x.1≠0)
    (Y : ℝ) (hcut : x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) x ∈
        nonzeroChildFrequencyBall 1 Y := by
  have hh := (mem_nonzeroChildFrequencyBall _
    (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ x.1 hx) _ _).mp hcut
  apply (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ _).mpr
  simpa only [one_mul,firstPhysicalMultiplier_row] using hh

theorem retained_cube_energy_to_second (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (source : Finset (Ideal O×O)) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ x∈source,Squarefree x.1) → (∀ x∈source,x.1≠0) → (∀ x∈source,‖a x‖≤Γ) →
      (∀ x∈source,x.2∈nonzeroChildFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) →
      ∀ (negative : Bool) (H : Finset ι→ℂ) (selector : Finset ι→ℂ)
        (ω : ℝ→ℂ) (X t : ℝ),0<X →
      let Ψ := if negative then Ψ₁ else Ψ₂
      let m := if negative then m₁ else m₂
      let Hshift := fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)
      let w := retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a
      firstFamilyEnergy p hg source F (fun _=>selector)
        (fun x=>firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (multiplicativeCoreColumn p Ψ m Hshift)
          (∏i∈C,p i) d x.1) w negative ω X t Prod.snd ≤
      Γ*K*Y^ε*((32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
          (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m Hshift ω X (∏i∈C,p i) d core t Y).re) := by
  obtain ⟨K,hK,hstep⟩ := first_family_original_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a source Γ Y hΓ hY
    hs hn ha hcut negative H selector ω X t hX Ψ m Hshift w
  apply hstep p hp hinj hcop hg hc hpr F b.support selector _ _ _ b.support_pos negative Ψ m
    (by intro u; cases negative
        · exact hΨ₂ u
        · exact hΨ₁ u) Hshift ω X t hX (∏i∈C,p i) d source
    (nonzeroChildFrequencyBall 1 Y) w Γ Y hΓ hY hs
  · intro x hx
    exact retained_physical_row_support p hp b x (hn x hx) Y (hcut x hx)
  · intro z hz
    exact (Finset.mem_erase.mp hz).1
  · intro z hz
    have hb := ((mem_nonzeroChildFrequencyBall 1 one_ne_zero Y z).mp hz).2
    simpa only [one_mul,eisEmbedding_norm_sq_eq_absNorm_span] using hb
  · intro x hx
    exact (retainedCubeWeight_norm p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a x).trans (ha x hx)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstPriorityEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem first_fresh_real_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (H : Finset ι→ℂ) (ω : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d core height Y).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
        (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2 := by
  unfold firstFreshSecondPoisson
  rw [←firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) rowMajorant Y hY,
    rowMajorant_tsum_eq_sum _ Y hY]
  let P := fun z=>firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z
  change (∑ z∈rowMajorantBall Y,rowMajorant (‖eisEmbedding z‖^2/Y)*(‖P z‖^2 : ℝ)).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re*‖P z‖^2
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

lemma priority_norm_sum_sq {α : Type*} (s : Finset α) (f : α→ℂ) :
    ‖∑ i∈s,f i‖^2≤(s.card:ℝ)*∑ i∈s,‖f i‖^2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
  apply hnorm.trans
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _=>(1:ℝ)) (fun i=>‖f i‖)

theorem first_fresh_priority_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (H : Finset ι→ℂ) (ω : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (fun U=>primeMark slots lists a (A∪U)*H U) ω X c d core height Y).re ≤
    (2:ℝ)^slots.card * ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
        (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U) ω X c d core height Y).re := by
  rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ ω X c d core height Y hY]
  calc
    _ ≤ ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re *
        ((slots.powerset.card:ℝ)*∑ J∈slots.powerset,
          ‖primeMark J lists a (A∪D) * firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U)
            (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (rowMajorant_nonneg _)
      rw [firstCoreInputRow_marked_priority]
      exact priority_norm_sum_sq _ _
    _ = _ := by
      simp_rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ ω X c d core height Y hY]
      simp only [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,Finset.mul_sum,norm_mul,mul_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      apply Finset.sum_congr rfl
      intro z hz
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstUnequalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_family_integral_of_two_energies (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    (Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      (Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply hh.trans_eq
    rw [Real.sqrt_mul hB₁,Real.sqrt_mul hB₂]
    calc
      _=(Real.sqrt B₁*Real.sqrt B₂)*(Real.sqrt (tripleHeight J z.1*coordinateHeight J z.2))^2:=by ring
      _= _:=by rw [Real.sq_sqrt];unfold tripleHeight coordinateHeight;positivity
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),(Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _
end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FreshWindows -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem fresh_ratio_of_source_support (W : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n) (hw : W (g*v*n) ≠ 0) :
    n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)) := by
  have hgp : 0 < g := hg₀.trans_le hg.1
  have hvp : 0 < v := hv₀.trans_le hv.1
  have hghi : 0 < g₁ := hgp.trans_le hg.2
  have hvhi : 0 < v₁ := hvp.trans_le hv.2
  have hsource := hs hw
  constructor
  · apply (div_le_iff₀ (mul_pos hghi hvhi)).mpr
    calc
      a ≤ g*v*n := hsource.1
      _ ≤ (g₁*v₁)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.2 hv.2 hvp.le hghi.le) hn
      _ = _ := by ring
  · apply (le_div_iff₀ (mul_pos hg₀ hv₀)).mpr
    calc
      _ = (g₀*v₀)*n := by ring
      _ ≤ g*v*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.1 hv.1 hv₀.le hgp.le) hn
      _ ≤ b := hsource.2

theorem fresh_window_eq_one (W ω : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n)
    (hω : ∀ n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)), ω n = 1)
    (hw : W (g*v*n) ≠ 0) : ω n = 1 :=
  hω n (fresh_ratio_of_source_support W a b g₀ g₁ v₀ v₁ g v n hs hg₀ hv₀ hg hv hn hw)

theorem secondChildKernelPair_insert_fresh {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (K : Finset ι → Finset ι → ℂ) (ω₁ ω₂ : Finset ι → ℂ)
    (hω : ∀ N ∈ (F \ V).powerset, ∀ M ∈ (F \ V).powerset,
      K (V ∪ N) (V ∪ M) ≠ 0 → ω₁ (V ∪ N) = 1 ∧ ω₂ (V ∪ M) = 1) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (ω₁ S)*ω₂ T*K S T) := by
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hK : K (V ∪ N) (V ∪ M) = 0
  · simp only [hK,mul_zero]
  · obtain ⟨h1,h2⟩ := hω N hN M hM hK
    simp only [h1,h2,star_one,one_mul]

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hp hcop hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ m r c d e k slots lists a W X
  unfold canonicalMarkedSplit
  rw [← hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁, ← hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂]
  unfold secondChildKernelPair secondChildSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  simp only [secondChildColumn,star_mul,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalSplit -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def reopenedPhysicalSourceSum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (source : CubeCoordinates ι→Finset ι→Ideal O→ℂ) : ℂ :=
  ∑ b∈reopenedCubeFamily Q,∑ C∈(pool\b.support).powerset,∑ I∈labels,
    reopenedPairCoefficient β b C I*source b C I

def reopenedPhysicalCutoff (b : CubeCoordinates ι) (I : Ideal O)
    (R : Finset ι→ℝ) (D : Finset ι) : Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit I) (R D)

def reopenedPhysicalRetained (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ : O→*ℂ) (m : O) (I : Ideal O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (R : Finset ι→ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ Ψ m m (idealGenerator I)*
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i∈D,Ideal.span {p i}):ℂ)*
      ∑ h∈(reopenedPhysicalCutoff p b I R D).erase 0,
        firstCubePhysicalMode p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
          (mark b.rightExponent) (mark b.leftExponent) W W Φ K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

theorem original_reopened_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    (∑ I∈labels,∑' z:O,Φ (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z‖^2:ℝ)) =
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W Φ K (R b C I)) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K
        (reopenedPhysicalCutoff p b I (R b C I))) := by
  rw [varying_reopened_smoothed_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m]
  · unfold varyingCanonicalSourceTotal reopenedPhysicalSourceSum
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro C hC
    apply Finset.sum_congr rfl
    intro I hI
    have hCb : Disjoint C b.support := by
      exact Finset.disjoint_left.mpr (fun i hi hib=>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hib)
    have he := canonical_first_physical_split p hp hcop hg hinj hc hpr pool b
      (reopenedCubeFamily_admissible Q b hb) C hCb Ψ Ψ m m I (hlabels I hI)
      (mark I b.rightExponent) (mark I b.leftExponent) W W Φ K hK (R b C I) (hR b hb C hC I hI)
    dsimp only at he
    rw [he]
    simp only [reopenedPhysicalRetained]
    rw [show reopenedPhysicalCutoff p b I (R b C I) =
      (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
        b.leftBit b.rightBit I) (R b C I D)) from rfl]
    ring
  · exact hK

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem rowFamilyEnergy_le_of_full_split (labels : Finset (Ideal O))
    (P : Ideal O→O→ℂ) (K : ℝ) (hK : 0<K) (A B C : ℂ)
    (he : (∑ I∈labels,∑' z:O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ))=A+B+C) :
    CanonicalRowCompletion.rowFamilyEnergy labels P K ≤ ‖A‖+‖B‖+‖C‖ := by
  unfold CanonicalRowCompletion.rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re]
  rw [he]
  have hn : 0≤(∑ I∈labels,((‖P I 0‖^2:ℝ):ℂ)).re := by
    simp only [Complex.re_sum,Complex.ofReal_re]
    exact Finset.sum_nonneg (fun I hI=>sq_nonneg _)
  simp only [Complex.add_re]
  linarith [Complex.re_le_norm A,Complex.re_le_norm B,Complex.re_le_norm C]

theorem original_reopened_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ)
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W rowMajorant K (R b C I))‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  apply rowFamilyEnergy_le_of_full_split labels _ K hK
  exact original_reopened_physical_split p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m mark W rowMajorant K hK R hR

end
end SevenEighths.InverseMoment

end OAI

end

