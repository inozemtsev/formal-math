module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part024
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part007
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part025

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationErrorEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationSourceError CenteredMomentAmplificationSourceDomain
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

def localErrorCost (p : O) (n : ℕ) : ℝ :=
  if n=5 then (1-(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹)^2
  else (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹

theorem localErrorCost_nonneg (p : O) (n : ℕ) : 0≤localErrorCost p n := by
  unfold localErrorCost
  split_ifs <;> positivity

theorem localErrorCost_exact (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (h : O) (hh : ¬p∣h) : ‖errorScalar p hp.ne_zero n h‖^2=localErrorCost p n := by
  have he := errorScalar_norms p hp hs hg hc h hh
  rcases hn with rfl|rfl|rfl
  · simpa only [localErrorCost,show ¬(0:ℕ)=5 by decide,ite_false] using he.1
  · simpa only [localErrorCost,ite_true] using he.2.1
  · simpa only [localErrorCost,show ¬(6:ℕ)=5 by decide,ite_false] using he.2.2

theorem finite_original_error_energy (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2 ∣ p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) (T : ℝ) (hT : 0<T)
    (rows : Finset O) (hrows : ∀ h∈rows,¬p∣h)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)≤
      localErrorCost p n *
        ((sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => c ((Ideal.span {p})^(n+1)*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re /
          (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  let Q := residualColumns S p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  let d : supportedColumns Q → ℂ := fun I =>
    c ((Ideal.span {p})^(n+1)*I)*residualCharacter p (n+1) (primaryGenerator I)
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he : (∑ h∈rows,‖amplificationError Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => (Real.sqrt T:ℂ)⁻¹*c I)
      (fun I => multiplicity p (sourceGenerator S I)) p (n+1) h‖^2)=
      localErrorCost p n *∑ h∈rows,
        ‖gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I => (Real.sqrt T':ℂ)⁻¹*d I) h‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [normalized_source_error_sq S c p hp hs hpp n h T hT,
      localErrorCost_exact p hp hs hg hc n hn h (hrows h hh)]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (localErrorCost_nonneg p n)
  have hh := finite_energy_le_gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I => (Real.sqrt T':ℂ)⁻¹*d I) W K hK rows hW hmajor
  rw [gaussEnergy_central _ _ _ d T' ht] at hh
  exact hh

end SevenEighths.CenteredMomentAmplificationErrorEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationFamily -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentFixedRay
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSecondChildProfile CenteredMomentSourceRow CenteredMomentChildRows
local notation "O" => ActualEisensteinCubic.O

def amplificationPhase (p : O) (k : ℕ) (r : RayRing) : ℂ :=
  (QuadraticAllOddCRT.quadraticRaySign (ActualEisensteinCoordinates.residue p)
    (QuadraticGaussRay.residueQuotientFour r):ℂ)^k

theorem amplificationPhase_mk (p u : O) (k : ℕ) :
    amplificationPhase p k (Ideal.Quotient.mk _ u)=sexticReciprocityPhase p u^k := by
  simp only [amplificationPhase,QuadraticGaussRay.residueQuotientFour_mk,sexticReciprocityPhase]

theorem amplificationPhase_norm (p : O) (k : ℕ) (r : RayRing) :
    ‖amplificationPhase p k r‖≤1 := by
  unfold amplificationPhase QuadraticAllOddCRT.quadraticRaySign
  split_ifs <;> cases k <;> simp

theorem amplificationPhase_mass (p : O) (k : ℕ) :
    (∑ χ : RayCharacter,‖phaseCoeff (amplificationPhase p k) χ‖)≤16 := by
  simpa only [mul_one] using phaseCoeff_sum_norm_le (amplificationPhase p k) 1
    (fun u => amplificationPhase_norm p k u)

theorem amplificationPhase_expansion (p u : O) (k : ℕ)
    (hu : Supported (Ideal.span {u})) :
    sexticReciprocityPhase p u^k=
      ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*rayCharacter χ u := by
  have he := phase_expansion (amplificationPhase p k) u
  simpa only [supported_rayMask u hu,one_mul,amplificationPhase_mk] using he

theorem exists_amplification_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I := by
  choose τ hN hτ using fun χ : RayCharacter =>
    exists_second_height_character η χ m (p^(2*k)) hm (pow_ne_zero _ hp) hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn := supported_primaryGenerator_ne_zero I hI
  have hgen : Supported (Ideal.span {primaryGenerator I}) := by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem original_column_family (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (C I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
      rowWeight η m 1 1 t C *
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*(β (C*I)*heightCoeff (τ χ) t I) := by
  rw [map_mul]
  calc
    _ = rowWeight η m 1 1 t C *
      (β (C*I)*(rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I))) := by ring
    _ = _ := by rw [hτ I hI t,Finset.mul_sum];congr 1;apply Finset.sum_congr rfl;intro χ hχ;ring

end SevenEighths.CenteredMomentAmplificationFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationFamilyEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationFamilyEnergy
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationFamily
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRow CenteredMomentChildRows CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentSourceSmoothedAllocation CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O

theorem amplification_family_energy (η : Character) (m p : O) (k : ℕ)
    (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
        ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I)
    (Q : Finset (Ideal O)) (C : Ideal O) (hC : C≠0) (β : Ideal O → ℂ) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
      (fun I => residualCharacter p k (primaryGenerator I)) W K).re≤
      16*∑ χ : RayCharacter,
        (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  let b : RayCharacter → ℂ := fun χ => rowWeight η m 1 1 t C*phaseCoeff (amplificationPhase p k) χ
  let d : RayCharacter → supportedColumns Q → ℂ := fun χ I => β (C*I)*heightCoeff (τ χ) t I
  have he (I : supportedColumns Q) :
      (β (C*I)*rowWeight η m 1 1 t (C*I))*residualCharacter p k (primaryGenerator I)=
        ∑ χ,b χ*d χ I := by
    rw [original_column_family η m p k τ hτ C I (Finset.mem_filter.mp I.property).2 β t,Finset.mul_sum]
    simp only [b,d,mul_assoc]
  have hb (χ : RayCharacter) : ‖b χ‖≤1 := by
    dsimp only [b]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m 1 1 t C hC)).trans
      (phaseCoeff_norm_le _ 1 (fun u => amplificationPhase_norm p k u) χ)
  have hd (χ : RayCharacter) : 0≤(sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re :=
    sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hh := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [funext he]
  apply hh.trans
  apply mul_le_mul
  · exact_mod_cast rayCharacter_card_le
  · apply Finset.sum_le_sum
    intro χ hχ
    apply mul_le_of_le_one_left (hd χ)
    nlinarith [hb χ,norm_nonneg (b χ)]
  · exact Finset.sum_nonneg (fun χ _ => mul_nonneg (sq_nonneg _) (hd χ))
  · norm_num

theorem exists_amplification_energy_family (η : Character) (m p : O)
    (hm : m≠0) (hp : p≠0) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ, (τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*k))) ∧
      ∀ (Q : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p k (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_family η m p hm hp hs hpp hmLam hm2 k
  exact ⟨τ,hN,fun Q C hC β t W K hK hW => amplification_family_energy η m p k τ hτ Q C hC β t W K hK hW⟩

end SevenEighths.CenteredMomentAmplificationFamilyEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFactor -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFactor
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge CompletedGauss
open CenteredMomentAmplificationShortening CenteredMomentSupportedCorrelation
open CenteredMomentAmplificationSourceDomain CenteredMomentAmplificationSourcePool
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def errorMovingExponent (n : ℕ) : ℕ := if n=5 then 0 else 1

theorem residual_six_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 6 u=residualCharacter p 0 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*(idealRowHom u (Ideal.span {p})^6)^2 := by ring
    _ = 1 := by rw [hphase,hx];norm_num
    _ = _ := by simp

theorem residual_seven_unit (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) : residualCharacter p 7 u=residualCharacter p 1 u := by
  have hx := idealRowHom_sixth_mask u (Ideal.span {p}) hp
  rw [idealRowHom_argument_pow u 6 _ hp,Ideal.isCoprime_span_singleton_iff,ite_eq_left hcop] at hx
  have hphase := supported_phase_sq p u hp hu
  unfold residualCharacter
  norm_num only
  calc
    _ = (sexticReciprocityPhase p u^2)^3*sexticReciprocityPhase p u*
        (idealRowHom u (Ideal.span {p})^6)^2*idealRowHom u (Ideal.span {p})^2 := by ring
    _ = _ := by rw [hphase,hx];ring

theorem error_residual_factor (p u : O)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hcop : IsCoprime p u) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    residualCharacter p (n+1) u=residualCharacter p (errorMovingExponent n) u := by
  rcases hn with rfl|rfl|rfl
  · rfl
  · exact residual_six_unit p u hp hu hcop
  · exact residual_seven_unit p u hp hu hcop

theorem residualColumns_coprime (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (k : ℕ) (I : Ideal O) (hI : I∈residualColumns S p hp k) :
    IsCoprime (Ideal.span {p}) I := by
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact residualIdeal_coprime p hp J (valuationColumns_supported S p k J hJ)

theorem residual_column_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (I : Ideal O) (hI : I∈residualColumns S p hp (n+1)) :
    residualCharacter p (n+1) (primaryGenerator I)=
      residualCharacter p (errorMovingExponent n) (primaryGenerator I) := by
  have hsI := residualColumns_supported S p hp (n+1) I hI
  apply error_residual_factor p _ hs _ _ n hn
  · rw [primary_span_supported I hsI];exact hsI
  · apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [primary_span_supported I hsI]
    exact residualColumns_coprime S p hp (n+1) I hI

end SevenEighths.CenteredMomentAmplificationActiveFactor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationActiveFamily -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationActiveFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationShortening CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationFamilyEnergy CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem actual_error_energy_active (S : Finset (Ideal O)) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K=
    sourceGaussEnergy (residualColumns S p hp (n+1)) c
      (fun I => residualCharacter p (errorMovingExponent n) (primaryGenerator I)) W K := by
  let Q := residualColumns S p hp (n+1)
  apply congrArg (fun f : supportedColumns Q → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) f W K)
  funext I
  dsimp only
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

theorem exists_actual_error_family (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1
        (p^(2*errorMovingExponent n))) ∧
      ∀ (S : Finset (Ideal O)) (C : Ideal O),C≠0 → ∀ (β : Ideal O → ℂ) (t : ℝ)
        (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I => β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑ χ : RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re := by
  obtain ⟨τ,hN,hτ⟩ := exists_amplification_energy_family η m p hm hp.ne_zero hs hpp hmLam hm2
    (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact hτ (residualColumns S p hp (n+1)) C hC β t W K hK hW

end SevenEighths.CenteredMomentAmplificationActiveFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationOriginalErrors -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationOriginalErrors
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationShortening
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentAmplificationSourceDomain CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_errors_to_children (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤_
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

end SevenEighths.CenteredMomentAmplificationOriginalErrors

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

abbrev ballProfile : 𝓢(ℝ,ℂ) := QuadraticInitialBound.sieveCutoff

theorem ballProfile_nonneg (x : ℝ) : 0 ≤ (ballProfile x).re := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.nonneg (x:=x))

theorem ballProfile_le_one (x : ℝ) : (ballProfile x).re ≤ 1 := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.le_one (x:=x))

theorem ballProfile_one (x : ℝ) (hx : 0≤x) (hx1 : x≤1) : ballProfile x=1 := by
  simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1,Complex.ofReal_one]

theorem ballProfile_majorizes (Y : ℝ) (hY : 0<Y) (z : O)
    (hz : normValue z≤Y) : 1≤(ballProfile (‖eisEmbedding z‖^2/Y)).re := by
  rw [←normValue_eq_embedding]
  have he := ballProfile_one (normValue z/Y)
    (div_nonneg (by unfold normValue; positivity) hY.le) ((div_le_one hY).mpr hz)
  rw [he]
  norm_num

def primeTest : ContDiffBump (3/4 : ℝ) where
  rIn := 1/16
  rOut := 1/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem primeTest_support : Function.support primeTest ⊆ Set.Ioo (1/2) 1 := by
  intro x hx
  rw [primeTest.support_eq,Metric.mem_ball,Real.dist_eq] at hx
  change |x-3/4|<1/8 at hx
  have hh := abs_lt.mp hx
  constructor <;> linarith

theorem primeTest_tsupport : tsupport primeTest ⊆ Set.Ioi 0 := by
  intro x hx
  rw [primeTest.tsupport_eq,Metric.mem_closedBall,Real.dist_eq] at hx
  change |x-3/4|≤1/8 at hx
  have hh := abs_le.mp hx
  change 0<x
  linarith

theorem primeTest_ne_zero : (primeTest : ℝ→ℝ)≠0 := by
  have h : primeTest (3/4)=1 := primeTest.one_of_mem_closedBall
    (by simp [primeTest,Metric.mem_closedBall])
  intro hz
  have he := congrFun hz (3/4)
  change primeTest (3/4)=0 at he
  linarith

theorem eventually_log_card_power (c ell loss : ℝ)
    (hc : 0<c) (hell : 0<ell) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤ c*Z^ell/Real.log (Z^ell) := by
  have hb := (isLittleO_log_rpow_atTop hloss).bound (div_pos hc hell)
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with Z hbound hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlog : 0<Real.log Z := Real.log_pos hZ
  have hpow : 0<Z^loss := Real.rpow_pos_of_pos hz _
  have hh : ell*Real.log Z≤ c*Z^loss := by
    have hh' : Real.log Z≤(c/ell)*Z^loss := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hpow] using hbound
    calc
      _ ≤ ell*((c/ell)*Z^loss) := mul_le_mul_of_nonneg_left hh' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hz]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    _ ≤ Z^(ell-loss)*(c*Z^loss) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hz,sub_add_cancel]

section Pool
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem eventually_actual_pool_card (Sbad : Finset (Ideal O))
    (ell loss : ℝ) (hell : 0<ell) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
  obtain ⟨c,hc,hcard⟩ := eventually_primePool_card M H hH Sbad primeTest
    primeTest.contDiff primeTest.hasCompactSupport primeTest_tsupport
    (fun _ => primeTest.nonneg) primeTest_ne_zero (1/2) 1 1
    (by norm_num) (by norm_num) (by norm_num) primeTest_support (fun _ => primeTest.le_one)
  filter_upwards [(tendsto_rpow_atTop hell).eventually hcard,
    eventually_log_card_power c ell loss hc hell hloss] with Z hcard hpower
  exact hpower.trans hcard

theorem eventually_actual_pool (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (ell loss cap b eta : ℝ)
    (hell : 0<ell) (hloss : 0<loss) (hgap : eta<ell/2) :
    ∀ᶠ Z : ℝ in atTop,
      1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^ell)
      P.Nonempty ∧ Z^(ell-loss)≤(P.card:ℝ) ∧
      2*(cap/(ell/2))≤(P.card:ℝ) ∧ b*Z^eta<Z^(ell/2) ∧
      ∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(ell/2)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤Z^ell := by
  have he : 0<ell/2 := by linarith
  filter_upwards [eventually_actual_pool_card M H hH Sbad ell loss hell hloss,
    eventually_actual_pool_card M H hH Sbad ell (ell/2) hell he,
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2*(cap/(ell/2)))),
    eventually_scale_gap b eta (ell/2) hgap,eventually_gt_atTop (1:ℝ)]
    with Z hcard hlarge htwo hcap hslot hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlarge' : Z^(ell/2)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
    simpa only [show ell-ell/2=ell/2 by ring] using hlarge
  have hp : (primePool M H Sbad (1/2) 1 (Z^ell)).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (ell/2)).trans_le hlarge'
  refine ⟨hZ,hp,hcard,hcap.trans hlarge',hslot.2,?_⟩
  intro Q hQ
  have hdata := primePool_data M H Sbad hbad (1/2) 1 (Z^ell) Q hQ
  have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz ell) (Finset.mem_sdiff.mp hQ).1
  have hs : Z^ell=(Z^(ell/2))^2 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  refine ⟨hdata.1,hdata.2,?_,?_⟩
  · rw [hs] at hn
    nlinarith [sq_nonneg (Z^(ell/2)-2)]
  · simpa only [mul_one] using hn.2

omit hH in
theorem reciprocal_pool_bound (Sbad : Finset (Ideal O)) (ell loss Z : ℝ)
    (hZ : 0<Z)
    (hc : Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card) :
    ((primePool M H Sbad (1/2) 1 (Z^ell)).card:ℝ)⁻¹≤Z^(-ell+loss) := by
  have hp := Real.rpow_pos_of_pos hZ (ell-loss)
  have he := (inv_le_inv₀ (hp.trans_le hc) hp).mpr hc
  simpa only [←Real.rpow_neg hZ.le,show -(ell-loss)=-ell+loss by ring] using he

end Pool

def dyadRows (n : ℤ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈dyadicScale n⌉₊).filter
    (fun h => dyadicWeight n (normValue h)≠0)

@[simp] theorem mem_dyadRows (n : ℤ) (h : O) :
    h∈dyadRows n ↔ dyadicWeight n (normValue h)≠0 := by
  constructor
  · exact fun hh => (Finset.mem_filter.mp hh).2
  · intro hh
    refine Finset.mem_filter.mpr ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    have hn := (dyadicWeight_support n hh).2.le.trans (Nat.le_ceil (dyadicScale n))
    unfold normValue at hn
    exact_mod_cast hn

theorem dyadRows_ne_zero (n : ℤ) (h : O) (hh : h∈dyadRows n) : h≠0 := by
  intro he
  have hn := (mem_dyadRows n h).mp hh
  subst h
  exact hn (by simpa [normValue] using dyadicWeight_zero_nonpos n 0 le_rfl)

theorem dyadRows_norm_lt (n : ℤ) (h : O) (hh : h∈dyadRows n) :
    normValue h<dyadicScale n :=
  (dyadicWeight_support n ((mem_dyadRows n h).mp hh)).2

theorem dyadRows_log_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℤ)
    (hne : (dyadRows n).Nonempty) : 0≤Real.logb Z (dyadicScale n) := by
  obtain ⟨h,hh⟩ := hne
  exact Real.logb_nonneg hZ
    ((normValue_ge_one h (dyadRows_ne_zero n h hh)).trans (dyadRows_norm_lt n h hh).le)

theorem dyadic_energy_eq_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)=
      ∑ h∈dyadRows n,dyadicWeight n (normValue h)*‖f h‖^2 := by
  apply tsum_eq_sum
  intro h hh
  have hz : dyadicWeight n (normValue h)=0 := by
    by_contra hn
    exact hh ((mem_dyadRows n h).mpr hn)
  rw [hz,zero_mul]

theorem dyadic_energy_le_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)≤
      ∑ h∈dyadRows n,‖f h‖^2 := by
  rw [dyadic_energy_eq_sum]
  exact Finset.sum_le_sum (fun h _ =>
    mul_le_of_le_one_left (sq_nonneg _) (dyadicWeight_bounds n (normValue h)).2)

theorem dyadic_energy_empty (n : ℤ) (f : O→ℂ) (h : dyadRows n=∅) :
    (∑' z : O,dyadicWeight n (normValue z)*‖f z‖^2)=0 := by
  rw [dyadic_energy_eq_sum,h,Finset.sum_empty]

def mainGain (D0 c sigma : ℝ) : ℝ := max (D0-c) 0+2*sigma

def errorRemoval (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*Real.logb Z (normValue p)

def errorMoving (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  if k=6 then 0 else Real.logb Z (normValue p)

def errorGain (D0 c sigma Z : ℝ) (p : O) (k : ℕ) : ℝ :=
  max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma

theorem mainGain_bounds (D0 c sigma : ℝ) (hs : 0≤ sigma) :
    2*sigma≤ mainGain D0 c sigma ∧ D0-c+sigma≤ mainGain D0 c sigma := by
  have h0 := le_max_right (D0-c) (0:ℝ)
  have h1 := le_max_left (D0-c) (0:ℝ)
  unfold mainGain
  constructor <;> linarith

theorem errorGain_bounds (D0 c sigma Z : ℝ) (p : O) (k : ℕ) (hs : 0≤ sigma) :
    sigma≤errorGain D0 c sigma Z p k ∧
    D0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤errorGain D0 c sigma Z p k ∧
    errorGain D0 c sigma Z p k≤
      max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+2*sigma := by
  have h0 := le_max_right (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  have h1 := le_max_left (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  unfold errorGain
  constructor
  · linarith
  constructor <;> linarith

theorem error_lengths (p : O) (Z sigma : ℝ) (hs : 0≤ sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hl : 0≤Real.logb Z (normValue p))
    (hu : Real.logb Z (normValue p)≤ sigma/3) :
    0≤errorMoving p Z k ∧ errorMoving p Z k≤errorRemoval p Z k ∧
      errorRemoval p Z k≤7*sigma/3 := by
  have hk1 : (1:ℝ)≤k := by rcases hk with rfl|rfl|rfl <;> norm_num
  have hk7 : (k:ℝ)≤7 := by rcases hk with rfl|rfl|rfl <;> norm_num
  unfold errorMoving errorRemoval
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem dyadRows_norm_power (Z : ℝ) (hZ : 1<Z) (n : ℤ)
    (h : O) (hh : h∈dyadRows n) :
    normValue h≤Z^(Real.logb Z (dyadicScale n)) := by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos n)]
  exact (dyadRows_norm_lt n h hh).le

theorem dyad_ball_majorant (Z : ℝ) (hZ : 1<Z) (n : ℤ) (g : ℝ) (hg : 0≤g)
    (h : O) (hh : h∈dyadRows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/Z^(Real.logb Z (dyadicScale n)+g))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact (dyadRows_norm_power Z hZ n h hh).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

theorem amplified_ball_majorant (Z sigma D0 c : ℝ) (hZ : 1<Z) (hs : 0≤ sigma)
    (n : ℤ) (h p : O) (hh : h∈dyadRows n)
    (hp : normValue p≤Z^(sigma/3)) :
    1≤(ballProfile (‖eisEmbedding (p^6*h)‖^2/
      Z^(Real.logb Z (dyadicScale n)+mainGain D0 c sigma))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hb := outputRow_norm (h,p) Z (Real.logb Z (dyadicScale n)) (sigma/3)
    (zero_lt_one.trans hZ) (dyadRows_norm_power Z hZ n h hh) hp
  change normValue (p^6*h)≤Z^(Real.logb Z (dyadicScale n)+6*(sigma/3)) at hb
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith [(mainGain_bounds D0 c sigma hs).1]))

theorem gaussEnergy_ball_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (Y : ℝ) (hY : 0<Y) :
    0≤(gaussEnergy S a ha c ballProfile Y).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun h => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))

theorem errorEnergy_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (h p : O) :
    0≤errorEnergy S a ha c h p := by
  unfold errorEnergy
  positivity

theorem eligible_error_sum {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (rows P : Finset O) (allow : O→O→Prop) :
    (∑x∈eligiblePairs rows P allow,errorEnergy S a ha c x.1 x.2)=
      ∑p∈P,∑h∈rows.filter (fun h => allow h p),errorEnergy S a ha c h p := by
  rw [←sum_eligiblePairs]
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

theorem dyadic_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Z sigma D0 cLog : ℝ) (hZ : 1<Z) (hsigma : 0≤ sigma) (n : ℤ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (gaussEnergy S a ha c ballProfile
        (Z^(Real.logb Z (dyadicScale n)+(max (D0-cLog) 0+sigma)))).re := by
  apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans
  apply finite_energy_le_gaussEnergy S a ha c ballProfile _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (dyadRows n)
    (fun _ => ballProfile_nonneg _)
  exact dyad_ball_majorant Z hZ n _ (by positivity)

theorem dyadic_amplification_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (P : Finset (Ideal O)) (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R≠0) (hs0 : s≠0)
    (Z sigma BR Bs Mmax D0 cLog : ℝ) (hZ : 1<Z) (hsigma : 0<sigma) (hM : 0≤Mmax)
    (hlower : ∀Q∈P,Z^(sigma/6)≤(Ideal.absNorm Q:ℝ))
    (hupper : ∀Q∈P,(Ideal.absNorm Q:ℝ)≤Z^(sigma/3))
    (hR : (Ideal.absNorm R:ℝ)≤Z^BR) (hs : (Ideal.absNorm s:ℝ)≤Z^Bs)
    (hsize : 2*((BR+Bs+Mmax)/(sigma/6))≤(P.card:ℝ))
    (n : ℤ) (hK : Real.logb Z (dyadicScale n)≤Mmax) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (8/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          (gaussEnergy S a ha c ballProfile
            (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
          ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
            errorEnergy S a ha c h p) := by
  let K := Real.logb Z (dyadicScale n)
  have hY : 0<Z^(K+mainGain D0 cLog sigma) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have henergy := gaussEnergy_ball_nonneg S a ha c _ hY
  by_cases hn : (dyadRows n).Nonempty
  · have hK0 := dyadRows_log_nonneg Z hZ n hn
    have hsize' : 2*((BR+Bs+K)/(sigma/6))≤(P.card:ℝ) := by
      apply le_trans _ hsize
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)
    have he := actual_eligible_amplification S a ha c (dyadRows n)
      (dyadRows_ne_zero n) P hp hbad hP R s hR0 hs0 Z (sigma/6) BR Bs K (sigma/3)
      hZ (by linarith) hlower hupper hR hs hsize' (dyadRows_norm_power Z hZ n)
    have hmajor : (∑y∈(eligiblePairs (dyadRows n) (elementPool P) (eligible R s)).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2)≤
        (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re := by
      apply finite_energy_le_gaussEnergy S a ha c ballProfile _ hY _
        (fun _ => ballProfile_nonneg _) _
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hx' := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
      have hpx := elementPool_data P hp hbad x.2 hx'.2
      exact amplified_ball_majorant Z sigma D0 cLog hZ hsigma.le n x.1 x.2 hx'.1
        (hupper _ hpx.2.1)
    apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans (he.trans ?_)
    rw [eligible_error_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    calc
      _ ≤ ((K+6*(sigma/3))/(sigma/6))*
          (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re :=
        mul_le_mul_of_nonneg_left hmajor (by dsimp [K];positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)) henergy
  · rw [dyadic_energy_empty n _ (Finset.not_nonempty_iff_eq_empty.mp hn)]
    apply mul_nonneg (by positivity)
    apply add_nonneg
    · exact mul_nonneg (by positivity) henergy
    · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg
        (fun h _ => errorEnergy_nonneg S a ha c h p))

theorem eventually_dyadic_amplification (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧ b*Z^eta<Z^(sigma/6) ∧
      (∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(sigma/6)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤Z^(sigma/3)) ∧
      ∀ {α : Type*} (S : Finset α) (a : α→O) (ha : ∀i,Supported (Ideal.span {a i}))
        (c : α→ℂ) (R s : Ideal O), R≠0 → s≠0 →
        (Ideal.absNorm R:ℝ)≤Z^BR → (Ideal.absNorm s:ℝ)≤Z^Bs →
        ∀ (n : ℤ),Real.logb Z (dyadicScale n)≤Mmax → ∀ (D0 cLog : ℝ),
        (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
          (8/(P.card:ℝ))*
            (((Mmax+2*sigma)/(sigma/6))*
              (gaussEnergy S a ha c ballProfile
                (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
              ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
                errorEnergy S a ha c h p) := by
  have he := eventually_actual_pool M H hH Sbad hbad (sigma/3) loss
    (BR+Bs+Mmax) b eta (by linarith) hloss (by linarith)
  simp only [show sigma/3/2=sigma/6 by ring] at he
  filter_upwards [he] with Z hz
  obtain ⟨hZ,hP,hcard,hsize,hslot,hdata⟩ := hz
  refine ⟨hZ,hP,hcard,hslot,hdata,?_⟩
  intro α S a ha c R s hR0 hs0 hR hs n hK D0 cLog
  exact dyadic_amplification_to_ball S a ha c _ (fun Q hQ => (hdata Q hQ).1)
    (fun Q hQ => (hdata Q hQ).2.1) hP R s hR0 hs0 Z sigma BR Bs Mmax D0 cLog
    hZ hsigma hM (fun Q hQ => (hdata Q hQ).2.2.1)
    (fun Q hQ => (hdata Q hQ).2.2.2) hR hs hsize n hK

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor

local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

structure OriginalData (ι : Type*) [Fintype ι] where
  S : (ι ⊕ Fin 2) → Finset (Ideal O)
  R : Ideal O
  s : Ideal O
  nu : ι → Ideal O → ℂ
  slot : ι → ℝ → ℂ
  lengths : ι → ℝ
  W₁ : ℝ → ℂ
  W₂ : ℝ → ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  B₁ : Ideal O
  B₂ : Ideal O

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def profile (D : OriginalData ι) : Tuple ι → ℂ :=
  profileCoefficient D.R D.nu D.slot D.lengths D.W₁ D.W₂
    D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ D.s

def columns (D : OriginalData ι) : Finset (Ideal O) :=
  finiteColumns (Fintype.piFinset D.S)

def beta (D : OriginalData ι) : Ideal O → ℂ :=
  finiteColumnCoefficient (Fintype.piFinset D.S) D.profile

def coefficient (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ)
    : supportedColumns D.columns → ℂ :=
  fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)

theorem coefficient_eq (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ) :
    D.coefficient η m t T = fun I : supportedColumns D.columns =>
      (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I) := rfl

def childEnergy (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) : ℝ :=
  let C := (Ideal.span {p})^(n+1)
  (16*(n+2:ℝ)*localErrorCost p n) *
    ((∑ χ : RayCharacter,∑ B : actualAllocations D.S C,
      (sourceGaussEnergy
        (finiteColumns (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1))
        (finiteColumnCoefficient
          (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C D.R D.s D.nu D.slot D.lengths D.W₁ D.W₂
            D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂))
        (heightCoeff (τ χ) t) ballProfile K).re) /
      (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)))

theorem childEnergy_nonneg (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) (hT : 0≤T) (hK : 0<K) :
    0≤D.childEnergy τ p n t T K := by
  apply mul_nonneg (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_nonneg _ (div_nonneg hT (by positivity))
  exact Finset.sum_nonneg (fun χ _ => Finset.sum_nonneg (fun B _ =>
    sourceGaussEnergy_nonneg _ _ _ ballProfile K hK (fun _ => ballProfile_nonneg _)))

end OriginalData

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤ sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

def errorIndex (i : Fin 3) : ℕ := ![0,5,6] i

theorem errorIndex_cases (i : Fin 3) : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
  fin_cases i <;> simp [errorIndex]

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤ sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem original_slot_coprime {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (Z sigma b eta : ℝ) (hZ : 1≤Z) (hb : 0≤b)
    (hgap : b*Z^eta<Z^(sigma/6))
    (z : ι → ℝ) (hz : ∀i,z i≤eta) (hlen : ∀i,D.lengths i=Z^(z i))
    (hsupp : ∀i,Function.support (D.slot i)⊆Set.Iic b)
    (hslot : ∀i,∀I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0)
    (hprime : ∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q : Ideal O) (hQ : Prime Q) (hQN : Z^(sigma/6)≤(Ideal.absNorm Q:ℝ)) :
    ∀i,∀I∈D.S (Sum.inl i),IsCoprime Q I := by
  intro i I hI
  have hW := hslot i I hI
  rw [hlen] at hW
  have hN := live_profile_norm_bound (D.slot i) b Z (z i) eta I hb hZ (hz i) (hsupp i) hW
  exact ((HeckeInverseAmplification.prime_coprime_iff ⟨Q,hQ⟩ I).mpr
    (amplifier_not_dvd_slot Q I hQ (hprime i I hI) Z (sigma/6) eta b hgap hQN hN)).symm

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def active (D : OriginalData ι) : OriginalData ι :=
  { D with S := fun i => match i with
    | Sum.inl j => (D.S i).filter (fun I => D.slot j ((Ideal.absNorm I:ℝ)/D.lengths j)≠0)
    | Sum.inr _ => D.S i }

theorem active_subset (D : OriginalData ι) (i : ι ⊕ Fin 2) : D.active.S i⊆D.S i := by
  cases i <;> simp only [active]
  · exact Finset.filter_subset _ _
  · exact fun _ h => h

theorem active_profile (D : OriginalData ι) : D.active.profile=D.profile := rfl

theorem active_slot (D : OriginalData ι) (i : ι) (I : Ideal O) (hI : I∈D.active.S (Sum.inl i)) :
    D.active.slot i ((Ideal.absNorm I:ℝ)/D.active.lengths i)≠0 :=
  (Finset.mem_filter.mp hI).2

theorem active_profile_zero (D : OriginalData ι) (v : Tuple ι)
    (hv : v∈Fintype.piFinset D.S) (hn : v∉Fintype.piFinset D.active.S) : D.profile v=0 := by
  have hn' : ¬∀i,v i∈D.active.S i := by simpa only [Fintype.mem_piFinset] using hn
  obtain ⟨i,hi⟩ := not_forall.mp hn'
  have hvi := Fintype.mem_piFinset.mp hv i
  cases i with
  | inr j => exact False.elim (hi hvi)
  | inl j =>
    have hz : D.slot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/D.lengths j)=0 := by
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨hvi,hne⟩)
    have hp : (∏k,D.nu k (v (Sum.inl k))*D.slot k
        ((Ideal.absNorm (v (Sum.inl k)):ℝ)/D.lengths k))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz,mul_zero]
    simp only [profile,profileCoefficient,hp,zero_mul]

theorem active_beta (D : OriginalData ι) : D.active.beta=D.beta := by
  funext I
  unfold beta finiteColumnCoefficient
  rw [active_profile]
  apply Finset.sum_subset (Finset.filter_subset_filter _
    (Fintype.piFinset_subset _ _ (D.active_subset)))
  intro v hv hn
  have hv' := Finset.mem_filter.mp hv
  apply D.active_profile_zero v hv'.1
  intro hm
  exact hn (Finset.mem_filter.mpr ⟨hm,hv'.2⟩)

theorem active_columns_subset (D : OriginalData ι) : D.active.columns⊆D.columns :=
  Finset.image_subset_image (Fintype.piFinset_subset _ _ D.active_subset)

theorem active_gaussPolynomial (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) h=
    gaussPolynomial Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) h := by
  unfold coefficient
  rw [D.active_beta]
  rw [CenteredMomentLiveDomain.source_gaussPolynomial D.active.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h,
    CenteredMomentLiveDomain.source_gaussPolynomial D.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h]
  apply Finset.sum_subset (Finset.filter_subset_filter _ D.active_columns_subset)
  intro I hI hn
  have hz : D.beta I=0 := by
    by_contra hne
    have hm := CenteredMomentLiveDomain.finite_column_mem
      (Fintype.piFinset D.active.S) D.active.profile I
      (by change D.active.beta I≠0;rw [D.active_beta];exact hne)
    exact hn (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hI).2⟩)
  rw [hz,zero_mul,mul_zero,zero_mul]

theorem active_gaussEnergy (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) W K=
    gaussEnergy Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) W K := by
  unfold gaussEnergy
  simp_rw [D.active_gaussPolynomial]

end OriginalData

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstExtractedLedger
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

def nominalLog (I J E : Ideal O) (K X Z : ℝ) : ℝ :=
  Real.logb Z (firstNominalScale I J E K X)

theorem retained_nominal_choice (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n)
    (hne : (dyadRows n).Nonempty) :
    0≤Real.logb Z (dyadicScale n) ∧
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi ∧
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec xi≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
        Real.logb Z (dyadicScale n) := by
  have hs : Tsec≤Csec*Z^(nominalLog I J E K X Z) := by
    rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)]
    exact hsec
  have he := retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC hs n hn
  exact ⟨dyadRows_log_nonneg Z hZ n hne,he,by linarith⟩

theorem canonical_active_log_le (η τ : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}) :
    0≤Real.logb Z (τ.modulus.absNorm:ℝ) ∧
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)≤
      Real.logb Z (τ.modulus.absNorm:ℝ) := by
  have hpos : 0<τ.modulus.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hd : Ideal.span {activeConductor I J}∣τ.modulus := by
    rw [hmod,←Ideal.span_singleton_mul_span_singleton]
    exact (dvd_mul_left (Ideal.span {activeConductor I J}) _).trans (dvd_mul_left _ _)
  have hN : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)
  refine ⟨Real.logb_nonneg hZ (by exact_mod_cast hpos),?_⟩
  exact Real.logb_le_logb_of_le hZ (active_norm_pos I J) hN

theorem retained_main_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi) (hsigma : 0≤ sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hne : (dyadRows n).Nonempty) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale n)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*c/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R) (mainGain D0 c sigma) (sigma/3) := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn hne).2.2
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale n)
  have he := actual_extracted_first_saving I J hI hJ Z hZ
    D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0 (mainGain D0 c sigma) (sigma/3) sigma (frequencyLoss Z Csec xi)
    (by norm_num) hq.1 (by norm_num) hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD (by simp only [mainGain,c,mul_zero,sub_zero,add_zero];exact le_rfl)
    (by positivity) (by positivity)
  simpa only [add_zero] using he

theorem pool_prime_log_range (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (Z sigma : ℝ) (hZ : 1<Z) (p : O)
    (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
    0≤Real.logb Z (normValue p) ∧ Real.logb Z (normValue p)≤ sigma/3 := by
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hb := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3)) (Finset.mem_sdiff.mp hd.2.1).1
  have hu : normValue p≤Z^(sigma/3) := by simpa only [normValue,mul_one] using hb.2
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one p hd.1.ne_zero),?_⟩
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos p hd.1.ne_zero) hu
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hh

theorem errorRemoval_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (k : ℕ) :
    Z^(errorRemoval p Z k)=(normValue p)^k := by
  unfold errorRemoval
  rw [mul_comm,Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)]

theorem errorMoving_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    Z^(2*errorMoving p Z (n+1))=normValue (p^(2*errorMovingExponent n)) := by
  have he := errorRemoval_power p hp Z hZ 2
  have hn2 : normValue (p^2)=(normValue p)^2 := by
    unfold normValue
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rcases hn with rfl|rfl|rfl
  · simpa only [errorMoving,errorMovingExponent,show ¬(0:ℕ)=5 by decide,
      show ¬(1:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he
  · norm_num [errorMoving,errorMovingExponent,normValue]
  · simpa only [errorMoving,errorMovingExponent,show ¬(6:ℕ)=5 by decide,
      show ¬(7:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he

theorem shortened_raw_exact (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (T : ℝ) (k : ℕ) :
    T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k=T/Z^(errorRemoval p Z k) := by
  rw [errorRemoval_power p hp Z hZ]
  rfl

theorem eventually_frequency_loss (Csec xi : ℝ) (hC : 1≤Csec) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧ 0≤frequencyLoss Z Csec xi ∧ frequencyLoss Z Csec xi<xi := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (2*Real.log (4*Csec)/xi)),eventually_gt_atTop (1:ℝ)] with Z hlog hZ
  have hh := (div_lt_iff₀ hxi).mp hlog
  have hr : Real.log (4*Csec)/Real.log Z<xi/2 := by
    apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
    nlinarith
  refine ⟨hZ,frequencyLoss_nonneg Z Csec xi hZ hC hxi.le,?_⟩
  unfold frequencyLoss Real.logb
  linarith

theorem retained_error_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi) (hsigma : 0≤ sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (j : ℤ) (hj : Retained (frequencyRadius Tsec Z xi) j) (hne : (dyadRows j).Nonempty)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale j)
    let u := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*(c+errorRemoval p Z k)/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 (errorRemoval p Z k) (Real.logb Z (τ.modulus.absNorm:ℝ))
        (errorMoving p Z k) (c+d-2*u-R) (errorGain D0 c sigma Z p k) 0 := by
  dsimp only
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale j)
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec j hj hne).2.2
  have hl := pool_prime_log_range M H Sbad hbad Z sigma hZ p hp
  have hw := error_lengths p Z sigma hsigma k hk hl.1 hl.2
  have hg := (errorGain_bounds D0 c sigma Z p k hsigma).2.2
  exact actual_extracted_first_saving I J hI hJ Z hZ D0 (errorRemoval p Z k)
    (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p Z k)
    (errorGain D0 c sigma Z p k) 0 sigma (frequencyLoss Z Csec xi)
    (hw.1.trans hw.2.1) hq.1 hw.1 hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD hg (by norm_num) hw.2.2

end SevenEighths.CenteredMomentFirstAmplificationChoice

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentHeckeColumnWindow CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def original (s : Input ι) (R seed : Ideal O) : OriginalData ι where
  S := s.pools
  R := R
  s := seed
  nu := s.ν
  slot := s.W
  lengths := s.P
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  B₁ := 1
  B₂ := 1

def volume (s : Input ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem volume_pos (s : Input ι) : 0<volume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem residual_ne (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (B : Ideal O) (hB : B≠0) : ∀I∈residualPool B hB S,I≠0 := by
  intro I hI
  exact right_ne_zero_of_mul (hS (B*I) ((mem_residualPool B hB S I).mp hI))

theorem residual_one (S : Finset (Ideal O)) (h : (1:Ideal O)≠0) :
    residualPool 1 h S=S := by
  ext I
  simp only [mem_residualPool,one_mul]

theorem residual_coverage (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B : Ideal O) (hB : B≠0) (X Y : ℝ) (h : PlainCoverage S W 1 X Y) :
    PlainCoverage (residualPool B hB S) W 1 (X/B.absNorm) (Y/B.absNorm) := by
  have he := plainCoverage_residualPool S W 1 B hB X Y h
  intro I hi
  apply he I
  simpa only [one_mul,map_mul,map_one,Nat.cast_mul,Nat.cast_one,mul_one,div_div_eq_mul_div,mul_comm] using hi

def child (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : Input (liveIndices B.val) where
  toData := {commonData s C R B with η:=τ,t:=t}
  plain₁ := residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁
  plain₂ := residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := fun i=>s.ν_bound i.val
  W_bound := fun i=>s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le i.val
  upper_ge := fun i=>s.upper_ge i.val

@[simp] theorem child_modulus (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).m=fixedBadMask*idealGenerator (R*C) := rfl

@[simp] theorem child_character (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).η=τ := rfl

@[simp] theorem child_height (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).t=t := rfl

theorem live_slot_one (B : Tuple ι) (i : liveIndices B) : B (Sum.inl i.val)=1 :=
  (Finset.mem_filter.mp i.property).2

theorem child_tuplePool (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 =
      Fintype.piFinset (child s C R B τ t).pools := by
  ext v
  simp only [liveBox,Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i =>
      have hi:=h (Sum.inl i)
      simpa only [remainingSets,child,commonData,Input.pools,Sum.elim_inl,live_slot_one B.val i,
        residual_one] using hi
    | inr j =>
      fin_cases j
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 0)
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 1)

theorem child_profile (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 = (original (child s C R B τ t) (R*C) seed).profile := by
  funext v
  simp only [maskedLiveProfile,OriginalData.profile,original,child,commonData,
    profileCoefficient,one_mul,idealRectangle_extract]
  rfl

theorem prime_slot_one (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) (i : ι) : B.val (Sum.inl i)=1 :=
  allocation_slot_one s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B i

theorem prime_slots_live (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : liveIndices B.val=Finset.univ :=
  all_slots_live s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem prime_plain_norm_product (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) :
    (B.val (Sum.inr 0)).absNorm*(B.val (Sum.inr 1)).absNorm=Q.absNorm^k := by
  rw [←map_mul,allocation_plain_product s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B,map_pow]

theorem child_products (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    (child s (Q^k) R B τ t).X₁*(child s (Q^k) R B τ t).X₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k ∧
    (child s (Q^k) R B τ t).Y₁*(child s (Q^k) R B τ t).Y₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k := by
  have hnorm : ((B.val (Sum.inr 0)).absNorm:ℝ)*(B.val (Sum.inr 1)).absNorm=(Q.absNorm:ℝ)^k := by
    exact_mod_cast prime_plain_norm_product s Q hQ k hslot B
  change (s.X₁/_)*(s.X₂/_)=_ ∧ (s.Y₁/_)*(s.Y₂/_)=_
  rw [div_mul_div_comm,div_mul_div_comm,hnorm,s.same_product]
  exact ⟨rfl,rfl⟩

theorem child_volume (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    volume (child s (Q^k) R B τ t)=volume s/(Q.absNorm:ℝ)^k := by
  change (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    (∏i:liveIndices B.val,s.P i.val)=_
  rw [div_mul_div_comm]
  exact remainingRaw_exact s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B s.P (s.X₁*s.X₂)

theorem child_slot_card (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : Fintype.card (liveIndices B.val)=Fintype.card ι :=
  live_slot_card s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem child_slot_scale_ge_one (s : Input ι) (hs : ∀i,1≤ s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀i,1≤(child s C R B τ t).P i := fun i=>hs i.val

theorem child_plain_annuli (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t a₁ a₂ b₁ b₂ : ℝ)
    (h₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (h₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) :
    Function.support (child s C R B τ t).W₁⊆Set.Icc a₁ b₁ ∧
    Function.support (child s C R B τ t).W₂⊆Set.Icc a₂ b₂ := ⟨h₁,h₂⟩

theorem child_columns (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      (original (child s C R B τ t) (R*C) seed).columns ∧
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      (original (child s C R B τ t) (R*C) seed).beta := by
  dsimp only [OriginalData.columns, OriginalData.beta, original]
  rw [child_tuplePool s C R B τ t,child_profile s C R seed B τ t]
  dsimp only [original]
  constructor
  · apply congrArg finiteColumns
    ext v
    simp only [Fintype.mem_piFinset]
  · apply congrArg (fun S => finiteColumnCoefficient S _)
    ext v
    simp only [Fintype.mem_piFinset]

theorem child_gauss_source (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy
      (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff τ t) W K=
    sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta
      (heightCoeff (child s C R B τ t).η (child s C R B τ t).t) W K := by
  obtain ⟨hcols,hcoeff⟩ := child_columns s C R seed B τ t
  rw [hcols,hcoeff]
  rfl

def normalizedGaussSource (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (original s R seed).columns (original s R seed).beta
    (heightCoeff s.η s.t) W K).re / volume s

def childNormalizedGaussSource (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  normalizedGaussSource (child s C R B τ t) (R*C) seed W K

theorem original_childEnergy_eq_inputs (s : Input ι) (R seed : Ideal O)
    (τ : RayCharacter→Character) (p : O) (hp : p≠0)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime (Ideal.span {p}) I)
    (n : ℕ) (t K : ℝ) :
    (original s R seed).childEnergy τ p n t (volume s) K=
      (16*(n+2:ℝ)*localErrorCost p n)*
        ∑χ:RayCharacter,∑B:actualAllocations s.pools ((Ideal.span {p})^(n+1)),
          childNormalizedGaussSource s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K := by
  have hQ : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  unfold OriginalData.childEnergy
  simp only [original,Finset.sum_div]
  apply congrArg (fun x : ℝ => (16*(n+2:ℝ)*localErrorCost p n)*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_volume s (Ideal.span {p}) hQ (n+1) hslot R B (τ χ) t,
    child_gauss_source s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K]

end SevenEighths.CenteredMomentAmplificationChildInput

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def geometry (N : ℕ) (b b₁ b₂ : ℝ) : ℝ := b^(2*N)*b₁*b₂

lemma geometry_ge_one (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) : 1≤geometry N b b₁ b₂ := by
  unfold geometry
  have hp : 1≤b^(2*N):=one_le_pow₀ hb
  have hp1 : 1≤b^(2*N)*b₁ := by nlinarith
  nlinarith

lemma norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma allocation_product (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2

lemma allocation_ne (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←allocation_product s C B]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

theorem common_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)=
      CenteredMomentAmplificationChildInput.volume s/rawReduction B.val s.P := by
  have hh:=raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  change _ = CenteredMomentAmplificationChildInput.volume s at hh
  rw [←hh]
  congr 1
  unfold CenteredMomentAmplificationChildInput.volume child commonData remainingRaw plainNorm
  dsimp only
  ring

lemma live_card_le (B : Tuple ι) : Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa only [Fintype.card_coe] using (Finset.card_le_univ (liveIndices B))

theorem common_volume_le (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)≤
      b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ) := by
  have hc:=norm_ge_one C (allocation_ne s C B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx=>⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn':(C.absNorm:ℝ)≤b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  rw [common_volume]
  apply (div_le_div_iff₀ hr (zero_lt_one.trans_le hc)).mpr
  nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]

theorem frozen_zero (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (hz : frozenCoefficient B.val C R s.ν s.W s.P=0) (f : O→ℂ) (z : O) :
    frozenCoefficient B.val C R s.ν s.W s.P*f z=0 := by rw [hz,zero_mul]

theorem radius_le (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 0≤b₁) (_h₂ : 0≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤ s.hi i) (hhib : ∀i,s.hi i≤b)
    (hs₁ : 0≤ s.b₁) (hs₂ : 0≤ s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧ CenteredMomentOriginalCommonHarmonic.sourceRadius s≤(b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s := by
  have hp:0≤∏i,s.hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hp':(∏i,s.hi i)≤b^N := by
    calc
      _ ≤ ∏i:ι,b := Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>hhib i)
      _ = b^Fintype.card ι := by simp
      _ ≤ b^N := pow_le_pow_right₀ hb hc
  have hpp:=mul_le_mul (mul_le_mul hp' hb₁ hs₁ (pow_nonneg (zero_le_one.trans hb) _)) hb₂ hs₂
    (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) h₁)
  change 0≤_ ∧ _≤_
  have he:CenteredMomentOriginalCommonHarmonic.sourceRadius s=((∏i,s.hi i)*s.b₁*s.b₂)*CenteredMomentAmplificationChildInput.volume s := by
    unfold CenteredMomentOriginalCommonHarmonic.sourceRadius CenteredMomentAmplificationChildInput.volume; ring
  rw [he]
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg hp hs₁) hs₂)
    (CenteredMomentAmplificationChildInput.volume_pos s).le,
    mul_le_mul_of_nonneg_right hpp (CenteredMomentAmplificationChildInput.volume_pos s).le⟩

theorem original_beta (s : Input ι) (R seed : Ideal O) :
    (original s R seed).beta=coefficient s R seed := rfl

theorem child_column_norm (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hne : (original (child s C R B τ t) (R*C) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤CenteredMomentOriginalCommonHarmonic.sourceRadius (child s C R B τ t) := by
  rw [original_beta] at hne
  have hn:=original_column_norm (child s C R B τ t) (R*C) seed I hz₁ hz₂ hne
  exact ⟨hn.1,original_column_mask _ _ _ I hne,hn.2⟩

def nominal (s : Input ι) (K : ℝ) : ℝ := CenteredMomentAmplificationChildInput.volume s^2/K

lemma nominal_pos (s : Input ι) (K : ℝ) (hK : 0<K) : 0<nominal s K :=
  div_pos (sq_pos_of_pos (CenteredMomentAmplificationChildInput.volume_pos s)) hK

lemma nominal_lower (s : Input ι) (K : ℝ) :
    (CenteredMomentAmplificationChildInput.volume s)^2/K≤nominal s K := le_rfl

lemma nominal_upper (s : Input ι) (K G H : ℝ) (hK : 0<K) (_hG : 0≤G) (_hH : 0≤H)
    (h : CenteredMomentAmplificationChildInput.volume s≤G*H) :
    nominal s K≤G^2*H^2/K := by
  unfold nominal
  exact div_le_div_of_nonneg_right (by nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]) hK.le

def Endpoints (b b₁ b₂ : ℝ) (s : Input ι) : Prop :=
  s.upper≤b ∧ (∀i,0≤ s.hi i) ∧ 0≤ s.b₁ ∧ s.b₁≤b₁ ∧ 0≤ s.b₂ ∧ s.b₂≤b₂

lemma endpoints_child (b b₁ b₂ : ℝ) (s : Input ι) (h : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Endpoints b b₁ b₂ (child s C R B τ t) :=
  ⟨h.1,fun i=>h.2.1 i.val,h.2.2⟩

lemma radius_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤
      (b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s :=
  radius_le N b b₁ b₂ hb (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc he.2.1
    (fun i=>(s.upper_ge i).trans he.1) he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 he.2.2.2.2.2

def twiceChild (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :=
  child (child s C R B τ t) (Q^k) (R*C) Bp υ v

theorem twiceChild_data (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    (twiceChild s C R B τ t Q k Bp υ v).η=υ ∧
    (twiceChild s C R B τ t Q k Bp υ v).t=v ∧
    (twiceChild s C R B τ t Q k Bp υ v).m=
      fixedBadMask*idealGenerator ((R*C)*(Q^k)) := ⟨rfl,rfl,rfl⟩

theorem twice_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    CenteredMomentAmplificationChildInput.volume (twiceChild s C R B τ t Q k Bp υ v)=
      CenteredMomentAmplificationChildInput.volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [twiceChild,child_volume _ Q hQ k hslot,common_volume,div_div]

theorem twice_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    let H:=CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤CenteredMomentOriginalCommonHarmonic.sourceRadius d ∧
    CenteredMomentAmplificationChildInput.volume d≤geometry N b b₁ b₂*H ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC:=norm_ge_one C (allocation_ne s C B)
  have hNp:0<(Q.absNorm:ℝ)^k:=pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH:0<CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_pos (CenteredMomentAmplificationChildInput.volume_pos s)
      (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv:CenteredMomentAmplificationChildInput.volume (twiceChild s C R B τ t Q k Bp υ v)≤
      b^N*(CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [twiceChild,child_volume _ Q hQ k hslot]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne) hNp.le).trans_eq (by ring)
  have hc1:= (live_card_le B.val).trans hc
  have hc2:= (live_card_le Bp.val).trans hc1
  have hep:=endpoints_child b b₁ b₂ _ (endpoints_child b b₁ b₂ s he C R B τ t) (Q^k) (R*C) Bp υ v
  have hr:=radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hbf:0≤b^N*b₁*b₂:=by positivity
  have hpow: b^N≤geometry N b b₁ b₂ := by
    have hp:1≤b^N:=one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh:1≤b₁*b₂:=by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv hbf).trans_eq (by
    unfold geometry; rw [show 2*N=N+N by omega,pow_add];ring))

theorem twice_column (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤geometry N b b₁ b₂*
      (CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hi:=child_column_norm (child s C R B τ t) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨hi.1,hi.2.1,hi.2.2.trans hcap.2.2.2⟩

theorem twice_nominal (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v K : ℝ) (hK : 0<K) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    0<nominal d K ∧ CenteredMomentAmplificationChildInput.volume d^2/K=nominal d K ∧
    nominal d K≤(geometry N b b₁ b₂)^2*
      (CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K := by
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨nominal_pos _ K hK,rfl,nominal_upper _ K _ _ hK
    (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂)) hcap.1.le hcap.2.2.1⟩

theorem puncture_norm (R C Q : Ideal O) (k : ℕ) :
    (((R*C)*(Q^k)).absNorm:ℝ)=(R.absNorm:ℝ)*(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
  simp only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]

theorem live_puncture_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤geometry N b b₁ b₂*CenteredMomentAmplificationChildInput.volume s ∧
    (((R*C)*(Q^k)).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b b₁ b₂*CenteredMomentAmplificationChildInput.volume s := by
  have hi:=twice_column N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI
  have hh:1≤geometry N b b₁ b₂*(CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)):=
    (norm_ge_one I hi.1).trans hi.2.2
  have hd:0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k:=mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  rw [←mul_div_assoc] at hh
  have hn:=(le_div_iff₀ hd).mp hh
  simp only [one_mul] at hn
  refine ⟨hn,?_⟩
  rw [puncture_norm]
  nlinarith [mul_le_mul_of_nonneg_left hn (show (0:ℝ)≤R.absNorm by positivity)]

theorem eventual_geometry (G ε : ℝ) (hG : 1≤G) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ G≤Z^ε ∧ G^2≤Z^ε := by
  have hh:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (G^2)
  filter_upwards [eventually_gt_atTop (1:ℝ),hh] with Z hZ hpow
  exact ⟨hZ,(by nlinarith : G≤G^2).trans hpow,hpow⟩

theorem polynomial_caps (G V X H K Z A D ε ξ : ℝ)
    (hG : 1≤G) (hZ : 1<Z) (hGp : G^2≤Z^ε)
    (hV : 0<V) (hX : 0<X) (_hH : 0≤H) (hK : 0<K)
    (hXV : X≤G*V) (hHV : H≤G*V) (hVp : V≤Z^A) (hKp : K⁻¹≤Z^D) :
    X≤Z^(A+ε) ∧ H≤Z^(A+ε) ∧ X^2/K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (X^2/K) Z ξ ∧
    frequencyRadius (X^2/K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  have hz:=hZ.trans' zero_lt_one
  have hgp:G≤Z^ε := (by nlinarith : G≤G^2).trans hGp
  have hvpow:0<Z^A:=Real.rpow_pos_of_pos hz A
  have hrpow:0<Z^ε:=Real.rpow_pos_of_pos hz ε
  have hcap:G*V≤Z^(A+ε) := by
    rw [Real.rpow_add hz]
    nlinarith [mul_le_mul hgp hVp hV.le hrpow.le]
  have hsq:X^2≤G^2*(Z^A)^2 := by nlinarith [mul_le_mul_of_nonneg_left hVp (by linarith : 0≤G)]
  have ht:X^2/K≤Z^(2*A+D+ε) := by
    have hm:=mul_le_mul hsq hKp (inv_nonneg.mpr hK.le)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hg:=mul_le_mul_of_nonneg_right hGp (mul_nonneg (sq_nonneg (Z^A)) (Real.rpow_nonneg hz.le D))
    calc
      _ ≤ (G^2*(Z^A)^2)*Z^D := by simpa only [div_eq_mul_inv] using hm
      _ ≤ (Z^ε*(Z^A)^2)*Z^D := by nlinarith [hg]
      _ = _ := by rw [pow_two,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hXV.trans hcap,hHV.trans hcap,ht,?_,?_⟩
  · exact mul_pos (div_pos (sq_pos_of_pos hX) hK) (Real.rpow_pos_of_pos hz _)
  · unfold frequencyRadius
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hz.le _)

theorem eventual_twice_caps (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v K A D ξ:ℝ),
    0<K → CenteredMomentAmplificationChildInput.volume s≤Z^A → K⁻¹≤Z^D →
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    CenteredMomentAmplificationChildInput.volume d≤Z^(A+ε) ∧
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius d ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius d≤Z^(A+ε) ∧
    0<nominal d K ∧ nominal d K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (nominal d K) Z ξ ∧
    frequencyRadius (nominal d K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R B τ t hne Q hQ k hslot Bp υ v K A D ξ hK hVp hKp
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  have hd:1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc:=norm_ge_one C (allocation_ne s C B)
    have hq:1≤(Q.absNorm:ℝ)^k:=one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hH:CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤
      CenteredMomentAmplificationChildInput.volume s :=
    div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le hd
  have hm:=mul_le_mul_of_nonneg_left hH (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂))
  have hh:=polynomial_caps (geometry N b b₁ b₂) _ _ _ K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hZ.1 hZ.2.2
    (CenteredMomentAmplificationChildInput.volume_pos s)
    (CenteredMomentAmplificationChildInput.volume_pos _) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKp
  exact ⟨hh.1,hcap.2.1,hh.2.1,nominal_pos _ K hK,hh.2.2⟩

theorem plain_zero (s : Input ι) (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) : s.W₁ 0=0 ∧ s.W₂ 0=0 := by
  constructor
  · by_contra hn; exact (not_le_of_gt ha₁) (hs₁ hn).1
  · by_contra hn; exact (not_le_of_gt ha₂) (hs₂ hn).1

theorem twice_slots_ge_one (s : Input ι) (hs : ∀i,1≤ s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ) (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) : ∀i,1≤(twiceChild s C R B τ t Q k Bp υ v).P i :=
  fun i=>hs i.val.val

theorem child_localized (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0<K) :
    let d:=child s C R B τ t;
    let S:=(original d (R*C) seed).columns;
    let β:=(original d (R*C) seed).beta;
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff τ t) W K/
      (CenteredMomentAmplificationChildInput.volume d:ℂ)=
      (((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier W 0)*
          CenteredMomentSourceSecondZeroEnergy.sourceSecondZero S β τ t+
        CenteredMomentSecondLocalization.secondRetainedEnergy τ t S β W K (nominal d K) Z ξ+
        CenteredMomentSupportedTailAggregate.secondDiscardedEnergy τ t S β W K (nominal d K) Z ξ)/
      (CenteredMomentAmplificationChildInput.volume d:ℂ) := by
  dsimp only
  rw [CenteredMomentSecondLocalization.sourceGaussEnergy_localized τ t _ _ W K _ Z ξ hK]

theorem child_source_zero (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsmall : CenteredMomentOriginalCommonHarmonic.sourceRadius (child s C R B τ t)<1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta (heightCoeff τ t) W K=0 := by
  have hz (I:Ideal O):(original (child s C R B τ t) (R*C) seed).beta I=0 := by
    by_contra hn
    have hh:=child_column_norm s C R seed B τ t hz₁ hz₂ I hn
    exact (not_le_of_gt hsmall) ((norm_ge_one I hh.1).trans hh.2.2)
  simp [CenteredMomentOriginalChildEnergy.sourceGaussEnergy,CenteredMomentGaussEnergy.gaussEnergy,
    CenteredMomentGaussEnergy.gaussPolynomial,hz]

theorem eventual_live_puncture (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v A P:ℝ),
    s.W₁ 0=0 → s.W₂ 0=0 → CenteredMomentAmplificationChildInput.volume s≤Z^A →
    (R.absNorm:ℝ)≤Z^P →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v A P hz₁ hz₂ hVp hRp ⟨I,hI⟩
  have hn:=(live_puncture_bound N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI).2
  have hg:=geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hm:=mul_le_mul (mul_le_mul hRp hZ.2.1 (zero_le_one.trans hg)
    (Real.rpow_nonneg (by linarith : 0≤Z) P)) hVp
    (CenteredMomentAmplificationChildInput.volume_pos s).le
    (mul_nonneg (Real.rpow_nonneg (by linarith : 0≤Z) P) (Real.rpow_nonneg (by linarith : 0≤Z) ε))
  apply hn.trans (hm.trans_eq ?_)
  rw [←Real.rpow_add (by linarith : 0<Z),←Real.rpow_add (by linarith : 0<Z)]
  congr 1;ring

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalFamily -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentAmplificationRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentRadicalFamily CenteredMomentFirstFamily
open CenteredMomentAmplificationFamily CenteredMomentAmplificationFamilyEnergy
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSecondChildProfile
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentAmplificationEligibility
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def radicalBound (η:Character)(m p:O)(k:ℕ):ℕ :=
  η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (if k=0 then 1 else (Ideal.span {p}).absNorm)

theorem radicalBound_error_power (η:Character)(m p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    (radicalBound η m p (errorMovingExponent n):ℝ)=
      ((η.modulus.absNorm:ℝ)*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm)*
        Z^(errorMoving p Z (n+1)):=by
  have hpow:=Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)
  rcases hn with rfl|rfl|rfl <;>
    norm_num only [radicalBound,errorMovingExponent,errorMoving,Nat.cast_mul,
      Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals simp only [ite_false,ite_true,Nat.one_ne_zero,eq_self,
    Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals rw [hpow]; rfl

theorem exists_radical_row (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤ radicalBound η m p k ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (p^(2*k)) n:=by
  by_cases hk:k=0
  · obtain ⟨τ,hN,hτ⟩:=exists_supported_row_presentation η m 1 hm
      CenteredMomentAddedZero.supported_one_element hmLam hm2
    refine ⟨τ,?_,?_⟩
    · simp [radicalBound,hk,hN]
    · simpa [hk] using hτ
  · obtain ⟨τ,hM,hN,hτ⟩:=exists_radical_row_presentation η m hm hmLam hm2
      (fun _:Fin 1=>p) (fun _=>hs) (fun _=>2*k)
      (fun _=>Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk))
    refine ⟨τ,?_,?_⟩
    · simpa [radicalBound,hk] using hN
    · simpa using hτ

theorem exists_radical_height (η:Character)(χ:RayCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤ radicalBound (childCharacter η χ) m p k ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom (p^(2*k)) I*
          rayCharacter χ (primaryGenerator I):=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_row (childCharacter η χ) m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he:=idealCoeff_eq_row (childCharacter η χ) τ m 1 (p^(2*k)) hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom (p^(2*k)) I*rayCharacter χ (primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem exists_radical_family (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hpp:goodLambda^2∣p-1)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p k) ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑χ:RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I:=by
  choose τ hN hτ using fun χ:RayCharacter=>exists_radical_height η χ m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn:=supported_primaryGenerator_ne_zero I hI
  have hgen:Supported (Ideal.span {primaryGenerator I}):=by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem exists_actual_error_family (η:Character)(m p:O)
    (hm:m≠0)(hp:Prime p)(hs:Supported (Ideal.span {p}))
    (hpp:goodLambda^2∣p-1)(hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀(S:Finset (Ideal O))(C:Ideal O),C≠0→∀(β:Ideal O→ℂ)(t:ℝ)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I=>β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I=>residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑χ:RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I=>β (C*I)) (heightCoeff (τ χ) t) W K).re:=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_family η m p hm hs hpp hmLam hm2 (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact amplification_family_energy η m p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) C hC β t W K hK hW

theorem original_errors_to_children {ι : Type*} [Fintype ι] (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤_
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤ radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤ sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

end SevenEighths.CenteredMomentAmplificationRadicalFamily

end

end OAI

end

