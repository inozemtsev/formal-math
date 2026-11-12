module

public import Mathlib.RingTheory.Radical.Basic
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part020
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part009
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Complex.PhragmenLindelof

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part021

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => HeckeFamily.O

structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0<a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if h : 1≤U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : 1≤U*V.b) :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

lemma polynomial_zero (χ : Character) (X : ℝ) :
    HeckeDyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [HeckeDyadic.polynomial,HeckeDyadic.summand]

theorem retained_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤U₁*V₁.b
  · by_cases h₂ : 1≤U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2) : ℝ :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X : ℝ) (hX : 0<X) (j : Fin 2) : 0< rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

lemma raw_same_product (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X₁ X₂ Y₁ Y₂ : ℝ) (h : X₁*X₂=Y₁*Y₂) :
    rawScale D a X₁ 0*rawScale D a X₂ 1=rawScale D a Y₁ 0*rawScale D a Y₂ 1 := by
  simp only [rawScale,div_mul_div_comm,h]

theorem allocated_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=>pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=>P i)
    (fun i=>hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=>naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

omit [Fintype α] [DecidableEq α] in

theorem slot_controls (ν : α→Ideal O→ℂ) (W : α→ℝ→ℂ) (P b M : α→ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖≤1)
    (hW : ∀i x,‖W i x‖≤M i) (hs : ∀i,Function.support (W i)⊆Set.Iic (b i)) :
    (∀i I,‖ν i I*W i ((I.absNorm:ℝ)/P i)‖≤M i) ∧
    (∀i I,ν i I*W i ((I.absNorm:ℝ)/P i)≠0 → (I.absNorm:ℝ)≤b i*P i) := by
  constructor
  · intro i I
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hν i I) (norm_nonneg _)).trans (by simpa using hW i _)
  · intro i I hn
    exact (div_le_iff₀ (hP i)).mp (hs i (right_ne_zero_of_mul hn))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀F : Finset α,SharedBound F b M C ε := by
  have he (F : Finset α) : ∃C : ℝ,0<C ∧ SharedBound F b M C ε :=
    actual_shared_energy F b M (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑F : Finset α,C F
  have hsum : 0≤∑F : Finset α,C F:=Finset.sum_nonneg (fun F _=>(hC F).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro F ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C F≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ F)
    dsimp [B]
    linarith
  exact (hb F R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

lemma primeSupport_product_radical (R : Ideal O) (hR : R≠0) :
    (∏I∈CompletedGauss.primeSupport R,I)=R.radical := by
  ext x
  change x∈(∏I∈CompletedGauss.primeSupport R,I) ↔ ∃n : ℕ,x^n∈R
  simp_rw [←Ideal.span_singleton_le_iff_mem,←Ideal.dvd_iff_le,←Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hR).symm

def child (χ : Character) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

def AllocatedBound (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (α⊕Fin 2))),
  ∀{ι : Type*} [Fintype ι],∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)
    (R : Ideal O),R≠0 → ∀(V₁ V₂ : ι→Plain)
    (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)(t X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i)(hX₂ : ∀i,0<X₂ i),
    (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
    (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
    (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
    ∀E : ℝ,0≤E →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (η i) (z i) (hz i)).character D a (V₁ i) (V₂ i)
         (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i) D₁ D₂ J‖^2)≤E) →
    (∑i,‖allocatedPositiveRow (η i)
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (z i) (t i) (pool i) (β i) (P i) D a (V₁ i).W (V₂ i).W (X₁ i) (X₂ i)‖^2)≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*E

theorem allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ AllocatedBound b M C ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hh:=hbound (liveIndices D a) (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>(V₁ i).profile _ (rawScale_pos D a (X₁ i) (hX₁ i) 0) (t i))
    (fun i=>(V₂ i).profile _ (rawScale_pos D a (X₂ i) (hX₂ i) 1) (t i))
    (fun i=>clippedScale (rawScale D a (X₁ i) 0)) (fun i=>clippedScale (rawScale D a (X₂ i) 1))
    pool (fun i j=>heightCoefficient (β i j) (t i)) P
    (fun _=>by unfold clippedScale;positivity) (fun _=>by unfold clippedScale;positivity)
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι):=allocated_normalized (η i) (z i) (hz i) R hR D a (V₁ i) (V₂ i)
    (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  have hphase (U t : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
    positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
  simp_rw [he,norm_mul,hphase,one_mul]
  rw [←primeSupport_product_radical R hR]
  simpa only [SharedBound,excluded,norm_mul] using hh

theorem uniform_allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
      AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε := by
  have he (T : Finset α) : ∃C : ℝ,0<C ∧ AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε :=
    allocated_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro T D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C T≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ T)
    dsimp [B]
    linarith
  exact (hb T D a η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

theorem natural_nonprincipal_width (η : Character) (z : O) (hz : z≠0)
    (Q R : Ideal O) (hR : R≠0)
    (hex : ¬CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m) (hrow : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (naturalRow η z hz).character.residue≠1 ∧
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) :=
  ⟨(naturalRow η z hz).nonprincipal hz Q R hR hex,
    (naturalRow η z hz).modulus_power_bound Z m q Cz hZ hCz hη hrow⟩

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal O)
  ν : α→Ideal O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0<P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M : α→ℝ} (s : Slots α b M) (i : α) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

omit [Fintype α] [DecidableEq α] in
lemma Slots.controls {b M : α→ℝ} (s : Slots α b M) :
    (∀i I,‖s.coefficient i I‖≤M i) ∧
    (∀i I,s.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*s.P i) :=
  slot_controls s.ν s.W s.P b M s.P_pos s.ν_bound s.W_bound s.support

structure Row (α : Type*) (b M : α→ℝ) where
  η : Character
  z : O
  z_ne : z≠0
  plain₁ : Plain
  plain₂ : Plain
  slots : Slots α b M
  t : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : X₁*X₂=Y₁*Y₂

lemma Row.extracted_same_product {b M : α→ℝ} (s : Row α b M)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    rawScale D a s.X₁ 0*rawScale D a s.X₂ 1=rawScale D a s.Y₁ 0*rawScale D a s.Y₂ 1 :=
  raw_same_product D a _ _ _ _ s.same_product

theorem uniform_paired_nuW_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
    ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (T⊕Fin 2))),
    ∀{ι : Type*} [Fintype ι],∀s : ι→Row T (fun i=>b i) (fun i=>M i),
    ∀(R : Ideal O),R≠0 → ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).X₁ (s i).X₂ (s i).X₁_pos (s i).X₂_pos D₁ D₂ J‖^2)≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).Y₁ (s i).Y₂ (s i).Y₁_pos (s i).Y₂_pos D₁ D₂ J‖^2)≤E₂) →
    (∑i,(‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).X₁ (s i).X₂‖^2+
      ‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).Y₁ (s i).Y₂‖^2))≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C,hC,hbound⟩:=uniform_allocated_energy b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro T D a ι _ s R hR E₁ E₂ hE₁ hE₂ hleft hright
  have hl:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).X₁) (fun i=>(s i).X₂) (fun i=>(s i).X₁_pos) (fun i=>(s i).X₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₁ hE₁ hleft
  have hr:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).Y₁) (fun i=>(s i).Y₂) (fun i=>(s i).Y₁_pos) (fun i=>(s i).Y₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₂ hE₂ hright
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hl hr

def inputSlots (s : CenteredMomentCommonRadialData.Input α) : Slots α s.hi s.M where
  pool:=s.slots
  ν:=s.ν
  W:=s.W
  P:=s.P
  prime:=s.prime
  P_pos:=s.P_pos
  ν_bound:=s.ν_bound
  W_bound:=s.W_bound
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma inputSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) :
    (inputSlots s).coefficient=s.toData.coefficient := rfl

def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>s.hi i) (fun i=>s.M i) where
  pool:=fun i=>s.slots i
  ν:=fun i=>s.ν i
  W:=fun i=>s.W i
  P:=fun i=>s.P i
  prime:=fun i=>s.prime i
  P_pos:=fun i=>s.P_pos i
  ν_bound:=fun i=>s.ν_bound i
  W_bound:=fun i=>s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma commonSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    (commonSlots s C B).coefficient=(CenteredMomentCommonRadialData.commonData s C R B).coefficient := rfl

end SevenEighths.CenteredMomentAllocatedNaturalSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionTails -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma ideal_norm_rpow_summable (B : ℕ) (hB : 2≤B) :
    Summable (fun I : NI=>(I.val.absNorm:ℝ)^(-(B:ℝ))) := by
  have hb : (1:ℝ)<B := by exact_mod_cast (by omega : 1<B)
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (B:ℂ)
    (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NI=>I.val))
  apply hs.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property]
  change ‖((I.val.absNorm:ℝ):ℂ)^(-(B:ℂ))‖=_
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hi]
  simp

lemma plain_term_rapid_bound (η : Character) (F : ℝ→ℂ) (B : ℕ) (D Y : ℝ)
    (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) (I : NI) :
    ‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤
      (D*Y^B)*(I.val.absNorm:ℝ)^(-(B:ℝ)) := by
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  have hx : 0<(I.val.absNorm:ℝ)/Y := div_pos hi hY
  have hb : ‖F ((I.val.absNorm:ℝ)/Y)‖≤D/((I.val.absNorm:ℝ)/Y)^B :=
    (le_div_iff₀ (pow_pos hx B)).mpr (by simpa only [mul_comm] using hF _ hx)
  calc
    _≤‖F ((I.val.absNorm:ℝ)/Y)‖:=by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)
    _≤D/((I.val.absNorm:ℝ)/Y)^B:=hb
    _=_:=by
      rw [Real.rpow_neg hi.le,Real.rpow_natCast,div_pow]
      field_simp

theorem plain_rapid_summable (η : Character) (F : ℝ→ℂ) (B : ℕ) (hB : 2≤B)
    (D Y : ℝ) (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) :
    Summable (fun I : NI=>idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (plain_term_rapid_bound η F B D Y hY hF)
    ((ideal_norm_rpow_summable B hB).mul_left (D*Y^B))

theorem plain_rapid_bound (B : ℕ) (hB : 2≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(F : ℝ→ℂ)(D Y : ℝ),0≤D → 0<Y →
      (∀x : ℝ,0<x → x^B*‖F x‖≤D) →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*D*(Y^B/Real.sqrt Y) := by
  let C := 1+∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ))
  have hs := ideal_norm_rpow_summable B hB
  have hnon : 0≤∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ)) :=
    tsum_nonneg (fun I=>Real.rpow_nonneg (HeckeDyadic.norm_pos I).le _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro η F D Y hD hY hF
  have ht := plain_rapid_summable η F B hB D Y hY hF
  have hh := ht.norm.tsum_le_tsum (plain_term_rapid_bound η F B D Y hY hF)
    (hs.mul_left (D*Y^B))
  rw [tsum_mul_left] at hh
  have hb : ‖∑' I : NI,idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤D*Y^B*C := by
    exact (norm_tsum_le_tsum_norm ht.norm).trans (hh.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C];linarith) (by positivity)))
  rw [polynomial_plain η F Y hY,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _≤(Real.sqrt Y)⁻¹*(D*Y^B*C):=mul_le_mul_of_nonneg_left hb (by positivity)
    _=C*D*(Y^B/Real.sqrt Y):=by ring

theorem actual_reflected_absolute_bound (a b : ℝ) (ha : 0<a) (B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y : ℝ),0<Y →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y) := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha B 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y hY
  have hf : ∀x : ℝ,0<x → x^B*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) B)
      (norm_nonneg _)).trans hh
  exact (hKb η _ (D*(1+‖t‖)^n) Y (by positivity) hY hf).trans_eq (by ring)

lemma discarded_rapid_control (F : ℝ→ℂ) (A B : ℕ) (D R : ℝ)
    (hD : 0≤D) (hR : 0<R) (hF : ∀x : ℝ,0<x → x^(B+A)*‖F x‖≤D) :
    ∀x : ℝ,0<x → x^B*‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤D/R^A := by
  intro x hx
  by_cases hz : CenteredMomentSectorLocalization.discardedWeight R x=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
    positivity
  have hRx := (CenteredMomentSectorLocalization.discardedWeight_support R x hz).le
  have hw := CenteredMomentSectorLocalization.discardedWeight_bounds R x
  have hnorm : ‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤‖F x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  apply (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hx.le B)).trans
  apply (le_div_iff₀ (pow_pos hR A)).mpr
  calc
    _≤(x^B*‖F x‖)*x^A :=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRx A) (by positivity)
    _=x^(B+A)*‖F x‖ :=by rw [pow_add];ring
    _≤D :=hF x hx

theorem actual_reflected_discarded_bound (a b : ℝ) (ha : 0<a) (A B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y R : ℝ),0<Y → 0<R →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y R hY hR
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*(1+‖t‖)^n) R (by positivity) hR hf
  exact (hKb η _ ((D*(1+‖t‖)^n)/R^A) Y (by positivity) hY hm).trans_eq (by ring)

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionLength -/

section

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma nonempty_clipped_scale (S B q : ℝ) (hS : 0<S) (hq : 1≤q)
    (hsupport : q/S≤B) : max 1 S≤ max 1 B*S := by
  have hh : 1≤B*S := hq.trans ((div_le_iff₀ hS).mp hsupport)
  apply max_le
  · exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hS.le)
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 B) hS.le

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤ s)
    (hcap : Q*R≤C*Z^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z^(xi/2)) :
    s*(Q*d/(Z^n*h))≤C*Z^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : 0<Z^n := Real.rpow_pos_of_pos hz _
  have hp : Q*d≤C*Z^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z^n*h)≤C*Z^M/Z^n := by
    calc
      _≤Q*d/Z^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z^M/Z^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z^(xi/2)*(C*Z^M/Z^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

theorem eventually_reflected_length (C B box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M n Q R d h s q : ℝ),
      0<Q → 0<d → 0<s → Q*R≤C*Z^M → d≤R → 1≤h →
      s≤Z^(xi/2) → 1≤q → q/(s*(Q*d/(Z^n*h)))≤B →
      let declared := Real.logb Z (box*max 1 (s*(Q*d/(Z^n*h))))
      0≤declared ∧ declared≤M-n+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (C*max 1 B*box))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hconst
  refine ⟨hZ,?_⟩
  intro M n Q R d h s q hQ hd hs hcap hdR hh hsm hq hsupport
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp : 0<s*(Q*d/(Z^n*h)) := by positivity
  have hraw := reflected_scale_bound Z M n xi C Q R d h s hZ hC.le hQ.le hd.le hs.le hcap hdR hh hsm
  have hclip := nonempty_clipped_scale _ B q hp hq hsupport
  have hT : 1≤box*max 1 (s*(Q*d/(Z^n*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤box*max 1 (s*(Q*d/(Z^n*h))) :=
        mul_le_mul hbox (le_max_left _ _) (by norm_num) (by linarith)
  constructor
  · exact Real.logb_nonneg hZ hT
  · apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hT)).mpr
    calc
      _≤box*(max 1 B*(C*Z^(M-n+xi/2))) :=
        mul_le_mul_of_nonneg_left (hclip.trans
          (mul_le_mul_of_nonneg_left hraw (le_max_of_le_left (by norm_num)))) (by linarith)
      _=(C*max 1 B*box)*Z^(M-n+xi/2) :=by ring
      _≤Z^(xi/2)*Z^(M-n+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
      _=Z^(M-n+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonMaskChildCapacity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.CenteredMomentCommonMaskChildCapacity
open HeckeFamily HeckeDyadic CenteredMomentComparisonReflection
local notation "O" => HeckeFamily.O

lemma polynomial_nonzero_support (χ : Character) (W : ℝ→ℂ) (X sigma t b : ℝ)
    (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) : 1≤b*X := by
  by_contra hh
  have hb : b*X<1:=lt_of_not_ge hh
  apply hn
  unfold polynomial
  have hzero : ∀I : NonzeroIdeal,summand χ false W X sigma t I=0 := by
    intro I
    have hW : W (norm I/X)=0 := by
      by_contra hW
      have hu:=hs hW
      have hle : norm I≤b*X:=(div_le_iff₀ hX).mp hu
      have hi : 1≤norm I := by
        change 1≤(I.val.absNorm:ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      linarith
    simp only [summand,hW,mul_zero,zero_mul]
  simp only [hzero,tsum_zero,mul_zero]

lemma actual_clipped_log (χ : Character) (W : ℝ→ℂ) (Z X sigma t b : ℝ)
    (hZ : 1<Z) (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) :
    0≤Real.logb Z (max 1 X) ∧
      Real.logb Z (max 1 X)≤Real.logb Z X+Real.logb Z (max 1 b) := by
  have hB : 0< max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  have hclip : max 1 X≤ max 1 b*X := by
    apply max_le
    · exact (polynomial_nonzero_support χ W X sigma t b hX hs hn).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 b) hX.le
  refine ⟨Real.logb_nonneg hZ (le_max_left _ _),?_⟩
  have hh:=Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 X)) hclip
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  linarith

lemma deleted_same_product (X₁ X₂ Y₁ Y₂ T d₁ d₂ : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/d₁)*(X₂/d₂)=T/(d₁*d₂) ∧
      (Y₁/d₁)*(Y₂/d₂)=T/(d₁*d₂) := by
  constructor <;> rw [div_mul_div_comm]
  · rw [hX]
  · rw [hY]

theorem actual_deleted_capacity {α : Type*} [DecidableEq α]
    (F J : Finset α) (hJ : J⊆F) (P : α→ℝ) (hP : ∀i∈F,1≤P i)
    (χ : Character) (W₁ W₂ : ℝ→ℂ) (Z X₁ X₂ t₁ t₂ b₁ b₂ kappa M : ℝ)
    (D₁ D₂ : Ideal O) (hD₁ : D₁≠0) (hD₂ : D₂≠0)
    (hZ : 1<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hk : 0≤kappa)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hn : polynomial χ false W₁ (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
      polynomial χ false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂≠0)
    (hcap : Real.logb Z (X₁*X₂)+6*kappa*(∑i∈F,Real.logb Z (P i))≤M) :
    let n₁:=Real.logb Z (max 1 (X₁/(D₁.absNorm:ℝ)))
    let n₂:=Real.logb Z (max 1 (X₂/(D₂.absNorm:ℝ)))
    0≤n₁ ∧ 0≤n₂ ∧ n₁+n₂+6*kappa*(∑i∈J,Real.logb Z (P i))≤
      M+Real.logb Z (max 1 b₁*max 1 b₂) := by
  have hd₁ : 1≤(D₁.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₁)
  have hd₂ : 1≤(D₂.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₂)
  have hd₁p : 0<(D₁.absNorm:ℝ):=zero_lt_one.trans_le hd₁
  have hd₂p : 0<(D₂.absNorm:ℝ):=zero_lt_one.trans_le hd₂
  have hc₁:=actual_clipped_log χ W₁ Z _ 0 t₁ b₁ hZ (div_pos hX₁ hd₁p) hs₁ (mul_ne_zero_iff.mp hn).1
  have hc₂:=actual_clipped_log χ W₂ Z _ 0 t₂ b₂ hZ (div_pos hX₂ hd₂p) hs₂ (mul_ne_zero_iff.mp hn).2
  have hslots : (∑i∈J,Real.logb Z (P i))≤∑i∈F,Real.logb Z (P i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hJ (fun i hi _=>Real.logb_nonneg hZ (hP i hi))
  have hslots' := mul_le_mul_of_nonneg_left hslots (by positivity : 0≤6*kappa)
  have hlog₁:=Real.logb_nonneg hZ hd₁
  have hlog₂:=Real.logb_nonneg hZ hd₂
  rw [Real.logb_div hX₁.ne' hd₁p.ne'] at hc₁
  rw [Real.logb_div hX₂.ne' hd₂p.ne'] at hc₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne'] at hcap
  have hb₁ : 0< max 1 b₁:=zero_lt_one.trans_le (le_max_left _ _)
  have hb₂ : 0< max 1 b₂:=zero_lt_one.trans_le (le_max_left _ _)
  dsimp only
  refine ⟨hc₁.1,hc₂.1,?_⟩
  rw [Real.logb_mul hb₁.ne' hb₂.ne']
  linarith [hc₁.2,hc₂.2]

lemma eventually_fixed_clipping_cost (b₁ b₂ delta : ℝ) (hdelta : 0<delta) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤delta := by
  have hc:=(tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop (max 1 b₁*max 1 b₂))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hC
  refine ⟨hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hC
end SevenEighths.CenteredMomentCommonMaskChildCapacity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionNegligible -/

section

namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson

lemma normalized_power_eq (Y : ℝ) (hY : 0<Y) (B : ℕ) :
    Y^B/Real.sqrt Y=Y^((B:ℝ)-1/2) := by
  rw [Real.rpow_sub hY,Real.rpow_natCast,Real.sqrt_eq_rpow]

theorem actual_reflected_small_negligible (a b xi saving : ℝ) (ha : 0<a) (hxi : 0<xi) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Z^(-xi) →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨B,hB⟩ := exists_nat_gt (max (2:ℝ) (saving/xi+1/2))
  have hB2 : 2≤B := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hB))
  have hBp : 0≤(B:ℝ)-1/2 := by have := (le_max_left _ _).trans_lt hB;linarith
  have hsav : saving≤xi*((B:ℝ)-1/2) := by
    have hh := (le_max_right _ _).trans_lt hB
    have hh' : saving/xi≤(B:ℝ)-1/2 := by linarith
    exact (div_le_iff₀ hxi).mp hh' |>.trans_eq (mul_comm _ _)
  obtain ⟨n,hn⟩ := actual_reflected_absolute_bound a b ha B hB2
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply (hbound η t Y hY).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [normalized_power_eq Y hY B]
  calc
    _≤(Z^(-xi))^((B:ℝ)-1/2) := Real.rpow_le_rpow hY.le hYZ hBp
    _=Z^((-xi)*((B:ℝ)-1/2)) := (Real.rpow_mul hz.le _ _).symm
    _≤Z^(-saving) := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem actual_reflected_upper_negligible (a b xi saving L Cscale : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hCscale : 0<Cscale) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨n,hn⟩ := actual_reflected_discarded_bound a b ha A 2 (by omega)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hCscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*(1+‖t‖)^n*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A := hbound η t Y _ hY hR
    _≤C*(1+‖t‖)^n*(Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*(1+‖t‖)^n*Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength -/

section

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0<Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M a Q R d h : ℝ),
      0<Q → 0<d → Q*R≤C*Z^M → d≤R → 1≤h →
      ∀n : ℤ,∀hY : 0<Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0<xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0<Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

lemma one_reflection_total_width (M A z b xi reflected : ℝ)
    (hb : b≤M/4) (hreflection : reflected≤M-(A-z-b)+xi) :
    reflected+b+z≤3*M/2-A+2*z+xi := by linarith

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (hM : 0≤M) (hz : 0≤z) (hk : 3/4≤kappa)
    (hA : 5*M/6≤A) (hcap : A+(6*kappa-1)*z≤M) :
    3*M/2-A+2*z+xi≤23*M/30+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤14*M/15+xi := by
  have hkz : 7/2*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤M/21 := by linarith
  constructor <;> nlinarith

end SevenEighths.CenteredMomentReflectionRetainedLength

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionTailMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectionTailMass
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma subset_norm_le (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S) :
    (Ideal.absNorm (∏P∈D,P):ℝ)≤(Ideal.absNorm (∏P∈S,P):ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS)))
    (map_dvd Ideal.absNorm (Finset.prod_dvd_prod_of_subset D S (fun P=>P) hD))

lemma restoration_norm_one (S : Finset (Ideal O)) (H : SmoothIdeal S) : 1≤norm H.val := by
  unfold CenteredMomentReflectionDeletion.norm
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr H.val.property))

lemma dual_scale_bounds (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S)
    (H : SmoothIdeal S) (Q X U : ℝ) (hQ : 0<Q) (hX : 0<X)
    (hcap : Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤U*X) :
    0<Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val) ∧
    Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)≤U := by
  have hd := subset_product_norm_pos D (fun P hP=>hS P (hD hP))
  have hh := norm_pos H.val
  refine ⟨by positivity,?_⟩
  calc
    _≤Q*(Ideal.absNorm (∏P∈D,P):ℝ)/X :=
      div_le_div_of_nonneg_left (by positivity) hX
        (by nlinarith [restoration_norm_one S H])
    _≤Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (subset_norm_le S D hS hD) hQ.le) hX.le
    _≤U := (div_le_iff₀ hX).mpr hcap

theorem coefficient_column_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
      (η ηi : Character)(f : Finset (Ideal O)→SmoothIdeal S→ℂ)(B : ℝ),0≤B →
      (∀D∈S.powerset,∀H,‖f D H‖≤B) →
      (∀D∈S.powerset,Summable (fun H=>coefficient η ηi S D H*f D H)) ∧
      ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*f D H‖≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*B := by
  obtain ⟨C,hC,hbound⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi f B hB hf
  have hs (D : Finset (Ideal O)) (hD : D∈S.powerset) :
      Summable (fun H : SmoothIdeal S=>‖coefficient η ηi S D H*f D H‖) := by
    apply ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    intro H
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
  refine ⟨fun D hD=>(hs D hD).of_norm,?_⟩
  calc
    _≤∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H*f D H‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D hD=>norm_tsum_le_tsum_norm (hs D hD)))
    _≤∑D∈S.powerset,(∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)*B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [←tsum_mul_right]
      apply (hs D hD).tsum_le_tsum _
        ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B)
      intro H
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
    _≤_ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound S hS η ηi).2 hB

theorem actual_deleted_discarded_negligible (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
        (η ηi χ : Character)(t Q X Z : ℝ),1≤Z → 0<Q → 0<X →
        Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
        let F := fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x
        (∀D∈S.powerset,Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0)) ∧
        ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0‖≤
          C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_reflected_upper_negligible a b xi saving L Cscale ha hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound ε hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro S hS η ηi χ t Q X Z hZ hQ hX hcap
  dsimp only
  have hh := hDb S hS η ηi
    (fun E H=>HeckeDyadic.polynomial χ false
      (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
        paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*(1+‖t‖)^n*Z^(-saving)) (by positivity) (by
      intro E hE H
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X (Cscale*Z^L) hQ hX hcap
      exact hCb χ t _ Z hZ hy.1 hy.2)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

end SevenEighths.CenteredMomentReflectionTailMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionWeightedEnergy
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentReflectedAnnuli
local notation "O" => HeckeFamily.O

abbrev Index (S : Finset (Ideal O)) := (S.powerset × SmoothIdeal S) × ℤ

def baseIndex (S : Finset (Ideal O)) : Index S :=
  ((⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩,unitSmooth S),0)

def signedWeight (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (a : Index S) : ℂ :=
  coefficient η ηi S a.1.1.val a.1.2 * (annularMass B a.2 : ℂ)

lemma signedWeight_norm (η ηi : Character) (S : Finset (Ideal O))
    (B : ℕ) (a : Index S) :
    ‖signedWeight η ηi S B a‖ =
      ‖coefficient η ηi S a.1.1.val a.1.2‖ * annularMass B a.2 := by
  rw [signedWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (annularMass_nonneg _ _)]

lemma annularMass_le_two (B : ℕ) (hB : 2≤B) (n : ℤ) :
    annularMass B n ≤ annularMass 2 n := by
  have hp := CenteredMomentSectorLocalization.dyadicScale_pos n
  unfold annularMass
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by linarith [CenteredMomentSectorLocalization.dyadicScale_pos n]) hB)

lemma coefficient_joint_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    Summable (fun a : S.powerset × SmoothIdeal S =>
      ‖coefficient η ηi S a.1.val a.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun D => coefficient_summable_norm η ηi S hS D.val
    (Finset.mem_powerset.mp D.property),(hasSum_fintype _).summable⟩

lemma coefficient_joint_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    (∑' a : S.powerset × SmoothIdeal S,‖coefficient η ηi S a.1.val a.2‖) =
      ∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖ := by
  rw [(coefficient_joint_summable η ηi S hS).tsum_prod,tsum_fintype]
  exact Finset.sum_coe_sort S.powerset (fun D => ∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)

lemma signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) := by
  simp_rw [signedWeight_norm]
  exact (coefficient_joint_summable η ηi S hS).mul_of_nonneg
    (annularMass_summable B hB) (fun _ => norm_nonneg _) (annularMass_nonneg B)

lemma signedWeight_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    (∑'a : Index S,‖signedWeight η ηi S B a‖) =
      (∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖) *
        ∑'n : ℤ,annularMass B n := by
  rw [(signedWeight_summable_norm η ηi S hS B hB).tsum_prod]
  simp_rw [signedWeight_norm,tsum_mul_left]
  rw [tsum_mul_right,coefficient_joint_mass η ηi S hS]

lemma signed_series_reindex (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (f : Index S→ℂ) (hs : Summable (fun a=>‖signedWeight η ηi S B a*f a‖)) :
    (∑'a : Index S,signedWeight η ηi S B a*f a) =
      ∑D : S.powerset,∑'H : SmoothIdeal S,∑'n : ℤ,
        coefficient η ηi S D.val H*(annularMass B n:ℂ)*f ((D,H),n) := by
  rw [hs.of_norm.tsum_prod,hs.of_norm.prod.tsum_prod,tsum_fintype]
  rfl

lemma signedWeight_base (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ) :
    signedWeight η ηi S B (baseIndex S)=(annularMass B 0:ℂ) := by
  simp only [signedWeight,baseIndex,coefficient_empty_unit,one_mul]

theorem signed_mass_subpower (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(∑'n : ℤ,annularMass B n) := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi B hB
  refine ⟨signedWeight_summable_norm η ηi S hS B hB,?_⟩
  rw [signedWeight_mass η ηi S hS B hB]
  exact mul_le_mul_of_nonneg_right (hb S hS η ηi).2 (tsum_nonneg (annularMass_nonneg B))

def annularConstant : ℝ := 1 + ∑'n : ℤ,annularMass 2 n

lemma annularConstant_pos : 0<annularConstant := by
  have h : 0≤∑'n : ℤ,annularMass 2 n := tsum_nonneg (annularMass_nonneg 2)
  dsimp [annularConstant]
  linarith

lemma annularMass_total_le (B : ℕ) (hB : 2≤B) :
    (∑'n : ℤ,annularMass B n) ≤ annularConstant := by
  apply ((annularMass_summable B hB).tsum_le_tsum (annularMass_le_two B hB)
    (annularMass_summable 2 le_rfl)).trans
  dsimp [annularConstant]
  linarith

theorem uniform_signed_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := signed_mass_subpower ε hε
  refine ⟨C*annularConstant,mul_pos hC annularConstant_pos,?_⟩
  intro S hS η ηi B hB
  refine ⟨(hb S hS η ηi B hB).1,(hb S hS η ηi B hB).2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (annularMass_total_le B hB) (by positivity)).trans_eq (by ring)

lemma sum_iSup_le_of_selection {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (g : ∀i,α i→ℝ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,g i (a i))≤E) :
    (∑i,⨆a,g i a)≤E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/((Fintype.card ι:ℝ)+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  choose a ha using fun i => exists_lt_of_lt_ciSup
    (show (⨆a,g i a)-δ < (⨆a,g i a) by linarith)
  have hh : (∑i,⨆a,g i a) ≤ ∑i,(g i (a i)+δ) := by
    apply Finset.sum_le_sum
    intro i _
    linarith [ha i]
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  have he : ((Fintype.card ι:ℝ)+1)*δ=ε := by
    dsimp [δ]
    field_simp
  have hn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  have hb := hselection a
  simp only [Finset.card_univ] at hh
  nlinarith

lemma selection_point_bound {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (f : ∀i,α i→ℂ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) (i : ι) (a : α i) :
    ‖f i a‖^2≤E := by
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>‖f j (Function.update base i a j)‖^2)
    (fun j _=>sq_nonneg _) (Finset.mem_univ i)
  exact (by simpa using hh : ‖f i a‖^2≤∑j,‖f j (Function.update base i a j)‖^2).trans
    (hselection (Function.update base i a))

theorem weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (w f : ∀i,α i→ℂ) (M E : ℝ) (_hM : 0≤M)
    (hs : ∀i,Summable (fun a=>‖w i a‖))
    (hm : ∀i,(∑'a,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∀i,Summable (fun a=>‖w i a*f i a‖)) ∧
      (∑i,‖∑'a,w i a*f i a‖^2)≤M^2*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  let v (i : ι) : ℝ := ⨆a,‖f i a‖^2
  have hbd (i : ι) : BddAbove (Set.range (fun a=>‖f i a‖^2)) :=
    ⟨E,by rintro _ ⟨a,rfl⟩;exact selection_point_bound base f E hselection i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^2≤v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0≤v i := (sq_nonneg _).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖≤Real.sqrt (v i) :=
    (Real.le_sqrt (norm_nonneg _) (hv0 i)).mpr (hv i a)
  have hw (i : ι) : Summable (fun a=>‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (v i))).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a,w i a*f i a‖≤M*Real.sqrt (v i) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (v i)))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  refine ⟨hw,?_⟩
  calc
    (∑i,‖∑'a,w i a*f i a‖^2) ≤ ∑i,(M*Real.sqrt (v i))^2 :=
      Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hsum i) 2)
    _ = M^2*∑i,v i := by simp only [mul_pow,Real.sq_sqrt (hv0 _),Finset.mul_sum]
    _ ≤ M^2*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a=>‖f i a‖^2) E hselection) (sq_nonneg M)

theorem finite_weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (s : ∀i,Finset (α i)) (w f : ∀i,α i→ℂ)
    (M E : ℝ) (hM : 0≤M) (hm : ∀i,(∑a∈s i,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∑i,‖∑a∈s i,w i a*f i a‖^2)≤M^2*E := by
  let w' (i : ι) (a : α i) : ℂ := if a∈s i then w i a else 0
  have hs (i : ι) : Summable (fun a=>‖w' i a‖) := by
    apply summable_of_ne_finset_zero (s:=s i)
    intro a ha
    simp [w',ha]
  have hmass (i : ι) : (∑'a,‖w' i a‖)≤M := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    calc
      (∑a∈s i,‖w' i a‖) = ∑a∈s i,‖w i a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [w',ha]
      _ ≤ M := hm i
  have hh := (weighted_selection_energy base w' f M E hM hs hmass hselection).2
  have he (i : ι) : (∑'a,w' i a*f i a)=∑a∈s i,w i a*f i a := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    apply Finset.sum_congr rfl
    intro a ha
    simp [w',ha]
  simpa only [he] using hh

lemma masked_signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    Summable (fun a=>‖mask a*signedWeight η ηi S B a‖) := by
  apply (signedWeight_summable_norm η ηi S hS B hB).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

lemma masked_signedWeight_mass_le (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    (∑'a,‖mask a*signedWeight η ηi S B a‖)≤∑'a,‖signedWeight η ηi S B a‖ := by
  apply (masked_signedWeight_summable_norm η ηi S hS B hB mask hm).tsum_le_tsum
    _ (signedWeight_summable_norm η ηi S hS B hB)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

theorem actual_masked_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀(mask f : ∀i,Index (S i)→ℂ),(∀i a,‖mask i a‖≤1) →
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i,‖∑'a,(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^2) ≤
        C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0≤R := by linarith
  let M := C*R^(ε/2)
  have hM : 0≤M := by dsimp [M];positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a,‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖)≤M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0≤ε/2)) hC.le
  have hh := weighted_selection_energy (fun i=>baseIndex (S i))
    (fun i a=>mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/2))^2=R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

theorem actual_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀f : ∀i,Index (S i)→ℂ,
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖)) ∧
      (∑i,‖∑'a,signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖^2)≤C*R^ε*E := by
  obtain ⟨C,hC,h⟩ := actual_masked_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap f hselection
  simpa only [norm_one,one_mul] using
    h S hS η ηi B hB R E hR hcap (fun _ _=>1) f (by intro i a;simp) hselection

end SevenEighths.CenteredMomentReflectionWeightedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ThetaRegularity -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem norm_gaussian (a : ℝ) (z : ℂ) :
    ‖gaussian a z‖ = Real.exp (-Real.pi * a * ‖z‖ ^ 2) := by
  simp [gaussian, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

theorem gaussian_le_inverse_square (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖gaussian a z‖ ≤ ((1 + a * ‖z‖ ^ 2) ^ 2)⁻¹ := by
  let x := a * ‖z‖ ^ 2
  have hx : 0 ≤ x := mul_nonneg ha (sq_nonneg _)
  have h1 : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hs : (1 + x) ^ 2 ≤ Real.exp (Real.pi * x) := calc
    _ ≤ (Real.exp x) ^ 2 := by gcongr
    _ = Real.exp (2 * x) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right Real.two_le_pi hx)
  rw [norm_gaussian]
  have hexp : -Real.pi * a * ‖z‖ ^ 2 = -(Real.pi * x) := by dsimp [x]; ring
  rw [hexp]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hs

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

def decayRate : ℝ := Real.pi * parameter c 1

theorem decayRate_pos : 0 < decayRate c :=
  mul_pos Real.pi_pos (parameter_pos c 1 one_pos)

omit [NeZero c] in
theorem parameter_eq (t : ℝ) : parameter c t = parameter c 1 * t := by
  unfold parameter
  ring

omit [NeZero c] in
theorem norm_gaussian_parameter (t : ℝ) (z : ℂ) :
    ‖gaussian (parameter c t) z‖ = Real.exp (-decayRate c * t * ‖z‖ ^ 2) := by
  rw [norm_gaussian, parameter_eq]
  congr 1
  unfold decayRate
  ring

theorem coefficient_norm_le_one (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hu : ‖χ (u : O ⧸ Ideal.span {c})‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact hu.le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem term_norm_le (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (z : O) :
    ‖χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)‖ ≤
        Real.exp (-decayRate c * t * ‖eisEmbedding z‖ ^ 2) := by
  rw [norm_mul, norm_gaussian_parameter]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (coefficient_norm_le_one c χ _)

theorem continuousOn_theta_above (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (δ : ℝ) (hδ : 0 < δ) : ContinuousOn (theta c χ) (Set.Ioi δ) := by
  apply continuousOn_tsum (u := fun z : O => ‖gaussian (parameter c δ) (eisEmbedding z)‖)
  · intro z
    unfold gaussian parameter
    fun_prop
  · exact (gaussian_summable _ (parameter_pos c δ hδ)).norm
  · intro z t ht
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ decayRate c * ‖eisEmbedding z‖ ^ 2 :=
      mul_nonneg (decayRate_pos c).le (sq_nonneg _)
    have htd : δ < t := ht
    nlinarith

theorem continuousAt_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (theta c χ) t := by
  have h := continuousOn_theta_above c χ (t / 2) (half_pos ht)
  exact h.continuousAt (isOpen_Ioi.mem_nhds (show t / 2 < t by linarith))

theorem continuousOn_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    ContinuousOn (theta c χ) (Set.Ioi 0) :=
  fun t ht => (continuousAt_theta c χ t ht).continuousWithinAt

theorem theta_locallyIntegrableOn (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    MeasureTheory.LocallyIntegrableOn (theta c χ) (Set.Ioi 0) :=
  (continuousOn_theta c χ).locallyIntegrableOn measurableSet_Ioi

def tailConstant : ℝ := ∑' z : O, ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖

omit [NeZero c] in
theorem tailConstant_nonneg : 0 ≤ tailConstant c := tsum_nonneg (fun _z => norm_nonneg _)

theorem tailConstant_le_cauchy :
    tailConstant c ≤ 4 * (1 + Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  apply le_trans (Summable.tsum_le_tsum
    (fun z : O => gaussian_le_inverse_square _ ha.le (eisEmbedding z))
    (gaussian_summable _ ha).norm
    (EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable _ ha))
  exact EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_bound _ ha

theorem tailConstant_le_linear :
    tailConstant c ≤ 8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  have hs : (Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 =
      Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖ := by
    rw [div_pow, Real.sq_sqrt ha.le]
    simp only [parameter]
    norm_num
    field_simp
  have h := tailConstant_le_cauchy c
  have hsq := sq_nonneg (1 - Real.pi / Real.sqrt (parameter c (1 / 2)))
  nlinarith

theorem tail_eq_tsum (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    theta c χ t - constantTerm c χ = ∑' z : O, if z = 0 then 0 else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z) := by
  have h := (theta_summable c χ t ht).tsum_eq_add_tsum_ite (0 : O)
  rw [theta_zero_term c χ t] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [theta, add_comm] using h)

theorem tail_term_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) (z : O) :
    ‖if z = 0 then (0 : ℂ) else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z)‖ ≤
      Real.exp (-decayRate c * t / 2) *
        ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖ := by
  by_cases hz : z = 0
  · simp only [ite_eq_left hz, norm_zero]
    positivity
  · rw [ite_eq_right hz]
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := lattice_gap z hz
    have hβ := decayRate_pos c
    have hprod : 0 ≤ (t - 1) * (‖eisEmbedding z‖ ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hn)
    have hineq : t / 2 + ‖eisEmbedding z‖ ^ 2 / 2 ≤ t * ‖eisEmbedding z‖ ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hineq hβ.le]

theorem theta_tail_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      tailConstant c * Real.exp (-decayRate c * t / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [tail_eq_tsum c χ t ht0]
  have hsum := (gaussian_summable _ (parameter_pos c (1 / 2) (by norm_num))).norm
  have hmajor := hsum.mul_left (Real.exp (-decayRate c * t / 2))
  have hnorm := Summable.of_nonneg_of_le (fun z => norm_nonneg _)
    (tail_term_bound c χ t ht) hmajor
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have h := Summable.tsum_le_tsum (tail_term_bound c χ t ht) hnorm hmajor
  simpa only [tsum_mul_left, tailConstant, mul_comm] using h

theorem theta_tail_bound_conductor (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) *
        Real.exp (-decayRate c * t / 2) :=
  (theta_tail_bound c χ t ht).trans
    (mul_le_mul_of_nonneg_right (tailConstant_le_linear c) (Real.exp_nonneg _))

theorem theta_tail_isBigO_exp (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop]
      (fun t : ℝ => Real.exp (-(decayRate c / 2) * t)) := by
  apply isBigO_iff.mpr
  refine ⟨tailConstant c, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have he : -(decayRate c / 2) * t = -decayRate c * t / 2 := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he] using theta_tail_bound c χ t ht

theorem theta_tail_isBigO_rpow (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (r : ℝ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop] (fun t : ℝ => t ^ r) :=
  (theta_tail_isBigO_exp c χ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (half_pos (decayRate_pos c)) r).isBigO

end SevenEighths.ThetaRegularity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.Strip -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

def gammaConstant : ℝ := Real.Gamma (11 / 10) / Real.Gamma (19 / 10)

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem gamma_ratio_left_bound (t : ℝ) :
    ‖Complex.Gamma (1 - ((-(1 / 10) : ℂ) + t * Complex.I)) /
      Complex.Gamma ((-(1 / 10) : ℂ) + t * Complex.I)‖ ≤
        gammaConstant * (3 + |t|) ^ 2 := by
  let s : ℂ := -(1 / 10) + t * Complex.I
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1 / 2) (3 / 5) (-t) 2 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_neg] at hb
  have hnum : ((1 / 2 : ℝ) : ℂ) + ((3 / 5 : ℝ) + (-t) * Complex.I) = 1 - s := by
    dsimp [s]; push_cast; ring
  have hden : ((1 / 2 : ℝ) : ℂ) - ((3 / 5 : ℝ) + (-t) * Complex.I) + (2 : ℕ) = s + 2 := by
    dsimp [s]; push_cast; ring
  rw [hnum, hden] at hb
  norm_num only [show (1 / 2 : ℝ) + 3 / 5 = 11 / 10 by norm_num,
    show (1 / 2 : ℝ) - 3 / 5 + (2 : ℕ) = 19 / 10 by norm_num] at hb
  have heq : Complex.Gamma (1 - s) / Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s + k)) *
        (Complex.Gamma (1 - s) / Complex.Gamma (s + 2)) := by
    rw [div_eq_mul_inv, CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat, div_eq_mul_inv]
    ring
  have hs : ‖s‖ ≤ 1 / 10 + |t| := by
    simpa [s, norm_mul] using norm_add_le (-(1 / 10) : ℂ) ((t : ℂ) * Complex.I)
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  have hf' : ‖∏ k ∈ Finset.range 2, (s + k)‖ ≤ (3 + |t|) ^ 2 := by
    have hs2 : ‖s‖ + (2 : ℝ) ≤ 3 + |t| := by linarith
    exact hf.trans (pow_le_pow_left₀ (by positivity) hs2 2)
  change ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤ _
  rw [heq, norm_mul]
  exact (mul_le_mul hf' hb (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_left_bound_of_re (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ gammaConstant * (3 + |z.im|) ^ 2 := by
  have he : (-(1 / 10) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.re_add_im z
  simpa only [he] using gamma_ratio_left_bound z.im

def completionScale (Q : ℝ) : ℝ := Real.sqrt (3 * Q) / (2 * Real.pi)

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

theorem completionScale_left_power (Q : ℝ) (hQ : 0 < Q) :
    completionScale Q ^ (6 / 5 : ℝ) =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
  have he : completionScale Q = (Real.sqrt 3 / (2 * Real.pi)) * Real.sqrt Q := by
    unfold completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow Q, ← Real.rpow_mul hQ.le]
  norm_num

def leftConstant : ℝ :=
  (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * gammaConstant

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

theorem left_boundary_of_functional_equation (Q D : ℝ) (hQ : 0 < Q) (_hD : 0 ≤ D)
    (L Ldual : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖L z‖ ≤ leftConstant * D * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hscale : ‖(completionScale Q : ℂ) ^ (1 - 2 * z)‖ =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (completionScale_pos Q hQ)]
    have hre : (1 - 2 * z).re = 6 / 5 := by simp [hz]; norm_num
    rw [hre, completionScale_left_power Q hQ]
  have hd : ‖Ldual (1 - z)‖ ≤ D := hdual _ (by simp [hz]; norm_num)
  rw [hfe z hz, norm_mul, norm_mul, norm_mul, hε, one_mul, hscale]
  have hg := gamma_ratio_left_bound_of_re z hz
  have hc := gammaConstant_pos
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (by positivity)) hd (norm_nonneg _)
    (by positivity : 0 ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
      (gammaConstant * (3 + |z.im|) ^ 2))
  calc
    _ ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
        (gammaConstant * (3 + |z.im|) ^ 2) * D := hm
    _ = _ := by unfold leftConstant; ring

def strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 10)) (11 / 10)
def closedStrip : Set ℂ := Complex.re ⁻¹' Icc (-(1 / 10)) (11 / 10)

theorem vertical_strip_of_exp_bound (F : ℂ → ℂ) (C : ℝ)
    (hF : DiffContOnCl ℂ F strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖F z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) → ‖F z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖F z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) : ‖F z‖ ≤ C := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := hgrowth
  apply PhragmenLindelof.vertical_strip hF ?_ hleft hright hz.1 hz.2
  refine ⟨1, ?_, B, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 10 - -(1 / 10))).mpr
    linarith [Real.two_le_pi]
  · apply isBigO_iff.mpr
    refine ⟨A, eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (hgrowth z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hB

theorem closure_strip_subset : closure strip ⊆ closedStrip :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (isClosed_Icc.preimage Complex.continuous_re)

theorem shift_norm_lower (z : ℂ) (hz : z ∈ closedStrip) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num at h
  linarith [hz.1]

theorem shift_ne_zero (z : ℂ) (hz : z ∈ closedStrip) : z + 2 ≠ 0 := by
  have h := shift_norm_lower z hz
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

theorem height_le_shift_norm (z : ℂ) (hz : z ∈ closedStrip) :
    3 + |z.im| ≤ 3 * ‖z + 2‖ := by
  have hr := Complex.re_le_norm (z + 2)
  have hi := Complex.abs_im_le_norm (z + 2)
  norm_num at hr hi
  linarith [hz.1]

theorem shift_norm_le_height (z : ℂ) (hz : z ∈ closedStrip) :
    ‖z + 2‖ ≤ 2 * (3 + |z.im|) := by
  have hr : 0 ≤ z.re + 2 := by linarith [hz.1]
  have h := Complex.norm_le_abs_re_add_abs_im (z + 2)
  norm_num [abs_of_nonneg hr] at h
  linarith [hz.2, abs_nonneg z.im]

def normalized (Q : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z / (((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2)

theorem norm_normalized (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ) (z : ℂ) :
    ‖normalized Q L z‖ = ‖L z‖ / (Q ^ (3 / 5 : ℝ) * ‖z + 2‖ ^ 2) := by
  simp [normalized, norm_pow,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ _)]

theorem normalized_diffContOnCl (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hL : DiffContOnCl ℂ L strip) : DiffContOnCl ℂ (normalized Q L) strip := by
  have hqn : ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)).ne'
  have hd : Differentiable ℂ (fun z : ℂ => ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2) := by
    fun_prop
  refine ⟨hL.differentiableOn.div hd.differentiableOn ?_, hL.continuousOn.div hd.continuous.continuousOn ?_⟩
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z ⟨hz.1.le, hz.2.le⟩))
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z (closure_strip_subset hz)))

theorem normalized_exp_bound (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖normalized Q L z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, B, hA, hB, hg⟩ := hgrowth
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  refine ⟨A / Q ^ (3 / 5 : ℝ), B, div_nonneg hA hq.le, hB, ?_⟩
  intro z hz
  have hn := shift_norm_lower z ⟨hz.1.le, hz.2.le⟩
  have hn2 : 1 ≤ ‖z + 2‖ ^ 2 := by nlinarith
  rw [norm_normalized Q hQ]
  calc
    _ ≤ ‖L z‖ / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hq (by nlinarith)
    _ ≤ (A * Real.exp (B * |z.im|)) / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_right (hg z hz) hq.le
    _ = _ := by ring

theorem normalized_boundary_bound (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (z : ℂ) (hz : z ∈ closedStrip)
    (hL : ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2) :
    ‖normalized Q L z‖ ≤ 9 * C := by
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hn : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  have hh := height_le_shift_norm z hz
  have hh2 : (3 + |z.im|) ^ 2 ≤ 9 * ‖z + 2‖ ^ 2 := by
    nlinarith [abs_nonneg z.im, norm_nonneg (z + 2)]
  rw [norm_normalized Q hQ]
  apply (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hn))).mpr
  apply hL.trans
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC hq.le)
  nlinarith

theorem uniform_strip_bound_of_edges (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hn : ‖normalized Q L z‖ ≤ 9 * C := by
    apply vertical_strip_of_exp_bound _ _ (normalized_diffContOnCl Q hQ L hL)
      (normalized_exp_bound Q hQ L hgrowth) ?_ ?_ z hz
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw], by rw [hw]; norm_num⟩) (hleft w hw)
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw]; norm_num, by rw [hw]⟩) (hright w hw)
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hnz : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  rw [norm_normalized Q hQ] at hn
  have hb := (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hnz))).mp hn
  have hh := shift_norm_le_height z hz
  have hh2 : ‖z + 2‖ ^ 2 ≤ 4 * (3 + |z.im|) ^ 2 := by
    nlinarith [norm_nonneg (z + 2), abs_nonneg z.im]
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg (by positivity : 0 ≤ 9 * C) hq.le)
  nlinarith

theorem uniform_strip_bound (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  apply uniform_strip_bound_of_edges Q C (lt_of_lt_of_le zero_lt_one hQ) hC L hL
    hgrowth hleft ?_ z hz
  intro w hw
  apply (hright w hw).trans
  have hq : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (3 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
  calc
    C ≤ C * Q ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC hq
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC (le_trans zero_le_one hq)) hh

theorem uniform_strip_bound_of_functional_equation
    (Q D : ℝ) (hQ : 1 ≤ Q) (hD : 0 ≤ D) (L Ldual : ℂ → ℂ)
    (ε : ℂ) (hε : ‖ε‖ = 1) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ D)
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * ((1 + leftConstant) * D) * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hQ0 := lt_of_lt_of_le zero_lt_one hQ
  have hc := leftConstant_pos
  apply uniform_strip_bound Q ((1 + leftConstant) * D) hQ (by positivity) L hL hgrowth ?_ ?_ z hz
  · intro w hw
    apply (left_boundary_of_functional_equation Q D hQ0 hD L Ldual ε hε hfe hdual w hw).trans
    have hbase : leftConstant * D ≤ (1 + leftConstant) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hQ0.le _)) (sq_nonneg _)
  · intro w hw
    apply (hright w hw).trans
    nlinarith

theorem uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * F z‖ ≤
        A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1 / 10)) (11 / 10)
  let S : ℝ := a ^ (-(11 / 10) : ℝ) + a ^ (1 / 10 : ℝ)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  refine ⟨S * G * C, Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro z hz
  have hzc : z ∈ closedStrip := ⟨hz.1.le, hz.2.le⟩
  have haBound : ‖(a : ℂ) ^ (-z)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact VerticalContourShift.rpow_between_endpoints a (-(11 / 10)) (1 / 10) (-z.re)
      ha (by linarith [hz.2]) (by linarith [hz.1])
  rw [norm_mul, norm_mul]
  have hgamma := hg z hzc
  have hprod := mul_le_mul (mul_le_mul haBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem mellin_uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hleft : MellinConvergent f (-(1 / 10) : ℂ))
    (hright : MellinConvergent f (11 / 10 : ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * mellin f z‖ ≤
        A * Real.exp (B * |z.im|) := by
  apply uncompleted_exp_bound a ha (mellin f)
  obtain ⟨C, hC, hb⟩ := VerticalContourShift.mellin_uniform_strip_bound f
    (-(1 / 10)) (11 / 10) (by simpa using hleft) (by simpa using hright)
  exact ⟨C, hC, fun z hz => hb z hz.1 hz.2⟩

end SevenEighths.HeckeStrip
end

end OAI

end

