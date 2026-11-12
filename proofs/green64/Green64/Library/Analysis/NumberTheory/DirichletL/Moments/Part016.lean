module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.ActiveCanonicalSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentActiveCanonicalSource
open CenteredMomentActiveAllocation
open CanonicalQuadraticSieve CenteredMomentFirstSectors
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRaw
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredMomentCommonRawScale CenteredMomentRestrictedSourceNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveChildren (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑ a ∈ activeAllocations η (fixedBadMask*idealGenerator R) 1 t slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
    (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂) (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂),
    ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices L a,M i)^2/formalReductionFactor L a P)*
      ∑' z:O,(if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)*
        (‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)‖^2+
         ‖allocatedPositiveRow η (fixedBadMask*idealGenerator R) 1 z t slots
          (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P L a W₁ W₂
          (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂)‖^2)

theorem positiveChildren_nonneg (η : Character) (t : ℝ) (slots : ι→Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (hP : ∀ i,0<P i) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).le
  · apply tsum_nonneg
    intro z
    apply mul_nonneg
    · split_ifs;exact hΦ z;exact le_rfl
    · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

def SmoothedBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (η : Character) (t : ℝ)
      (slots : ι→Finset (Ideal O)),(∀ i,∀ I∈slots i,Prime I) →
    ∀ (S₁ S₂ : Finset (Ideal O)) (R L : Ideal O),Squarefree L →
    ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i,0≤M i) →
      (∀ i,∀ I∈slots i,‖ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)‖≤M i) →
    ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O),
      B₁≠0 → B₂≠0 → Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage S₁ W₁ B₁ X₁ Y₁ → PlainCoverage S₂ W₂ B₂ X₂ Y₂ →
    ∀(keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ),0<K →
      (∀z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q := finiteColumns (tuplePool slots S₁ S₂)
      let β := finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L)
      let raw := T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep Q β (heightCoeff η t) Φ K/(raw*∏i,P i)≤
      D*(Ideal.absNorm L:ℝ)^ε*
        positiveChildren η t slots R L ν Wslot P M W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_smoothed_bound (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,SmoothedBound J D ε := by
  have hex (J:Finset ι) : ∃ D:ℝ,0<D ∧ SmoothedBound J D ε := by
    simpa only [SmoothedBound,positiveChildren] using
      CenteredMomentActiveSmoothedSource.source_plain_to_active_smoothed
        (ι:=J) (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose D hD hbound using hex
  let C:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hC:0<C:=by dsimp [C];linarith
  have hDC (J:Finset ι):D J≤C:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  have hh:=hbound J η t slots hp S₁ S₂ R L hL ν Wslot P M hP hM hcoeff W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ hB₁ hB₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ keep Φ K hK hΦ
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hDC J) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (positiveChildren_nonneg η t slots R L ν Wslot P M hP W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K hΦ))

omit [DecidableEq ι] in

def commonPositiveChildren (τ : Character) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  positiveChildren τ t (fun i:liveIndices B=>S (Sum.inl i.val)) (R*C) L
    (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) keep Φ K

local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
  obtain ⟨D,hD,hbound⟩:=uniform_smoothed_bound (ι:=ι) ε hε
  refine ⟨D,hD,?_⟩
  intro τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  dsimp only
  have hbn (I:Ideal O) (hI:I≠0):(0:ℝ)<Ideal.absNorm I:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hraw:0<T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂):=
    div_pos (hXT ▸ mul_pos hX₁ hX₂) (mul_pos (hbn B₁ hB₁) (hbn B₂ hB₂))
  have hcommon:=CenteredMomentSecondSourceCost.source_divisor_common_saving τ S hS hp C R s hC hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L t _ hraw hP M hν hWnorm hM a b ha hslot keep Φ K hK hΦ
  dsimp only at hcommon
  refine hcommon.trans ?_
  let pref:ℝ:=((actualAllocations S C).card:ℝ)*
    (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))
  have hpref:0≤pref:=by dsimp [pref];positivity
  change pref*_≤pref*D*(Ideal.absNorm L:ℝ)^ε*_
  calc
    _ ≤ pref*∑ B:actualAllocations S C,
      D*(Ideal.absNorm L:ℝ)^ε*commonPositiveChildren τ t S B C R L ν Wslot P M
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K := by
      apply mul_le_mul_of_nonneg_left ?_ hpref
      apply Finset.sum_le_sum
      intro B _
      have hB:= (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
      have hcoeff (i:liveIndices (B:Tuple ι)) (I:Ideal O) :
          ‖ν i.val I*Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val)‖≤M i.val := by
        rw [norm_mul]
        calc
          _ ≤ 1*M i.val := mul_le_mul (hν _ _) (hWnorm _ _) (norm_nonneg _) (by norm_num)
          _ = _ := one_mul _
      have hh:=hbound (liveIndices (B:Tuple ι)) τ t
        (fun i:liveIndices (B:Tuple ι)=>S (Sum.inl i.val))
        (fun i I hI=>hp i.val I hI)
        (residualPool (B.val (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
        (residualPool (B.val (Sum.inr 1)) (hB _) (S (Sum.inr 1)))
        (R*C) L hL (fun i=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val) (fun i=>M i.val)
        (fun i=>hP i.val) (fun i=>(hM i.val).trans' zero_le_one) (fun i I _=>hcoeff i I)
        W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1))
        (mul_ne_zero hB₁ (hB _)) (mul_ne_zero hB₂ (hB _)) hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ hXT hYT
        (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ hcov₁)
        (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ hcov₂) keep Φ K hK hΦ
      dsimp only at hh
      rw [remainingRaw_source B hB B₁ B₂ hB₁ hB₂ T P,CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
      exact hh
    _ = _ := by rw [←Finset.mul_sum];ring

def CanonicalBound (ι : Type*) [Fintype ι] [DecidableEq ι] (D ε : ℝ) : Prop :=
∀ (τ : Character)
      (S : (ι⊕Fin 2)→Finset (Ideal O)),
      (∀ j,∀ I∈S j,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      ∀ (C R s : Ideal O) (hC : Supported C),s∣C →
      ∀ (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ),
      (∀ i,0<P i) → (∀ i I,‖ν i I‖≤1) → (∀ i x,‖Wslot i x‖≤M i) → (∀ i,1≤M i) →
      ∀ (a b : ℝ),0<a → (∀ i,Function.support (Wslot i)⊆Set.Icc a b) →
      ∀ (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ L : Ideal O),
      B₁≠0 → B₂≠0 → Squarefree L →
      Function.support W₁⊆Set.Iic b₁ → Function.support W₂⊆Set.Iic b₂ →
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁ →
      PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂ →
      ∀ (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z:O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let Q:=finiteColumns (Fintype.piFinset S)
      let β:=finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let raw:=T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)
      sourceRestrictedEnergy keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ t) Φ K/(raw*∏ i,P i)≤
        ((actualAllocations S C).card:ℝ)*
          (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          D*(Ideal.absNorm L:ℝ)^ε*
          ∑ B:actualAllocations S C,
            commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
              b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K

theorem uniform_canonical_source_to_positive (ε : ℝ) (hε : 0<ε) :
    ∃ D:ℝ,0<D ∧ ∀ J:Finset ι,CanonicalBound J D ε := by
  have hex (J:Finset ι):∃ D:ℝ,0<D ∧ CanonicalBound J D ε:=by
    simpa only [CanonicalBound] using canonical_source_to_positive (ι:=J) ε hε
  choose D hD hbound using hex
  let E:ℝ:=1+∑ J:Finset ι,D J
  have hs:0≤∑ J:Finset ι,D J:=Finset.sum_nonneg (fun J _=>(hD J).le)
  have hE:0<E:=by dsimp [E];linarith
  have hDE (J:Finset ι):D J≤E:=by
    have hh:=Finset.single_le_sum (fun J _=>(hD J).le) (Finset.mem_univ J)
    dsimp [E];linarith
  refine ⟨E,hE,?_⟩
  intro J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  have hh:=hbound J τ S hS hp C R s hC hsC ν Wslot P M hP hν hWnorm hM a b ha hslot
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ L hB₁ hB₂ hL hs₁ hs₂
    hX₁ hX₂ hY₁ hY₂ hXT hYT hcov₁ hcov₂ t keep Φ K hK hΦ
  refine hh.trans ?_
  have hsum:0≤∑ B:actualAllocations S C,
      commonPositiveChildren τ t S B C R L ν Wslot P M W₁ W₂
        b₁ b₂ X₁ X₂ Y₁ Y₂ B₁ B₂ keep Φ K:=by
    apply Finset.sum_nonneg
    intro B _
    exact positiveChildren_nonneg (ι:=liveIndices (B.val : Tuple J)) τ t
      (fun i=>S (Sum.inl i.val)) (R*C) L (fun i=>ν i.val) (fun i=>Wslot i.val)
      (fun i=>P i.val) (fun i=>M i.val) (fun i=>hP i.val)
      W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ (B₁*B.val (Sum.inr 0)) (B₂*B.val (Sum.inr 1)) keep Φ K hΦ
  apply mul_le_mul_of_nonneg_right ?_ hsum
  apply mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  apply mul_le_mul_of_nonneg_left (hDE J)
  positivity

end SevenEighths.CenteredMomentActiveCanonicalSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonRadialData -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Input (ι:Type*) [Fintype ι] extends Data ι where
  plain₁ : Finset (Ideal O)
  plain₂ : Finset (Ideal O)
  plain₁_ne : ∀I∈plain₁,I≠0
  plain₂_ne : ∀I∈plain₂,I≠0
  coverage₁ : PlainCoverage plain₁ W₁ 1 X₁ Y₁
  coverage₂ : PlainCoverage plain₂ W₂ 1 X₂ Y₂
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  lower : ℝ
  upper : ℝ
  lower_pos : 0<lower
  lower_le : ∀i,lower≤lo i
  upper_ge : ∀i,hi i≤upper

 def Input.pools (s:Input ι) : (ι⊕Fin 2)→Finset (Ideal O) :=
  Sum.elim s.slots (fun j=>if j=0 then s.plain₁ else s.plain₂)

omit [DecidableEq ι] in
lemma Input.pools_ne (s:Input ι) (j:ι⊕Fin 2) : ∀I∈s.pools j,I≠0 := by
  cases j with
  | inl i => exact fun I hI=>(s.prime i I hI).ne_zero
  | inr j =>
    fin_cases j
    · simpa [Input.pools] using s.plain₁_ne
    · simpa [Input.pools] using s.plain₂_ne

omit [DecidableEq ι] in
lemma Input.slot_support (s:Input ι) (i:ι) : Function.support (s.W i)⊆Set.Icc s.lower s.upper :=
  fun _x hx=>⟨(s.lower_le i).trans (s.support i hx).1,((s.support i hx).2).trans (s.upper_ge i)⟩

omit [DecidableEq ι] in
lemma alloc_ne (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : B.val j≠0 :=
  (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 j

omit [DecidableEq ι] in
lemma alloc_norm_pos (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C)
    (j:ι⊕Fin 2) : (0:ℝ)<Ideal.absNorm (B.val j) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))

 def commonData (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) : Data (liveIndices B.val) where
  η:=s.η
  m:=fixedBadMask*idealGenerator (R*C)
  A:=1
  t:=s.t
  slots:=fun i=>s.slots i.val
  prime:=fun i I hI=>s.prime i.val I hI
  ν:=fun i=>s.ν i.val
  W:=fun i=>s.W i.val
  lo:=fun i=>s.lo i.val
  hi:=fun i=>s.hi i.val
  P:=fun i=>s.P i.val
  lo_pos:=fun i=>s.lo_pos i.val
  P_pos:=fun i=>s.P_pos i.val
  support:=fun i=>s.support i.val
  W₁:=s.W₁
  W₂:=s.W₂
  X₁:=s.X₁/Ideal.absNorm (B.val (Sum.inr 0))
  X₂:=s.X₂/Ideal.absNorm (B.val (Sum.inr 1))
  Y₁:=s.Y₁/Ideal.absNorm (B.val (Sum.inr 0))
  Y₂:=s.Y₂/Ideal.absNorm (B.val (Sum.inr 1))
  M:=fun i=>s.M i.val
  M_ge_one:=fun i=>s.M_ge_one i.val
  coefficient_bound:=fun i I hI=>s.coefficient_bound i.val I hI
  b₁:=s.b₁
  b₂:=s.b₂
  support₁:=s.support₁
  support₂:=s.support₂
  X₁_pos:=div_pos s.X₁_pos (alloc_norm_pos s C B _)
  X₂_pos:=div_pos s.X₂_pos (alloc_norm_pos s C B _)
  Y₁_pos:=div_pos s.Y₁_pos (alloc_norm_pos s C B _)
  Y₂_pos:=div_pos s.Y₂_pos (alloc_norm_pos s C B _)
  same_product:=by rw [div_mul_div_comm,div_mul_div_comm,s.same_product]
  rows:=∅
  weight:=fun _=>0
  weight_nonneg:=by simp

omit [DecidableEq ι] in
lemma common_profile_le (s:Input ι) (C R:Ideal O) (B:actualAllocations s.pools C) :
    (commonData s C R B).profileFactor≤ s.toData.profileFactor := by
  unfold Data.profileFactor
  change (2*(max 1 s.b₁*max 1 s.b₂))*(∏i:liveIndices B.val,s.M i.val)^2≤_
  rw [Finset.prod_coe_sort]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i)))
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

end SevenEighths.CenteredMomentCommonRadialData

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonRadialCost -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialCost
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentAllocationCost
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma sqrt_nat_le_add_one (n:ℕ) : Real.sqrt (n:ℝ)≤(n:ℝ)+1 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]

omit [DecidableEq ι] in
 theorem paired_card_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι) (C D:Ideal O),C≠0 → D≠0 →
      ∀Z:ℝ,1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      (Real.sqrt ((actualAllocations s.pools C).card:ℝ)*Real.sqrt ((actualAllocations s.pools D).card:ℝ))*
        (((actualAllocations s.pools C).card:ℝ)*((actualAllocations s.pools D).card:ℝ))≤C0*Z^δ := by
  let ε:ℝ:=δ/(4*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨D0,hD0,hcard⟩:=actualAllocations_uniform_small_power (Fintype.card (ι⊕Fin 2)) ε hε
  refine ⟨(D0+1)^4,by positivity,?_⟩
  intro s C D hC hD Z hZ hNC hND
  have hz:0<Z:=zero_lt_one.trans hZ
  have bound (I:Ideal O) (hI:I≠0) (hn:(Ideal.absNorm I:ℝ)≤Z^B):
      ((actualAllocations s.pools I).card:ℝ)+1≤(D0+1)*Z^(B*ε):=by
    have hi:(1:ℝ)≤Ideal.absNorm I:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hh:=hcard (le_refl (Fintype.card (ι⊕Fin 2))) s.pools I hI
    have hp:(Ideal.absNorm I:ℝ)^ε≤Z^(B*ε):=by
      apply (Real.rpow_le_rpow (by positivity) hn hε.le).trans_eq
      rw [←Real.rpow_mul hz.le]
    have hone:1≤Z^(B*ε):=Real.one_le_rpow hZ.le (mul_nonneg hB hε.le)
    nlinarith [mul_le_mul_of_nonneg_left hp hD0.le]
  have hc:=bound C hC hNC
  have hd:=bound D hD hND
  have hSc:Real.sqrt ((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hc
  have hSd:Real.sqrt ((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=
    (sqrt_nat_le_add_one _).trans hd
  have hcc:((actualAllocations s.pools C).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  have hdd:((actualAllocations s.pools D).card:ℝ)≤(D0+1)*Z^(B*ε):=by linarith
  calc
    _≤(((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε)))*
        (((D0+1)*Z^(B*ε))*((D0+1)*Z^(B*ε))):=by gcongr
    _=(D0+1)^4*Z^(4*B*ε):=by
      rw [show ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))*
        ((D0+1)*Z^(B*ε)*((D0+1)*Z^(B*ε)))=(D0+1)^4*(Z^(B*ε))^4 by ring]
      rw [←Real.rpow_mul_natCast hz.le]
      congr 2
      ring
    _≤_:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have he:ε*(4*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
      nlinarith

omit [DecidableEq ι] in
 theorem card_squared_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι) (C:Ideal O),C≠0 →
      ∀Z:ℝ,1<Z → (Ideal.absNorm C:ℝ)≤Z^B →
      ((actualAllocations s.pools C).card:ℝ)^2≤C0*Z^δ := by
  obtain ⟨C0,hC0,hbound⟩:=paired_card_subpower (ι:=ι) B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s C hC Z hZ hn
  have hh:=hbound s C C hC hC Z hZ hn hn
  have he:Real.sqrt ((actualAllocations s.pools C).card:ℝ)*
      Real.sqrt ((actualAllocations s.pools C).card:ℝ)=((actualAllocations s.pools C).card:ℝ):=by
    rw [←pow_two,Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [he] at hh
  by_cases hz:(actualAllocations s.pools C).card=0
  · rw [hz,Nat.cast_zero,zero_pow (by decide)]
    positivity
  · have hc:(1:ℝ)≤(actualAllocations s.pools C).card:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    apply le_trans ?_ hh
    nlinarith [sq_nonneg ((actualAllocations s.pools C).card:ℝ)]

end SevenEighths.CenteredMomentCommonRadialCost

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonRadialSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonRadialSource
open CenteredMomentCommonRadialData CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationLiveMask CenteredMomentAddedZeroUniform CenteredMomentCommonRawScale
open CenteredMomentRestrictedSource CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def sourceEnergy (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O) : ℝ :=
  let Q:=finiteColumns (Fintype.piFinset s.pools)
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
    (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
    (heightCoeff s.η s.t) r.profile r.scale/(s.X₁*s.X₂*∏i,s.P i)

 def commonCost (s:Input ι) (C:Ideal O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(Ideal.absNorm C:ℝ))

omit [DecidableEq ι] in
lemma commonCost_nonneg (s:Input ι) (C:Ideal O) : 0≤ commonCost s C := by
  unfold commonCost
  positivity

 theorem live_source_eq (s:Input ι) (r:Radial) (C R L:Ideal O) (B:actualAllocations s.pools C) :
    sourceRestrictedEnergy r.keep
      (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
      (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
        (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P=
      energy (commonData s C R B) r L := by
  rw [CenteredMomentCanonicalRetainedSource.liveBox_original_pools]
  have hcov₁:=plainCoverage_residualPool (s.pools (Sum.inr 0)) s.W₁ 1 _
    (alloc_ne s C B (Sum.inr 0)) s.X₁ s.Y₁ s.coverage₁
  have hcov₂:=plainCoverage_residualPool (s.pools (Sum.inr 1)) s.W₂ 1 _
    (alloc_ne s C B (Sum.inr 1)) s.X₂ s.Y₂ s.coverage₂
  simp only [one_mul] at hcov₁ hcov₂
  have hh:=CenteredMomentRadialSourceDictionary.actual_source_energy (commonData s C R B) r
    (residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) (s.pools (Sum.inr 0)))
    (residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) (s.pools (Sum.inr 1)))
    (R*C) L (B.val (Sum.inr 0)) (B.val (Sum.inr 1)) s.X₁ s.X₂ s.Y₁ s.Y₂
    rfl rfl rfl rfl rfl rfl hcov₁ hcov₂
  refine Eq.trans ?_ hh
  apply congrArg₂ (fun x y : ℝ => x / y)
  · simp only [maskedLiveProfile,commonData,one_mul,Input.pools,Sum.elim_inl]
  · dsimp only [remainingRaw,plainNorm,commonData]
    ring

 theorem original_source_common_bound (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C)
    (R seed L:Ideal O) (hseed:seed∣C) :
    sourceEnergy s r C hC R seed L≤ commonCost s C*
      ∑B:actualAllocations s.pools C,energy (commonData s C R B) r L := by
  have hh:=CenteredMomentSecondSourceCost.source_divisor_common_saving (ι:=ι) s.η s.pools s.pools_ne
    (fun i I hI=>s.prime i I hI) C R seed hC hseed s.ν s.W s.P s.W₁ s.W₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L s.t (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos)
    s.P_pos s.M s.ν_bound s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
    r.keep r.profile r.scale r.scale_pos r.nonneg
  have hsum:(∑B:actualAllocations s.pools C,
      sourceRestrictedEnergy r.keep
        (finiteColumns (liveBox s.pools B.val (alloc_ne s C B)))
        (finiteColumnCoefficient (liveBox s.pools B.val (alloc_ne s C B))
          (maskedLiveProfile B.val C R L s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
        (heightCoeff s.η s.t) r.profile r.scale/remainingRaw B.val (s.X₁*s.X₂) s.P)=
      ∑B:actualAllocations s.pools C,energy (commonData s C R B) r L:=
    Finset.sum_congr rfl (fun B _=>live_source_eq s r C R L B)
  rw [hsum] at hh
  exact hh

end SevenEighths.CenteredMomentCommonRadialSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonRadialPointwise -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadialPointwise
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

 def profileCost (s:Input ι) : ℝ :=
  ((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)*s.toData.profileFactor

omit [DecidableEq ι] in
lemma profileCost_nonneg (s:Input ι) : 0≤profileCost s :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) s.toData.profile_nonneg

 theorem actual_common_source_pointwise (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      (∀b:actualAllocations s.pools C,∀a∈(commonData s C R b).toSource.active L,
        childEnergy (commonData s C R b) r L a≤E) →
      sourceEnergy s r C hC R seed L≤C0*Z^δ*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L) := by
  obtain ⟨C₁,hC₁,hchild⟩:=CenteredMomentRadialPointwiseUniform.actual_uniform_divisor lo hi B (δ/2) hB (by linarith)
  obtain ⟨C₂,hC₂,hcount⟩:=card_squared_subpower (ι:=ι) B (δ/2) hB (by linarith)
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s hlo hhi r C hC R seed L hseed hL E Z hE hZ hNC hNL hc
  have hnC:0<(Ideal.absNorm C:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hnL:0<(Ideal.absNorm L:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hz:0<Z:=zero_lt_one.trans hZ
  have heach (b:actualAllocations s.pools C):
      energy (commonData s C R b) r L≤C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ):=by
    have hh:=hchild (liveIndices b.val) (commonData s C R b)
      (fun i=>hlo i.val) (fun i=>hhi i.val) r L hL E Z hE hZ hNL (hc b)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hnL.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (common_profile_le s C R b) hE
  have hh:sourceEnergy s r C hC R seed L≤ commonCost s C*
      (((actualAllocations s.pools C).card:ℝ)*(C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ))):=by
    apply (original_source_common_bound s r C hC R seed L hseed).trans
    apply mul_le_mul_of_nonneg_left _ (commonCost_nonneg s C)
    apply (Finset.sum_le_sum (fun b _=>heach b)).trans_eq
    simp
  apply hh.trans
  have hc2:=hcount s C hC.1 Z hZ hNC
  calc
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (C₁*Z^(δ/2)*(profileCost s*E)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=by
      unfold commonCost profileCost
      ring
    _≤(C₂*Z^(δ/2))*(C₁*Z^(δ/2)*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=
      mul_le_mul_of_nonneg_right hc2 (div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (profileCost_nonneg s) hE)) (mul_nonneg hnC.le hnL.le))
    _=_:=by
      have hp:Z^(δ/2)*Z^(δ/2)=Z^δ:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=(C₁*C₂)*(Z^(δ/2)*Z^(δ/2))*(profileCost s*E)/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm L):=by ring
        _=_:=by rw [hp]

end SevenEighths.CenteredMomentCommonRadialPointwise

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHeightEnvelope
open HeckeFamily CenteredMomentCommonRadialSource CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

 def withHeight (s:Input ι) (η:Character) (t:ℝ) : Input ι := {s with η:=η,t:=t}

 def envelope (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)

 theorem actual_height_envelope (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      ∀J:ℕ,∀(τ:Character) (v:ℝ),
      (∀b:actualAllocations s.pools C,∀a∈(commonData (withHeight s τ v) C R b).toSource.active L,
        childEnergy (commonData (withHeight s τ v) C R b) r L a≤E*(1+‖v‖)^(2*J)) →
      let Q:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ v) r.profile r.scale≤envelope s C L C0 Z δ E*(1+‖v‖)^(2*J) := by
  obtain ⟨C0,hC0,hbound⟩:=actual_common_source_pointwise lo hi B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s hlo hhi r C hC R seed L hs hL E Z hE hZ hNC hNL J τ v hc
  have hh:=hbound (withHeight s τ v) hlo hhi r C hC R seed L hs hL
    (E*(1+‖v‖)^(2*J)) Z (mul_nonneg hE (by positivity)) hZ hNC hNL hc
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  unfold sourceEnergy at hh
  have hmul:=(div_le_iff₀ hraw).mp hh
  apply hmul.trans_eq
  change (C0*Z^δ*(profileCost s*(E*(1+‖v‖)^(2*J)))/
      ((Ideal.absNorm C:ℝ)*Ideal.absNorm L))*(s.X₁*s.X₂*∏i,s.P i)=_
  unfold envelope
  ring

end SevenEighths.CenteredMomentCommonHeightEnvelope

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonLiveFrozen -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonLiveFrozen
open CenteredMomentCommonRadialSource CenteredMomentCommonRadialData CenteredMomentCommonRadialCost
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CanonicalQuadraticSieve
open CenteredMomentCommonRadialPointwise CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSourceNormalization CenteredMomentSecondLiveEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma source_mask_energy (keep:O→Prop) (Q:Finset (Ideal O)) (C L:Ideal O)
    (c f:Ideal O→ℂ) (W:𝓢(ℝ,ℂ)) (K:ℝ):
    CenteredMomentRestrictedSource.sourceRestrictedEnergy keep Q
      (fun I=>if IsCoprime C I ∧ L∣I then c I else 0) f W K =
    CenteredMomentRestrictedSource.sourceRestrictedEnergy keep Q
      (fun I=>if IsCoprime C I then c I else 0)
      (fun I=>(if L∣I then 1 else 0)*f I) W K := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem original_source_weighted (s:Input ι) (r:Radial) (C:Ideal O) (hC:Supported C)
    (R seed L:Ideal O) (hseed:seed∣C) :
    sourceEnergy s r C hC R seed L≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
          energy (commonData s C R B) r L := by
  have hh:=normalized_restricted_child_energy s.pools s.pools_ne
    (fun i I hI=>s.prime i I hI) C R seed hC hseed s.ν s.W s.P s.W₁ s.W₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos)
    s.P_pos (fun I=>(if L∣I then 1 else 0)*heightCoeff s.η s.t I)
    r.keep r.profile r.scale r.scale_pos r.nonneg
  simp_rw [live_divisor_energy] at hh
  dsimp only [sourceEnergy]
  rw [source_mask_energy]
  apply hh.trans_eq
  apply congrArg (fun x:ℝ=>((actualAllocations s.pools C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  exact congrArg (fun x:ℝ=>(‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*x)
    (live_source_eq s r C R L B)

 theorem actual_common_source_pointwise (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData s C R b).toSource.active L,
        childEnergy (commonData s C R b) r L a≤E) →
      sourceEnergy s r C hC R seed L≤C0*Z^δ*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L) := by
  obtain ⟨C₁,hC₁,hchild⟩:=CenteredMomentRadialPointwiseUniform.actual_uniform_divisor lo hi B (δ/2) hB (by linarith)
  obtain ⟨C₂,hC₂,hcount⟩:=card_squared_subpower (ι:=ι) B (δ/2) hB (by linarith)
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s hlo hhi r C hC R seed L hseed hL E Z hE hZ hNC hNL hc
  have hnC:0<(Ideal.absNorm C:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hnL:0<(Ideal.absNorm L:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hz:0<Z:=zero_lt_one.trans hZ
  have hprof:=s.toData.profile_nonneg
  have heach (b:actualAllocations s.pools C) (hlive:frozenCoefficient b.val C R s.ν s.W s.P≠0):
      energy (commonData s C R b) r L≤C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ):=by
    have hh:=hchild (liveIndices b.val) (commonData s C R b)
      (fun i=>hlo i.val) (fun i=>hhi i.val) r L hL E Z hE hZ hNL (hc b hlive)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ hnL.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (common_profile_le s C R b) hE
  have hh:sourceEnergy s r C hC R seed L≤ commonCost s C*
      (((actualAllocations s.pools C).card:ℝ)*(C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(Ideal.absNorm L:ℝ))):=by
    apply (original_source_weighted s r C hC R seed L hseed).trans
    unfold commonCost
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _≤∑b:actualAllocations s.pools C,
          (((∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι)/(C.absNorm:ℝ))*
            (C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(L.absNorm:ℝ)):=by
        apply Finset.sum_le_sum
        intro b hb
        by_cases hzero:frozenCoefficient b.val C R s.ν s.W s.P=0
        · simp only [hzero,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul]
          positivity
        · have hcost:=frozen_normalized_cost (ι:=ι) b.val (alloc_ne s C b) C R hC.1
            (Finset.mem_filter.mp b.property).2 s.ν s.W s.P s.M s.P_pos s.ν_bound
            s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
          exact mul_le_mul hcost (heach b hzero)
            (CenteredMomentRadialEligibleEnergy.energy_nonneg _ _ _) (by positivity)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring
  apply hh.trans
  have hc2:=hcount s C hC.1 Z hZ hNC
  calc
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (C₁*Z^(δ/2)*(profileCost s*E)/((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=by
      unfold commonCost profileCost
      ring
    _≤(C₂*Z^(δ/2))*(C₁*Z^(δ/2)*(profileCost s*E)/
        ((Ideal.absNorm C:ℝ)*Ideal.absNorm L)):=
      mul_le_mul_of_nonneg_right hc2 (div_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (profileCost_nonneg s) hE)) (mul_nonneg hnC.le hnL.le))
    _=_:=by
      have hp:Z^(δ/2)*Z^(δ/2)=Z^δ:=by rw [←Real.rpow_add hz];congr 1;ring
      calc
        _=(C₁*C₂)*(Z^(δ/2)*Z^(δ/2))*(profileCost s*E)/
          ((Ideal.absNorm C:ℝ)*Ideal.absNorm L):=by ring
        _=_:=by rw [hp]

end SevenEighths.CenteredMomentCommonLiveFrozen

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonLiveHeight -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLiveHeight
open HeckeFamily CenteredMomentCommonRadialSource CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceLiveColumn
 theorem actual_height_envelope (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      ∀J:ℕ,∀(τ:Character) (v:ℝ),
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData (withHeight s τ v) C R b).toSource.active L,
        childEnergy (commonData (withHeight s τ v) C R b) r L a≤E*(1+‖v‖)^(2*J)) →
      let Q:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ v) r.profile r.scale≤envelope s C L C0 Z δ E*(1+‖v‖)^(2*J) := by
  obtain ⟨C0,hC0,hbound⟩:=CenteredMomentCommonLiveFrozen.actual_common_source_pointwise lo hi B δ hB hδ
  refine ⟨C0,hC0,?_⟩
  intro s hlo hhi r C hC R seed L hs hL E Z hE hZ hNC hNL J τ v hc
  have hh:=hbound (withHeight s τ v) hlo hhi r C hC R seed L hs hL
    (E*(1+‖v‖)^(2*J)) Z (mul_nonneg hE (by positivity)) hZ hNC hNL hc
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  unfold sourceEnergy at hh
  have hmul:=(div_le_iff₀ hraw).mp hh
  apply hmul.trans_eq
  change (C0*Z^δ*(profileCost s*(E*(1+‖v‖)^(2*J)))/
      ((Ideal.absNorm C:ℝ)*Ideal.absNorm L))*(s.X₁*s.X₂*∏i,s.P i)=_
  unfold envelope
  ring

end SevenEighths.CenteredMomentCommonLiveHeight

end

end OAI

end

