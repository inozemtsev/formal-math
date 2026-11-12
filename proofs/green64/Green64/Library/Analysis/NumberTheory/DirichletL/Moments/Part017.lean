module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SupportedTailAggregate
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part017

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.TerminalEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentTerminalEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O

theorem actual_small_width_source_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (Z mExp q M AExp ρ δ : ℝ),1≤Z →
      0≤ mExp → 0≤q → mExp+q=M → M≤ρ → AExp≤M+δ →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      H=Z^AExp →
      ‖finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ (Z^mExp)‖/H≤C*Z^(M+ρ+δ) := by
  obtain ⟨C,hC,hbound⟩ := smooth_subset_source_absolute_energy F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Z mExp q M AExp ρ δ hZ hm hq hM hsmall hA H hscale
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hh := (hbound J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S (Z^mExp) (Real.rpow_pos_of_pos hZ0 _)).2
  change _≤C*max 1 (Z^mExp)*H at hh
  rw [max_eq_right (Real.one_le_rpow hZ hm),hscale] at hh
  apply hh.trans
  rw [mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

end SevenEighths.CenteredMomentTerminalEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UncenteredTerminal -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

def uncenteredProfileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    (W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂))*
    (if s∣finiteTupleProduct v then 1 else 0)

def comparisonScale (b : ℝ) : ℝ := 1/(2*max 1 b)

lemma comparisonScale_pos (b : ℝ) : 0<comparisonScale b := by
  have hb : 0< max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  unfold comparisonScale
  positivity

lemma comparison_product (b T : ℝ) : comparisonScale b*(T/comparisonScale b)=T := by
  have hy := (comparisonScale_pos b).ne'
  field_simp

theorem comparison_first_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (B I : Ideal O) (hB : B≠0) :
    W ((Ideal.absNorm (B*I):ℝ)/comparisonScale b)=0 := by
  by_contra h
  have ht := hs h
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hn : 1≤(Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hmax : 1≤ max 1 b := le_max_left _ _
  have hb : b≤ max 1 b := le_max_right _ _
  have harg : (Ideal.absNorm (B*I):ℝ)/comparisonScale b=
      (Ideal.absNorm (B*I):ℝ)*(2*max 1 b) := by
    simp [comparisonScale,div_eq_mul_inv]
  rw [harg] at ht
  have hupper := ht.2
  nlinarith

theorem profileCoefficient_eq_uncentered {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ : ℝ) (ha₁ : 0<a₁)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (X₁ X₂ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hB₁ : B₁≠0) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) Y₂ B₁ B₂ s=
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ s := by
  funext v
  simp only [profileCoefficient,idealRectangle,
    comparison_first_zero W₁ a₁ b₁ ha₁ hs₁ B₁ (v (Sum.inr 0)) hB₁,
    zero_mul,sub_zero,uncenteredProfileCoefficient]

theorem smooth_subset_uncentered_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (uncenteredProfileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨C,hC,hbound⟩ := smooth_subset_source_absolute_energy F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ T B₁ B₂ s hP hX₁ hX₂ hB₁ hB₂ hX S K hK
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have he := hbound J hJ η m A t R ν hν P X₁ X₂
    (comparisonScale b₁) (T/comparisonScale b₁) T B₁ B₂ s
    hP hX₁ hX₂ (comparisonScale_pos b₁) (div_pos hT (comparisonScale_pos b₁))
    hB₁ hB₂ hX (comparison_product b₁ T) S K hK
  rw [profileCoefficient_eq_uncentered R (fun j : J => ν j.val)
    (fun j : J => Wslot j.val) (fun j : J => P j.val) W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (T/comparisonScale b₁) B₁ B₂ s hB₁] at he
  exact he

theorem actual_small_width_uncentered_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → ∀ (S : Finset (Tuple J)) (Z mExp q M AExp ρ δ : ℝ),1≤Z →
      0≤ mExp → 0≤q → mExp+q=M → M≤ρ → AExp≤M+δ →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      H=Z^AExp →
      ‖finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (uncenteredProfileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
          W₁ W₂ X₁ X₂ B₁ B₂ s)) Φ (Z^mExp)‖/H≤C*Z^(M+ρ+δ) := by
  obtain ⟨C,hC,hbound⟩ := CenteredMomentTerminalEnergy.actual_small_width_source_energy
    F Wslot W₁ W₂ Φ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ T B₁ B₂ s
    hP hX₁ hX₂ hB₁ hB₂ hX S Z mExp q M AExp ρ δ hZ hm hq hM hsmall hA H hscale
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have he := hbound J hJ η m A t R ν hν P X₁ X₂
    (comparisonScale b₁) (T/comparisonScale b₁) T B₁ B₂ s
    hP hX₁ hX₂ (comparisonScale_pos b₁) (div_pos hT (comparisonScale_pos b₁))
    hB₁ hB₂ hX (comparison_product b₁ T) S Z mExp q M AExp ρ δ
    hZ hm hq hM hsmall hA hscale
  rw [profileCoefficient_eq_uncentered R (fun j : J => ν j.val)
    (fun j : J => Wslot j.val) (fun j : J => P j.val) W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (T/comparisonScale b₁) B₁ B₂ s hB₁] at he
  exact he

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainSource
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAddedZeroUniform
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentUncenteredTerminal CenteredMomentHeckeExpansion
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentDivisorRowEnergy
open CenteredMomentRetainedEnergy CenteredMomentRectangle CenteredMomentSourceRectangleEnergy
open CenteredMomentHeckeColumnWindow
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentSecondHeightFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def completePool (slots : ι→Finset (Ideal O)) (b₁ b₂ X₁ X₂ : ℝ) : Finset (Tuple ι) :=
  tuplePool slots (plainSupportPool b₁ X₁ (comparisonScale b₁))
    (plainSupportPool b₂ X₂ (X₁*X₂/comparisonScale b₁))

lemma support_zero (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) : W 0=0 := by
  by_contra hn
  have := (hs hn).1
  linarith

lemma comparison_row_zero (η : Character) (m A z : O) (t : ℝ)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) :
    rowTwistedSum η m A z W t (comparisonScale b)=0 := by
  rw [rowTwistedSum_eq_weight]
  calc
    _ = ∑' _I : Ideal O, (0:ℂ) := by
      apply tsum_congr
      intro I
      have h := comparison_first_zero W a b ha hs 1 I one_ne_zero
      simpa only [one_mul,mul_zero] using congrArg (fun v : ℂ=>rowWeight η m A z t I*v) h
    _ = 0 := tsum_zero

theorem complete_source_polynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    (∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
      finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
        (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
          rowWeight η m A z t I)=
      (rowTwistedSum η (m*idealGenerator R) A z W₁ t X₁*
        rowTwistedSum η (m*idealGenerator R) A z W₂ t X₂)*
        ∏ i,rowSlot η (m*idealGenerator R) A z (slots i)
          (fun I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t := by
  let : DecidableEq (ι⊕Fin 2) := Classical.decEq _
  have hs₁' : Function.support W₁⊆Set.Iic b₁ := fun x hx=>(hs₁ hx).2
  have hs₂' : Function.support W₂⊆Set.Iic b₂ := fun x hx=>(hs₂ hx).2
  have hy₁ := comparisonScale_pos b₁
  have hy₂ := div_pos (mul_pos hX₁ hX₂) hy₁
  have hc₁ := plainSupportPool_coverage W₁ b₁ X₁ (comparisonScale b₁)
    (support_zero W₁ a₁ b₁ ha₁ hs₁) hs₁' hX₁ hy₁
  have hc₂ := plainSupportPool_coverage W₂ b₂ X₂ (X₁*X₂/comparisonScale b₁)
    (support_zero W₂ a₂ b₂ ha₂ hs₂) hs₂' hX₂ hy₂
  have he := source_polynomial_eq_maskedRectangle η m A z t hmLam hm2 slots _ _ R 1
    ν Wslot P W₁ W₂ X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) 1 1 hc₁ hc₂
  rw [profileCoefficient_eq_uncentered R ν Wslot P W₁ W₂ a₁ b₁ ha₁ hs₁
    X₁ X₂ (X₁*X₂/comparisonScale b₁) 1 1 1 one_ne_zero] at he
  simp only [map_one,Nat.cast_one,div_one] at he
  unfold completePool
  rw [he]
  have hr := actual_slot_rectangle_sum η (m*idealGenerator R) A z slots
    (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) t W₁ W₂ b₁ b₂
    X₁ X₂ (comparisonScale b₁) (X₁*X₂/comparisonScale b₁) hs₁' hs₂' hX₁ hX₂ hy₁ hy₂
  simp only [maskedRectangle,one_dvd,ite_true,one_mul]
  rw [hr,comparison_row_zero η (m*idealGenerator R) A z t W₁ a₁ b₁ ha₁ hs₁,
    zero_mul,sub_zero]

theorem positiveSlotRow_eq_complete_source (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (m*idealGenerator R) A z W₁ W₂ slots
      (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂=
      (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹*
      ∑ I∈finiteColumns (completePool slots b₁ b₂ X₁ X₂),
        finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1) I *
            rowWeight η m A z t I := by
  rw [complete_source_polynomial η m A z t hmLam hm2 slots R ν Wslot P W₁ W₂
    a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂]
  rfl

theorem positive_energy_eq_complete_source (η : Character) (t : ℝ) (keep : O→Prop)
    (slots : ι→Finset (Ideal O)) (R : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (hP : ∀ i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ X₁ X₂ : ℝ)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑' z : O,if keep z then
      ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂ slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P t X₁ X₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      sourceRestrictedEnergy keep (finiteColumns (completePool slots b₁ b₂ X₁ X₂))
        (finiteColumnCoefficient (completePool slots b₁ b₂ X₁ X₂)
          (uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ 1 1 1))
        (heightCoeff η t) Φ K / (X₁*X₂*∏ i,P i) := by
  have htotal : 0<X₁*X₂*∏ i,P i := mul_pos (mul_pos hX₁ hX₂)
    (Finset.prod_pos (fun i _=>hP i))
  unfold sourceRestrictedEnergy restrictedEnergy
  rw [← tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [ite_eq_left hk,ite_eq_left hk,
      positiveSlotRow_eq_complete_source η fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) slots R ν Wslot P W₁ W₂
        a₁ b₁ a₂ b₂ X₁ X₂ ha₁ ha₂ hs₁ hs₂ hX₁ hX₂,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ htotal]
    ring
  · simp only [ite_eq_right hk,zero_div]

end SevenEighths.CenteredMomentDetectorPlainSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ZeroMeanBridge -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentZeroMeanBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentCorrelation CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstReduced CenteredMomentCanonicalFirst
open CenteredMomentActive CenteredMomentFirstDiscardedEnergy CenteredMomentFirstLocalization
local notation "O" => ActualEisensteinCubic.O

def quotientMean (a : O) (F : Residue a → ℂ) : ℂ :=
  (normValue a : ℂ)⁻¹ * ∑' x : Residue a, F x

lemma normValue_ne_zero (a : O) (ha : a ≠ 0) : normValue a ≠ 0 :=
  by
    rw [normValue_eq_embedding]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

theorem quotientMean_pullback (a m : O) (ha : a ≠ 0) (hm : m ≠ 0)
    (h : a ∣ m) (F : Residue a → ℂ) :
    quotientMean m (fun x => F (frequencyReduction a m h x)) = quotientMean a F := by
  obtain ⟨b, rfl⟩ := h
  have hb : b ≠ 0 := right_ne_zero_of_mul hm
  have hh := conductorFourier_lift a b ha hb F 0
  simp only [mul_zero, conductorFourier, map_zero, zero_mul, AddChar.map_zero_eq_one,
    mul_one] at hh
  have he : frequencyReduction a (a*b) (dvd_mul_right a b) = conductorReduction a b := rfl
  unfold quotientMean
  rw [he, hh, normValue_mul, Complex.ofReal_mul]
  have ha' : (normValue a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero a ha)
  have hb' : (normValue b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (normValue_ne_zero b hb)
  change ((normValue a : ℂ) * (normValue b : ℂ))⁻¹ *
    ((normValue b : ℂ) * _) = _
  field_simp

def dilationMask (e d : O) (F : Residue d → ℂ) (x : Residue (d*e)) : ℂ :=
  if frequencyReduction e (d*e) (dvd_mul_left e d) x = 0 then
    F (frequencyReduction d (d*e) (dvd_mul_right d e) x) else 0

@[simp] theorem dilationMask_mk (e d : O) (F : Residue d → ℂ) (z : O) :
    dilationMask e d F (Ideal.Quotient.mk _ z) =
      if e ∣ z then F (Ideal.Quotient.mk _ z) else 0 := by
  simp only [dilationMask, frequencyReduction_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem dilationMask_sum (e d : O) (he : e ≠ 0) (F : Residue d → ℂ) :
    (∑' x : Residue (d*e), dilationMask e d F x) =
      ∑' y : Residue d, F (Ideal.Quotient.mk _ e * y) := by
  have hi := scaledResidue_injective d e (d*e) rfl he
  have hz (x : Residue (d*e)) (hx : x ∉ Set.range (scaledResidue d e (d*e) rfl)) :
      dilationMask e d F x = 0 := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [dilationMask_mk]
    split_ifs with h
    · obtain ⟨y,rfl⟩ := h
      exact False.elim (hx ⟨Ideal.Quotient.mk _ y, rfl⟩)
    · rfl
  have hs : Function.support (dilationMask e d F) ⊆ Set.range (scaledResidue d e (d*e) rfl) := by
    intro x hx
    by_contra hn
    exact hx (hz x hn)
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro y
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, dilationMask_mk, ite_eq_left (dvd_mul_right e z), map_mul]

theorem quotientMean_dilation (e d : O) (he : e ≠ 0) (_hd : d ≠ 0)
    (F : Residue d → ℂ) (hF : ∀ x y, F (x*y) = F x * F y) :
    quotientMean (d*e) (dilationMask e d F) =
      (normValue e : ℂ)⁻¹ * F (Ideal.Quotient.mk _ e) * quotientMean d F := by
  rw [quotientMean, dilationMask_sum e d he]
  simp_rw [hF]
  rw [tsum_mul_left, normValue_mul, Complex.ofReal_mul, quotientMean]
  ring

theorem quotientMean_finite_sum {ι : Type*} [Fintype ι]
    (a : O) (ha : a ≠ 0) (F : Residue a → ℂ)
    (d : ι → O) (hd : ∀ i, d i ≠ 0) (G : (i : ι) → Residue (d i) → ℂ)
    (c : ι → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      ∑ i, c i * G i (Ideal.Quotient.mk _ z)) :
    quotientMean a F = ∑ i, c i * quotientMean (d i) (G i) := by
  let m := a * ∏ i, d i
  have hm : m ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))
  have haM : a ∣ m := dvd_mul_right _ _
  have hdM (i : ι) : d i ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) a
  let := finite_quotient_span hm
  let : Fintype (Residue m) := Fintype.ofFinite _
  rw [← quotientMean_pullback a m ha hm haM F]
  have hh (x : Residue m) : F (frequencyReduction a m haM x) =
      ∑ i, c i * G i (frequencyReduction (d i) m (hdM i) x) := by
    obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa only [frequencyReduction_mk] using h z
  simp_rw [quotientMean, hh, tsum_fintype]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hl := quotientMean_pullback (d i) m (hd i) hm (hdM i) (G i)
  rw [quotientMean, tsum_fintype] at hl
  rw [← Finset.mul_sum, mul_left_comm, hl]
  rfl

theorem row_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (z : O) (v : ℂ) :
    rowCoprimeMask P S z * v =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (if primeSubsetGenerator P E ∣ z then v else 0) := by
  rw [rowCoprimeMask_subsets, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro E hE
  have hp (i : ι) : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_product_moebius P hp hinj E]
  have he : primeSubsetGenerator P E ∣ z ↔ ∀ i ∈ E, z ∈ P i := by
    rw [← Ideal.mem_span_singleton, primeSubsetGenerator, span_idealGenerator,
      mem_prime_product_iff P hinj E z]
  rw [he]
  split_ifs <;> ring

theorem quotientMean_mask_expansion {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset ι) (a d : O) (ha : a ≠ 0) (hd : d ≠ 0)
    (F : Residue a → ℂ) (G : Residue d → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y)
    (hFG : ∀ z : O, F (Ideal.Quotient.mk _ z) =
      rowCoprimeMask P S z * G (Ideal.Quotient.mk _ z)) :
    quotientMean a F =
      ∑ E ∈ S.powerset, (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
        (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
          G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G := by
  have h := quotientMean_finite_sum a ha F
    (fun E : S.powerset => d * primeSubsetGenerator P E.val)
    (fun E => mul_ne_zero hd (primeSubsetGenerator_ne_zero P E.val))
    (fun E => dilationMask (primeSubsetGenerator P E.val) d G)
    (fun E => (UniqueFactorizationMonoid.moebius (∏ i∈E.val,P i) : ℂ)) (by
      intro z
      rw [hFG, row_mask_expansion P hinj S z]
      simp only [dilationMask_mk]
      exact (Finset.sum_coe_sort S.powerset _).symm)
  simp_rw [quotientMean_dilation _ _ (primeSubsetGenerator_ne_zero P _) hd G hG] at h
  simp only [← mul_assoc] at h
  exact h.trans (Finset.sum_coe_sort S.powerset (fun E : Finset ι =>
    (UniqueFactorizationMonoid.moebius (∏ i∈E,P i) : ℂ) *
      (normValue (primeSubsetGenerator P E) : ℂ)⁻¹ *
        G (Ideal.Quotient.mk _ (primeSubsetGenerator P E)) * quotientMean d G))

theorem tripleResidue_mul (a b r : O) (χa : MulChar (Residue a) ℂ)
    (χb : MulChar (Residue b) ℂ) (G : Residue r → ℂ)
    (hG : ∀ x y, G (x*y) = G x * G y) (x y : Residue (a*(b*r))) :
    tripleResidue a b r χa χb G (x*y) =
      tripleResidue a b r χa χb G x * tripleResidue a b r χa χb G y := by
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, tripleResidue_mk, tripleResidue_mk, tripleResidue_mk]
  exact tripleRow_mul a b r χa χb G hG u v

theorem original_pair_reduced_mask (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (z : O) :
    idealRowHom z I * star (idealRowHom z J) =
      rowCoprimeMask (fun P : CommonIndex I J => P.val)
        (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) z := by
  rw [original_pair_factor I J hI hJ]
  rw [common_ideal_pair_active (fun P : CommonIndex I J => P.val) (common_good I J hI)
    (common_odd I J hI) Finset.univ (leftExponent I J) (rightExponent I J)
    (fun P _ => (leftExponent_pos I J P).ne') (fun P _ => (rightExponent_pos I J P).ne')]
  have hactive : activeFunction I J hI (Ideal.Quotient.mk _ z) =
      finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z :=
    principalSexticRow_mk (activePrime I J) (activeCoprime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) (activeConductor I J)
      (span_finitePrimeModulus _) z
  simp only [tripleRow, hactive]
  convert mul_left_comm
    ((residualCharacter I J hI) (Ideal.Quotient.mk _ z) *
      (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ z))
    (rowCoprimeMask (fun P : CommonIndex I J => P.val)
      (principalSupport Finset.univ (leftExponent I J) (rightExponent I J)) z)
    (finiteSexticRow (activePrime I J) (activeGood I J hI)
      (CenteredMomentCanonicalFirst.activeExponent I J) z) using 1
  congr 2

theorem original_pair_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    quotientMean (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
      (CenteredMomentRowNorm.pairResidue _ _ hi hj) =
    ∑ E ∈ inactiveSubsets I J,
      (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)) := by
  dsimp only
  have h := quotientMean_mask_expansion (fun P : CommonIndex I J => P.val) Subtype.val_injective
    (principalSupport Finset.univ (leftExponent I J) (rightExponent I J))
    (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)
    (residualGenerator I J * (residualGenerator J I * activeConductor I J))
    (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported I J hI))
      (mul_ne_zero (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
        (finitePrimeModulus_ne_zero _)))
    (CenteredMomentRowNorm.pairResidue _ _
      ((CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI)
      ((CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ))
    (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
      (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (tripleResidue_mul _ _ _ _ _ _ (principalSexticRow_mul _ _ _ _ _ _)) (by
      intro z
      rw [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
        CenteredMomentSourceRow.primary_span_supported J hJ, tripleResidue_mk]
      exact original_pair_reduced_mask I J hI hJ z)
  simpa only [inactiveSubsets, tripleResidue_mk] using h

theorem canonicalZeroTerm_eq_mean (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroTerm I J hI hJ E W K = (K : ℂ) *
      ((UniqueFactorizationMonoid.moebius (∏ P∈E,P.val) : ℂ) *
        (normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) : ℂ)⁻¹ *
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
        (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E) *
      quotientMean (residualGenerator I J * (residualGenerator J I * activeConductor I J))
        (tripleResidue (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))) *
      paperRadialFourier W 0 := by
  simp only [canonicalZeroTerm, tripleFourier, map_zero, zero_mul,
    AddChar.map_zero_eq_one, mul_one, quotientMean, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem canonicalZeroPair_eq_original (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let hi : Supported (Ideal.span {CompletedGauss.primaryGenerator I}) :=
      (CenteredMomentSourceRow.primary_span_supported I hI).symm ▸ hI
    let hj : Supported (Ideal.span {CompletedGauss.primaryGenerator J}) :=
      (CenteredMomentSourceRow.primary_span_supported J hJ).symm ▸ hJ
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (CompletedGauss.primaryGenerator I * CompletedGauss.primaryGenerator J)‖^2 : ℝ) : ℂ) *
        CenteredMomentRowNorm.pairFourier (CompletedGauss.primaryGenerator I) (CompletedGauss.primaryGenerator J)
          hi hj 0) * paperRadialFourier W 0 := by
  dsimp only
  rw [canonicalZeroPair]
  simp_rw [canonicalZeroTerm_eq_mean]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← original_pair_mean I J hI hJ]
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem quotientMean_congr (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (F : Residue a → ℂ) (G : Residue b → ℂ)
    (h : ∀ z : O, F (Ideal.Quotient.mk _ z) = G (Ideal.Quotient.mk _ z)) :
    quotientMean a F = quotientMean b G := by
  have hh := quotientMean_finite_sum a ha F (fun _ : Unit => b) (fun _ => hb)
    (fun _ => G) (fun _ => (1 : ℂ)) (by intro z; simpa using h z)
  simpa using hh

theorem scaled_pairFourier_eq_mean (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) (K : ℝ) :
    (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) =
      (K : ℂ) * quotientMean (a*b) (CenteredMomentRowNorm.pairResidue a b ha hb) := by
  rw [CenteredMomentZeroMode.pairFourier_zero, quotientMean, ← normValue_eq_embedding,
    Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem canonicalZeroPair_eq_generators (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (haI : Ideal.span {a} = I) (hbJ : Ideal.span {b} = J) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalZeroPair I J hI hJ W K =
      (((K / ‖eisEmbedding (a*b)‖^2 : ℝ) : ℂ) * CenteredMomentRowNorm.pairFourier a b ha hb 0) *
        paperRadialFourier W 0 := by
  rw [canonicalZeroPair_eq_original, scaled_pairFourier_eq_mean, scaled_pairFourier_eq_mean]
  congr 2
  apply quotientMean_congr
    _ _ (mul_ne_zero (supported_primaryGenerator_ne_zero I hI) (supported_primaryGenerator_ne_zero J hJ))
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
  intro z
  simp only [CenteredMomentRowNorm.pairResidue_mk, CenteredMomentSourceRow.primary_span_supported I hI,
    CenteredMomentSourceRow.primary_span_supported J hJ, haI, hbJ]

theorem canonical_ideal_zero_sum (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      canonicalZeroPair I.val J.val (hS I.val I.property) (hS J.val J.property) W K) =
      CenteredMomentZeroMode.idealZeroEnergy S hS c K * paperRadialFourier W 0 := by
  rw [CenteredMomentZeroMode.idealZeroEnergy]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [canonicalZeroPair_eq_generators I.val J.val (hS I.val I.property) (hS J.val J.property)
    (CenteredMomentZeroMode.idealColumn S I) (CenteredMomentZeroMode.idealColumn S J)
    (CenteredMomentZeroMode.idealColumn_supported S hS I) (CenteredMomentZeroMode.idealColumn_supported S hS J)
    (CenteredMomentZeroMode.idealColumn_span S I) (CenteredMomentZeroMode.idealColumn_span S J)]
  ring

theorem zeroEnergy_eq_original (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      CenteredMomentZeroMode.idealZeroEnergy (CenteredMomentSourceRow.supportedColumns S)
        (fun _ h => (Finset.mem_filter.mp h).2)
        (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  unfold zeroEnergy
  exact canonical_ideal_zero_sum (CenteredMomentSourceRow.supportedColumns S)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun I => c I * CenteredMomentHeckeExpansion.rowWeight η m A 1 t I) W K

theorem productColumnCoefficient_mul_whole (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (w : Ideal O → ℂ) (I : Ideal O) :
    productColumnCoefficient S T (fun J L => β J L * w (J*L)) I =
      productColumnCoefficient S T β I * w I := by
  rw [productColumnCoefficient, productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem zeroEnergy_product_eq (η : HeckeFamily.Character) (m A : O) (t : ℝ)
    (S T : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
      (productColumnCoefficient S T β) W K =
    CenteredMomentZeroMode.productZeroEnergy S T hS hT
      (fun I J => β I J * CenteredMomentHeckeExpansion.rowWeight η m A 1 t (I*J)) K *
      paperRadialFourier W 0 := by
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2)
  have hp := CenteredMomentZeroMode.productColumns_supported S T hS hT
  have hs : CenteredMomentSourceRow.supportedColumns P = P := Finset.filter_eq_self.mpr hp
  have hh := zeroEnergy_eq_original η m A t P (productColumnCoefficient S T β) W K
  simp only [hs] at hh
  rw [hh]
  congr 1
  unfold CenteredMomentZeroMode.productZeroEnergy
  congr 1
  funext I
  exact (productColumnCoefficient_mul_whole S T β
    (CenteredMomentHeckeExpansion.rowWeight η m A 1 t) I).symm

theorem normalized_zeroEnergy_product_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : HeckeFamily.Character) (m A : O) (t : ℝ)
      (S T : Finset (Ideal O)) (_hS : ∀ I ∈ S, Supported I) (_hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I*J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        zeroEnergy η m A t ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1*p.2))
          (productColumnCoefficient S T β) W K‖ ≤
        C * K * B^2 * ‖paperRadialFourier W 0‖ * X^ε := by
  obtain ⟨C,hC,hc⟩ := CenteredMomentZeroMode.normalized_product_zero_mode_bound ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S T hS hT β W X K B hX hK hB hN hβ
  rw [zeroEnergy_product_eq η m A t S T hS hT]
  apply hc S T hS hT _ W X K B hX hK hB hN
  intro I hi J hj
  rw [norm_mul]
  exact (mul_le_mul (hβ I hi J hj)
    (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t (I*J)
      (mul_ne_zero (hS I hi).1 (hT J hj).1)) (norm_nonneg _) hB).trans_eq (mul_one B)

end SevenEighths.CenteredMomentZeroMeanBridge

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem idealZeroEnergy_filter (S : Finset (Ideal O)) (hS : ∀ I∈S,Supported I)
    (c : Ideal O → ℂ) (K : ℝ) (p : Ideal O → Prop) [DecidablePred p]
    (hc : ∀ I∈S, ¬p I → c I=0) :
    idealZeroEnergy S hS c K =
      idealZeroEnergy (S.filter p) (fun I h => hS I (Finset.mem_filter.mp h).1) c K := by
  let e : S.filter p → S := fun I => ⟨I.val,(Finset.mem_filter.mp I.property).1⟩
  let ep : (S.filter p) × (S.filter p) → S × S := fun q => (e q.1,e q.2)
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h
  have hep : Function.Injective ep := by
    intro q r h
    exact Prod.ext (he (congrArg Prod.fst h)) (he (congrArg Prod.snd h))
  let f : S × S → ℂ := fun q => (c q.1.val * star (c q.2.val)) *
    (((K / ‖eisEmbedding (idealColumn S q.1 * idealColumn S q.2)‖^2 : ℝ) : ℂ) *
      CenteredMomentRowNorm.pairFourier (idealColumn S q.1) (idealColumn S q.2)
        (idealColumn_supported S hS q.1) (idealColumn_supported S hS q.2) 0)
  have hs : Function.support f ⊆ Set.range ep := by
    intro q hq
    have hi : p q.1.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.1.val q.1.property hn,zero_mul])
    have hj : p q.2.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.2.val q.2.property hn,star_zero,mul_zero,zero_mul])
    exact ⟨(⟨q.1.val,Finset.mem_filter.mpr ⟨q.1.property,hi⟩⟩,
      ⟨q.2.val,Finset.mem_filter.mpr ⟨q.2.property,hj⟩⟩),rfl⟩
  have ht := hep.tsum_eq hs
  simpa only [tsum_fintype,Fintype.sum_prod_type,f,ep,e,idealZeroEnergy,idealColumn] using ht.symm

def activeColumns (S : Finset (Ideal O)) (c : Ideal O → ℂ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => c I≠0)

lemma activeColumns_supported (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (I : Ideal O) (hI : I∈activeColumns S c) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem zeroEnergy_eq_active_original (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      idealZeroEnergy (activeColumns S c) (activeColumns_supported S c)
        (fun I => c I*rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  rw [zeroEnergy_eq_original]
  congr 1
  exact idealZeroEnergy_filter (supportedColumns S) (fun I h => (Finset.mem_filter.mp h).2)
    (fun I => c I*rowWeight η m A 1 t I) K (fun I => c I≠0)
    (fun I _ h => by simp only [not_not] at h; rw [h,zero_mul])

theorem zeroEnergy_eq_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K = zeroEnergy η m A t (activeColumns S c) c W K := by
  rw [zeroEnergy_eq_active_original,zeroEnergy_eq_original]
  have he : supportedColumns (activeColumns S c)=activeColumns S c :=
    Finset.filter_eq_self.mpr (activeColumns_supported S c)
  simp only [he]

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

theorem finite_tuple_fiber_card {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (I : Ideal O) (hI : I≠0) :
    (S.filter (fun v => finiteTupleProduct v=I)).card ≤
      (idealDivisors I).card^(Fintype.card ι+2) := by
  let T := S.filter (fun v => finiteTupleProduct v=I)
  let f (v : T) : (ι ⊕ Fin 2) → idealDivisors I := fun i => ⟨v.val i,by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact Finset.dvd_prod_of_mem v.val (Finset.mem_univ i)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_sum,Fintype.card_fin,T]
    using Fintype.card_le_of_injective f hf

theorem finiteColumnCoefficient_norm_le {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (B : ℝ) (hB : 0≤B)
    (hβ : ∀ v∈S, finiteTupleProduct v≠0 → ‖β v‖≤B) (I : Ideal O) (hI : I≠0) :
    ‖finiteColumnCoefficient S β I‖ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) := by
  calc
    _ ≤ ∑ v∈S.filter (fun v => finiteTupleProduct v=I),‖β v‖ := norm_sum_le _ _
    _ ≤ ∑ _v∈S.filter (fun v => finiteTupleProduct v=I),B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hβ v (Finset.mem_filter.mp hv).1 ((Finset.mem_filter.mp hv).2 ▸ hI)
    _ = B*((S.filter (fun v => finiteTupleProduct v=I)).card:ℝ) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast finite_tuple_fiber_card S I hI

theorem active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^(1+ε) := by
  let δ := ε/(4*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hn : (N+2:ℝ)≠0 := by positivity
  have hδn : δ*(N+2:ℕ)=ε/4 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  obtain ⟨C,hC,hc⟩ := ideal_zero_energy_bound (ε/2) (by positivity)
  refine ⟨C*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  let c := finiteColumnCoefficient S β
  let Q := activeColumns (finiteColumns S) c
  have hQ : ∀ I∈Q,Supported I := activeColumns_supported _ _
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hNX (I : Ideal O) (hI : I∈Q) : (Ideal.absNorm I:ℝ)≤X :=
    hN I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2
  have hbase : 1≤(1+D)*X^δ := by
    have hxδ : 1≤X^δ := Real.one_le_rpow hX hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈Q) :
      ‖c I*rowWeight η m A 1 t I‖ ≤ B*((1+D)^(N+2)*X^(ε/4)) := by
    have hI0 := (hQ I hI).1
    have hdI : ((idealDivisors I).card:ℝ) ≤ (1+D)*X^δ := by
      apply (hd I hI0).trans
      apply mul_le_mul (by linarith : D≤1+D)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hNX I hI) hδ.le) (by positivity) (by positivity)
    have hp : ((1+D)*X^δ)^(N+2) = (1+D)^(N+2)*X^(ε/4) := by
      rw [mul_pow,←Real.rpow_mul_natCast hX0.le,hδn]
    rw [norm_mul]
    calc
      _ ≤ ‖c I‖*1 := mul_le_mul_of_nonneg_left
        (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t I hI0) (norm_nonneg _)
      _ = ‖c I‖ := mul_one _
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*X^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*X^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := hc Q hQ (fun I => c I*rowWeight η m A 1 t I)
    X K (B*((1+D)^(N+2)*X^(ε/4))) hX hK (by positivity) hNX hcoeff
  rw [zeroEnergy_eq_active_original,norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  have hxpow : (X^(ε/4))^2*X^(1+ε/2)=X^(1+ε) := by
    rw [←Real.rpow_mul_natCast hX0.le,←Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C*((1+D)^(N+2))^2*K*B^2*‖paperRadialFourier W 0‖*
      ((X^(ε/4))^2*X^(1+ε/2)) := by ring
    _ = _ := by rw [hxpow]

theorem normalized_active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hb := hc hi η m A t S β W X K B hX hK hB hβ hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hX0)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hX0.le)).trans_eq
  rw [Real.rpow_add hX0,Real.rpow_one]
  field_simp

theorem normalized_supported_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,‖β v‖≤B) →
      (∀ v∈S,β v≠0 → (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := normalized_active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  apply hc hi η m A t S β W X K B hX hK hB (fun v hv _ => hβ v hv)
  intro I _ hI
  obtain ⟨v,hv,hne,he⟩ := finiteColumnCoefficient_witness S β I hI
  rw [←he]
  exact hN v hv hne

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceZeroEnergy
open ActualEisensteinCubic HeckeFamily CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy
open CenteredMomentFirstLocalization CenteredMomentSourceRow
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem profileCoefficient_norm_le {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (Wslot : ι → ℝ → ℂ) (P D : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (D₁ D₂ : ℝ)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hslot : ∀ j x,‖Wslot j x‖≤D j)
    (h₁ : ∀ x,‖W₁ x‖≤D₁) (h₂ : ∀ x,‖W₂ x‖≤D₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    ‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖≤
      2*D₁*D₂*(∏ j,D j) := by
  have hp : ‖∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j)‖≤∏ j,D j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j _
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hslot j _)
      (norm_nonneg _) zero_le_one
  have hr (I J : Ideal O) : ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖≤2*D₁*D₂ := by
    unfold idealRectangle
    apply (norm_sub_le _ _).trans
    rw [norm_mul,norm_mul]
    have hx := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/X₁))
      (h₂ ((Ideal.absNorm J:ℝ)/X₂)) (norm_nonneg _) hD₁
    have hy := mul_le_mul (h₁ ((Ideal.absNorm I:ℝ)/Y₁))
      (h₂ ((Ideal.absNorm J:ℝ)/Y₂)) (norm_nonneg _) hD₁
    linarith
  have hm (p : Prop) [Decidable p] : ‖(if p then 1 else 0 : ℂ)‖≤1 := by
    split_ifs <;> norm_num
  have hDp : 0≤∏ j,D j := Finset.prod_nonneg (fun j _ => hD j)
  unfold profileCoefficient
  rw [norm_mul,norm_mul,norm_mul]
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul hp (hm (IsCoprime (finiteTupleProduct v) R)) (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hD j)))
      (hr (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))) (norm_nonneg _) (by positivity))
    (hm (s∣finiteTupleProduct v)) (norm_nonneg _) (by positivity)
  simpa only [mul_one] using h.trans_eq (by ring)

theorem profileCoefficient_product_bound {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ)
    (P b : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hz : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀ j x,Wslot j x≠0 → x≤b j)
    (hs₁ : ∀ x,W₁ x≠0 → x≤b₁) (hs₂ : ∀ x,W₂ x≠0 → x≤b₂)
    (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤
      (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hz (e.symm j)) (And.intro hz₁ hz₂)
  have hsup : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0 →
      x≤ sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hs (e.symm j)) (And.intro hs₁ hs₂)
  have hn : CenteredMomentAddedZero.originalCoefficient (Fintype.card ι) 1
      (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
      (fun j => ν (e.symm j)) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (tupleEquiv e v)≠0 := by
    rw [originalCoefficient_reindex,←profileCoefficient_eq_original]
    exact hv
  have hh := originalCoefficient_product_bound (Fintype.card ι) 1
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j => Wslot (e.symm j)) (fun j => P (e.symm j)) (fun j => b (e.symm j))
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP (e.symm j))
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hsup (tupleEquiv e v) hn
  simpa only [tupleProduct_reindex,sourceRadius,e.symm.prod_comp] using hh

theorem zeroEnergy_eq_zero_of_subunit {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Y : ℝ) (hY : Y<1)
    (hN : ∀ v∈S,β v≠0 → finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) :
    zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K=0 := by
  have hb (v : Tuple ι) (hv : v∈S) : β v=0 := by
    by_contra hn
    have hh := hN v hv hn
    have hnorm : (1:ℝ)≤Ideal.absNorm (finiteTupleProduct v) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh.1)
    linarith
  have hc (I : Ideal O) : finiteColumnCoefficient S β I=0 := by
    unfold finiteColumnCoefficient
    exact Finset.sum_eq_zero (fun v hv => hb v (Finset.mem_filter.mp hv).1)
  simp only [zeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem smooth_source_zero_energy {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (X K : ℝ),
      0<X → 0≤K → (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)≤X →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K‖≤
        C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  have hend : 0≤(∏ j,b j)*b₁*b₂ := mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂
  let L := 1+(∏ j,b j)*b₁*b₂
  have hL : 0<L := by dsimp only [L]; linarith
  have hendL : (∏ j,b j)*b₁*b₂≤L := by dsimp only [L]; linarith
  obtain ⟨C₀,hC₀,hbound⟩ := active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let C := C₀*(1+B^2)*L^(1+ε)
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos hL _)
  refine ⟨C,hC,?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK hscale
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw : 0≤(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) :=
    mul_nonneg (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*X := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY
      hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
    refine ⟨hh.1,hh.2.trans ?_⟩
    calc
      _ = ((∏ j,b j)*b₁*b₂)*((T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)) := by ring
      _ ≤ L*X := mul_le_mul hendL hscale hraw hL.le
  by_cases hsmall : L*X<1
  · have he := zeroEnergy_eq_zero_of_subunit η m A t S β Φ K (L*X) hsmall
      (fun v _ hv => hN v hv)
    change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤_
    rw [he,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (norm_nonneg _)) (Real.rpow_nonneg hXX.le _)
  have hradius : 1≤L*X := le_of_not_gt hsmall
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ (L*X) K B hradius hK hB
    (fun v _ _ => hβ v) (fun I _ hI => by
      obtain ⟨v,hv,hne,hprod⟩ := finiteColumnCoefficient_witness S β I hI
      rw [←hprod]
      exact (hN v hne).2)
  have hpower : X⁻¹*(L*X)^(1+ε)=L^(1+ε)*X^ε := by
    rw [Real.mul_rpow hL.le hXX.le,Real.rpow_add hXX,Real.rpow_one]
    field_simp
  change ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) Φ K‖≤_
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hXX)]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXX.le)).trans
  calc
    _ = C₀*B^2*L^(1+ε)*K*‖paperRadialFourier Φ 0‖*X^ε := by
      calc
        _ = C₀*B^2*K*‖paperRadialFourier Φ 0‖*(X⁻¹*(L*X)^(1+ε)) := by ring
        _ = _ := by rw [hpower];ring
    _ ≤ C*K*‖paperRadialFourier Φ 0‖*X^ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX.le _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hK
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le)
        (Real.rpow_nonneg hL.le _)

theorem smooth_source_zero_energy_at_radius {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (R : Ideal O) (ν : ι → Ideal O → ℂ), (∀ j I,‖ν j I‖≤1) →
      ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple ι)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ), 0≤K →
      let X := (∏ j,b j)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (X<1 → E=0) ∧ ‖((X⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  choose D hD hDb hz hs using fun j => smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let B := 2*D₁*D₂*(∏ j,D j)
  have hB : 0≤B := mul_nonneg (by positivity) (Finset.prod_nonneg (fun j _ => hD j))
  obtain ⟨C₀,hC₀,hbound⟩ := normalized_supported_tuple_zero_energy_bound (Fintype.card ι) ε hε
  refine ⟨C₀*(1+B^2),mul_pos hC₀ (by positivity),?_⟩
  intro η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK X E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤B :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂ hDb hDb₁ hDb₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hN (v : Tuple ι) (hv : β v≠0) :
      finiteTupleProduct v≠0 ∧ (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X :=
    profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hsb₁ hsb₂ v hv
  have hzero (hx : X<1) : E=0 :=
    zeroEnergy_eq_zero_of_subunit η m A t S β Φ K X hx (fun v _ hv => hN v hv)
  refine ⟨hzero,?_⟩
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hXX : 0≤X := by
    dsimp only [X]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun j _ => hb j)) hb₁) hb₂)
      (div_nonneg hT.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
      (Finset.prod_nonneg (fun j _ => (hP j).le))
  by_cases hx : X<1
  · rw [hzero hx,mul_zero,norm_zero]
    positivity
  have he := hbound (le_refl (Fintype.card ι)) η m A t S β Φ X K B
    (le_of_not_gt hx) hK hB (fun v _ => hβ v) (fun v _ hv => (hN v hv).2)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXX _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    C₀*K*B^2 = C₀*B^2*K := by ring
    _ ≤ C₀*(1+B^2)*K := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : B^2≤1+B^2) hC₀.le) hK

theorem smooth_subset_source_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),0≤K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let ρ := (∏ j∈J,b j)*b₁*b₂*H
      let E := zeroEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      (ρ<1 → E=0) ∧
      ‖((ρ⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*ρ^ε ∧
      ∀ X : ℝ,0<X → H≤X → ‖((X⁻¹:ℝ):ℂ)*E‖≤C*K*‖paperRadialFourier Φ 0‖*X^ε := by
  have hraw (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  have hrad (J : Finset α) (hJ : J⊆F) := smooth_source_zero_energy_at_radius
    (fun j : J => Wslot j.val) W₁ W₂ (fun j : J => a j.val) (fun j : J => b j.val)
    a₁ b₁ a₂ b₂ (fun j => ha j.val (hJ j.property)) (fun j => hb j.val (hJ j.property))
    ha₁ hb₁ ha₂ hb₂ (fun j => hsSlot j.val (hJ j.property)) hs₁ hs₂
    (fun j => hWslot j.val (hJ j.property)) hW₁ hW₂ ε hε
  let D (J : Finset α) : ℝ := if hJ : J⊆F then (hraw J hJ).choose+(hrad J hJ).choose else 1
  have hD (J : Finset α) : 0<D J := by
    dsimp only [D]
    split_ifs with hJ
    · exact add_pos (hraw J hJ).choose_spec.1 (hrad J hJ).choose_spec.1
    · norm_num
  let C := 1+∑ J∈F.powerset,D J
  have hC : 0<C := by
    have hsum := Finset.sum_nonneg (fun J (_ : J∈F.powerset) => (hD J).le)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK H ρ E
  have hDC : D J≤C := by
    have hle := Finset.single_le_sum (fun L (_ : L∈F.powerset) => (hD L).le) (Finset.mem_powerset.mpr hJ)
    dsimp only [C]
    linarith
  have hde : D J=(hraw J hJ).choose+(hrad J hJ).choose := by simp only [D,dite_eq_left hJ]
  have hrawC : (hraw J hJ).choose≤C := by
    rw [hde] at hDC
    linarith [(hrad J hJ).choose_spec.1]
  have hradC : (hrad J hJ).choose≤C := by
    rw [hde] at hDC
    linarith [(hraw J hJ).choose_spec.1]
  have hr := (hrad J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
    (fun j I => hν j.val j.property I) (fun j : J => P j.val)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ K hK
  have heq : (∏ j : J,b j.val)*b₁*b₂*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j : J,P j.val)=ρ := by
    rw [Finset.prod_coe_sort,Finset.prod_coe_sort]
    dsimp only [ρ,H]
    ring
  dsimp only at hr
  rw [heq] at hr
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodB : 0≤∏ j∈J,b j := Finset.prod_nonneg (fun j hj => hb j (hJ hj))
  have hprodP : 0≤∏ j∈J,P j := Finset.prod_nonneg (fun j hj => (hP j hj).le)
  have hρ : 0≤ρ := by dsimp only [ρ,H]; positivity
  refine ⟨hr.1,hr.2.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hradC hK) (norm_nonneg _))
      (Real.rpow_nonneg hρ _)
  · intro X hXX hscale
    have hx := (hraw J hJ).choose_spec.2 η m A t R (fun j : J => ν j.val)
      (fun j I => hν j.val j.property I) (fun j : J => P j.val)
      X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j => hP j.val j.property)
      hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S Φ X K hXX hK
      (by simpa only [Finset.prod_coe_sort] using hscale)
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrawC hK) (norm_nonneg _))
      (Real.rpow_nonneg hXX.le _))

end SevenEighths.CenteredMomentSourceZeroEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSecondZeroEnergy
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def sourceSecondZero (S : Finset (Ideal O)) (β : Ideal O→ℂ) (η : Character) (t : ℝ) : ℂ :=
  secondZeroEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I => β I*heightCoeff η t I)

lemma heightCoeff_norm_le_one (η : Character) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact idealCoeff_norm_le_one η I

theorem secondZeroEnergy_filter {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (p : α→Prop) [DecidablePred p] (hc : ∀ i∈S,¬p i→c i=0) :
    secondZeroEnergy S a ha c=secondZeroEnergy (S.filter p) a ha c := by
  unfold secondZeroEnergy
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i
  · rw [ite_eq_left hpi]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpj : p j
    · rw [ite_eq_left hpj]
    · simp only [ite_eq_right hpj,hc j hj hpj,star_zero,mul_zero,zero_mul]
  · simp only [ite_eq_right hpi,hc i hi hpi,zero_mul,Finset.sum_const_zero]

lemma sourceGenerator_span (S : Finset (Ideal O)) (I : supportedColumns S) :
    Ideal.span {sourceGenerator S I}=(I:Ideal O) :=
  primary_span_supported I (Finset.mem_filter.mp I.property).2
lemma sourceGenerator_primary (S : Finset (Ideal O)) (I : supportedColumns S) :
    ConcretePrimeRowBridge.goodLambda^2∣sourceGenerator S I-1 :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2)).2
lemma sourceGenerator_injective (S : Finset (Ideal O)) : Function.Injective (sourceGenerator S) := by
  intro I J h
  apply Subtype.ext
  rw [←sourceGenerator_span S I,←sourceGenerator_span S J,h]

theorem sourceSecondZero_divisor_bound (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t B Y : ℝ) (hB : 0≤B) (hY : 0≤Y)
    (s : Ideal O) (hs : s≠0)
    (hc : ∀ I∈supportedColumns S,β I≠0→‖β I‖≤B)
    (hdiv : ∀ I∈supportedColumns S,β I≠0→s∣I)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    ‖sourceSecondZero S β η t‖≤128*B^2*Y/(Ideal.absNorm s:ℝ) := by
  let Q : Finset (supportedColumns S) := Finset.univ.filter (fun I => β I≠0)
  rw [sourceSecondZero,secondZeroEnergy_filter Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I => β I*heightCoeff η t I) (fun I => β I≠0)
      (by intro I _ h; simp only [not_not] at h; rw [h,zero_mul])]
  refine secondZeroEnergy_divisor_bound Q (sourceGenerator S) (sourceGenerator_supported S)
    (sourceGenerator_primary S) (sourceGenerator_injective S).injOn _ B hB ?_ s hs ?_ Y hY ?_
  · intro I hI
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heightCoeff_norm_le_one η t I
      (Finset.mem_filter.mp I.property).2.1) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hc I I.property (Finset.mem_filter.mp hI).2)
  · intro I hI
    rw [sourceGenerator_span]
    exact hdiv I I.property (Finset.mem_filter.mp hI).2
  · intro I hI
    rw [sourceGenerator_span]
    exact hN I I.property (Finset.mem_filter.mp hI).2

theorem sourceSecondZero_eq_zero_of_subunit (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t Y : ℝ) (hY : Y<1)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    sourceSecondZero S β η t=0 := by
  have hc (I : supportedColumns S) : β I=0 := by
    by_contra hn
    have hi : (1:ℝ)≤Ideal.absNorm (I:Ideal O) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp I.property).2.1)
    linarith [hN I I.property hn]
  simp only [sourceSecondZero,secondZeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B Y : ℝ),
      0≤B → 1≤Y → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) →
      ‖sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*B^2*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  let δ := ε/(2*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : δ*(N+2:ℕ)=ε/2 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi S β η t B Y hB hY hβ s hs hdiv hN
  let c := finiteColumnCoefficient S β
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hbound (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      (Ideal.absNorm I:ℝ)≤Y := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  have hbase : 1≤(1+D)*Y^δ := by
    have hp := Real.one_le_rpow hY hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      ‖c I‖≤B*((1+D)^(N+2)*Y^(ε/2)) := by
    have hI0 := (Finset.mem_filter.mp hI).2.1
    have hdI : ((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
      (hd I hI0).trans (mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hbound I hI hn) hδ.le) (by positivity) (by positivity))
    have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^(ε/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
    calc
      _ ≤ B*((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*Y^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := sourceSecondZero_divisor_bound (finiteColumns S) c η t
    (B*((1+D)^(N+2)*Y^(ε/2))) Y (by positivity) hY0.le s hs hcoeff
    (by
      intro I hI hn
      obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
      rw [←he]
      exact hdiv v hv hv0) hbound
  apply hb.trans_eq
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  calc
    _ = (128*((1+D)^(N+2))^2)*B^2*((Y^(ε/2))^2*Y)/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [hp]

theorem normalized_tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B L T : ℝ),
      0≤B → 0<L → 0<T → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*T) →
      (L*T<1 → sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0) ∧
      ∀ κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*‖κ‖*B^2*L^(1+ε)*T^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi S β η t B L T hB hL hT hβ s hs hdiv hN
  have hz (hsmall : L*T<1) : sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0 := by
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*T) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  refine ⟨hz,?_⟩
  intro κ
  by_cases hsmall : L*T<1
  · rw [hz hsmall,mul_zero,norm_zero]
    positivity
  have hb := hbound hi S β η t B (L*T) hB (le_of_not_gt hsmall) hβ s hs hdiv hN
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hT.le)).trans_eq
  rw [Real.mul_rpow hL.le hT.le,Real.rpow_add hT,Real.rpow_one]
  field_simp

lemma profileCoefficient_dvd {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    s∣finiteTupleProduct v := by
  by_contra h
  exact hv (by simp only [profileCoefficient,ite_eq_right h,mul_zero])

theorem profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P D b : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (D₁ D₂ b₁ b₂ : ℝ),
      (∀ j,0≤D j) → 0≤D₁ → 0≤D₂ → (∀ j,0≤b j) → 0≤b₁ → 0≤b₂ →
      (∀ j x,‖Wslot j x‖≤D j) → (∀ x,‖W₁ x‖≤D₁) → (∀ x,‖W₂ x‖≤D₂) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b j) → (∀ x,W₁ x≠0→x≤b₁) → (∀ x,W₂ x≠0→x≤b₂) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let L := (∏ j,b j)*b₁*b₂
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (L*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*(2*D₁*D₂*(∏ j,D j))^2*(1+L)^(1+ε)*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P D b W₁ W₂ D₁ D₂ b₁ b₂
    hD hD₁ hD₂ hb hb₁ hb₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw L E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤2*D₁*D₂*(∏ j,D j) :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂
      hslot h₁ h₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hraw : 0<Traw := mul_pos (div_pos hT (mul_pos hn₁ hn₂)) (Finset.prod_pos (fun j _=>hP j))
  have hL : 0≤L := mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=>hb j)) hb₁) hb₂
  have hN (v : Tuple ι) (hv : β v≠0) : (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*Traw := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hs₁ hs₂ v hv
    exact hh.2.trans_eq (by dsimp only [L,Traw];ring)
  refine ⟨?_,?_⟩
  · intro hsmall
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*Traw) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv0
  · exact (hbound hi S β η t (2*D₁*D₂*(∏ j,D j)) (1+L) Traw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD₁) hD₂) (Finset.prod_nonneg (fun j _=>hD j)))
      (by linarith) hraw (fun v _ _=>hβ v) s hsz
      (fun v _ hv=>profileCoefficient_dvd R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hv)
      (fun v _ hv=>(hN v hv).trans (mul_le_mul_of_nonneg_right (by linarith : L≤1+L) hraw.le))).2

theorem bounded_profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε)
    (D b : ℝ) (hD : 0≤D) (hb : 0≤b) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ),
      (∀ j x,‖Wslot j x‖≤D) → (∀ x,‖W₁ x‖≤D) → (∀ x,‖W₂ x‖≤D) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b) → (∀ x,W₁ x≠0→x≤b) → (∀ x,W₂ x≠0→x≤b) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (b^(Fintype.card ι+2)*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C₀,hC₀,hmain⟩ := profile_second_zero_energy N ε hε
  let B := 2*D*D*(1+D)^N
  let L := (1+b)^(N+2)
  let C := C₀*(1+B^2)*(1+L)^(1+ε)
  have hB : 0≤B := by dsimp [B];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P W₁ W₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw E
  have hTpos : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw0 : 0≤Traw := mul_nonneg (div_nonneg hTpos.le (by positivity))
    (Finset.prod_nonneg (fun j _=>(hP j).le))
  have hh := hmain hi η t R ν hν Wslot P (fun _=>D) (fun _=>b) W₁ W₂ D D b b
    (fun _=>hD) hD hD (fun _=>hb) hb hb hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  simp only [Finset.prod_const,Finset.card_univ] at hh
  have heL : b^Fintype.card ι*b*b=b^(Fintype.card ι+2) := by
    rw [pow_add,pow_two];ring
  rw [heL] at hh
  refine ⟨hh.1,?_⟩
  intro κ
  have hBbound : 2*D*D*D^Fintype.card ι≤B := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_left₀ hD (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  have hLbound : b^(Fintype.card ι+2)≤L :=
    (pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hpow : (1+b^(Fintype.card ι+2))^(1+ε)≤(1+L)^(1+ε) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hcoef : C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε)≤C := by
    dsimp only [C]
    apply mul_le_mul _ hpow (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    exact (pow_le_pow_left₀ (by positivity) hBbound 2).trans (by linarith)
  apply (hh.2 κ).trans
  calc
    _ = (C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε))*
        (‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) := by ring
    _ ≤ C*(‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

theorem smooth_subset_source_second_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α→ℝ→ℂ) (W₁ W₂ : ℝ→ℂ) (a b : α→ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : α→Ideal O→ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) → ∀ (P : α→ℝ)
      (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T →
      ∀ (pools : (J⊕Fin 2)→Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),
      let S := Fintype.piFinset pools
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let Y := (∏ j∈J,b j)*b₁*b₂*Traw
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (Y<1 → E=0) ∧
        ‖(((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)/(Traw:ℂ))*E‖≤
          C*‖(K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  choose D hD hDb hz hsb using fun j : F => smooth_annular_bound
    (Wslot j.val) (a j.val) (b j.val) (ha j.val j.property)
    (hsSlot j.val j.property) (hWslot j.val j.property)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let Dmax := 1+D₁+D₂+∑ j : F,D j
  let bmax := 1+b₁+b₂+∑ j : F,b j.val
  have hDs : 0≤∑ j : F,D j := Finset.sum_nonneg (fun j _=>hD j)
  have hbs : 0≤∑ j : F,b j.val := Finset.sum_nonneg (fun j _=>hb j.val j.property)
  have hDmax : 0≤Dmax := by dsimp only [Dmax];linarith
  have hbmax : 0≤bmax := by dsimp only [bmax];linarith
  have hD₁max : D₁≤Dmax := by dsimp only [Dmax];linarith
  have hD₂max : D₂≤Dmax := by dsimp only [Dmax];linarith
  have hb₁max : b₁≤bmax := by dsimp only [bmax];linarith
  have hb₂max : b₂≤bmax := by dsimp only [bmax];linarith
  have hDj (j : F) : D j≤Dmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hD k) (Finset.mem_univ j)
    dsimp only [Dmax]
    linarith
  have hbj (j : F) : b j.val≤bmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hb k.val k.property) (Finset.mem_univ j)
    dsimp only [bmax]
    linarith
  obtain ⟨C,hC,hbound⟩ := bounded_profile_second_zero_energy F.card ε hε Dmax bmax hDmax hbmax
  refine ⟨C,hC,?_⟩
  intro J hJ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY pools Φ K S Traw Y E
  let β := profileCoefficient R (fun j : J=>ν j.val) (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hcard : Fintype.card J≤F.card := by simpa only [Fintype.card_coe] using Finset.card_le_card hJ
  have hh := hbound hcard η t R (fun j : J=>ν j.val) (fun j I=>hν j.val j.property I)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂
    (fun j x=>(hDb ⟨j.val,hJ j.property⟩ x).trans (hDj ⟨j.val,hJ j.property⟩))
    (fun x=>(hDb₁ x).trans hD₁max) (fun x=>(hDb₂ x).trans hD₂max)
    (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j x hx=>(hsb ⟨j.val,hJ j.property⟩ x hx).trans (hbj ⟨j.val,hJ j.property⟩))
    (fun x hx=>(hsb₁ x hx).trans hb₁max) (fun x hx=>(hsb₂ x hx).trans hb₂max)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  rw [Finset.prod_coe_sort] at hh
  refine ⟨?_,hh.2 ((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)⟩
  intro hsmall
  apply sourceSecondZero_eq_zero_of_subunit _ _ η t Y hsmall
  intro I hI hn
  obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
  have hN := profileCoefficient_product_bound R (fun j : J=>ν j.val)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) (fun j : J=>b j.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j=>hsb ⟨j.val,hJ j.property⟩) hsb₁ hsb₂ v hv0
  rw [←he]
  exact hN.2.trans_eq (by rw [Finset.prod_coe_sort,Finset.prod_coe_sort];dsimp only [Y,Traw];ring)

end SevenEighths.CenteredMomentSourceSecondZeroEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondLocalization -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSourcePoisson CenteredMomentSecondWholeKernel CenteredMomentSecondTail
open CenteredMomentFirstLocalization CenteredMomentSectorLocalization CenteredMomentSupportedCorrelation
open CenteredMomentSupportedTailAggregate CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def secondRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
    ∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
      actualCorrelation (primaryGenerator I) (primaryGenerator J)
        ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) (-h)*
      paperRadialFourier W (K*‖eisEmbedding h‖^2/
        ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2)

theorem secondSourceKernel_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        actualCorrelation (primaryGenerator I) (primaryGenerator J)
          ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) 0*
          paperRadialFourier W 0+
      secondRetainedPair I J hI hJ W K Tsec Z ξ+
      secondDiscardedPair I J hI hJ W K Tsec Z ξ := by
  have hpI := (supported_span_primaryGenerator_iff I).mpr hI
  have hpJ := (supported_span_primaryGenerator_iff J).mpr hJ
  have hk : 0<K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos I hI.1) (CenteredMomentFirstScale.norm_pos J hJ.1))
  have hs := lattice_fourier_split W _ hk
    (fun h => actualCorrelation (primaryGenerator I) (primaryGenerator J) hpI hpJ (-h))
    _ (fun h => CenteredMomentTail.actualCorrelation_norm_le _ _ hpI hpJ (-h))
    (frequencyRadius Tsec Z ξ)
  have he (h : O) : K*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2=
      (K/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)))*normValue h := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq I hI,primary_norm_sq J hJ,normValue_eq_embedding]
    ring
  rw [secondSourceKernel_poisson I J hI hJ W K hK]
  unfold secondRetainedPair secondDiscardedPair
  simp_rw [he]
  rw [hs]
  simp only [neg_zero]
  ring

def secondRetainedEnergy (η : Character) (t : ℝ) (S : Finset (Ideal O))
    (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*heightCoeff η t I)*star (c J*heightCoeff η t J))*
      secondRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem sourceGaussEnergy_localized (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff η t) W K=
      ((K:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β η t+
      secondRetainedEnergy η t S β W K Tsec Z ξ+
      secondDiscardedEnergy η t S β W K Tsec Z ξ := by
  rw [sourceGaussEnergy_poisson η t S β W K hK]
  unfold sourceSecondZero secondZeroEnergy secondRetainedEnergy secondDiscardedEnergy
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  have he := secondSourceKernel_split I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ hK
  rw [secondSourceKernel_poisson I J (Finset.mem_filter.mp I.property).2
    (Finset.mem_filter.mp J.property).2 W K hK] at he
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  convert congrArg (fun x : ℂ => ((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*x) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondLocalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ActiveSource -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentActiveSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentGaussEnergy
open CenteredMomentLiveDomain CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open CenteredMomentFirstSectors CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

def activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) : Finset (Ideal O) :=
  S.filter (fun I => β I≠0)

@[simp] theorem mem_activeSource (S : Finset (Ideal O)) (β : Ideal O → ℂ) (I : Ideal O) :
    I∈activeSource S β ↔ I∈S ∧ β I≠0 := Finset.mem_filter

theorem supportedColumns_active (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    supportedColumns (activeSource S β)=(supportedColumns S).filter (fun I => β I≠0) := by
  ext I
  simp only [supportedColumns,activeSource,Finset.mem_filter]
  tauto

theorem active_sum (S : Finset (Ideal O)) (β F : Ideal O → ℂ) :
    (∑I∈supportedColumns (activeSource S β),β I*F I)=
      ∑I∈supportedColumns S,β I*F I := by
  rw [supportedColumns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with h <;> simp_all

theorem sourceGaussEnergy_active (S : Finset (Ideal O)) (β f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (activeSource S β) β f W K=sourceGaussEnergy S β f W K := by
  unfold sourceGaussEnergy gaussEnergy
  apply tsum_congr
  intro z
  congr 2
  have hp := source_gaussPolynomial (activeSource S β) (fun I => β I*f I) z
  have hq := source_gaussPolynomial S (fun I => β I*f I) z
  rw [hp,hq]
  congr 2
  simpa only [mul_assoc] using active_sum S β (fun I => f I*primaryGaussRow I z)

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    secondRetainedPair I J hI hJ W K T Z ξ else 0 else 0

theorem secondRetainedEnergy_eq_sum (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K T Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*CenteredMomentHeckeColumnWindow.heightCoeff η t I)*
          star (β J*CenteredMomentHeckeColumnWindow.heightCoeff η t J))*
          retainedKernel I J W K T Z ξ := by
  unfold secondRetainedEnergy
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel,dite_eq_left (Finset.mem_filter.mp I.property).2,
    dite_eq_left (Finset.mem_filter.mp J.property).2]

theorem secondRetainedEnergy_active (η : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K T Z ξ : ℝ) :
    secondRetainedEnergy η t (activeSource S β) β W K T Z ξ=
      secondRetainedEnergy η t S β W K T Z ξ := by
  rw [secondRetainedEnergy_eq_sum,secondRetainedEnergy_eq_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : β J=0 <;> simp [hj]

theorem commonLabel_witnesses (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    ∃I∈S,∃J∈S,Supported I ∧ Supported J ∧ β I≠0 ∧ β J≠0 ∧
      commonPart I J=C ∧ commonPart J I=D := by
  obtain ⟨⟨I,J⟩,hp,he⟩ := Finset.mem_image.mp h
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
  obtain ⟨hi,hIs⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hJs⟩ := Finset.mem_filter.mp hj
  obtain ⟨hi,hβi⟩ := mem_activeSource S β I |>.mp hi
  obtain ⟨hj,hβj⟩ := mem_activeSource S β J |>.mp hj
  exact ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

theorem commonLabel_norm_bounds (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (h : (C,D)∈commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) :
    (Ideal.absNorm C:ℝ)≤H ∧ (Ideal.absNorm D:ℝ)≤H := by
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β C D h
  constructor
  · rw [←hC]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le I J hIs.1)).trans (hH I hi hβi)
  · rw [←hD]
    exact (Nat.cast_le.mpr (absNorm_commonPart_le J I hJs.1)).trans (hH J hj hβj)

theorem residualPool_data (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (a : Ideal O)
    (ha : a∈residualPool C hC (supportedColumns (activeSource S β))) :
    C*a∈S ∧ β (C*a)≠0 ∧ Supported (C*a) ∧ a≠0 ∧
      1≤(Ideal.absNorm a:ℝ) ∧ (Ideal.absNorm a:ℝ)≤H/(Ideal.absNorm C:ℝ) := by
  have hm := (mem_residualPool C hC _ a).mp ha
  obtain ⟨hm,hsa⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm,hβ⟩ := (mem_activeSource S β (C*a)).mp hm
  have ha0 : a≠0 := right_ne_zero_of_mul hsa.1
  have hpos := CenteredMomentFirstScale.norm_pos C hC
  have hab := hH (C*a) hm hβ
  rw [map_mul,Nat.cast_mul] at hab
  refine ⟨hm,hβ,hsa,ha0,?_,?_⟩
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ha0)
  · exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hab)

theorem source_energy_active_sectors (τ : HeckeFamily.Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (CenteredMomentHeckeColumnWindow.heightCoeff τ t) W K =
      ∑p∈commonLabels (supportedColumns (activeSource S β))
        (supportedColumns (activeSource S β)),
      ∑q∈pairSector p.1 p.2 (supportedColumns (activeSource S β))
        (supportedColumns (activeSource S β)),
      ((β q.1*CenteredMomentHeckeColumnWindow.heightCoeff τ t q.1)*
        star (β q.2*CenteredMomentHeckeColumnWindow.heightCoeff τ t q.2))*
        CenteredMomentSecondSourceEnergy.secondSourceKernel q.1 q.2 W K := by
  rw [←sourceGaussEnergy_active S β]
  exact CenteredMomentSecondSourceEnergy.source_energy_common_sectors τ t _ β W K hK

end SevenEighths.CenteredMomentActiveSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstRetainedActive -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedActive
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedSector CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentSupportedCorrelation
open CenteredMomentActiveSource (activeSource supportedColumns_active)
local notation "O"=>ActualEisensteinCubic.O

 theorem retained_energy_sum (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ=
      ∑I∈supportedColumns S,∑J∈supportedColumns S,
        ((β I*rowWeight η m A 1 t I)*star (β J*rowWeight η m A 1 t J))*
          CenteredMomentFirstRetainedSector.retainedKernel I J W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedEnergy
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I hI
  conv_rhs=>rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]

 theorem retained_energy_active (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t (activeSource S β) β W K X Z ξ=
      CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S β W K X Z ξ:=by
  rw [retained_energy_sum,retained_energy_sum,supportedColumns_active]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi:β I=0
  · simp [hi]
  · rw [ite_eq_left hi]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj:β J=0 <;> simp [hj]

end SevenEighths.CenteredMomentFirstRetainedActive

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondActiveCount -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondActiveCount
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentRankinScale
open CenteredMomentRankinRadical
local notation "O" => ActualEisensteinCubic.O

def commonShell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) : Finset (Ideal O×Ideal O) :=
  (commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β))).filter
    (fun p=>(Ideal.absNorm (commonRadical p.1 p.2):ℝ)≤Y)

def partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Finset ((Ideal O×Ideal O)×Finset (Ideal O)) :=
  (commonShell S β Y).biUnion (fun p=>(IdealMobiusDivisorSum.primeSupport (commonRadical p.1 p.2)).powerset.image
    (fun U=>(p,U)))

theorem mem_partitionLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (p : (Ideal O×Ideal O)×Finset (Ideal O)) :
    p∈partitionLabels S β Y ↔ p.1∈commonShell S β Y ∧
      p.2⊆IdealMobiusDivisorSum.primeSupport (commonRadical p.1.1 p.1.2) := by
  simp only [partitionLabels,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨q,hq,U,hU,rfl⟩
    exact ⟨hq,hU⟩
  · rintro ⟨hp,hU⟩
    exact ⟨p.1,hp,p.2,hU,rfl⟩

theorem active_common_data (S : Finset (Ideal O)) (β : Ideal O→ℂ) (s : Ideal O)
    (hs : Squarefree s) (hmask : ∀I∈S,β I≠0 → s∣I) (Y : ℝ)
    (p : Ideal O×Ideal O) (hp : p∈commonShell S β Y) :
    p.1≠0 ∧ p.2≠0 ∧ CompletedGauss.primeSupport p.1=CompletedGauss.primeSupport p.2 ∧
      s∣p.1 ∧ s∣p.2 := by
  have hm := (Finset.mem_filter.mp hp).1
  obtain ⟨I,hi,J,hj,hIs,hJs,hβi,hβj,hC,hD⟩ := commonLabel_witnesses S β p.1 p.2 hm
  have hsR := old_mask_dvd_commonRadical s I J hs hIs.1 hJs.1 (hmask I hi hβi) (hmask J hj hβj)
  refine ⟨hC ▸ commonPart_ne_zero I J,hD ▸ commonPart_ne_zero J I,?_,?_,?_⟩
  · rw [←hC,←hD]
    exact commonParts_equal_support I J
  · rw [←hC]
    exact hsR.trans (commonRadical_dvd_commonPart I J)
  · rw [←hD]
    have hr : commonRadical I J=commonRadical J I := by unfold commonRadical;rw [Finset.inter_comm]
    rw [hr] at hsR
    exact hsR.trans (commonRadical_dvd_commonPart J I)

theorem actual_partition_count (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z p s₀:ℝ,1≤Z → 0≤p → p≤B →
      ∀s:Ideal O,Squarefree s → s≠0 → Z^s₀≤(Ideal.absNorm s:ℝ) →
      ∀(S:Finset (Ideal O)) (β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → s∣I) →
      (∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤Z^B) →
      ((partitionLabels S β (Z^p)).card:ℝ)≤C*Z^(p-s₀+δ) := by
  obtain ⟨C,hC,hcount⟩:=source_partition_count B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z p s₀ hZ hp hpB s hs hs0 hNs S β hmask hN
  have hd (v) (hv:v∈partitionLabels S β (Z^p)) :=
    active_common_data S β s hs hmask (Z^p) v.1 ((mem_partitionLabels S β (Z^p) v).mp hv).1
  apply hcount Z p s₀ hZ hp hpB s hs hs0 hNs _
  · intro v hv
    exact ⟨(hd v hv).1,(hd v hv).2.1⟩
  · intro v hv
    exact (hd v hv).2.2.1
  · intro v hv
    exact (hd v hv).2.2.2
  · intro v hv
    exact ((mem_partitionLabels S β (Z^p) v).mp hv).2
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^p) v).mp hv).1).1
  · intro v hv
    exact (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^p) v).mp hv).1).2

end SevenEighths.CenteredMomentSecondActiveCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentOriginalCommonHarmonic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy CenteredMomentAddedZeroUniform
open CenteredMomentSecondActiveCount CenteredMomentActiveSource CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def coefficient (s:Input ι) (R seed:Ideal O) : Ideal O→ℂ:=
  finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)

def sourceRadius (s:Input ι):ℝ:=(∏i,s.hi i)*s.b₁*s.b₂*(s.X₁*s.X₂)*(∏i,s.P i)

omit [DecidableEq ι] in
 theorem original_column_mask (s:Input ι) (R seed I:Ideal O) (h:coefficient s R seed I≠0):
    seed∣I:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero]

omit [DecidableEq ι] in
 theorem original_column_norm (s:Input ι) (R seed I:Ideal O)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (h:coefficient s R seed I≠0):
    I≠0 ∧ (Ideal.absNorm I:ℝ)≤ sourceRadius s:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I h
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    have hh:=(s.support i hn).1
    linarith [s.lo_pos i]
  have hh:=profileCoefficient_product_bound R s.ν s.W s.P s.hi s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    one_ne_zero one_ne_zero rfl s.same_product hz hz₁ hz₂
    (fun i x hx=>(s.support i hx).2) (fun x hx=>s.support₁ hx) (fun x hx=>s.support₂ hx) v hv0
  rw [he] at hh
  simpa only [sourceRadius,map_one,Nat.cast_one,mul_one,div_one] using hh

omit [DecidableEq ι] in
 theorem actual_common_gates (s:Input ι) (R seed:Ideal O) (hs:Squarefree seed)
    (hz₁:s.W₁ 0=0) (hz₂:s.W₂ 0=0) (C D:Ideal O)
    (hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
      (CenteredMomentSourceRow.supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))):
    C≠0 ∧ D≠0 ∧ CompletedGauss.primeSupport C=CompletedGauss.primeSupport D ∧
      seed∣C ∧ seed∣D ∧ (Ideal.absNorm C:ℝ)≤ sourceRadius s ∧ (Ideal.absNorm D:ℝ)≤ sourceRadius s:=by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hp:(C,D)∈commonShell S β (Ideal.absNorm (CenteredMomentRankinRadical.commonRadical C D):ℝ):=
    Finset.mem_filter.mpr ⟨hlabel,le_rfl⟩
  have hh:=active_common_data S β seed hs hm _ (C,D) hp
  have hn:=commonLabel_norm_bounds S β (sourceRadius s)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2) C D hlabel
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hn⟩

omit [DecidableEq ι] in
 theorem actual_original_common_mass (B δ:ℝ) (hB:0≤B) (hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀(s:Input ι),s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀R seed:Ideal O,Squarefree seed → seed≠0 → ∀Y:ℝ,
      (∑v∈partitionLabels (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Y,
        1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hbound⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ s hz₁ hz₂ hcap R seed hs hs0 Y
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s R seed
  have hm (I:Ideal O) (_:I∈S) (hI:β I≠0):seed∣I:=original_column_mask s R seed I hI
  have hN (I:Ideal O) (_:I∈S) (hI:β I≠0):(Ideal.absNorm I:ℝ)≤Z^B:=
    (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap
  apply hbound Z hZ seed hs hs0 (partitionLabels S β Y)
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β Y v).mp hv
    have hh:=active_common_data S β seed hs hm Y v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    have hp:=(mem_partitionLabels S β Y v).mp hv
    exact commonLabel_norm_bounds S β (Z^B) hN v.1.1 v.1.2 (Finset.mem_filter.mp hp.1).1

end SevenEighths.CenteredMomentOriginalCommonHarmonic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSectorRetained -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorFrequency CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def physicalKernel (C D : Ideal O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (j : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ)))*
    (retainedWeight R (normValue j):ℂ)*
      paperRadialFourier W (K*‖eisEmbedding j‖^2/
        ‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2)

theorem physical_sector_summable (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    Summable (sectorFrequency η t S β C D hC hD (physicalKernel C D W K R)) := by
  unfold sectorFrequency
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hcop : IsCoprime (I:Ideal O) (J:Ideal O)
  · simp only [ite_eq_left hcop]
    have hCI : Supported (C*(I:Ideal O)) := (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
    have hDJ : Supported (D*(J:Ideal O)) := (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
    have hk : 0<K/((Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O))) :=
      div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hCI.1) (CenteredMomentFirstScale.norm_pos _ hDJ.1))
    have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hCI hDJ j‖≤
        (Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O)) := by
      have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
        ((supported_span_primaryGenerator_iff _).mpr hCI) ((supported_span_primaryGenerator_iff _).mpr hDJ) j
      simpa only [CenteredMomentSupport.idealCorrelation,primary_span_supported _ hCI,primary_span_supported _ hDJ] using hh
    have hs := weighted_fourier_summable W _ hk
      (fun j=>idealCorrelation (C*I) (D*J) hCI hDJ j)
      (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=>retained_complex_norm R _)
    have he (j : O) : K*‖eisEmbedding j‖^2/‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2=
        (K/((Ideal.absNorm (C*(I:Ideal O)):ℝ)*Ideal.absNorm (D*(J:Ideal O))))*normValue j := by
      rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hCI,primary_norm_sq _ hDJ,normValue_eq_embedding]
      ring
    convert hs.mul_left
      (((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*(I:Ideal O)):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*(J:Ideal O)):ℝ):ℂ)))) using 1
    funext j
    dsimp only [physicalKernel]
    rw [he]
    ring
  · simp only [ite_eq_right hcop,zero_mul]
    exact summable_zero

theorem actual_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    (∑' j : O,sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j)=
      ∑ U : Finset (CommonIndex C D),∑' h : O,
        if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
          sectorFrequency η t S β C D hC hD (physicalKernel C D W K R)
            ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [sectorFrequency_tsum_common η t S β C D hC hD hCD]
  rw [sectorFrequency_tsum_partition η t S β C D hC hD _
    ((physical_sector_summable η t S β C D hC hD W K R hK).comp_injective
      (mul_right_injective₀ (commonFrequencyGenerator_ne_zero C D hC)))]
  exact Finset.sum_congr rfl (fun U _=>sectorFrequency_partition_nonunit η t S β C D hC hD U _)

end SevenEighths.CenteredMomentSecondSectorRetained

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondPhysicalWindow -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorColumns
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic
local notation "O" => ActualEisensteinCubic.O

theorem physical_kernel_window (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (V : Fin 4→ℝ→ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    physicalKernel C D W K R (A*h) I J*
      windows V (secondEffectiveScale C D A K) (normValue h)
        (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) K₀ H₀ A₀ B₀=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log (secondEffectiveScale C D A K/K₀)) (Real.log (normValue h/H₀))
            (Real.log ((Ideal.absNorm I:ℝ)/A₀)) (Real.log ((Ideal.absNorm J:ℝ)/B₀)) := by
  have he := second_frequency_whole_kernel C D I J hC hD hI hJ A h hA hh K hK 1 W V
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
  dsimp only at he
  simp only [mul_one,normValue_eq_embedding] at he ⊢
  have hd : ‖eisEmbedding (CompletedGauss.primaryGenerator (C*I)*
      CompletedGauss.primaryGenerator (D*J))‖^2=
      (Ideal.absNorm (C*I):ℝ)*(Ideal.absNorm (D*J):ℝ) := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hC,hI⟩),
      primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hD,hJ⟩)]
  rw [hd] at he
  unfold physicalKernel
  rw [hd]
  simp only [normValue_eq_embedding]
  convert congrArg (fun x : ℂ=>(retainedWeight R (‖eisEmbedding (A*h)‖^2):ℂ)*x) he using 1 <;> ring

theorem physical_kernel_dyadic (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (n : Fin 4→ℤ) :
    physicalKernel C D W K R (A*h) I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
        dyadicWeight (n 2) (Ideal.absNorm I:ℝ)*dyadicWeight (n 3) (Ideal.absNorm J:ℝ):ℝ):ℂ)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W (fun _=>logAnnulus)
            (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
            (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
            (Real.log (normValue h/dyadicScale (n 1)))
            (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
            (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  rw [actual_product_windows _ _ _ _ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (normValue_pos h hh) (CenteredMomentFirstScale.norm_pos I hI.1)
    (CenteredMomentFirstScale.norm_pos J hJ.1)]
  exact physical_kernel_window C D I J hC hD hI hJ A h hA hh W K R hK _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)

end SevenEighths.CenteredMomentSecondPhysicalWindow

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondDyadicPartition -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicPartition
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O

abbrev Blocks (a b : Fin 4→ℝ) := ∀ i : Fin 4,↥(indices (a i) (b i))

theorem dyadic_product_partition (a b q : Fin 4→ℝ)
    (ha : ∀i,0<a i) (hq : ∀i,q i∈Set.Icc (a i) (b i)) :
    (∑ n : Blocks a b,∏ i : Fin 4,dyadicWeight (n i) (q i))=1 := by
  change (∑ n : (∀ i : Fin 4,↥(indices (a i) (b i))),∏ i : Fin 4,dyadicWeight (n i) (q i))=1
  rw [←Fintype.prod_sum (fun (i : Fin 4) (n : indices (a i) (b i))=>dyadicWeight n (q i))]
  have he (i : Fin 4) : (∑ n : indices (a i) (b i),dyadicWeight n (q i))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun n : ℤ=>dyadicWeight n (q i))]
    exact dyadic_partition_on_interval _ _ _ (ha i) (hq i)
  simp_rw [he]
  simp

theorem physical_kernel_dyadic_partition (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (a b : Fin 4→ℝ) (ha : ∀i,0<a i)
    (hband : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)] : Fin 4→ℝ) i∈Set.Icc (a i) (b i)) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks a b,
        ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
          (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
          (retainedWeight R (normValue (A*h)):ℂ)*
            wholeKernel W (fun _=>logAnnulus)
              (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
              (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
              (Real.log (normValue h/dyadicScale (n 1)))
              (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
              (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  let q : Fin 4→ℝ := ![secondEffectiveScale C D A K,normValue h,
    (Ideal.absNorm I:ℝ),(Ideal.absNorm J:ℝ)]
  have he : (∑ n : Blocks a b,((∏i : Fin 4,dyadicWeight (n i) (q i)):ℝ):ℝ)=1 :=
    dyadic_product_partition a b q ha hband
  calc
    _ = physicalKernel C D W K R (A*h) I J*(1:ℂ) := (mul_one _).symm
    _ = ∑ n : Blocks a b,physicalKernel C D W K R (A*h) I J*
        ((∏i : Fin 4,dyadicWeight (n i) (q i):ℝ):ℂ) := by
      rw [←Finset.mul_sum,←Complex.ofReal_sum,he,Complex.ofReal_one]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Fin.prod_univ_four]
      exact physical_kernel_dyadic C D I J hC hD hI hJ A h hA hh W K R hK (fun i=>n i)

end SevenEighths.CenteredMomentSecondDyadicPartition

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondIdealBlockBound -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondIdealBlockBound
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem logAnnulus_enclosure (x : ℝ) (hx : logAnnulus x≠0) : |x|≤Real.log 4 := by
  have hh := logAnnulus_support hx
  exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩

theorem actual_nonexceptional_block_bound (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ B : ℝ,0≤B ∧ ∀ r : ℝ,0< r →
      ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
        (C D : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C=primeSupport D →
      ∀ (U : Finset (CommonIndex C D)) (R : ℝ) (rows : Finset O)
        (ρ x : O→ℝ) (u : sectorPool C hC.1 S→ℝ) (v : sectorPool D hD.1 S→ℝ)
        (Q : Ideal O) (m : O) (χ₀ : RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
      (∀ z∈rows,nonexceptional η χ₀ Q m A z) →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (H : ℝ),0<H →
      (∀ z : O,0≤(Φ (normValue z/H)).re) →
      (∀ z∈rows,1≤(Φ (normValue z/H)).re) →
      ∀ E₁ E₂ : Ideal O→ℝ,
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₁ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),0≤E₂ L) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) Φ H≤
              (E₁ L*(1+‖w‖)^J₁)^2) →
      (∀ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),∀ χ : RayCharacter,∀ w : ℝ,
        restrictedEnergy (nonexceptional η χ Q m A) Finset.univ (sectorElement D hD.1 S)
          (fun J=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient A (sectorElement D hD.1 S) d) χ J*star (columnPhase logAnnulus (v J) w)) Φ H≤
              (E₂ L*(1+‖w‖)^J₂)^2) →
      (1+r)^decay*‖∑ z∈rows,retainedScalar C D U R z*
        ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤
        B*∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S=>(J:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(E₁ L*E₂ L) := by
  obtain ⟨B,hB,hbound⟩ := whole_kernel_nonexceptional_second_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num)) (fun _ x hx=>logAnnulus_enclosure x hx)
    decay J₁ J₂
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows Φ H hH hΦ hmajor E₁ E₂ hE₁ hE₂ hleft hright
  have hcopD (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun J=>β (D*J)*heightCoeff η t J) u v ρ x η χ₀ Q m hQ hmLam hm2 hrows
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _)
    Φ H hH (by simpa only [normValue_eq_embedding] using hΦ)
    (by simpa only [normValue_eq_embedding] using hmajor) E₁ E₂
    (by simpa only [sectorElement_span] using hE₁) (by simpa only [sectorElement_span] using hE₂)
    (by simpa only [sectorElement_span] using hleft) (by simpa only [sectorElement_span] using hright)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondIdealBlockBound

end

end OAI

end

