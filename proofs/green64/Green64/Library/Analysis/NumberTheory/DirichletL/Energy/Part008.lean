module

public import Green64.Library.OAI.NumberTheory.DirichletL.Energy.NaturalLowSourceBound
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part032
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part026
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part030
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part005

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalSourceAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyNaturalInputMatches
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyInputParentCapacity CenteredMomentAmplificationChildInput
open CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource HeckeDyadic HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSourceRow CenteredMomentRetainedEnergy
open CenteredMomentSourceInputTailUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := energyOriginalSourceDecidableSum

def lowerProduct (N : ℕ) (aslot a : ℝ) : ℝ := (min 1 aslot)^N*a*a

lemma lowerProduct_pos (N : ℕ) {aslot a : ℝ} (hs : 0 < aslot) (ha : 0 < a) :
    0 < lowerProduct N aslot a := by unfold lowerProduct; positivity

section Source
variable (Q : Ideal O) [NeZero Q]
variable (H : Subgroup (O ⧸ Q)ˣ) (hH : RayOrthogonality.globalUnits Q ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters Q H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ)
variable (p : Profiles a b) (ha : 0 < a) (t X₁ X₂ : ℝ)
variable (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "s" => sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
local notation "s₀" => zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂

theorem both_matches :
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s η₀ θ w σ freq W bslot Z ∧
    CenteredMomentAllocatedRayDictionary.Matches Q H hH s₀ η₀ θ w σ freq W bslot Z := by
  constructor <;> constructor <;> intros <;> rfl

lemma source_fields :
    (s).η = state.character ∧ (s₀).η = state.character ∧
    (s).m = state.mask ∧ (s₀).m = state.mask ∧ (s).A = 1 ∧ (s₀).A = 1 ∧
    (s).t = t ∧ (s₀).t = t ∧
    (s).W₁ = p.profile 0 ∧ (s₀).W₁ = p.profile 0 ∧
    (s).W₂ = p.profile 1 ∧ (s₀).W₂ = p.profile 1 ∧
    (s).lower = aslot ∧ (s₀).lower = aslot ∧ (s).upper = bslot ∧ (s₀).upper = bslot := by
  repeat' constructor

lemma slot_fields (i : ι) :
    (s).P i = Z^(w i) ∧ (s₀).P i = Z^(w i) ∧
    (s).lo i = aslot ∧ (s₀).lo i = aslot ∧ (s).hi i = bslot ∧ (s₀).hi i = bslot ∧
    (s).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s₀).M i = profileBound W hW aslot bslot lo hi haslot hWs ∧
    (s).slots i = primePool Q H bslot (Z^(w i)) ∧
    (s₀).slots i = primePool Q H bslot (Z^(w i)) := by repeat' constructor

lemma slot_coefficient (i : ι) (I : Ideal O) :
    (s).toData.coefficient i I = idealCoeff (relativeCharacter Q H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (freq i) I ∧
    (s₀).toData.coefficient i I = (s).toData.coefficient i I := ⟨rfl, rfl⟩

lemma rectangles :
    (s).X₁ = X₁ ∧ (s).X₂ = X₂ ∧ (s).Y₁ = X₁ ∧ (s).Y₂ = X₂ ∧
    (s₀).X₁ = X₁ ∧ (s₀).X₂ = X₂ ∧
    (s₀).Y₁ = smallScale b ∧ (s₀).Y₂ = X₁*X₂/smallScale b ∧
    (s₀).Y₁*(s₀).Y₂ = X₁*X₂ := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact (s₀).same_product

lemma raw_volume : volume s = X₁*X₂*∏ i, Z^(w i) ∧ volume s₀ = volume s := ⟨rfl,rfl⟩

lemma volume_log (hZ : 1 < Z) :
    Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i ∧
    Real.logb Z (volume s₀) = Real.logb Z X₁ + Real.logb Z X₂ + ∑ i, w i := by
  have hh := input_volume_log s Z
  change Real.logb Z (volume s) = Real.logb Z X₁ + Real.logb Z X₂ +
    ∑ i, Real.logb Z (Z^(w i)) at hh
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  exact ⟨hh,hh⟩

theorem capacity_admission (hZ : 1 < Z) (hw : ∀ i, 0 ≤ w i) (κ : ℝ)
    (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width) :
    (∀ i, 1 ≤ (s).P i ∧ 1 ≤ (s₀).P i) ∧
    volume s ≤ Z^state.width ∧ volume s₀ ≤ Z^state.width := by
  have hPi : ∀ i, 1 ≤ (s).P i := fun i => Real.one_le_rpow hZ.le (hw i)
  have hv := original_volume_cap s Z κ state.width hZ hκ hPi (by
    change length Z X₁ + length Z X₂ + 6*κ*(∑ i, Real.logb Z (Z^(w i))) ≤ _
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap)
  exact ⟨fun i => ⟨hPi i,hPi i⟩,hv,hv⟩

theorem low_admission (hZ : 1 < Z)
    (hlow : length Z X₁ + length Z X₂ + ∑ i, w i ≤ 5*state.width/6) :
    Real.logb Z (volume s) ≤ 5*state.width/6 ∧
    Real.logb Z (volume s₀) ≤ 5*state.width/6 := by
  have hv := volume_log Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂ hZ
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor <;> linarith [hv.1,hv.2]

theorem lower_product_admission (N : ℕ) (hN : Fintype.card ι ≤ N) :
    0 < lowerProduct N aslot a ∧
    lowerProduct N aslot a ≤ (∏ i, (s).lo i)*a*a ∧
    lowerProduct N aslot a ≤ (∏ i, (s₀).lo i)*a*a := by
  have hh := lower_product s N aslot haslot hN (fun _ => le_rfl)
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le
  exact ⟨lowerProduct_pos N haslot ha,hb,hb⟩

theorem profile_control_admission (N : ℕ) (hN : Fintype.card ι ≤ N)
    (S : Finset (ℕ×ℕ)) :
    (plainControl s (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 ∧
    (plainControl s₀ (p.profile 0) (p.profile 1))^2 ≤
      (profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2 := by
  have hh := plain_control_sq_le s p S N _
    (profileBound_ge_one W hW aslot bslot lo hi haslot hWs) hN (fun _ => le_rfl)
  exact ⟨hh,hh⟩

theorem normalized_zero_source (R : Ideal O) (z : O) :
    positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ =
    (Real.sqrt (volume s) : ℂ)⁻¹ *
      ∑ I ∈ finiteColumns (Fintype.piFinset (s₀).pools),
        CenteredMomentOriginalCommonHarmonic.coefficient s₀ R 1 I * rowWeight state.character fixedBadMask 1 z t I := by
  have hh := normalized_input_difference s₀ R z
  have hz := comparison_row_zero s
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero _ a b ha (p.support 1)) R z
  change positiveSlotRow state.character (fixedBadMask*idealGenerator R) 1 z
      (p.profile 0) (p.profile 1) (s).slots (s).toData.coefficient (s).P t X₁ X₂ -
    positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
      (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = _ at hh
  change positiveSlotRow (s).η (fixedBadMask*idealGenerator R) 1 z (s).W₁ (s).W₂ (s).slots
    (s).toData.coefficient (s).P (s).t (s₀).Y₁ (s₀).Y₂ = 0 at hz
  rw [hz,sub_zero] at hh
  exact hh

end Source

theorem radial_admission {Z Bmask bΦ : ℝ} (state : NaturalState Z Bmask bΦ) :
    1 ≤ state.radial.scale ∧ state.radial.scale⁻¹ ≤ 1 ∧
    state.radial.scale⁻¹ ≤ Z^state.width := by
  have hs : 1 ≤ state.radial.scale := by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  have hi := inv_le_one_of_one_le₀ hs
  exact ⟨hs,hi,hi.trans (Real.one_le_rpow state.base_ge_one state.width_nonneg)⟩

theorem original_scale_caps {Z X₁ X₂ M L κ : ℝ} (w : ι → ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hw : ∀ i, 0 ≤ w i) (hκ : 1/6 ≤ κ)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ M)
    (hM : M ≤ L) : X₁ ≤ Z^L ∧ X₂ ≤ Z^L := by
  have hn : 0 ≤ 6*κ*(∑ i, w i) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => hw i))
  have h1 := raw_log_le_length Z X₁ hZ hX₁
  have h2 := raw_log_le_length Z X₂ hZ hX₂
  constructor
  · apply (Real.logb_le_iff_le_rpow hZ hX₁).mp
    linarith [length_nonneg Z X₂ hZ]
  · apply (Real.logb_le_iff_le_rpow hZ hX₂).mp
    linarith [length_nonneg Z X₁ hZ]

theorem eventually_scale_admission (b L ε : ℝ) (hL : 0 ≤ L) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
    ∀ (Q : Ideal O) [NeZero Q] (H : Subgroup (O ⧸ Q)ˣ)
      (hH : RayOrthogonality.globalUnits Q ≤ H) (η₀ : Character)
      (θ : ι → RayQuotient.Characters Q H),
    ∀ (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
      (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot),
    ∀ (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi),
    ∀ (Bmask bΦ a : ℝ) (state : NaturalState Z Bmask bΦ) (p : Profiles a b)
      (ha : 0 < a) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (κ : ℝ),
    (∀ i, 0 ≤ w i) → 1/6 ≤ κ → state.width ≤ L →
    length Z X₁ + length Z X₂ + 6*κ*(∑ i, w i) ≤ state.width →
    let s := sourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    let s₀ := zeroSourceInput Q H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha t X₁ X₂ hX₁ hX₂
    (s).X₁ ≤ Z^L ∧ (s).X₂ ≤ Z^L ∧ (s).Y₁ ≤ Z^L ∧ (s).Y₂ ≤ Z^L ∧
    (s₀).X₁ ≤ Z^L ∧ (s₀).X₂ ≤ Z^L ∧
    (s₀).Y₁ ≤ Z^(2*L+ε) ∧ (s₀).Y₂ ≤ Z^(2*L+ε) := by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1 : ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ Q _ H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ hw hκ hM hcap
  dsimp only
  have hx := original_scale_caps w hZ hX₁ hX₂ hw hκ hcap hM
  refine ⟨hx.1,hx.2,hx.1,hx.2,hx.1,hx.2,?_,?_⟩
  · exact (smallScale_le_one b).trans (Real.one_le_rpow hZ.le (by positivity))
  · change X₁*X₂/smallScale b ≤ _
    have hp : X₁*X₂ ≤ Z^(2*L) := by
      have hh := mul_le_mul hx.1 hx.2 hX₂.le (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) L).le
      rw [←Real.rpow_add (zero_lt_one.trans hZ)] at hh
      simpa only [two_mul] using hh
    unfold smallScale
    rw [div_div_eq_mul_div,div_one]
    exact (mul_le_mul hp hc (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le).trans_eq
        (Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

end SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=>balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hx (X:ℝ):X≤Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=>Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving (fun _=>hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=>le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssembly
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
lemma low_restrict (W:ℝ→ℂ)(bslot a b bΦ Bmask L L' Lslot lo hi Mcap d d' κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hZ:1≤Z)(hL:L'≤L)(hd:d≤d')(hC:0≤C)
    (h:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap d κ Z η₀ Q degree S C):
    PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L' Lslot lo hi
      Mcap d' κ Z η₀ Q degree S C:=by
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
  have hscale:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale) hcap hlow
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (by have hh:=diagonalControl_nonneg s.radial.profile;positivity)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0<d ∧ 0≤L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0<Cu ∧ 0<Cr ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap (min du dr) du κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) (min_le_left _ _) hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap (min du dr) dr κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) (min_le_right _ _) hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · left
    exact hzu.2 Lslot κ η₀ Q K hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 Lslot κ η₀ Q K hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.CenteredMomentEnergyPositiveHighAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParameters
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma actual_width_le (hZ:1<Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1<Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤ s.width:=by
  have hv:0<CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=>le_rfl)

omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤N)(hZ:1<Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0<s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=>le_rfl)
  have hconst:0≤Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst

end SevenEighths.CenteredMomentEnergyPositiveHighParameters

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePower CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSource CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

theorem fixed_fields :
    (balancedSource).lower=aslot ∧ (balancedSource).upper=bslot ∧
    (balancedSource).b₁=b ∧ (balancedSource).b₂=b ∧
    (balancedSource).W₁=p.profile 0 ∧ (balancedSource).W₂=p.profile 1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧ (balancedSource).t=t ∧
    (∀i,(balancedSource).lo i=aslot) ∧ (∀i,(balancedSource).hi i=bslot) ∧
    (∀i,(balancedSource).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (∀i,(balancedSource).P i=Z^(w i)) := by
  repeat' constructor
  all_goals intro i;rfl

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=>le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

lemma exact_log_volume (hZ:1<Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem four_upper_scales (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤L) :
    (balancedSource).X₁≤Z^L ∧ (balancedSource).X₂≤Z^L ∧
    (balancedSource).Y₁≤Z^L ∧ (balancedSource).Y₂≤Z^L := by
  have hp:0<Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=>hw i))
  have hxy:X₁*X₂≤volume balancedSource:=by
    change X₁*X₂≤X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

theorem four_lower_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem state_capacity_packet (κ L:ℝ)(hZ:1<Z)(hw:∀i,0≤w i)(hκ:3/4≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤L) :
    1≤ s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤ s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤ s.width ∧
    volume balancedSource≤Z^s.width ∧ Real.logb Z (volume balancedSource)≤ s.width ∧
    volume balancedSource≤Z^L ∧
    (s.puncture.absNorm:ℝ)≤Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLiveBounded CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0<aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)

open CenteredMomentEnergyPositiveHighSource

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e→ 0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=>bslot) a b Mcap εdiag ξ saving (fun _=>hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=>le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+e+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSourceBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBounded
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBounded CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0<d ∧ 0≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧0<Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0<Cu ∧ 0<Cr ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e→ 0≤K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+e+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+e+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hLuUpper,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,max_le hLuUpper hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) le_rfl hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) le_rfl hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · left
    exact hzu.2 e Lslot κ η₀ Q K he hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 e Lslot κ η₀ Q K he hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBounded CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

open CenteredMomentEnergyPositiveHighAssemblyBounded CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hbslot:0≤bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤w i)→ (∀i,w i≤Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤hi),
      0≤height→ (∀i,|freq i|≤height)→ 3/4≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) →
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤
          Cmass*(p.control Smass)^2*(1+|t|+height)^Jmass*Z^(s.width+emass)) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|+height)^Jout*Z^(s.width+efinal) :=by
  obtain ⟨d,L,hd,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hstage⟩:=
    actual_high_source_split (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨L,hL,hLupper,Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,hbound⟩:=hstage degree S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=(profileBound Wslot hcSlot aslot bslot lo hi haslot hsSlot)^(2*Fintype.card α)
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Lslot κ η₀ Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ s hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z^(s.width+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z^(s.width+ej)≤F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej≤ s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by dsimp [Jout];omega
  have hjr:Jr≤Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced|⟨hfour,hsource⟩
  · change _≤Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z^(s.width+e+ε) at hunbalanced
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        CenteredMomentAmplificationChildInput.volume inp≤Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
        (Fintype.card α) le_rfl U
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(s.width+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          calc
            _ = (c*P*A*(p.control U)^2*Z^(s.width+efinal))*1 := by ring
            _ ≤ (c*P*A*(p.control U)^2*Z^(s.width+efinal))*
                (1+|t|+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
            _ = c*P*A*F := by dsimp [F]; ring
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|+height)^Jout*Z^(s.width+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyPositiveHighBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveHighSource (balancedInput)
open CenteredMomentEnergyPositiveHighBound CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyPositiveHighAssembly (low_restrict)
def PhysicalHighAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    5*state.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
    let inp:=balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂;
    (Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ/volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

def PositiveHighAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ rho≤ s.width→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i)→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem actual_high_stage_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hrho:0< rho)(hε:0<ε)(hMcap:0≤Mcap)(hBmask:0≤Bmask)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(L Lslot κ e emass efinal:ℝ)(η₀:Character)(Q:Ideal O)(K Cphysical:ℝ),
      3/4≤κ→0≤e→0≤K→0≤Cphysical→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
        Lslot lo hi Mcap e κ Z η₀ Q degree S K→
      PhysicalHighAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ emass Z ha Ψ η₀ Q Smass Jmass Cphysical→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap efinal κ Z η₀ Q
        Jout U (Cfixed*(K+Cphysical+1)):=by
  have hfixed (T:Finset α):=actual_high_from_physical (α:=T) M H hH W aslot bslot lo hi
    haslot hWs hW a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε
    hMcap hBmask hbslot hεdiag hξ
  choose Lj hLj hLjcap Ψ hΨs hΨn hj using hfixed
  refine ⟨Ψ,hΨs,hΨn,?_⟩
  intro degree S Jmass Smass
  have hall (T:Finset α):=hj T degree S Jmass Smass
  choose Jj Uj Cj hCj hbound using hall
  let Jout:ℕ:=∑T:Finset α,Jj T
  let U:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset α):Jj T≤Jout:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hUU (T:Finset α):Uj T⊆U:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ T,hx⟩
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  have hevent:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro L Lslot κ e emass efinal η₀ Q K Cphysical hκ he hK hCphysical hefinal hmassFinal
    hdiagFinal htailFinal hlow hmass
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hlowT:=CenteredMomentEnergyLowBandSubtype.positiveLowAt_subtype (α:=α) M H hH T
    W bslot a b bΦ Bmask (Mcap+Bmask+rho/100) Lslot lo hi Mcap e κ Z η₀ Q degree S K hlow
  have hlowLj:=low_restrict (α:=T) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
    (Lj T) Lslot lo hi Mcap e e κ Z η₀ Q degree S K hZ1.le (hLjcap T) le_rfl hK hlowT
  have hphys:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo
    hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hh:=(hZ T).2 e emass efinal Lslot κ η₀ Q K Cphysical he hK hCphysical
    hefinal hmassFinal hdiagFinal htailFinal hlowLj θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ state hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcapacity hphys
  have hc:=hCC T
  have hp:=profile_control_mono p (hUU T)
  have hp0:=p.control_nonneg (Uj T)
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hpow:=pow_le_pow_right₀ hbase (hJJ T)
  have hd:=diagonalControl_nonneg state.radial.profile
  have hz:0≤Z:=zero_le_one.trans hZ1.le
  apply hh.trans
  gcongr

omit [Fintype α] [DecidableEq α] in
theorem positive_from_stages
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(J:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hold:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q J S C)
    (hlow:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C)
    (hhigh:PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hsmall:s.width≤ rho
  · exact hold T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hsmall p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hl:length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6
  · exact hlow T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity hl
  exact hhigh T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ (le_of_not_ge hsmall) hs
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity (le_of_not_ge hl)

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveLowBandSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowBandSource
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PhysicalLowAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0<a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤hi,
    0≤height→(∀i,|freq i|≤height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,
    X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*state.width/6→
    physicalMass (zeroSourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)
      state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ /
      volume (sourceInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂)≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical:ℝ),
      1/6≤κ→0≤Cphysical→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1))→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)):=by
  have hfixed (T:Finset α):=natural_low_source_bound (ι:=T) W hW aslot bslot lo hi
    a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ hMcap hεdiag hξ
  choose Ψ hΨs hΨn Cj hCj hbound using hfixed
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical hκ hCphysical he hsave hold hmass
  have hpositive:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cphysical+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidth
      p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    by_cases hsmall:state.width≤ rho
    · exact hold T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
        state hQ hsmall p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
    have hp:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      state hQ (le_of_not_ge hsmall) hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
    have hh:=(hZ T).2 M H hH η₀ θ w σ freq hw (fun i=>⟨hσlo i,hσhi i⟩)
      Bmask state p t X₁ X₂ hX₁ hX₂ κ hκ (hcapacity.trans hwidth)
      S J Cphysical height e hCphysical hheight he hsave hp
    have hc:=hCC T
    have hd:=diagonalControl_nonneg state.radial.profile
    have hz:0≤Z:=zero_le_one.trans hZ1.le
    apply hh.trans
    gcongr
  exact ⟨hpositive,CenteredMomentEnergyLowBandEmpty.positive_low_zero (α:=α) M H hH
    W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J (insert (0,0) S)
    (Cfixed*(Cphysical+1)) hpositive⟩

end SevenEighths.CenteredMomentEnergyPositiveLowBandSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PositiveLowSourceControlled -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyPositiveLowBandSource (PhysicalLowAt)
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_stages_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ Mcap εdiag ξ saving:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hMcap:0≤Mcap)
    (hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧∃Cfixed:ℝ,0<Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Lslot rho κ e:ℝ)(η₀:Character)(Q:Ideal O)(S:Finset (ℕ×ℕ))(J:ℕ)(Cphysical Cprevious:ℝ),
      1/6≤κ→0≤Cphysical→0≤Cprevious→εdiag≤e→-saving≤e→
      PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
        J S Cprevious→
      PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cphysical→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q
        J (insert (0,0) S) (Cfixed*(Cphysical+1)+Cprevious) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap e Z J (insert (0,0) S)
        (Cfixed*(Cphysical+1)+Cprevious) :=by
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hbound⟩:=
    CenteredMomentEnergyPositiveLowBandSource.actual_low_stages_from_physical (α:=α) M H hH
      W hW aslot bslot lo hi a b bΦ Mcap εdiag ξ saving haslot hWs hbslot ha hb hbΦ
      hMcap hεdiag hξ
  refine ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot rho κ e η₀ Q S J Cphysical Cprevious hκ hCphysical hCprevious he hsave hold hmass
  let Cm:=Cphysical+Cprevious/Cfixed
  have hdiv:0≤Cprevious/Cfixed:=div_nonneg hCprevious hCfixed.le
  have hCm:0≤Cm:=by dsimp [Cm];positivity
  have hcc:Cphysical≤Cm:=by dsimp [Cm];linarith
  have heq:Cfixed*(Cm+1)=Cfixed*(Cphysical+1)+Cprevious:=by
    dsimp [Cm]
    field_simp
    ; ring
  have hprev:Cprevious≤Cfixed*(Cm+1):=by
    rw [heq]
    have hh:0≤Cfixed*(Cphysical+1):=by positivity
    linarith
  have hold':PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q
      J (insert (0,0) S) (Cfixed*(Cm+1)):=
    positiveAt_transport (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z
      a b bΦ Bmask L rho e η₀ Q J J S (insert (0,0) S) Cprevious (Cfixed*(Cm+1)) hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.subset_insert _ _)
      hCprevious hprev hold
  have hmass':PhysicalLowAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
      a b bΦ Bmask L Lslot rho Mcap κ ξ e Z ha Ψ η₀ Q S J Cm:=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hlo hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤Z:=zero_le_one.trans hZ.1.le
    apply hh.trans
    gcongr
  have hh:=hZ.2 Bmask L Lslot rho κ e η₀ Q S J Cm hκ hCm he hsave hold' hmass'
  simpa only [heq] using hh

end SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.SourceInputReindexGates -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSecondInputGates CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstChildProfileControl CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma mass_map (e : α≃β) (s : Input α) : mass (reindex e s)=mass s :=
  (controls_map e s).1

lemma nominal_map (e : α≃β) (s : Input α) (K : ℝ) :
    nominal (reindex e s) K=nominal s K := by
  unfold nominal
  rw [volume_map]

theorem ready_map (e : α≃β) (s : Input α) (R : Ideal O) (K Z ξ B : ℝ)
    (h : Ready s R K Z ξ B) : Ready (reindex e s) R K Z ξ B := by
  rcases h with ⟨hR0,hK,hV,hs0,hs,hq,hr,hn0,hn,hf0,hf⟩
  exact ⟨hR0,hK,by simpa only [volume_map] using hV,
    by simpa only [sourceRadius_map] using hs0,
    by simpa only [sourceRadius_map] using hs,hq,hr,
    by simpa only [nominal_map] using hn0,
    by simpa only [nominal_map] using hn,
    by simpa only [nominal_map] using hf0,
    by simpa only [nominal_map] using hf⟩

section Dictionary
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem matches_map (e : α≃β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (reindex e s) η₀
      (θ ∘ e.symm) (w ∘ e.symm) (σ ∘ e.symm) (freq ∘ e.symm) W bslot Z :=
  ⟨fun i I=>h.character (e.symm i) I,fun i y=>h.profile (e.symm i) y,
    fun i=>h.pool (e.symm i),fun i=>h.scale (e.symm i)⟩

theorem matches_child (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) W bslot Z :=
  ⟨fun i I=>h.character i.val I,fun i y=>h.profile i.val y,
    fun i=>h.pool i.val,fun i=>h.scale i.val⟩

omit [Fintype α] [Fintype β] in
theorem imageInput_matches (e : α↪β) (T : Finset α) (s : Input T) (η₀ : Character)
    (θ : T→RayQuotient.Characters M H) (w σ freq : T→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (imageInput e T s) η₀
      (θ ∘ (Finset.equivMap e T).symm) (w ∘ (Finset.equivMap e T).symm)
      (σ ∘ (Finset.equivMap e T).symm) (freq ∘ (Finset.equivMap e T).symm) W bslot Z :=
  matches_map M H hH (Finset.equivMap e T) s η₀ θ w σ freq W bslot Z h

omit [Fintype β] in
theorem allocatedImage_matches (e : α↪β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (allocatedImage e s C R B τ t) η₀
      (fun i=>θ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>w ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>σ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>freq ((Finset.equivMap e (liveIndices B.val)).symm i).val) W bslot Z :=
  imageInput_matches M H hH e (liveIndices B.val) (child s C R B τ t) η₀
    _ _ _ _ W bslot Z (matches_child M H hH s η₀ θ w σ freq W bslot Z h C R B τ t)
end Dictionary

theorem active_map (e : α≃β) (s : Input α) :
    activeInput (reindex e s)=reindex e (activeInput s) := rfl

lemma allocationLabels_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (allocationLabels s.pools C).image (tupleMap e)=
      allocationLabels (reindex e s).pools C := by
  unfold allocationLabels
  rw [←pools_map,Finset.image_image,Finset.image_image]
  congr 1

lemma actualAllocations_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (actualAllocations s.pools C).image (tupleMap e)=
      actualAllocations (reindex e s).pools C := by
  change ((allocationLabels s.pools C).filter (fun B=>finiteTupleProduct B=C)).image (tupleMap e)=
    (allocationLabels (reindex e s).pools C).filter (fun B=>finiteTupleProduct B=C)
  rw [←allocationLabels_map e s C,Finset.filter_image]
  simp only [tupleMap_product]

def allocationEquiv (e : α≃β) (s : Input α) (C : Ideal O) :
    actualAllocations s.pools C ≃ actualAllocations (reindex e s).pools C where
  toFun B := ⟨tupleMap e B.val,by
    rw [←actualAllocations_map]
    exact Finset.mem_image.mpr ⟨B.val,B.property,rfl⟩⟩
  invFun B := ⟨(tupleMap e).symm B.val,by
    have hh : B.val∈(actualAllocations s.pools C).image (tupleMap e) := by
      simpa only [actualAllocations_map e s C] using B.property
    obtain ⟨v,hv,hvB⟩:=Finset.mem_image.mp hh
    simpa only [←hvB,Equiv.symm_apply_apply] using hv⟩
  left_inv B := Subtype.ext ((tupleMap e).symm_apply_apply B.val)
  right_inv B := Subtype.ext ((tupleMap e).apply_symm_apply B.val)

@[simp] lemma allocationEquiv_val (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) :
    (allocationEquiv e s C B).val=tupleMap e B.val := rfl

def liveEquiv (e : α≃β) (B : Tuple α) : liveIndices B ≃ liveIndices (tupleMap e B) where
  toFun i := ⟨e i.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.symm_apply_apply] using (Finset.mem_filter.mp i.property).2⟩
  invFun j := ⟨e.symm j.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl]
      using (Finset.mem_filter.mp j.property).2⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

@[simp] lemma liveEquiv_val (e : α≃β) (B : Tuple α) (i : liveIndices B) :
    (liveEquiv e B i).val=e i.val := rfl

@[simp] lemma liveEquiv_symm_val (e : α≃β) (B : Tuple α)
    (j : liveIndices (tupleMap e B)) : ((liveEquiv e B).symm j).val=e.symm j.val := rfl

theorem child_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    reindex (liveEquiv e B.val) (child s C R B τ t)=
      child (reindex e s) C R (allocationEquiv e s C B) τ t := rfl

theorem child_mass_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      mass (child s C R B τ t) := by
  exact mass_map (liveEquiv e B.val) (child s C R B τ t)

theorem child_volume_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      volume (child s C R B τ t) := by
  exact volume_map (liveEquiv e B.val) (child s C R B τ t)

theorem child_normalized_map (e : α≃β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (reindex e s) C R seed (allocationEquiv e s C B) τ t W K=
      childNormalizedGaussSource s C R seed B τ t W K := by
  exact normalizedGaussSource_map (liveEquiv e B.val) (child s C R B τ t) (R*C) seed W K

theorem active_allocation_pullback (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val := by
  exact ⟨(allocationEquiv e (activeInput s) C).symm B,
    congrArg Subtype.val ((allocationEquiv e (activeInput s) C).apply_symm_apply B)⟩

omit [Fintype α] [Fintype β] in
theorem imageInput_ready (e : α↪β) (T : Finset α) (s : Input T)
    (R : Ideal O) (K Z ξ B : ℝ) (h : Ready s R K Z ξ B) :
    Ready (imageInput e T s) R K Z ξ B :=
  ready_map (Finset.equivMap e T) s R K Z ξ B h

omit [Fintype β] in
theorem allocatedImage_ready (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t K Z ξ bound : ℝ)
    (h : Ready (child s C R B τ t) (R*C) K Z ξ bound) :
    Ready (allocatedImage e s C R B τ t) (R*C) K Z ξ bound :=
  imageInput_ready e (liveIndices B.val) (child s C R B τ t) (R*C) K Z ξ bound h

omit [Fintype α] [Fintype β] in
lemma imageInput_mass (e : α↪β) (T : Finset α) (s : Input T) :
    mass (imageInput e T s)=mass s := mass_map (Finset.equivMap e T) s

omit [Fintype β] in
lemma allocatedImage_mass (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (allocatedImage e s C R B τ t)=mass (child s C R B τ t) :=
  imageInput_mass e (liveIndices B.val) (child s C R B τ t)

omit [Fintype β] in
lemma allocatedImage_volume (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (allocatedImage e s C R B τ t)=volume (child s C R B τ t) :=
  volume_map (Finset.equivMap e (liveIndices B.val)) (child s C R B τ t)

lemma source_fields_map (e : α≃β) (s : Input α) :
    (reindex e s).η=s.η ∧ (reindex e s).m=s.m ∧ (reindex e s).A=s.A ∧
    (reindex e s).t=s.t ∧ (reindex e s).W₁=s.W₁ ∧ (reindex e s).W₂=s.W₂ ∧
    (reindex e s).X₁=s.X₁ ∧ (reindex e s).X₂=s.X₂ ∧
    (reindex e s).Y₁=s.Y₁ ∧ (reindex e s).Y₂=s.Y₂ ∧
    (reindex e s).lower=s.lower ∧ (reindex e s).upper=s.upper ∧
    (reindex e s).plain₁=s.plain₁ ∧ (reindex e s).plain₂=s.plain₂ ∧
    (reindex e s).rows=s.rows ∧ (reindex e s).weight=s.weight := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem active_child_pullback (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) (τ : Character) (t : ℝ) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val ∧
      mass (child (activeInput (reindex e s)) C R B τ t)=
        mass (child (activeInput s) C R A τ t) ∧
      volume (child (activeInput (reindex e s)) C R B τ t)=
        volume (child (activeInput s) C R A τ t) ∧
      ∀(seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        childNormalizedGaussSource (activeInput (reindex e s)) C R seed B τ t W K=
          childNormalizedGaussSource (activeInput s) C R seed A τ t W K := by
  obtain ⟨A,hA⟩:=(allocationEquiv e (activeInput s) C).surjective B
  subst B
  exact ⟨A,rfl,child_mass_map e (activeInput s) C R A τ t,
    child_volume_map e (activeInput s) C R A τ t,
    fun seed W K=>child_normalized_map e (activeInput s) C R seed A τ t W K⟩

end SevenEighths.CenteredMomentEnergySourceInputReindexGates

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.StageMonotonicity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyStageMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentEnergyZeroGrowth
local notation "O"=>HeckeFamily.O

theorem zeroLowAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroLowAt Q a b radial mask L Mcap eps Z J S C):
    ZeroLowAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hlow
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hlow
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

theorem zeroGrowthAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroGrowthAt Q a b radial mask L Mcap eps Z J S C):
    ZeroGrowthAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(max s.width (length Z X₁+length Z X₂)+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(max s.width (length Z X₁+length Z X₂)+eps)≤Z^(max s.width (length Z X₁+length Z X₂)+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveLowAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveLowAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveLowAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlow
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlow
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

omit [Fintype α] [DecidableEq α] in
theorem positiveHighAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi rho Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' rho' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(hrho:rho≤ rho')(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveHighAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi rho Mcap eps κ Z η₀ Q J S C):
    PositiveHighAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi rho' Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hrho.trans hwidthLo) (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity hlarge
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyStageMonotonicity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CappedSuccessorPacking -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedSuccessorPacking
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceBound CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem certified_from_stages
    (W:ℝ→ℂ)(bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (ha:0<a)(hmask:0≤Bmask)(hMcap:0≤Mcap)(hκ:0≤κ)(hε:0<ε)(k:ℕ)
    (ez el eh:ℝ)
    (hez:ez≤ stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (hel:el≤ stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (heh:eh≤ stageLoss Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k)
    (hzero:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) ez Z J S C)
    (hlow:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1)) (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) el κ Z η₀ Q J S C)
    (hhigh:∃J:ℕ,∃S:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        PositiveHighAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (lengthAt Mcap Bmask L ε (k+1)) (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε k)
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1)) eh κ Z η₀ Q J S C):
    CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hr:0< reserve Mcap Bs ε:=(bounds Mcap Bs κ ε hMcap hBs hκ hε).2.2.2.1
  have hlower:lowerAt a b Mcap ε k≤lowerAt a b Mcap ε (k+1):=
    CenteredMomentEnergyProfiles.lower_antitone a b ha (by unfold remaining;omega)
  have hlength:lengthAt Mcap Bmask L ε (k+1)≤lengthAt Mcap Bmask L ε k:=
    range_mono Mcap Bmask L hMcap hmask (by unfold remaining;omega)
  have hloss:stageLoss Mcap Bs ε k≤ stageLoss Mcap Bs ε (k+1):=by
    unfold stageLoss
    rw [loss_succ]
    linarith
  obtain ⟨Jold,Sold,hold⟩:=hold
  obtain ⟨Jz,Sz,hzero⟩:=hzero
  obtain ⟨Jl,Sl,hlow⟩:=hlow
  obtain ⟨Jh,Sh,hhigh⟩:=hhigh
  let J:=Jold+Jz+Jl+Jh
  let S:=Sold∪Sz∪Sl∪Sh
  have hJo:Jold≤J:=by dsimp [J];omega
  have hJz:Jz≤J:=by dsimp [J];omega
  have hJl:Jl≤J:=by dsimp [J];omega
  have hJh:Jh≤J:=by dsimp [J];omega
  have hSo:Sold⊆S:=by intro x hx;simp [S,hx]
  have hSz:Sz⊆S:=by intro x hx;simp [S,hx]
  have hSl:Sl⊆S:=by intro x hx;simp [S,hx]
  have hSh:Sh⊆S:=by intro x hx;simp [S,hx]
  refine ⟨J,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Coz,Cop,hCoz,hCop,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,hCz,hzero⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cl,hCl,hlow⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ch,hCh,hhigh⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
  let Cp:=Cop+Cl+Ch
  have hCp:0<Cp:=by dsimp [Cp];linarith
  have hCop':Cop≤Cp:=by dsimp [Cp];linarith
  have hCl':Cl≤Cp:=by dsimp [Cp];linarith
  have hCh':Ch≤Cp:=by dsimp [Cp];linarith
  refine ⟨Cz,Cp,hCz,hCp,?_⟩
  filter_upwards [hold,hzero,hlow,hhigh] with Z hold hz hl hh
  refine ⟨hold.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      Jz J Sz S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      hez hJz hSz hCz.le le_rfl hz
  · apply positive_from_stages (α:=α) M H hH W bslot _ _ _ _ _ _ _ _
      (bandWidth Mcap Bs ε k) _ _ κ Z η₀ Q J S Cp
    · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ η₀ Q Jold J Sold S Cop Cp hold.1.le
        hlower le_rfl le_rfl le_rfl hlength le_rfl hloss hJo hSo hCop.le hCop' hold.2.2
    · exact positiveLowAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ η₀ Q Jl J Sl S Cl Cp hold.1.le
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl hel hJl hSl hCl.le hCl' hl
    · exact positiveHighAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ _ κ Z
        _ _ _ _ _ _ _ _ η₀ Q Jh J Sh S Ch Cp hold.1.le
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl heh hJh hSh hCh.le hCh' hh

end SevenEighths.CenteredMomentEnergyCappedSuccessorPacking

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroBalancedDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedDictionary
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyNaturalInputMatches
open CenteredMomentAmplificationChildInput CenteredMomentFirstSourceReduction
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "zeroInput"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem balanced_matches (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)
    (w σ freq:Fin 0→ℝ)(W:ℝ→ℂ)(bslot:ℝ):
    CenteredMomentAllocatedRayDictionary.Matches M H hH zeroInput η₀ θ w σ freq W bslot Z:=by
  constructor <;> intro i <;> exact Fin.elim0 i

theorem balanced_eq_positive_empty (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)
    (w σ freq:Fin 0→ℝ):
    zeroInput=CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
      (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
      (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
      s p ha t X₁ X₂ hX₁ hX₂:=by
  unfold CenteredMomentEnergyZeroReferencePhysical.balancedInput
    CenteredMomentEnergyPositiveHighSource.balancedInput input naturalInput naturalData completeInput
  congr 5 <;> exact Subsingleton.elim _ _

variable (η₀:Character)(θ:Fin 0→RayQuotient.Characters M H)(w σ freq:Fin 0→ℝ)
def positiveEmptyInput : Input (Fin 0):=
  CenteredMomentEnergyPositiveHighSource.balancedInput M H hH η₀ θ
  (fun _=>0) continuous_const 1 1 0 0 (by norm_num)
  (by simp [Function.support]) w σ freq (fun i=>Fin.elim0 i)
  s p ha t X₁ X₂ hX₁ hX₂

local notation "positiveInput"=>positiveEmptyInput M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq

lemma balanced_pools_eq : (zeroInput).pools=(positiveInput).pools:=
  congrArg Input.pools (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)

lemma balanced_normalized_gauss_eq (R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource zeroInput R seed W K=normalizedGaussSource positiveInput R seed W K:=
  congrArg (fun inp=>normalizedGaussSource inp R seed W K)
    (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)

lemma balanced_physical_mass_eq (R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z₀ ξ:ℝ):
    physicalMass zeroInput R seed m A Φ K Z₀ ξ=physicalMass positiveInput R seed m A Φ K Z₀ ξ:=
  congrArg (fun inp=>physicalMass inp R seed m A Φ K Z₀ ξ)
    (balanced_eq_positive_empty M H hH s p ha t X₁ X₂ hX₁ hX₂ η₀ θ w σ freq)

lemma balanced_current_source :
    (zeroInput).η=s.character ∧ (zeroInput).m=s.mask ∧ (zeroInput).t=t ∧
    (zeroInput).X₁=X₁ ∧ (zeroInput).X₂=X₂ ∧
    (zeroInput).Y₁=comparisonFirst Z s.width ∧
    (zeroInput).Y₂=comparisonSecond Z s.width X₁ X₂:=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem declared_capacity (hZ:1<Z):
    let Mdecl:=max s.width (length Z X₁+length Z X₂);
    Real.logb Z (volume zeroInput)≤Mdecl ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width ∧
    volume zeroInput≤Z^Mdecl:=by
  have hlog (X:ℝ)(hX:0<X):Real.logb Z X≤length Z X:=by
    rw [CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z X hZ hX]
    exact le_max_right _ _
  have hV:Real.logb Z (volume zeroInput)≤length Z X₁+length Z X₂:=by
    rw [CenteredMomentEnergyZeroReferencePhysical.balanced_volume,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact add_le_add (hlog X₁ hX₁) (hlog X₂ hX₂)
  have hdecl:=hV.trans (le_max_right s.width (length Z X₁+length Z X₂))
  refine ⟨hdecl,CenteredMomentEnergyPositiveHighParameters.actual_width_le s hZ,
    CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos zeroInput)).mp hdecl

theorem balanced_four_scales (hZ:1<Z)(hwidth:0<s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)):
    Z^(s.width/4)≤(zeroInput).X₁ ∧ Z^(s.width/4)≤(zeroInput).X₂ ∧
    Z^(s.width/4)≤(zeroInput).Y₁ ∧ Z^(s.width/4)≤(zeroInput).Y₂:=by
  have h:=CenteredMomentEnergyOriginalHighReflectionSymmetric.balanced_four_scale_gates
    Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩

lemma declared_capacity_upper (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal):
    max s.width (length Z X₁+length Z X₂)≤ max Mcap (2*Lgoal):=by
  have hlen (X:ℝ)(hcap:X≤Z^Lgoal):length Z X≤Lgoal:=by
    unfold length
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mpr
      (max_le (Real.one_le_rpow hZ.le hL) hcap)
  exact max_le_max hs (by linarith [hlen X₁ hc₁,hlen X₂ hc₂])

end SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroBalancedAdmission -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedAdmission
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyReferenceState CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyOriginalProfileControl CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "inp"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem fixed_fields :
    (inp).lower=1 ∧ (inp).upper=1 ∧
    (inp).b₁=b ∧ (inp).b₂=b ∧
    (inp).W₁=p.profile 0 ∧ (inp).W₂=p.profile 1 ∧
    (∀i,(inp).lo i=1) ∧ (∀i,(inp).hi i=1) ∧
    (∀i,(inp).M i≤1) ∧ Fintype.card (Fin 0)=0 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,by simp⟩
  all_goals intro i; exact Fin.elim0 i

lemma lower_product : 0<a*a ∧ (∏i,(inp).lo i)*a*a=a*a := by
  exact ⟨mul_pos ha ha,by simp⟩

lemma profile_control (S:Finset (ℕ×ℕ)) :
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (p.control (insert (0,0) S))^2 := by
  simpa using plain_control_sq_le inp p S 0 1 (by norm_num)
    (by simp) (fun i=>Fin.elim0 i)

lemma source_factor (hZ:1<Z) :
    sourceFactor inp a a s.radial.scale≤
      (Real.exp (Real.log 4)*fixedPresentationCost/(a*a))*Z^s.width := by
  have hK:0<s.radial.scale:=s.radial.scale_pos
  have hh:=source_factor_le inp 0 1 a s.radial.scale (by norm_num) ha hK
    (by simp) (fun i=>Fin.elim0 i)
  simp only [pow_zero,one_mul] at hh
  have hcap:=CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ
  have hc:0≤Real.exp (Real.log 4)*fixedPresentationCost/(a*a):=by
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le fixedPresentationCost_pos.le)
      (mul_pos ha ha).le
  apply hh.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hcap hc

theorem four_upper_scales (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    (inp).X₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).X₂≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₂≤Z^(max Mcap (2*Lgoal)) := by
  have hLg:Lgoal≤ max Mcap (2*Lgoal):=by linarith [le_max_right Mcap (2*Lgoal)]
  have hp:0<Z:=zero_lt_one.trans hZ
  have hquarter:0≤ s.width/4:=div_nonneg s.width_nonneg (by norm_num)
  have hY₁:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le hquarter
  refine ⟨hc₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),
    hc₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),?_,?_⟩
  · change Z^(s.width/4)≤_
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [s.width_nonneg,le_max_left Mcap (2*Lgoal)]
  · change X₁*X₂/comparisonFirst Z s.width≤_
    calc
      _≤X₁*X₂:=div_le_self (mul_pos hX₁ hX₂).le hY₁
      _≤Z^Lgoal*Z^Lgoal:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_pos_of_pos hp _).le
      _=Z^(2*Lgoal):=by rw [←Real.rpow_add hp];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_right _ _)

theorem capacity_packet (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    let Mdecl:=max s.width (length Z X₁+length Z X₂)
    0≤Mdecl ∧ Mdecl≤ max Mcap (2*Lgoal) ∧
    volume inp≤Z^Mdecl ∧ volume inp≤Z^(max Mcap (2*Lgoal)) ∧
    1≤ s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width := by
  have hd:=CenteredMomentEnergyZeroBalancedDictionary.declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hu:=CenteredMomentEnergyZeroBalancedDictionary.declared_capacity_upper s X₁ X₂ Mcap Lgoal hZ hL hs hc₁ hc₂
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨s.width_nonneg.trans (le_max_left _ _),hu,hd.2.2.2,
    hd.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hu),hr.1,hr.2.1,hd.2.1,hd.2.2.1⟩

end SevenEighths.CenteredMomentEnergyZeroBalancedAdmission

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthHighBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyZeroReferencePhysical (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyOriginalProfileControl
local notation "O"=>HeckeFamily.O
local instance : DecidableEq (Fin 0⊕Fin 2):=Classical.decEq _

lemma low_restrict (Q:Ideal O)(a b bΦ Bmask L L' Mcap e Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(K:ℝ)(hZ:1≤Z)(hL:L'≤L)
    (h:ZeroLowAt Q a b bΦ Bmask L Mcap e Z degree S K):
    ZeroLowAt Q a b bΦ Bmask L' Mcap e Z degree S K:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hl
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hL
  exact h s hQ hs p t X₁ X₂ hX₁ hX₂ (hc₁.trans hp) (hc₂.trans hp) hl

theorem actual_high_from_physical
    (a b bΦ rho ε Mcap Bmask B εdiag ξ saving:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask)(hB:0≤B)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0<Cfixed ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(e emass efinal:ℝ)(Q:Ideal O)(K Cmass:ℝ),
      0≤e→0≤K→0≤Cmass→e+ε≤efinal→emass≤efinal→εdiag≤efinal→-saving≤efinal→
      ZeroLowAt Q a b bΦ Bmask (Mcap+Bmask+rho/100) Mcap e Z degree S K→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q→ rho≤ s.width→s.width≤Mcap→
      ∀(p:Profiles a b)(t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂),X₁*X₂≤Z^B→
      5*s.width/6≤length Z X₁+length Z X₂→
      let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂)→
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/(X₁*X₂)≤
          Cmass*(p.control Smass)^2*(1+|t|)^Jmass*
            Z^(max s.width (length Z X₁+length Z X₂)+emass))→
      s.plainEnergy p t X₁ X₂≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|)^Jout*Z^(max s.width (length Z X₁+length Z X₂)+efinal):=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuCap,hLu,hLuCap,huStage⟩:=
    CenteredMomentEnergyZeroUnbalancedOriginal.original_unbalanced_from_zero_low
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirCap,hLr,hLrCap,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrStage⟩:=
    CenteredMomentEnergyZeroReferencePhysicalBounded.actual_positive_source_entry
      a b bΦ rho ε Mcap Bmask B εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hB hεdiag hξ
  refine ⟨Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Uu,Cu,hCu,huBound⟩:=huStage S
  obtain ⟨Jr,Ur,Cr,hCr,hrBound⟩:=hrStage S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=1
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤P:=by norm_num [P]
  have hD:0≤D:=by dsimp [D];positivity
  have hT:0≤T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [huBound,hrBound] with Z hZu hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂ hvolume hlarge
  dsimp only
  intro hphysical
  let inp:=balancedInput s p ha t X₁ X₂ hX₁ hX₂
  have hlowU:=low_restrict Q a b bΦ Bmask _ Lu Mcap e Z degree S K hZ.1.le hLuCap hlow
  have hlowR:=low_restrict Q a b bΦ Bmask _ Lr Mcap e Z degree S K hZ.1.le hLrCap hlow
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|:=by exact le_add_of_nonneg_right (abs_nonneg t)
  let Mout:ℝ:=max s.width (length Z X₁+length Z X₂)
  have hwm:s.width≤Mout:=le_max_left _ _
  let F:ℝ:=(p.control U)^2*(1+|t|)^Jout*Z^(Mout+efinal)
  have hF:0≤F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤Jout)(hej:ej≤efinal):
      (p.control Sj)^2*(1+|t|)^jj*Z^(s.width+ej)≤F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (add_le_add hwm hej)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤Jout:=by dsimp [Jout];omega
  have hjr:Jr≤Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤Cfixed*(K+Cmass+1):=by
    have hCuC : Cu ≤ Cfixed := by
      dsimp only [Cfixed]
      linarith only [hCr, hD, hT]
    exact mul_le_mul hCuC (by linarith only [hCmass])
      (by linarith only [hK]) hCfixed.le
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · have hunbalanced:=hZu.2 e Q degree K he hK hlowU s hQ hwidthLo hwidth
      p t X₁ X₂ hX₁ hX₂ hshort hlarge
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hfour':=balanced_four_scale_gates Z s.width X₁ X₂ hZ.1 (hrho.trans_le hwidthLo)
      hX₁ hX₂ (le_of_not_ge hshort)
    have hfour:Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂:=
      ⟨hfour'.1,hfour'.2.1,hfour'.2.2.1,hfour'.2.2.2.1⟩
    rcases hZ.2 e Q degree K he hK hlowR s hQ hwidthLo hwidth p t X₁ X₂ hX₁ hX₂
      hvolume hlarge with hzero|hsource
    · rw [hzero]
      positivity
    have hmass:=hphysical hfour
    have hmEnv:(p.control Smass)^2*(1+|t|)^Jmass*Z^(Mout+emass)≤F:=by
      have hp:=profile_control_mono p hm
      have hp0:=p.control_nonneg Smass
      have hj:=pow_le_pow_right₀ hbase hjm
      have hx:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show Mout+emass≤Mout+efinal by linarith only [hmassFinal])
      dsimp [F]
      gcongr
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        (X₁*X₂)≤Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤P*(p.control U)^2:=by
      have hc:=plain_control_sq_le inp p U 0 1 (by norm_num) (by simp) (by intro i;exact Fin.elim0 i)
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [P,Finset.insert_eq_of_mem h00,one_pow,one_mul] using hc
    have hheight1:1≤(1+|t|)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤efinal):s.radial.scale*Z^x≤Z^(Mout+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by have hh:=hwm;unfold NaturalState.width at hh;linarith only [hh, hx, s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤A)(hx:x≤efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(Mout+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          dsimp [F]
          nlinarith only [mul_nonneg (show 0≤ c*P*A*(p.control U)^2*Z^(Mout+efinal) by positivity)
            (sub_nonneg.mpr hheight1)]
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu, hCr, hD, hT, hK, hCmass, mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|)^Jout*Z^(Mout+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyZeroGrowthHighBound

end

end OAI

end

