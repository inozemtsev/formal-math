module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part036
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.BandMonotonicity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def widenState {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    NaturalState Z B' b':=
  {s with
    puncture_bound:=s.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hB)
    radial_support:=fun _x hx=>le_trans (s.radial_support hx) hb}

def widenProfiles {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b'):Profiles a' b' where
  profile:=p.profile
  support:=fun i _x hx=>⟨ha.trans (p.support i hx).1,(p.support i hx).2.trans hb⟩

lemma widenState_width {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    (widenState s hB hb).width=s.width:=rfl

lemma widenProfiles_control {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b')
    (S:Finset (ℕ×ℕ)):(widenProfiles p ha hb).control S=p.control S:=rfl

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem zeroAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b radial mask L Mcap eps Z J S C):
    ZeroAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
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

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤ radial)(hm:mask'≤ mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity
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

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.InputParentCapacity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (le_max_right _ _)

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X) := by
  by_cases hx:1≤X
  · rw [length,max_eq_right hx,max_eq_right (Real.logb_nonneg hZ hx)]
  · have hh:X≤1:=le_of_not_ge hx
    have hl:Real.logb Z X≤0 := by
      simpa using Real.logb_le_logb_of_le hZ hX hh
    rw [length,max_eq_left hh,Real.logb_one,max_eq_left hl]

theorem postmask_length (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)=length Z X-min (Real.logb Z D) (length Z X) := by
  have hp:0< max 1 X:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd:0<D:=zero_lt_one.trans_le hD
  rw [length_eq_max_log Z _ hZ (div_pos hp hd),Real.logb_div hp.ne' hd.ne']
  change max 0 (length Z X-Real.logb Z D)=_
  by_cases h:Real.logb Z D≤length Z X
  · rw [min_eq_left h,max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),sub_self]

lemma postmask_length_le (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)≤length Z X := by
  rw [postmask_length Z X D hZ hD]
  have hm:0≤ min (Real.logb Z D) (length Z X):=
    le_min (Real.logb_nonneg hZ hD) (length_nonneg Z X hZ)
  linarith

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

theorem input_reference_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (s.Y₁*s.Y₂*∏i,s.P i)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [s.same_product]
  exact input_affine_capacity s Z κ M hZ hcap

theorem original_slot_logs (s:Input ι)(Z:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hw:∀i,0≤w i)(hP:∀i,s.P i=Z^(w i)):
    (∀i,1≤ s.P i) ∧ (∀i,Real.logb Z (s.P i)=w i) := by
  constructor
  · intro i;rw [hP i];exact Real.one_le_rpow hZ.le (hw i)
  · intro i;rw [hP i,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem original_exponent_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hP:∀i,s.P i=Z^(w i))
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,w i)≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  apply input_affine_capacity s Z κ M hZ
  simpa only [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap

theorem original_volume_cap (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(hk:1/6≤κ)
    (hP:∀i,1≤ s.P i)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    volume s≤Z^M := by
  have hh:=input_affine_capacity s Z κ M hZ hcap
  have hn:0≤∑i,Real.logb Z (s.P i):=
    Finset.sum_nonneg (fun i _=>Real.logb_nonneg hZ (hP i))
  have hp:0≤(6*κ-1)*(∑i,Real.logb Z (s.P i)):=mul_nonneg (by linarith) hn
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (by linarith)

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.DeletedChildCapacity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSecondCapacityLedger CenteredMomentLiveCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hF))

lemma prime_deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,Prime I) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm :=
  deletion_norm F (fun I hI=>(hF I hI).ne_zero)

def postmaskLength (Z U : ℝ) (F : Finset (Ideal O)) : ℝ :=
  length Z (clippedScale U/((∏I∈F,I).absNorm:ℝ))

lemma postmaskLength_eq (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F=Real.logb Z (clippedScale U)-
      min (Real.logb Z ((∏I∈F,I).absNorm:ℝ)) (Real.logb Z (clippedScale U)) :=
  postmask_length Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_le (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F≤Real.logb Z (clippedScale U) :=
  postmask_length_le Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_nonneg (Z U : ℝ) (F : Finset (Ideal O)) (hZ : 1<Z) :
    0≤postmaskLength Z U F := length_nonneg Z _ hZ

theorem child_survives (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0) :
    1≤ rawScale D a X₁ 0*V₁.b ∧ 1≤ rawScale D a X₂ 1*V₂.b := by
  unfold child at hne
  have hp:=left_ne_zero_of_mul hne
  exact ⟨profile_polynomial_survives χ V₁ _ (rawScale_pos D a X₁ h₁ 0) t _ 0 0
    (left_ne_zero_of_mul hp),
    profile_polynomial_survives χ V₂ _ (rawScale_pos D a X₂ h₂ 1) t _ 0 0
      (right_ne_zero_of_mul hp)⟩

def deletedExcess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι) : ℝ :=
  excess (liveIndices D a\J) (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) M κ

lemma deletedExcess_le (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0) :
    deletedExcess D a Z X₁ X₂ κ M P F₁ F₂ J≤
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := by
  have h₁:=postmaskLength_le Z (rawScale D a X₁ 0) F₁ hZ hF₁
  have h₂:=postmaskLength_le Z (rawScale D a X₂ 1) F₂ hZ hF₂
  have hsum:(∑i∈liveIndices D a\J,Real.logb Z (P i))≤ remainingLogs D a Z P :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _=>Real.logb_nonneg hZ (hP i))
  have hh:=mul_le_mul_of_nonneg_left hsum (by positivity : 0≤6*κ)
  unfold deletedExcess excess plainLogs
  exact max_le_max (by linarith) le_rfl

theorem child_excess_from_parent (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 := by
  obtain ⟨hs₁,hs₂⟩:=child_survives χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J hne
  apply (deletedExcess_le D a Z X₁ X₂ κ Mactual P F₁ F₂ J hZ hκ hP hF₁ hF₂).trans
  apply (excess_le_remaining D a Z X₁ X₂ V₁.b V₂.b κ Mactual hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
  linarith

theorem child_paid_width (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    Mactual+deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6≤
      Mnom+δ₂+w+ell+δ₁/6+θ/3 := by
  have he:=child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne hparent hshift hclip
  have hh:=width_defect_cost (Mactual-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mactual-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mactual by ring] at hh
  linarith

lemma eventually_endpoint_cost (b₁ b₂ θ : ℝ) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ :=
  CenteredMomentCommonMaskChildCapacity.eventually_fixed_clipping_cost b₁ b₂ (2*θ) (by positivity)

theorem paired_child_excess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ Y₁ Y₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hsame : Y₁*Y₂=X₁*X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    (∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0 →
      deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) ∧
    (∀χ t,child χ D a V₁ V₂ pool β P t Y₁ Y₂ hY₁ hY₂ F₁ F₂ J≠0 →
      deletedExcess D a Z Y₁ Y₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) := by
  constructor
  · intro χ t hn
    exact child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
      w ell δ θ hX₁ hX₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift hclip
  · intro χ t hn
    apply child_excess_from_parent χ D a V₁ V₂ pool β P t Z Y₁ Y₂ κ A M Mnom Mactual
      w ell δ θ hY₁ hY₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent _ hclip
    simpa only [hsame] using hshift

theorem source_removal_width_cost (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ mesh : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hm : 0≤ mesh) (hmesh : ∀i∈liveIndices D a\J,Real.logb Z (P i)≤ mesh) :
    ∃removed : Finset ι,removed⊆liveIndices D a\J ∧
      (removed=liveIndices D a\J ∨
        postmaskLength Z (rawScale D a X₁ 0) F₁+
        postmaskLength Z (rawScale D a X₂ 1) F₂+
        6*κ*(∑i∈(liveIndices D a\J)\removed,Real.logb Z (P i))≤Mactual) ∧
      ∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0 →
        Mactual-Mnom+κ*(∑i∈removed,Real.logb Z (P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  by_cases hk : κ=0
  · refine ⟨liveIndices D a\J,Finset.Subset.refl _,Or.inl rfl,?_⟩
    intro χ t _
    simp only [hk,zero_mul,add_zero]
    linarith
  have hkpos : 0<κ := lt_of_le_of_ne hκ (Ne.symm hk)
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a\J)
    (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) Mactual κ mesh hkpos hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  intro χ t hn
  have hp:=child_paid_width χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift
    hwidth hw hell hδ₁ hδ₂ hθ hclip
  change κ*(∑i∈removed,Real.logb Z (P i))≤
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6+κ*mesh at hcost
  linarith

lemma postmask_scale_pos (U : ℝ) (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    0<clippedScale U/((∏I∈F,I).absNorm:ℝ) :=
  div_pos (zero_lt_one.trans_le (clippedScale_ge_one U))
    (zero_lt_one.trans_le (deletion_norm F hF))

theorem input_parent_child_excess (s : CenteredMomentCommonRadialData.Input ι)
    (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (V₁ V₂ : Plain)
    (t Z X₁ X₂ κ M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤ s.P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ s.slots s.coefficient s.P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s)-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual s.P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 :=
  child_excess_from_parent χ D a V₁ V₂ s.slots s.coefficient s.P t Z X₁ X₂ κ
    (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) M Mnom Mactual w ell δ θ
    h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne
    (input_affine_capacity s Z κ M hZ hparent) hshift hclip

end SevenEighths.CenteredMomentEnergyDeletedChildCapacity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionCapacity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionCapacity
open HeckeFamily CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands CenteredMomentLiveCapacity

local notation "O"=>HeckeFamily.O

lemma deleted_short_length (Z M:ℝ)(hZ:1<Z)(hM:0≤M)
    (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤ comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤ comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he

theorem deleted_reflection_excess {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤w i)
    (Z M X₁ X₂ κ xi reflected:ℝ)(hZ:1<Z)(hM:0≤M)
    (hX₁:0<X₁)(hX₂:0<X₂)(hκ:3/4≤κ)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    excess J w (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ≤
      xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=by
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hn₂p:0<((∏I∈D₂,I).absNorm:ℝ):=zero_lt_one.trans_le hn₂
  have hlog:0≤Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=Real.logb_nonneg hZ hn₂
  have hell:0≤∑i∈F,w i:=Finset.sum_nonneg hw
  have hY₂:0<comparisonSecond Z M X₁ X₂:=by
    unfold comparisonSecond
    exact div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  rw [Real.logb_div hY₂.ne' hn₂p.ne'] at href
  have hb:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+
      (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)):=by linarith
  have hh:=(balanced_reflection_margins Z M X₁ X₂ (∑i∈F,w i) κ
    (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)) reflected hZ hM hX₁ hX₂ hell hκ hlarge hcap hb).2
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hsum:(∑i∈J,w i)≤∑i∈F,w i:=
    Finset.sum_le_sum_of_subset_of_nonneg hJF (fun i hi _=>hw i hi)
  have hks:=mul_le_mul_of_nonneg_left hsum (by linarith:0≤6*κ)
  unfold excess
  apply max_le _ (add_nonneg hxi hlog)
  nlinarith

theorem deleted_reflection_removal {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤w i)
    (Z M X₁ X₂ κ xi reflected mesh:ℝ)(hZ:1<Z)(hM:0≤M)
    (hX₁:0<X₁)(hX₂:0<X₂)(hκ:3/4≤κ)(hxi:0≤xi)(hm:0≤ mesh)(hwm:∀i∈J,w i≤ mesh)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    ∃removed:Finset α,removed⊆J ∧
      (removed=J ∨ length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+reflected+
        6*κ*(∑i∈J\removed,w i)≤M) ∧
      κ*(∑i∈removed,w i)≤xi/6+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)/6+κ*mesh:=by
  obtain ⟨removed,hr,hcapacity,hcost⟩:=removal_excess_cost J w
    (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ mesh
    (by linarith) hm (fun i hi=>hw i (hJF hi)) hwm
  refine ⟨removed,hr,hcapacity,?_⟩
  have he:=deleted_reflection_excess F J hJF w hw Z M X₁ X₂ κ xi reflected
    hZ hM hX₁ hX₂ hκ hxi hlarge hcap D₁ D₂ hD₁ hD₂ href
  linarith

lemma plain_kappa_eq (beta : ℝ) :
    (3/4:ℝ)+2*(beta-7/8)=2*beta-1 := by ring

lemma plain_kappa_lower (beta : ℝ) (hbeta : 7/8 < beta) :
    (3/4:ℝ) < (3/4:ℝ)+2*(beta-7/8) := by linarith

lemma paid_divisor_power (Z cost xi kappa mesh : ℝ) (hZ : 1 < Z)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (hcost : cost ≤ xi/6 + Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6 + kappa*mesh) :
    Z^cost ≤ Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hn : 0 < ((∏ I ∈ D, I).absNorm:ℝ) :=
    zero_lt_one.trans_le (product_norm_ge_one D hD)
  calc
    Z^cost ≤ Z^((xi/6+kappa*mesh)+Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
      rw [Real.rpow_add hZp]
      congr 1
      rw [div_eq_mul_inv, Real.rpow_mul hZp.le,
        Real.rpow_logb hZp hZ.ne' hn]
      norm_num

end SevenEighths.CenteredMomentEnergyReferenceDeletionCapacity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionClipped -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionClipped
open HeckeFamily CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

lemma deleted_long_le_width (Z M X₁ X₂ ell kappa : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 3/4 ≤ kappa)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I) :
    Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) ≤ M := by
  have hg := balanced_reference_geometry Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap
  have hn := product_norm_ge_one D hD
  have hp : 0 < ((∏ I ∈ D, I).absNorm:ℝ) := zero_lt_one.trans_le hn
  have hy := (comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂).2
  rw [Real.logb_div hy.ne' hp.ne']
  have hlog := Real.logb_nonneg hZ hn
  linarith [hg.2.2.2.2]

lemma clipped_reflected_bound (Z M X₁ X₂ ell kappa xi reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 3/4 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (href : reflected ≤ max 0 (M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi)) :
    reflected ≤ M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi := by
  have hlong := deleted_long_le_width Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap D hD
  rwa [max_eq_right (by linarith)] at href

end SevenEighths.CenteredMomentEnergyReferenceDeletionClipped

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget CenteredMomentEnergyReferenceDeletionCapacity
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤M)(hell:0≤ell)(hk:3/4≤kappa)
    (hlarge:5*M/6≤total+ell)(hcap:total+ell+(6*kappa-1)*ell≤M):
    ell≤M/21 ∧ (6*kappa-1)*ell≤M/6:=by
  have hkell:7/2*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤M)(_hs:0≤ short)(hsM:short≤M/4)(_hell:0≤ell)(_hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(he:ell≤M/21)(hbudget:(6*kappa-1)*ell≤M/6)(hxi:0≤xi)
    (hhigh:5*M/6<short+max 0 along+z)
    (href:reflected≤ max 0 (M-along+xi)):
    0<along ∧ reflected+short+z≤16*M/21+xi ∧
      reflected+short+6*kappa*z≤13*M/14+xi:=by
  have haz:0<along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤M/21:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem deleted_reference_cases (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤M) ∨
    (0<Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
      reflected+short+z≤16*M/21+xi ∧ reflected+short+6*kappa*z≤13*M/14+xi):=by
  dsimp only
  have hg:=balanced_reference_geometry Z M X₁ X₂ ell kappa hZ hM hX₁ hX₂ hell hk hlarge hcap
  have hpos:=comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hlongpos:=div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0:=length_nonneg Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ)) hZ
  have hlong:length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))≤
      Real.logb Z (comparisonSecond Z M X₁ X₂):=by
    have hY:1≤ comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
    have hdiv:=div_le_self hpos.2.le hn₂
    exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le hY hdiv)
  by_cases hlo:length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+
      length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6
  · refine Or.inl ⟨hlo,?_⟩
    have hzcap:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*kappa)
    rw [hg.2.2.2.1] at hlong
    nlinarith
  · apply Or.inr
    obtain ⟨he,hbudget⟩:=slot_budgets M (Real.logb Z (X₁*X₂)) ell kappa hM hell hk hlarge hcap
    apply reflected_low M _ _ ell z kappa xi reflected hM hshort0 hshort hell hz hze hk he hbudget hxi _ href
    rw [←length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤M/14)(ht:reflected+short+z≤16*M/21+xi)
    (hc:reflected+short+6*kappa*z≤13*M/14+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤M:=by
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowWindow
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O

lemma reflection_window_length (Z R x:ℝ)(hZ:1<Z)(hR:0≤R)
    (hx:x∈Set.Icc 0 (R*Real.log Z)):
    length Z (Real.exp x)≤R ∧ Real.exp x≤Z^R:=by
  have hlog:0<Real.log Z:=Real.log_pos hZ
  have hexp:Real.exp x≤Z^R:=by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using hx.2
  refine ⟨?_,hexp⟩
  have hmax:max 1 (Real.exp x)≤Z^R:=
    max_le (Real.one_le_rpow hZ.le hR) hexp
  have hl:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.exp x))) hmax
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hl

theorem deleted_reference_window (Z M X₁ X₂ ell z kappa xi:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(hxi:0≤xi)(hxiM:xi≤M/14)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+6*kappa*z≤M) ∨
    (0<along ∧ ∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
      length Z (Real.exp x)+short+z≤5*M/6 ∧
      length Z (Real.exp x)+short+6*kappa*z≤M):=by
  dsimp only
  let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))
  rcases deleted_reference_cases Z M X₁ X₂ ell z kappa xi (max 0 (M-along+xi))
    hZ hM hX₁ hX₂ hell hz hze hk hxi hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h|h
  · exact Or.inl h
  · refine Or.inr ⟨h.1,?_⟩
    intro x hx
    have hh:=reflection_window_length Z (max 0 (M-along+xi)) x hZ (le_max_left _ _) hx
    have hb:=reflected_low_admissible M xi _ (max 0 (M-along+xi)) z kappa hxiM h.2.1 h.2.2
    constructor <;> linarith [hh.1]

end SevenEighths.CenteredMomentEnergyReferenceLowWindow

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowDeletedGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow
local notation "O"=>HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(hxiM:xi≤ s.width/14)
    (hlarge:5*s.width/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):=by
  dsimp only
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hd:=balanced_divisor_range s hZ Mcap X₁ X₂ ell κ hwidth
    hX₁ hX₂ hell hκ hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hd
  have hn₁:=divisor_norm s D₁ hD₁
  have hn₂:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁.1
  have hl₂:=Real.logb_nonneg hZ hn₂.1
  have hMcap:0≤Mcap:=s.width_nonneg.trans hwidth
  have hLc:0≤L:=by linarith
  refine ⟨hd.2.2.2.1,hd.2.2.2.2,by linarith,by linarith [s.width_nonneg],?_,
    hd.2.2.1,?_,?_⟩
  · linarith [hg.2.2.2.2]
  · exact max_le hLc (by linarith [hd.2.1])
  · have hp₁:∀I∈D₁,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₁ hi)
    have hp₂:∀I∈D₂,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₂ hi)
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)
    have halong:Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ))=along:=by
      rw [←hd.2.2.2.2]
      exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
    rcases CenteredMomentEnergyReferenceLowBranchGeometry.deleted_reference_cases
      Z s.width X₁ X₂ ell z κ xi (max 0 (s.width-along+xi)) hZ s.width_nonneg
      hX₁ hX₂ hell hz hze hκ hxi hlarge hcap D₁ D₂ hp₁ hp₂
      (by rw [halong]) with hc|hc
    · apply Or.inl
      simpa only [hd.2.2.2.1,hd.2.2.2.2] using hc
    · apply Or.inr
      have hh:=CenteredMomentEnergyReferenceLowBranchGeometry.reflected_low_admissible
        s.width xi _ (max 0 (s.width-along+xi)) z κ hxiM hc.2.1 hc.2.2
      simpa only [hd.2.2.2.1] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O

lemma original_long_positive (Z M X₁ X₂ ell κ:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤M):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hbudget:=slot_budgets M (length Z X₁+length Z X₂) ell κ hM.le hell hκ hlarge (by linarith)
  have hpos:0<length Z X₂:=by linarith [hbudget.1]
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma deleted_length_le (Z X N:ℝ)(hZ:1<Z)(hX:0<X)(hN:1≤N):
    length Z (X/N)≤length Z X:=by
  exact Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
    (max_le_max_left 1 (div_le_self hX.le hN))

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hM:0<s.width)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(hxiM:xi≤ s.width/14)
    (hshort:length Z X₁≤ s.width/4)
    (hlarge:5*s.width/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ));
    let along:=Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ));
    Z^short=X₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):=by
  dsimp only
  have hZ0:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hp₁:=div_pos hX₁ (zero_lt_one.trans_le hn₁)
  have hp₂:=div_pos hX₂ (zero_lt_one.trans_le hn₂)
  have he₁:=Real.rpow_logb hZ0 hZ.ne' hp₁
  have he₂:=Real.rpow_logb hZ0 hZ.ne' hp₂
  have hd₁:=deleted_length_le Z X₁ _ hZ hX₁ hn₁
  have hd₂:=deleted_length_le Z X₂ _ hZ hX₂ hn₂
  have hraw₁:Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ))≤
      length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₁];exact le_max_right _ _
  have hraw₂:Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))≤
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₂];exact le_max_right _ _
  have hlen₁:=length_nonneg Z X₁ hZ
  have hlen₂:=length_nonneg Z X₂ hZ
  have hslot:0≤6*κ*ell:=mul_nonneg (by linarith) hell
  have hl:=original_long_positive Z s.width X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hshort hlarge hcap
  have hrange:=divisor_reflection_range s hZ Mcap X₂ hwidth hl.2.2 D₂ hD₂
  dsimp only at hrange
  have hlogdiv:=Real.logb_div (b:=Z) hX₂.ne' (zero_lt_one.trans_le hn₂).ne'
  rw [←hlogdiv] at hrange
  have hL0:0≤L:=by linarith
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,hrange.2.1,
    max_le hL0 (by linarith [hrange.1]),?_⟩
  rw [he₁,he₂]
  by_cases hd:length Z (X₁/((∏P∈D₁,P).absNorm:ℝ))+
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+z≤5*s.width/6
  · refine Or.inl ⟨hd,?_⟩
    have hkz:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*κ)
    linarith
  · obtain ⟨he,hbudget⟩:=slot_budgets s.width (length Z X₁+length Z X₂) ell κ
      hM.le hell hκ hlarge (by linarith)
    have hlow:=reflected_low s.width (length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)))
      (Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))) ell z κ xi
      (max 0 (s.width-Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+xi))
      hM.le (length_nonneg Z _ hZ)
      (hd₁.trans hshort) hell hz hze hκ he hbudget hxi
      (by rw [←length_eq_max_log Z _ hZ hp₂];exact lt_of_not_ge hd) le_rfl
    exact Or.inr (reflected_low_admissible s.width xi _ _ z κ hxiM hlow.2.1 hlow.2.2)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.SlotHeight -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergySlotHeight
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy
open HeckePrimeAnnular CenteredMomentPrimeSlotShift
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α]

lemma height_coefficient (ν:Ideal O→ℂ)(W:ℝ→ℂ)(P σ freq t:ℝ)(hP:0<P)
    (I:Ideal O)(hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring

lemma row_slot_phase (η:Character)(m A z:O)(pool:Finset (Ideal O))
    (β γ:Ideal O→ℂ)(phase:ℂ)(t:ℝ)(he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring

lemma positive_row_phase (η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(he:∀i I,I∈pool i→β i I=phase i*γ i I):
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring

theorem energy_phase (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (he:∀i I,I∈pool i→β i I=phase i*γ i I)(hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]

theorem inherited_height_energy (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(ν:α→Ideal O→ℂ)(W:α→ℝ→ℂ)
    (P σ freq:α→ℝ)(hP:∀i,0<P i)(hpool:∀i I,I∈pool i→I≠0)
    (t rowt X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A rowt W₁ W₂ pool
      (fun i=>heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    exact height_coefficient (ν i) (W i) (P i) (σ i) (freq i) t (hP i) I (hpool i I hi)
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)

end SevenEighths.CenteredMomentEnergySlotHeight

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceChild -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergySlotHeight
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
local notation "O"=>HeckeFamily.O

def unpuncturedState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z 0 bΦ where
  character:=s.character
  fixedModulus:=s.fixedModulus
  puncture:=1
  radial:=(effectiveState s).radial
  rowWidth:=s.rowWidth
  characterWidth:=s.characterWidth
  base_ge_one:=s.base_ge_one
  row_nonneg:=s.row_nonneg
  character_nonneg:=s.character_nonneg
  scale_eq:=s.scale_eq
  modulus_bound:=s.modulus_bound
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=s.radial_support
  row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
  nonexceptional:=by
    intro z hz hh
    have hn:=s.row_ne_zero z hz.1
    have hunit:CenteredExceptionalProfile.FixedInducingRow s.character s.fixedModulus fixedBadMask 1 z:=
      (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator 1) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh
    exact s.nonexceptional z hz.1
      ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator s.puncture) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero _ s.puncture_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hunit)

lemma unpunctured_width {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    (unpuncturedState s).width=s.width:=rfl

def independentProfiles {a b:ℝ}(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(t₁ t₂:ℝ):Profiles a b where
  profile:=fun i=>if i=0 then normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
    else normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  support:=by
    intro i
    split_ifs
    · exact (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
    · exact (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂

theorem independent_child_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=natural_subset_radial_eq_energy s.character (effectiveState s).radial
    (fun z hz=>s.row_ne_zero z hz.1) F
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    pool β P X₁ X₂ hX₁ hX₂ hP
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at hh
  simpa only [independentProfiles,unpuncturedState,NaturalState.mask,
    show (1:Fin 2)≠0 by decide,ite_false,ite_true,effectiveState,effectiveRadial] using hh

theorem independent_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(W:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (t t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  rw [independent_child_energy s ha W₁ W₂ hs₁ hs₂ F pool _ P t₁ t₂ X₁ X₂ hX₁ hX₂ hP]
  exact inherited_height_energy _ _ _ _ _ (fun i:F=>pool i)
    (fun (i:F) I=>idealCoeff (ν i) I) (fun i:F=>W i)
    (fun i:F=>P i) (fun i:F=>σ i) (fun i:F=>freq i)
    (fun i=>hP i i.property) (fun i I hI=>(hp i i.property I hI).ne_zero)
    t 0 X₁ X₂ _ _ _

end SevenEighths.CenteredMomentEnergyReferenceChild

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChildProfiles
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyProfiles
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

def reflectionProfiles {a b:ℝ}(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t:ℝ):Profiles a b:=
  independentProfiles ha (derivativeChoice (annulusSeed a b hlo hhi).profile j)
    (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t

theorem reflected_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(Wslot:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v) *
      polynomial (naturalCharacter s.character z) false (scaleTest W k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 0)
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=independent_child_ray_energy s ha
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) F pool ν Wslot P σ freq hp hP
    t (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

theorem independent_profile_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t₁ t₂:ℝ,
      (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S≤
        C*(sourceControl T W₁*sourceControl T W₂)*(1+‖t₁‖+‖t₂‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hc⟩:=normPowerProfile_source_control a b ha S
  refine ⟨n,T,C^2,sq_pos_of_pos hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have h₁:=hc W₁ hs₁ t₁
  have h₂:=hc W₂ hs₂ t₂
  have hp₁:(1+‖t₁‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₂]) n
  have hp₂:(1+‖t₂‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₁]) n
  have h₁':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)≤C*sourceControl T W₁*(1+‖t₁‖+‖t₂‖)^n:=
    h₁.trans (mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  have h₂':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)≤C*sourceControl T W₂*(1+‖t₁‖+‖t₂‖)^n:=
    h₂.trans (mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  simp only [Profiles.control,independentProfiles,show (1:Fin 2)≠0 by decide,ite_true,ite_false]
  apply (mul_le_mul h₁' h₂' (apply_nonneg _ _)
    (mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg _ _)) (by positivity))).trans_eq
  rw [show (1+‖t₁‖+‖t₂‖)^(2*n)=((1+‖t₁‖+‖t₂‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

lemma derivative_choice_control (S:Finset (ℕ×ℕ)):
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),∀j:Fin 2,
      sourceControl S (derivativeChoice W j)≤C*sourceControl T W:=by
  obtain ⟨T,C,hC,hc⟩:=scale_source_control S
  refine ⟨S∪T,1+C,by positivity,?_⟩
  intro W j
  have h₁:sourceControl S W≤ sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:S⊆S∪T)) W
  have h₂:sourceControl T W≤ sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right:T⊆S∪T)) W
  by_cases hj:j=0
  · simp only [derivativeChoice,ite_eq_left hj]
    exact h₁.trans (le_mul_of_one_le_left (sourceControl_nonneg _ _) (by linarith))
  · simp only [derivativeChoice,ite_eq_right hj]
    exact (hc W).trans (mul_le_mul (by linarith) h₂ (sourceControl_nonneg _ _) (by positivity))

theorem reflected_profile_control (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t:ℝ,
      (reflectionProfiles ha hlo hhi W hs j k v t).control S≤
        C*sourceControl T W*(1+‖v‖+‖t‖)^n:=by
  obtain ⟨n,T,C,hC,hc⟩:=independent_profile_control a b ha S
  obtain ⟨U,D,hD,hd⟩:=derivative_choice_control T
  let A:ℝ:=1+∑j:Fin 2,sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)
  have hA:0<A:=by
    have hh:=Finset.sum_nonneg (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j))
    dsimp [A];linarith
  refine ⟨2*n,U,C*A*D*(1+2*Real.pi)^(2*n),by positivity,?_⟩
  intro W hs j k v t
  have haSeed:sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)≤A:=by
    have hh:=Finset.single_le_sum (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j)) (Finset.mem_univ j)
    dsimp [A];linarith
  have hheight:1+‖-2*Real.pi*v‖+‖t‖≤(1+2*Real.pi)*(1+‖v‖+‖t‖):=by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
    nlinarith [Real.pi_pos,norm_nonneg v,norm_nonneg t]
  have hh:=hc (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t
  apply hh.trans
  calc
    _≤C*(A*(D*sourceControl U W))*((1+2*Real.pi)*(1+‖v‖+‖t‖))^(2*n):=by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul haSeed (hd W k) (sourceControl_nonneg _ _) hA.le) hC.le
      · exact pow_le_pow_left₀ (by positivity) hheight _
      · positivity
      · exact mul_nonneg hC.le (mul_nonneg hA.le (mul_nonneg hD.le (sourceControl_nonneg _ _)))
    _=_:=by rw [mul_pow];ring

end SevenEighths.CenteredMomentEnergyReferenceChildProfiles

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def ZeroLowAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂≤5*s.width/6→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveLowAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyReferenceLowBands

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowChild -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

def unitBudgetState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hB:0≤Bmask):
    NaturalState Z Bmask bΦ:=
  {unpuncturedState s with
    puncture_bound:=by simpa only [unpuncturedState,map_one,Nat.cast_one] using Real.one_le_rpow s.base_ge_one hB}

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem reflected_child_from_low
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hfreq:∀i,|freq i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
    (hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>t+freq i)
    0 (|t|+height) (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (reflectionProfiles ha hlo hhi Wshort hsW j k v t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hsmall)
  rw [reflected_child_ray_energy s ha hlo hhi Wshort hsW F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>Wslot)
    (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _) j k v t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowChild

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowControl
open CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma height_product (v t H:ℝ)(hH:0≤H):
    1+‖v‖+‖t‖≤(1+‖v‖)*(1+|t|+H):=by
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg v,abs_nonneg t]

theorem reflected_child_control (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ))(degree:ℕ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t height:ℝ,0≤height →
      ((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2*
        (1+|t|+height)^degree≤
        D*(sourceControl T W)^2*(1+|t|+height)^(degree+2*n)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_profile_control a b ha hlo hhi S
  refine ⟨n,T,D^2,sq_pos_of_pos hD,?_⟩
  intro W hs j k v t height hheight
  have hbase:=hd W hs j k v t
  have hgrowth:(1+‖v‖+‖t‖)^n≤((1+‖v‖)*(1+|t|+height))^n:=
    pow_le_pow_left₀ (by positivity) (height_product v t height hheight) n
  have hprof:((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2≤
      (D*sourceControl T W*((1+‖v‖)*(1+|t|+height))^n)^2:=
    pow_le_pow_left₀ (Profiles.control_nonneg _ _) (hbase.trans
      (mul_le_mul_of_nonneg_left hgrowth (mul_nonneg hD.le (sourceControl_nonneg _ _)))) 2
  apply (mul_le_mul_of_nonneg_right hprof (by positivity)).trans_eq
  simp only [mul_pow] at *
  rw [pow_add,show (1+|t|+height)^(2*n)=((1+|t|+height)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul],
    show (1+‖v‖)^(2*n)=((1+‖v‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceLowControl

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowDirect -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowDirect
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceLowChild

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem direct_child_from_low
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤Bmask)(ha:0<a)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hfreq:∀i,|freq i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
    (hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      W₁ X₁ 0 t*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>t+freq i)
    0 (|t|+height) (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (independentProfiles ha W₁ W₂ hs₁ hs₂ t t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hsmall)
  rw [independent_child_ray_energy s ha W₁ W₂ hs₁ hs₂ F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>Wslot)
    (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _) t t t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowDirect

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowEmpty -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α][IsEmpty α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem zero_low_positive_empty
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)(hC:0≤C)
    (h:ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C):
    PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hsmall
  have hh:=h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ (by simpa using hsmall)
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid]
  apply hh.trans
  have hp:(1+‖t‖)^degree≤(1+|t|+height)^degree:=by
    apply pow_le_pow_left₀ (by positivity)
    rw [Real.norm_eq_abs]
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by unfold diagonalControl;positivity))
    (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)

end SevenEighths.CenteredMomentEnergyReferenceLowEmpty

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.LowBandEmpty -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLowBandEmpty
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positive_low_zero
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C):
    ZeroLowAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hsmall
  let T:Finset α:=∅
  let θ:T→RayQuotient.Characters M H:=fun i=>False.elim (Finset.notMem_empty _ i.property)
  let w:T→ℝ:=fun _=>0
  have hcap:length Z X₁+length Z X₂+6*κ*(∑i:T,w i)≤ s.width:=by
    simp only [T,w,Finset.sum_const_zero,mul_zero,add_zero]
    linarith [s.width_nonneg]
  have hl:length Z X₁+length Z X₂+(∑i:T,w i)≤5*s.width/6:=by
    simpa only [w,Finset.sum_const_zero,add_zero] using hsmall
  have hh:=h T θ w w w t 0 (fun _=>le_rfl)
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property))
    (fun i=>False.elim (Finset.notMem_empty _ i.property)) le_rfl
    (fun _=>by simp [w]) s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hl
  have hid:energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:T=>CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (w i) (w i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=
      s.plainEnergy p t X₁ X₂:=by
    simp only [T,energy,positiveSlotRow,NaturalState.plainEnergy,Finset.univ_eq_empty,
      Finset.prod_empty,mul_one]
  rw [hid] at hh
  simpa only [add_zero,Real.norm_eq_abs] using hh

end SevenEighths.CenteredMomentEnergyLowBandEmpty

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowMoments -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowMoments
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceLowChild CenteredMomentEnergyReferenceLowControl
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem reflected_child_uniform_from_low
    (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
    ∀(Wslot:ℝ→ℂ)(bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(C:ℝ)(_hC:0≤C)
    (_hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (_hB:0≤Bmask)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (_hw:∀i,0≤w i)(_hwL:∀i,w i≤Lslot)(_hσlo:∀i,lo≤σ i)(_hσhi:∀i,σ i≤hi)
    (_hheight:0≤height)(_hfreq:∀i,|freq i|≤height)
    (s:NaturalState Z Bmask bΦ)(_hQ:s.fixedModulus=internalQ Q η₀)(_hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(_hX₁:0<X₁)(_hX₂:0<X₂)(_hc₁:X₁≤Z^L)(_hc₂:X₂≤Z^L)
    (_hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
    (_hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6),
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n) :=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S degree
  refine ⟨n,T,D,hD,?_⟩
  intro Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q C hC hlow hB
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsW
    j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hsmall
  have hh:=reflected_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κ Z η₀ Q degree S C hlow hB ha hlo hhi F θ w σ freq t height hw hwL
    hσlo hσhi hheight hfreq s hQ hs Wshort hsW j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂
    hcapacity hsmall
  have hb:=hd Wshort hsW j k v t height hheight
  have hp:0≤C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 <;> ring

end SevenEighths.CenteredMomentEnergyReferenceLowMoments

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLowReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowMoments CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem reference_from_low
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Wslot:ℝ→ℂ)(bslot Bmask L Lslot lo hi Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤Bmask →
      ∀(F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤ s.width →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+(∑i∈F,w i)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=reflected_child_uniform_from_low (α:=α) M H hH a b ha hlo hhi degree S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only
  apply hZ.2 Bmask s Wlong Wshort hsLong hsShort α F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t)
    (fun i=>Z^(w i)) t along bshort _ hlength
  · have hz:0<Z:=zero_lt_one.trans hZ.1
    have hd:0≤diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
    positivity
  · intro v j k x hx
    have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
    exact hchild Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q K hK hlow hBmask
      F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsShort
      j k v (Real.exp x) (Z^bshort) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
      (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hL))
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbshort)
      (by linarith [hwindow.1]) (by linarith [hwindow.1])

end SevenEighths.CenteredMomentEnergyReferenceLowReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLowReflectionError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowMoments CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyReferenceLowReflection CenteredMomentEnergyReferenceLowError
theorem reference_from_low_with_error
    (Fmax:Finset α)(Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask L Lslot Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤Bmask →
      ∀(F:Finset α),F⊆Fmax → ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤Lreflect+along →
      max 0 (s.width-along+xi)≤L → bshort≤L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤ s.width →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+(∑i∈F,w i)≤5*s.width/6 →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^bshort)*∏i∈F,Z^(w i) :=by
  obtain ⟨Cerr,hCerr,herr⟩:=relative_slot_error Fmax Wslot aslot bslot lo hi b haslot hsSlot hcSlot
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low (α:=α) M H hH
    a b bΦ epsilon xi saving Lreflect ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cerr,hC,mul_pos hD hCerr,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask
    F hF θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only
  have hh:=hZ.2 Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity hsmall
  dsimp only at hh
  have he:=herr F hF Wshort (fun x hx=>(hsShort hx).2)
    (naturalCharacter s.character) (fun i=>relativeCharacter M H hH η₀ (θ i))
    (fun i=>primePool M H bslot (Z^(w i))) (fun i=>Z^(w i)) σ freq t
    (Z^bshort) s.radial.scale s.radial.profile (effectiveState s).radial.keep
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) s.radial.scale_pos
    (fun i _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    (fun i _=>hσlo i) (fun i _=>hσhi i)
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1) s.radial.nonneg
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hcoeff:0≤D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
      (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving):=by positivity
  apply hh.trans
  apply add_le_add le_rfl
  convert mul_le_mul_of_nonneg_left he hcoeff using 1 ; ring

end SevenEighths.CenteredMomentEnergyReferenceLowReflectionError

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLiveClippingDefect
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_support_witness (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X : ℝ) (h : rowTwistedSum η m A z W t X ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold rowTwistedSum
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · subst I
        rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
      · rw [hn I hI, mul_zero]
    _ = 0 := tsum_zero

theorem rowTwistedSum_support_scale (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b)
    (h : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b * X := by
  obtain ⟨I, hI, hW⟩ := rowTwistedSum_support_witness η m A z W t X h
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hn.trans ((div_le_iff₀ hX).mp (hs hW))

variable {ι : Type*} [Fintype ι]

theorem positiveSlotRow_support_scales (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  exact ⟨rowTwistedSum_support_scale η m A z W₁ t X₁ b hX₁ hs₁
      (left_ne_zero_of_mul hp),
    rowTwistedSum_support_scale η m A z W₂ t X₂ b hX₂ hs₂
      (right_ne_zero_of_mul hp)⟩

theorem positiveSlotRow_profiles_scales (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  exact positiveSlotRow_support_scales η m A z _ _ S β P t X₁ X₂ b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) h

theorem length_le_raw_add_endpoint (Z X b : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hs : 1 ≤ b * X) : length Z X ≤ Real.logb Z X + Real.logb Z (max 1 b) := by
  have hB : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hc : max 1 X ≤ max 1 b * X := by
    apply max_le
    · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) b) hX.le
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left (1 : ℝ) X)) hc
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  simpa [length, add_comm] using hh

theorem total_clipping_defect (Z X₁ X₂ b : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hs₁ : 1 ≤ b * X₁) (hs₂ : 1 ≤ b * X₂) :
    length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
      2 * Real.logb Z (max 1 b) := by
  have h1 := length_le_raw_add_endpoint Z X₁ b hZ hX₁ hs₁
  have h2 := length_le_raw_add_endpoint Z X₂ b hZ hX₂ hs₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  linarith

theorem endpoint_threshold (b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      2 * Real.logb Z (max 1 b) ≤ δ := by
  let Z₀ := Real.exp (1 + 2 * Real.log (max 1 b) / δ)
  have hb : 0 ≤ Real.log (max 1 b) := Real.log_nonneg (le_max_left _ _)
  have he : 0 < 1 + 2 * Real.log (max 1 b) / δ := by positivity
  have hZ₀ : 1 < Z₀ := Real.one_lt_exp_iff.mpr he
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ
  have hZ : 1 < Z := hZ₀.trans_le hZZ
  have hlog := Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hbound : 2 * Real.log (max 1 b) ≤ δ * Real.log Z := by
    have hh : 2 * Real.log (max 1 b) / δ ≤ Real.log Z := by linarith
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  rw [Real.logb, ← mul_div_assoc]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr hbound

theorem profiles_uniform_defect (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ (η : Character) (m A z : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0 →
        length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ δ := by
  obtain ⟨Z₀, hZ₀, hh⟩ := endpoint_threshold b δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  exact (total_clipping_defect Z X₁ X₂ b (hZ₀.trans_le hZZ) hX₁ hX₂ h1 h2).trans (hh Z hZZ)

theorem total_clipping_defect_nonneg (Z X₁ X₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) := by
  have h1 := Real.logb_le_logb_of_le hZ hX₁ (le_max_right (1 : ℝ) X₁)
  have h2 := Real.logb_le_logb_of_le hZ hX₂ (le_max_right (1 : ℝ) X₂)
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  dsimp only [length]
  linarith

theorem positiveSlotRow_zero_or_defect (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ Z : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases hrow : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
    exact Or.inr ⟨total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂,
      total_clipping_defect Z X₁ X₂ b hZ hX₁ hX₂ h1 h2⟩

theorem energy_support_witness (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : CenteredMomentInductionEnergy.energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≠ 0) :
    ∃ z : O, keep z ∧ positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold CenteredMomentInductionEnergy.energy
  calc
    _ = ∑' _z : O, (0 : ℝ) := by
      apply tsum_congr
      intro z
      by_cases hk : keep z
      · simp only [ite_eq_left hk, hn z hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      · simp only [ite_eq_right hk]
    _ = 0 := tsum_zero

theorem energy_zero_or_defect (η : Character) (m A : O) (t : ℝ)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ Z : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
        S β P X₁ X₂ keep Φ K = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases h : CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
      S β P X₁ X₂ keep Φ K = 0
  · exact Or.inl h
  · obtain ⟨z, _, hz⟩ := energy_support_witness η m A t _ _ S β P X₁ X₂ keep Φ K h
    exact Or.inr ((positiveSlotRow_zero_or_defect η m A z p S β P t X₁ X₂ Z hZ hX₁ hX₂).resolve_left hz)

theorem raw_gates_of_defect (Z M X₁ X₂ ell κ e : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hdefect : length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ e)
    (hlarge : 5*M/6 ≤ length Z X₁ + length Z X₂ + ell)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*ell ≤ M) :
    5*M/6-e ≤ Real.logb Z (X₁ * X₂)+ell ∧
      Real.logb Z (X₁ * X₂)+ell+(6*κ-1)*ell ≤ M := by
  have hnonneg := total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂
  constructor <;> nlinarith

theorem robust_slot_budgets (M total ell kappa defect : ℝ)
    (hell : 0 ≤ ell) (hk : 3/4 ≤ kappa)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M) :
    ell ≤ M/21+2*defect/7 ∧ (6*kappa-1)*ell ≤ M/6+defect := by
  have hkell : 7/2*ell ≤ (6*kappa-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M xi defect : ℝ) (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hreserve : xi+11*defect/7 ≤ M/14) : defect ≤ M := by
  linarith

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hk : 3/4 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (hreserve : xi+11*defect/7 ≤ M/14) :
    15*M/28-9*defect/7 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hb⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (_hs : 0 ≤ short) (hsM : short ≤ M/4)
    (_hell : 0 ≤ ell) (_hz : 0 ≤ z) (hze : z ≤ ell) (hk : 3/4 ≤ kappa)
    (he : ell ≤ M/21+2*defect/7)
    (hbudget : (6*kappa-1)*ell ≤ M/6+defect)
    (hxi : 0 ≤ xi) (hdefect : 0 ≤ defect) (hdefectM : defect ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+xi)) :
    0 < along ∧ reflected+short+z ≤ 16*M/21+xi+4*defect/7 ∧
      reflected+short+6*kappa*z ≤ 13*M/14+xi+11*defect/7 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*kappa-1)*z ≤ M/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ M/21+2*defect/7 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M xi defect short reflected z kappa : ℝ)
    (hd : 0 ≤ defect) (hreserve : xi+11*defect/7 ≤ M/14)
    (ht : reflected+short+z ≤ 16*M/21+xi+4*defect/7)
    (hc : reflected+short+6*kappa*z ≤ 13*M/14+xi+11*defect/7) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*kappa*z ≤ M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hk : 3/4 ≤ kappa)
    (hxi : 0 ≤ xi) (hd : 0 ≤ defect)
    (hreserve : xi+11*defect/7 ≤ M/14)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4)
    (href : reflected ≤ max 0 (M-along+xi)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*kappa*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧
      reflected+short+6*kappa*z ≤ M) := by
  obtain ⟨he,hbudget⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*kappa)
    nlinarith
  · obtain ⟨hapos, ht, hc⟩ := robust_reflected_low M short along ell z kappa xi defect reflected
      hM hs hsM hell hz hze hk he hbudget hxi hd
      (robust_defect_le_width M xi defect hM hxi hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨hapos, robust_reflected_low_admissible M xi defect short reflected z kappa hd hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀M : ℝ, M₀ ≤ M →
      M₀/56+11*(M₀/56)/7 ≤ M/14 := by
  constructor
  · positivity
  · intro M hM
    linarith

open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacity

theorem robust_deleted_reference_cases (Z M X₁ X₂ ell z κ ξ e reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 3/4 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+11*e/7 ≤ M/14)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I)
    (href : reflected ≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+ξ)) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let long := length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+long+z ≤ 5*M/6 ∧ short+long+6*κ*z ≤ M) ∨
    (0 < Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ∧
      reflected+short+z ≤ 16*M/21+ξ+4*e/7 ∧
      reflected+short+6*κ*z ≤ 13*M/14+ξ+11*e/7) := by
  dsimp only
  have hb := robust_balanced_long_nonneg M (Real.logb Z (X₁*X₂)) ell κ ξ e
    hM hell hκ hξ hlarge hcap hreserve
  have hpos := comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hlog : Real.logb Z (comparisonSecond Z M X₁ X₂) = Real.logb Z (X₁*X₂)-M/4 := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hY : 1 ≤ comparisonSecond Z M X₁ X₂ := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hn₂ := product_norm_ge_one D₂ hD₂
  have hlongpos := div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort := deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0 := length_nonneg Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ)) hZ
  have hlong : length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ≤
      Real.logb Z (X₁*X₂)-M/4 := by
    rw [← hlog]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _)) (max_le hY (div_le_self hpos.2.le hn₂))
  by_cases hlo : length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ))+
      length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hkc := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · apply Or.inr
    obtain ⟨hellbound, hslot⟩ := robust_slot_budgets M (Real.logb Z (X₁*X₂)) ell κ e
      hell hκ hlarge hcap
    apply robust_reflected_low M _ _ ell z κ ξ e reflected hM hshort0 hshort hell hz hze hκ
      hellbound hslot hξ he (robust_defect_le_width M ξ e hM hξ hreserve) _ href
    rw [← CenteredMomentEnergyReferenceLowBranchGeometry.length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

theorem robust_deleted_reference_window (Z M X₁ X₂ ell z κ ξ e : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 3/4 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+11*e/7 ≤ M/14)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
    (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
      length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
      length Z (Real.exp x)+short+6*κ*z ≤ M) := by
  dsimp only
  let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))
  rcases robust_deleted_reference_cases Z M X₁ X₂ ell z κ ξ e (max 0 (M-along+ξ))
    hZ hM hX₁ hX₂ hell hz hze hκ hξ he hreserve hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, ?_⟩
    intro x hx
    have hh := CenteredMomentEnergyReferenceLowWindow.reflection_window_length Z
      (max 0 (M-along+ξ)) x hZ (le_max_left _ _) hx
    have hb := robust_reflected_low_admissible M ξ e _ (max 0 (M-along+ξ)) z κ
      he hreserve h.2.1 h.2.2
    constructor <;> linarith [hh.1]

theorem live_profiles_reference_window (a b M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ e ξ Z₀ : ℝ, 0 < e ∧ 0 < ξ ∧ 1 < Z₀ ∧
      ∀ (Z M : ℝ), Z₀ ≤ Z → M₀ ≤ M →
      ∀ (η : Character) (m A u : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ ell z κ : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ ell →
        0 ≤ z → z ≤ ell → 3/4 ≤ κ →
        5*M/6 ≤ length Z X₁+length Z X₂+ell →
        length Z X₁+length Z X₂+6*κ*ell ≤ M →
      ∀ (D₁ D₂ : Finset (Ideal O)), (∀ I ∈ D₁, Prime I) → (∀ I ∈ D₂, Prime I) →
      positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
      (let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
       let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
       (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
        short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
       (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
         length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
         length Z (Real.exp x)+short+6*κ*z ≤ M)) := by
  have he : 0 < M₀/56 := by positivity
  obtain ⟨Z₀, hZ₀, hdefect⟩ := profiles_uniform_defect (ι := ι) a b (M₀/56) he
  refine ⟨M₀/56, M₀/56, Z₀, he, he, hZ₀, ?_⟩
  intro Z M hZZ hMM η m A u p S β P t X₁ X₂ ell z κ hX₁ hX₂ hell hz hze hκ hlarge hcap D₁ D₂ hD₁ hD₂
  by_cases hrow : positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · apply Or.inr
    have hZ := hZ₀.trans_le hZZ
    obtain ⟨hl, hc⟩ := raw_gates_of_defect Z M X₁ X₂ ell κ (M₀/56) hZ hX₁ hX₂
      (hdefect Z hZZ η m A u p S β P t X₁ X₂ hX₁ hX₂ hrow) hlarge hcap
    exact robust_deleted_reference_window Z M X₁ X₂ ell z κ (M₀/56) (M₀/56)
      hZ (hM₀.le.trans hMM) hX₁ hX₂ hell hz hze hκ he.le he.le
      ((robust_fixed_slack M₀ hM₀).2 M hMM) hl hc D₁ D₂ hD₁ hD₂

end SevenEighths.CenteredMomentEnergyLiveClippingDefect

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.DeletedRobustGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyDeletedRobustGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyLiveClippingDefect
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(he:0≤e)(hreserve:xi+11*e/7≤ s.width/14)
    (hlarge:5*s.width/6-e≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):= by
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hb := robust_balanced_long_nonneg s.width (Real.logb Z (X₁*X₂)) ell κ xi e
    s.width_nonneg hell hκ hxi hlarge hcap hreserve
  have hy₁ : 1 ≤ comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  have hy₂ : 1 ≤ comparisonSecond Z s.width X₁ X₂ := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hbase hZ.ne']
  have hd₁ := divisor_reflection_range s hZ Mcap _ hwidth hy₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap _ hwidth hy₂ D₂ hD₂
  dsimp only at hd₁ hd₂
  rw [hf] at hd₁
  rw [hl] at hd₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  have hlog₁ := Real.logb_nonneg hZ hn₁
  have hlog₂ := Real.logb_nonneg hZ hn₂
  have hMcap : 0 ≤ Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 ≤ L := by linarith
  have hslot : 0 ≤ (6*κ-1)*ell := mul_nonneg (by linarith) hell
  dsimp only
  refine ⟨hd₁.2.2, hd₂.2.2, by linarith, by linarith [s.width_nonneg],
    by linarith, hd₂.2.1, max_le hLc (by linarith [hd₂.1]), ?_⟩
  have hp₁ : ∀ I ∈ D₁, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₁ hi)
  have hp₂ : ∀ I ∈ D₂, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₂ hi)
  let along := Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
  have halong : Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏ P ∈ D₂, P).absNorm : ℝ)) = along := by
    rw [← hd₂.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  rcases robust_deleted_reference_cases Z s.width X₁ X₂ ell z κ xi e (max 0 (s.width-along+xi))
    hZ s.width_nonneg hX₁ hX₂ hell hz hze hκ hxi he hreserve hlarge hcap D₁ D₂ hp₁ hp₂
    (by rw [halong]) with hc | hc
  · exact Or.inl (by simpa only [hd₁.2.2, hd₂.2.2] using hc)
  · apply Or.inr
    have hh := robust_reflected_low_admissible s.width xi e _ (max 0 (s.width-along+xi)) z κ
      he hreserve hc.2.1 hc.2.2
    simpa only [hd₁.2.2] using hh

end SevenEighths.CenteredMomentEnergyDeletedRobustGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionDeleted -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeleted
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionGeometry CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem deleted_original_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi≤ s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=Real.logb Z (X₁/((∏I∈D₁,I).absNorm:ℝ))
  let along:=Real.logb Z (X₂/((∏I∈D₂,I).absNorm:ℝ))
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=>hw i)
  have hg:=actual_deleted_gates s hZ.1 (by linarith) hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=>hw i)) hsum hsumle hκ hxi.le hxiM hshort hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0<Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤L:=by linarith [s.width_nonneg]
  have hlog:0≤Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=>Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=>polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=>polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeleted

end

end OAI

end

