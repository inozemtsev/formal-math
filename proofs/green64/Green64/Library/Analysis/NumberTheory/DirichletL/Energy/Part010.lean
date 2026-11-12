module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part036
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part007
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.AllocatedHomogeneous -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_clipped_homogeneous_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(Bmask εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_clipped_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  obtain ⟨n,T,Cp,hCp,hprofile⟩:=retained_pair_control a b haPlain S
  refine ⟨n,T,dc,Cc*Cp^2,mul_pos hCc (sq_pos_of_pos hCp),?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ Bmask εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have he:=hbound Z hZ a b Bmask L εchild haPlain hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only at he ⊢
  let U:Fin 2→ℝ:=![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
  have hU:∀i,0<U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D alloc X₁ hX₁ 0
    · exact rawScale_pos D alloc X₂ hX₂ 1
  have hp:(pair D alloc haPlain p v X₁ X₂ hX₁ hX₂).control S≤
      Cp*p.control T*(1+|v|+height)^(2*n):=by
    have h:=hprofile p U hU v
    have hpw:(1+‖v‖)^(2*n)≤(1+|v|+height)^(2*n):=
      pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith) _
    exact h.trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hCp.le (p.control_nonneg T)))
  apply he.trans
  calc
    _≤Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (Cp*p.control T*(1+|v|+height)^(2*n))^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans st.base_ge_one) _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2)
        (mul_nonneg (mul_nonneg hCc.le (add_nonneg hC₀ hC₁)) (diagonalControl_nonneg _))
    _=_:=by
      have hpow:(1+|v|+height)^(4*n)=((1+|v|+height)^(2*n))^2:=by
        rw [←pow_mul]
        congr 1
        omega
      simp only [←add_assoc,mul_pow,pow_add,hpow]
      ring

end SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalChildBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalChildBound
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        ((τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1))*
        Z^(εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) (Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_clipped_homogeneous_bands (α:=α) M H hH W aslot bslot
    Mcap 2 Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap (by norm_num)
    hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hZ1:1<Z:=hZ₀.trans_le hZ
  let st:=canonicalState Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  have he:=hbound Z hZ 0 εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st rfl rfl hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hpow:=canonicalState_power Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  change Z^st.width=(τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1) at hpow
  dsimp only at he ⊢
  have heq:st.width+εchild+εremove+
      CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
        (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh =
    st.width+(εchild+εremove+CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by ring
  rw [heq,Real.rpow_add (zero_lt_one.trans hZ1),hpow] at he
  convert he using 1 <;> simp only [st,canonicalState,NaturalState.width] ; ring

end SevenEighths.CenteredMomentEnergyCanonicalChildBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalLiveBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveBound
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def LiveChild (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):Prop:=
  ∃z:O,r.keep z ∧ (r.profile (‖eisEmbedding z‖^2/r.scale)).re≠0 ∧
    child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0

theorem energy_zero_of_not_live (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α)
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hn:¬LiveChild η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
  rw [←child_radial_eq_energy η r hz D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂]
  unfold radialEnergy
  apply (tsum_congr (g:=fun _ : O=>(0:ℝ)) ?_).trans (tsum_zero)
  intro z
  by_cases hk:r.keep z
  · rw [ite_eq_left hk]
    by_cases hφ:(r.profile (‖eisEmbedding z‖^2/r.scale)).re=0
    · rw [hφ,mul_zero]
    · have hc:child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
        by_contra hh
        exact hn ⟨z,hk,hφ,hh⟩
      simp only [hc,norm_zero,zero_pow (by decide:2≠0),zero_mul]
  · rw [ite_eq_right hk]

open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_live_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀Mnom cost:ℝ,
    (LiveChild τ (canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J →
      Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom+
        CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
          (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂))
          (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6≤ cost) →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+cost+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro Mnom cost hcost
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  by_cases hne:LiveChild τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · have he:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    dsimp only at he
    have hnorm:0<(τ.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
    have hpower:Z^(Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))=
        (τ.modulus.absNorm:ℝ)*dyadicScale (dyad 1):=by
      rw [Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' (dyadicScale_pos _),
        Real.rpow_logb hz0 hz.ne' hnorm,mul_comm]
    apply he.trans
    rw [←hpower,mul_assoc,←Real.rpow_add hz0]
    apply mul_le_mul_of_nonneg_left _ (by
      have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
      have hp:=p.control_nonneg T
      positivity)
    apply Real.rpow_le_rpow_of_exponent_le hz.le
    have hh:=hcost hne
    linarith
  · have he:=energy_zero_of_not_live τ rad (fun z hz=>hz.1) D alloc V₁ V₂
      d.slots d.coefficient d.P d.P_pos v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hne
    change allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J≤_
    rw [he]
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hp:=p.control_nonneg T
    positivity

end SevenEighths.CenteredMomentEnergyCanonicalLiveBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalLiveCapacity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyCanonicalLiveBound
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentRetainedProfile
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyBands
open CenteredMomentEnergyDeletedChildCapacity CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

lemma original_deleted_excess (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ:Character)(v Z X₁ X₂ κ Mactual:ℝ)(w:α→ℝ)
    (hZ:1<Z)(hscale:∀i,src.P i=Z^(w i))(F₁ F₂:Finset (Ideal O)):
    deletedExcess D alloc Z X₁ X₂ κ Mactual
      (commonData (withHeight src τ v) C R B).P F₁ F₂ J =
    CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) Mactual κ:=by
  unfold deletedExcess CenteredMomentLiveCapacity.excess originalImage
  simp only [Finset.sum_map,originalEmbedding,Function.Embedding.coeFn_mk]
  congr 3
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change Real.logb Z (src.P i.val)=w i.val
  rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem live_source_paid_cost (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset
      (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (τ:Character)(rad:Radial)(V₁ V₂:Plain)(v Z X₁ X₂ κ A M Mnom Mactual u ell δ₁ δ₂ θ:ℝ)
    (w:α→ℝ)(h₁:0<X₁)(h₂:0<X₂)(F₁ F₂:Finset (Ideal O))
    (hZ:1<Z)(hκ:0≤κ)(hw:∀i,0≤w i)(hscale:∀i,src.P i=Z^(w i))
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hparent:A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-M+6*(u+ell)+δ₁)
    (hwidth:Mactual-Mnom≤δ₂)(hu:0≤u)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hlive:LiveChild τ rad D alloc V₁ V₂
      (commonData (withHeight src τ v) C R B).slots
      (commonData (withHeight src τ v) C R B).coefficient
      (commonData (withHeight src τ v) C R B).P v X₁ X₂ h₁ h₂ F₁ F₂ J):
    Mactual-Mnom+CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) Mactual κ/6≤
      δ₂+u+ell+δ₁/6+θ/3:=by
  obtain ⟨z,hz,hφ,hchild⟩:=hlive
  let d:=commonData (withHeight src τ v) C R B
  have hP:∀i,1≤d.P i:=by
    intro i
    change 1≤ src.P i.val
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i.val)
  have hp:A+(6*κ-1)*(∑i,Real.logb Z (d.P i))≤M:=by
    simpa only [d,commonData,withHeight,hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hparent
  have hb:=child_paid_width (naturalCharacter τ z) D alloc V₁ V₂ d.slots d.coefficient d.P
    v Z X₁ X₂ κ A M Mnom Mactual u ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J
    hZ hκ hP hF₁ hF₂ hchild hp hshift hwidth hu hell hδ₁ hδ₂ hθ hclip
  rw [original_deleted_excess src C R B D alloc J τ v Z X₁ X₂ κ Mactual w hZ hscale F₁ F₂] at hb
  linarith

end SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalPaidSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalPaidSource
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_canonical_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_live_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    Mnom (δ₂+u+ell+δ₁/6+θclip/3)
  intro hlive
  exact live_source_paid_cost src C R B D alloc J τ (canonicalRadial τ (internalQ Q η₀) dyad)
    (sourcePlain a b haPlain (p.profile 0) (p.support 0))
    (sourcePlain a b haPlain (p.profile 1) (p.support 1))
    v Z X₁ X₂ κ A Mparent Mnom
    (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))
    u ell δ₁ δ₂ θclip w hX₁ hX₂ F₁ F₂ (hZ₀.trans_le hZ)
    (by linarith) hw hmatch.scale hF₁ hF₂ hparent hshift hdefect hu hell hδ₁ hδ₂ hθclip hclip hlive

end SevenEighths.CenteredMomentEnergyCanonicalPaidSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalCommonPaid -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalCommonPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_common_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε hbeta hκ
  obtain ⟨Cm,hCm,hcommon⟩:=actual_common_from_energy (α:=α) (fun _=>bslot) (fun _=>Mslot)
    (fun _=>hMslot) εmask hεmask
  refine ⟨n,T,dc,2*Cm*Cc,by positivity,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent Mnom u ell δ₁ δ₂ θclip
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  let E:=Cc*(C₀+C₁)*diagonalControl rad.profile*(p.control T)^2*
    (1+(|v|+height))^(dc+degree+4*n)*
    Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh)
  have hz:1<Z:=hZ₀.trans_le hZ
  have he:0≤E:=by
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hz0:0<Z:=zero_lt_one.trans hz
    dsimp [E]
    positivity
  have hleft:∀X₁ X₂:ℝ,∀h₁:0<X₁,∀h₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
      X₁*X₂=d.X₁*d.X₂ → ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
      ∀J,allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
        v X₁ X₂ h₁ h₂ F₁ F₂ J≤E:=by
    intro X₁ X₂ h₁ h₂ hc₁ hc₂ hprod F₁ F₂ hF₁ hF₂ J
    apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ h₁ h₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
      A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent _ hdefect hclip
    simpa only [hprod] using hshift
  have hh:=hcommon src hhi hMs τ v C R hR B D alloc V₁ V₂ hp₁ hp₂ rad
    (fun z hz=>hz.1) E E he he (by
      intro left F₁ hF₁ F₂ hF₂ J hJ
      have hf₁:∀I∈F₁,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₁) hi)).ne_zero
      have hf₂:∀I∈F₂,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₂) hi)).ne_zero
      cases left
      · exact hleft d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos hY₁ hY₂ d.same_product F₁ F₂ hf₁ hf₂ J
      · exact hleft d.X₁ d.X₂ d.X₁_pos d.X₂_pos hX₁ hX₂ rfl F₁ F₂ hf₁ hf₂ J)
  apply hh.trans_eq
  dsimp [E]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalReferencePaid -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalReferencePaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_reference_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_common_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  have hr:1≤ ratioPenalty dyad:=le_max_left _ _
  have hr0:0< ratioPenalty dyad:=zero_lt_one.trans_le hr
  have hlog:0≤Real.logb Z (ratioPenalty dyad):=Real.logb_nonneg hz hr
  have hh:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent (Real.logb Z reference) u ell
    (δ₁+Real.logb Z (ratioPenalty dyad)) δ₂ θclip hu hell (by linarith) hδ₂ hθclip
    hparent (by linarith) hdefect hclip
  have hpow:Z^(Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh)=
      reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh):=by
    rw [show Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh=
      Real.logb Z reference+Real.logb Z (ratioPenalty dyad)*((1:ℝ)/6)+
        (εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) by ring]
    rw [Real.rpow_add hz0,Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' href,
      Real.rpow_mul hz0.le,Real.rpow_logb hz0 hz.ne' hr0]
  rw [hpow] at hh
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentEnergyCanonicalReferencePaid

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalNestedReference -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalNestedReference
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem nested_original_subsets_reference_paid (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀Jparent:Finset α,∀Jorig:Finset Jparent,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  let Pairs:=ΣJparent:Finset α,Finset Jparent
  have hex (J:Pairs):=actual_reference_paid_source (α:=J.2) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Pairs,n J
  let dc₀:=∑J:Pairs,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Pairs,Cc J
  have hCt:0<Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset Pairs))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Pairs,J.2→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1<Z₀:=by
    have hn:Nonempty Choices:=⟨⟨⟨∅,∅⟩,fun i=>False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jparent Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨⟨Jparent,Jorig⟩,θ⟩≤Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨⟨Jparent,Jorig⟩,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp₀:=positiveAt_subtype M H hH Jparent W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hp₀
  have hh:=hb ⟨⟨Jparent,Jorig⟩,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc ⟨Jparent,Jorig⟩≤Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
    dsimp [Ctot];linarith
  have ht:T ⟨Jparent,Jorig⟩⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨⟨Jparent,Jorig⟩,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T ⟨Jparent,Jorig⟩)≤p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n ⟨Jparent,Jorig⟩≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdc₀:dc ⟨Jparent,Jorig⟩≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdeg:dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T ⟨Jparent,Jorig⟩)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0< ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyCanonicalNestedReference

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalUniformReference
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_subsets_reference_paid (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀Jorig:Finset α,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0< reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  have hex (J:Finset α):=actual_reference_paid_source (α:=J) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Finset α,n J
  let dc₀:=∑J:Finset α,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Finset α,Cc J
  have hCt:0<Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset (Finset α)))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Finset α,J→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1<Z₀:=by
    have hn:Nonempty Choices:=⟨⟨∅,fun i=>False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨Jorig,θ⟩≤Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨Jorig,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hh:=hb ⟨Jorig,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc Jorig≤Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ Jorig)
    dsimp [Ctot];linarith
  have ht:T Jorig⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Jorig,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T Jorig)≤p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n Jorig≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Jorig)
  have hdc₀:dc Jorig≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Jorig)
  have hdeg:dc Jorig+degree+4*n Jorig≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc Jorig+degree+4*n Jorig)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T Jorig)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0< ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyCanonicalUniformReference

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

omit [DecidableEq α] in
lemma common_raw_caps (src:Input α)(C R:Ideal O)(B:actualAllocations src.pools C)
    (τ:Character)(t F:ℝ)(h₁:src.X₁≤F)(h₂:src.X₂≤F)(h₃:src.Y₁≤F)(h₄:src.Y₂≤F):
    let d:=commonData (withHeight src τ t) C R B
    d.X₁≤F ∧ d.X₂≤F ∧ d.Y₁≤F ∧ d.Y₂≤F:=by
  have hN (j:α⊕Fin 2):(1:ℝ)≤Ideal.absNorm (B.val j):=
    norm_ge_one _ (alloc_ne src C B j)
  exact ⟨(div_le_self src.X₁_pos.le (hN _)).trans h₁,
    (div_le_self src.X₂_pos.le (hN _)).trans h₂,
    (div_le_self src.Y₁_pos.le (hN _)).trans h₃,
    (div_le_self src.Y₂_pos.le (hN _)).trans h₄⟩

theorem actual_main_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤ sigma → 1≤ cost → 0<asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock τ t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kmain dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family τ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(sigma/3+δpaid/6+θclip/3)+κ*mesh):=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=child src C R0 B τ t
  let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hKmain:0<Kmain:=by dsimp [Kmain];unfold mainCommonRadius;positivity
  have hP:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_main_admission src τ τ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource hmod Scols βsource C₂ D₂
    hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical Cpick Rpick hside B₂ hB₂
    κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=matches_child M H hH hmatch C R0 B τ t
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps input Cpick Rpick B₂ (family χ) v (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hq:(τ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ):=by nlinarith
  have hdef:=actual_width_le_reference hfamily t Scols βsource Rwindow rows Wkernel Kmain hKmain dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)) Z hq hz χ
  have hn:=actual_dyad_ge_one t Scols βsource Rwindow rows Wkernel Kmain dyad hphysical
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>θ i.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) v height mesh hmesh
    (fun i=>hw i.val) (fun i=>hwm i.val) (fun i=>hwL i.val) (fun i=>hσlo i.val)
    (fun i=>hσhi i.val) hheight (fun i=>hfreq i.val) input hm
    (fun i=>hhi i.val) (fun i=>hMs i.val) Cpick Rpick B₂ Dalloc alloc hRpick
    (family χ) dyad hn hwidth p hp₁ hp₂ caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
    (Real.logb Z (volume src)) Mdecl (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad)
    0 (sigma/3) _ 0 θclip (envelope_pos _ (mul_pos hcost0 hτnorm) _ _ hC₂ _ _) le_rfl
    (by positivity) hδ le_rfl hθclip
    (by simpa only [input,CenteredMomentAmplificationChildInput.child,commonData,withHeight,hmatch.scale,
      Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hpar)
    (by simpa only [CenteredMomentAllocatedChildCapacity.preVolume,commonData,withHeight,
      zero_add] using hshift)
    (by linarith) hclip
  simpa only [zero_add] using hh

end SevenEighths.CenteredMomentEnergyCanonicalMainPaid

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPaid -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPaid
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][instα:DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

def castAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C):actualAllocations t.pools C:=
  ⟨B.val,by rw [←h];exact B.property⟩

def castDivisorAllocation (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val⊕Fin 2)):=alloc

def restoreDivisorAllocation (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))):
    Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val⊕Fin 2)):=alloc

lemma cast_child_energy (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight s τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight t τ v) C R (castAllocation s t h C B)) rad D
        (castDivisorAllocation s t h C B D alloc):=by
  subst t
  rfl

lemma restored_child_energy (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ)(D:Ideal O)
    (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (rad:Radial):
    childEnergy (commonData (withHeight (activeInput s) τ v) C R B) rad D alloc=
      childEnergy (commonData (withHeight s τ v) C R (restoreAllocation s C B)) rad D
        (restoreDivisorAllocation s C B D alloc):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  exact child_energy_active s C R B τ v D alloc rad

omit instα in
lemma cast_preVolume (s t:Input α)(h:s=t)(C R:Ideal O)
    (B:actualAllocations s.pools C)(τ:Character)(v:ℝ):
    CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight t τ v) C R (castAllocation s t h C B))=
      CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R B):=by
  subst t
  rfl

omit instα in
lemma cast_slot_sum (s t:Input α)(h:s=t)(C:Ideal O)
    (B:actualAllocations s.pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (castAllocation s t h C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

omit instα in
lemma restored_preVolume (s:Input α)(C R:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(τ:Character)(v:ℝ):
    CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight s τ v) C R (restoreAllocation s C B))=
      CenteredMomentAllocatedChildCapacity.preVolume (commonData (withHeight (activeInput s) τ v) C R B):=rfl

omit instα in
lemma restored_slot_sum (s:Input α)(C:Ideal O)
    (B:actualAllocations (activeInput s).pools C)(f:α→ℝ):
    (∑i:CenteredMomentCommonProfile.liveIndices (restoreAllocation s C B).val,f i.val)=
      ∑i:CenteredMomentCommonProfile.liveIndices B.val,f i.val:=rfl

theorem actual_error_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤ sigma → 1≤ cost → 0<asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(errorRemoval prime Z k+δpaid/6+θclip/3)+κ*mesh):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=nested_original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  subst input
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let restored:=restoredError src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have heInput:input=activeInput restored:=by
    exact error_source_active src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let B₂a:=castAllocation input (activeInput restored) heInput Cpick B₂
  let B₂r:=restoreAllocation restored Cpick B₂a
  let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hKerror:0<Kerror:=by dsimp [Kerror];unfold errorCommonRadius;positivity
  have hP:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_active_error_admission src τ υ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource prime hprime k hk hsigma hprimeScale
    hslot Bp v0 hmod Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    Cpick Rpick hside B₂ hB₂ κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=restoredError_matches M H hH hmatch C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps (child src C R0 B τ t) ((Ideal.span {prime})^k) (R0*C)
    (restoreAllocation (child src C R0 B τ t) ((Ideal.span {prime})^k) Bp) υ v0 (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have caps₃:=common_raw_caps restored Cpick Rpick B₂r (family χ) v (Z^L)
    caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=by positivity
  have hdef:=actual_width_le_reference hfamily v0 Scols βsource Rwindow rows Wkernel Kerror hKerror dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Z hυ hz χ
  have hn:=actual_dyad_ge_one v0 Scols βsource Rwindow rows Wkernel Kerror dyad hphysical
  have hrem:0≤errorRemoval prime Z k:=by
    have hn:0≤Real.logb Z (normValue prime):=by linarith
    unfold errorRemoval
    positivity
  have hsum:(∑i:CenteredMomentCommonProfile.liveIndices B₂.val,Real.logb Z (input.P i.val))=
      ∑i:CenteredMomentCommonProfile.liveIndices B₂.val,w i.val.val.val:=by
    apply Finset.sum_congr rfl
    intro i hi
    change Real.logb Z (src.P i.val.val.val)=w i.val.val.val
    rw [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne']
  have hparw:Real.logb Z (volume src)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B₂r.val,w i.val.val.val)≤Mdecl:=by
    rw [hsum] at hpar
    have heSum := (restored_slot_sum restored Cpick B₂a (fun i=>w i.val.val)).trans
      (cast_slot_sum input (activeInput restored) heInput Cpick B₂ (fun i=>w i.val.val))
    exact (congrArg (fun x=>Real.logb Z (volume src)+(6*κ-1)*x) heSum).trans_le hpar
  have hshiftw:
      Real.logb Z ((commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₁*
        (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₂*
        ∏i:CenteredMomentCommonProfile.liveIndices B₂r.val,restored.P i.val)-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)≤
      Real.logb Z (volume src)-Mdecl+6*(errorRemoval prime Z k+0)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          sourceReserve src input C D Z delta reserve cost asource)+Real.logb Z (ratioPenalty dyad):=by
    change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
      (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r))-_≤_
    have hpv:= (restored_preVolume restored Cpick Rpick B₂a (family χ) v).trans
      ((cast_preVolume input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v).trans
        (common_preVolume_height input Cpick Rpick B₂ (family χ) υ v v0))
    calc
      _ = Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
          (commonData (withHeight input υ v0) Cpick Rpick B₂)) -
          Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad) :=
        congrArg (fun x=>Real.logb Z x - Real.logb Z
          (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)) hpv
      _ ≤ _ := by
        dsimp only [input]
        simpa only [add_zero] using hshift
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val)
    (CenteredMomentCommonProfile.liveIndices Bp.val) (fun i=>θ i.val.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val.val) (fun i=>σ i.val.val) (fun i=>freq i.val.val) v height mesh hmesh
    (fun i=>hw i.val.val) (fun i=>hwm i.val.val) (fun i=>hwL i.val.val) (fun i=>hσlo i.val.val)
    (fun i=>hσhi i.val.val) hheight (fun i=>hfreq i.val.val)
  have hh := hh restored hm (fun i=>hhi i.val.val) (fun i=>hMs i.val.val)
  have hh := hh Cpick Rpick B₂r
  let allocA:=castDivisorAllocation input (activeInput restored) heInput Cpick B₂ Dalloc alloc
  let allocR:=restoreDivisorAllocation restored Cpick B₂a Dalloc allocA
  have hh := hh Dalloc allocR hRpick
  have hh := hh (family χ) dyad hn hwidth
  have hh := hh p hp₁ hp₂
  have hh := hh caps₃.1 caps₃.2.1 caps₃.2.2.1 caps₃.2.2.2
  have hh := hh (Real.logb Z (volume src)) Mdecl
    (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)
    (errorRemoval prime Z k) 0
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource)
    0 θclip (envelope_pos _ hqpos _ _ hC₂ _ _)
    hrem le_rfl hδ le_rfl hθclip
  have hh := hh hparw
  have hh := hh hshiftw
  have hh := hh (by linarith only [hdef]) hclip
  have he := (cast_child_energy input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v Dalloc alloc
    (canonicalRadial (family χ) (internalQ Q η₀) dyad)).trans
      (restored_child_energy restored Cpick Rpick B₂a (family χ) v Dalloc allocA
        (canonicalRadial (family χ) (internalQ Q η₀) dyad))
  apply he.trans_le
  simpa only [zero_add,add_zero] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPaid

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ChildEnvelopeFitting -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyChildEnvelopeFitting
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentSecondNonexceptionalChosenBlock
local notation "O" => HeckeFamily.O

lemma radical_product_power (R C:Ideal O)(hR:R≠0)(hC:C≠0)
    (Z BR BC ε:ℝ)(hZ:0<Z)(hε:0≤ε)
    (hRN:(R.absNorm:ℝ)≤Z^BR)(hCN:(C.absNorm:ℝ)≤Z^BC):
    ((R*C).radical.absNorm:ℝ)^ε≤Z^((BR+BC)*ε):=by
  have hRC:R*C≠0:=mul_ne_zero hR hC
  have hr:((R*C).radical.absNorm:ℝ)≤(R*C).absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hRC))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=R*C))))
  have hh:(R*C).absNorm≤Z^(BR+BC):=by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
    exact mul_le_mul hRN hCN (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hZ _).le
  rw [Real.rpow_mul hZ.le]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (hr.trans hh) hε

lemma independent_height (v height:ℝ)(hheight:0≤height)(degree:ℕ):
    (1+(|v|+height))^degree≤(1+height)^degree*(1+‖v‖)^(2*degree):=by
  have hh:1+(|v|+height)≤(1+height)*(1+‖v‖):=by
    rw [Real.norm_eq_abs]
    nlinarith [mul_nonneg hheight (abs_nonneg v)]
  have hp:=pow_le_pow_left₀ (by positivity:0≤1+(|v|+height)) hh degree
  rw [mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [norm_nonneg v]:1≤1+‖v‖) (by omega:degree≤2*degree)) (by positivity))

def coefficient {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ):ℝ:=
  Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
    (p.control T)^2*(1+height)^degree*Z^exponent

lemma coefficient_nonneg {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (height:ℝ)(degree:ℕ)(Z exponent:ℝ)(hC:0≤Cc)(h₀:0≤C₀)(h₁:0≤C₁)
    (hH:0≤height)(hZ:0≤Z):0≤ coefficient Cc C₀ C₁ p T height degree Z exponent:=by
  unfold coefficient
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  positivity

theorem paid_rhs_fit {a b:ℝ}(Cc C₀ C₁:ℝ)(p:Profiles a b)(T:Finset (ℕ×ℕ))
    (R C:Ideal O)(hR:R≠0)(hC:C≠0)(τ:Character)(Q:Ideal O)(dyad:Fin 4→ℤ)
    (v height:ℝ)(degree:ℕ)(Z BR BC εmask exponent loss reference ratio:ℝ)
    (hCc:0≤Cc)(h₀:0≤C₀)(h₁:0≤C₁)(hH:0≤height)(hZ:1≤Z)(hε:0≤εmask)
    (hRN:(R.absNorm:ℝ)≤Z^BR)(hCN:(C.absNorm:ℝ)≤Z^BC)
    (hloss:exponent≤loss)(href:0≤ reference)(hratio:0≤ ratio):
    Cc*((R*C).radical.absNorm:ℝ)^εmask*(C₀+C₁)*
      diagonalControl (canonicalRadial τ Q dyad).profile*(p.control T)^2*
      (1+(|v|+height))^degree*reference*ratio^((1:ℝ)/6)*Z^exponent≤
    coefficient Cc C₀ C₁ p T height degree Z ((BR+BC)*εmask+loss)*
      reference*ratio^((1:ℝ)/6)*(1+‖v‖)^(2*degree):=by
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hr:=radical_product_power R C hR hC Z BR BC εmask hZ0 hε hRN hCN
  have ht:=independent_height v height hH degree
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ hloss
  have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile
  have hsum:0≤C₀+C₁:=add_nonneg h₀ h₁
  change Cc*((R*C).radical.absNorm:ℝ)^εmask*(C₀+C₁)*
    diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*(p.control T)^2*
    (1+(|v|+height))^degree*reference*ratio^((1:ℝ)/6)*Z^exponent≤_
  calc
    _≤Cc*Z^((BR+BC)*εmask)*(C₀+C₁)*
      diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*(p.control T)^2*
      ((1+height)^degree*(1+‖v‖)^(2*degree))*reference*ratio^((1:ℝ)/6)*Z^loss:=by
        gcongr
    _=_:=by
      unfold coefficient
      rw [Real.rpow_add hZ0]
      ring

end SevenEighths.CenteredMomentEnergyChildEnvelopeFitting

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalErrorUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorUniform
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

theorem actual_error_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0<lower)(ha0:0<a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    Fintype.card α≤N → lower≤ src.lower → src.upper≤upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤ sigma → 1≤ cost → 0<asource →
    0≤delta → 0≤ reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤Z^BR → (Cpick.absNorm:ℝ)≤Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+errorRemoval prime Z k+
          (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    CenteredMomentEnergyCanonicalErrorPaid.actual_error_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
  obtain ⟨Zr,hZr,hr⟩:=CenteredMomentFirstAmplifiedPaidReserve.eventually_source_reserve
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource prime hprime k hk hprimeScale hslot Bp υ v0 hυ
    input hinput
    Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hupperInput:input.upper≤upper:=by rw [hinput];exact hupperSrc
  have hchild:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le B.val).trans hcard
  have herr:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le Bp.val).trans hchild
  have hsmall:sourceReserve src input C D Z delta reserve cost asource≤delta+reserve+θsource:=
    hr Z hZrZ src input hcard herr hlowerSrc hupperInput C D hC.1 hD.1
      delta reserve cost asource hdelta hreserve hcost haSource
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=
    mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _)
  have href:0<envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad:=
    envelope_pos _ hqpos C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)

end SevenEighths.CenteredMomentEnergyCanonicalErrorUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainUniform
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

theorem actual_main_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0<lower)(ha0:0<a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    Fintype.card α≤N → lower≤ src.lower → src.upper≤upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤ sigma → 1≤ cost → 0<asource →
    0≤delta → 0≤ reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock τ t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kmain dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family τ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤Z^BR → (Cpick.absNorm:ℝ)≤Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+
          (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3)+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    CenteredMomentEnergyCanonicalMainPaid.actual_main_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ
  obtain ⟨Zr,hZr,hr⟩:=CenteredMomentFirstAmplifiedPaidReserve.eventually_actual_amplified_reserves
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hsmall:sourceReserve src (child src C R0 B τ t) C D Z delta reserve cost asource≤
      delta+reserve+θsource:=
    (hr Z hZrZ src hcard hlowerSrc hupperSrc C D R0 hC.1 hD.1 B τ t delta reserve cost asource
      hdelta hreserve hcost haSource).1
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have href:0<envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad:=
    envelope_pos _ (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)

end SevenEighths.CenteredMomentEnergyCanonicalMainUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSlotProfile
local notation "O"=>HeckeFamily.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem physical_annular_all (S:ProbeFinalAssembly.SourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

theorem selected_physical_annular {ι:Type*}
    (S:ProbeFinalAssembly.SourceData D)(J:Finset ι)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(pools:ι→Finset (Ideal O))(P:ι→ℝ)(hP:∀i,0<P i)
    (ζ:ι→ℂ)(t X₁ X₂:ℝ):
    selectedProduct J η m A z W₁ W₂ pools
      (fun i=>physicalSlotCoefficient η₀ S.W (P i) (ζ i)) P t X₁ X₂=
    selectedProduct J η m A z W₁ W₂ pools
      (fun i I=>idealCoeff η₀.inverse I*
        annularWeight (fun x=>conj (S.W x)) (P i) (1-(ζ i).re) (-(ζ i).im) I) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_annular_all S η₀ (P i) (hP i) (ζ i) I

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem physical_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (S:ProbeFinalAssembly.SourceData D)(Lmod Lslot ε κ:ℝ)
    (hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤η₀.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(ζ:ι→ℂ)(t V:ℝ),(∀i,(ζ i).re∈Set.Icc (0:ℝ) 1) → 0≤V → (∀i,|(ζ i).im|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let pools:=fun i=>primePool M H 2 (P i)
      let coeff:=fun i=>physicalSlotCoefficient η₀ S.W (P i) (ζ i)
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2 := by
  obtain ⟨degree,C,hC,hbound⟩:=CenteredMomentRelativeCapacityRemoval.actual_relative_capacity_removal
    M H hH (ι:=ι) (fun _ x=>conj (S.W x)) (fun _=>1) (fun _=>2) (fun _=>by norm_num)
    (fun _=>conjugate_source_support S) (fun _=>Complex.conjCLE.contDiff.comp (S.W.smooth ⊤))
    Lmod Lslot ε 0 1 κ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun _=>η₀.inverse)
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hremaining,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hremaining,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQη hex ζ t V hζ hV him W₁ W₂ X₁ X₂
  dsimp only
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hP (i:ι):0<Z^(w i):=Real.rpow_pos_of_pos hZp _
  rw [selected_physical_annular S J η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂,
    selected_physical_annular S (J\R) η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂]
  exact henergy Z hZ η z hz F hcond Q hQM (fun _=>hQη) hex
    (fun i=>1-(ζ i).re) (fun i=>-(ζ i).im) t V
    (fun i=>by linarith [(hζ i).2]) (fun i=>by linarith [(hζ i).1]) hV
    (fun i=>by simpa only [abs_neg] using him i) W₁ W₂ X₁ X₂

end SevenEighths.CenteredMomentDetectorPlainCapacity

end

end OAI

end

