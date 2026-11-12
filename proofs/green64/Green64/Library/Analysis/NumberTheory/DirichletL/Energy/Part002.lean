module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part034
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeCounting.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part024
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.PrimeRows.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFixedRadialReduction
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyFixedRadialEntry
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputFirstRemainder
open CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

theorem actual_original_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧ 0<Ctail ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:Radial),Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ→
      volume s≤Z^B→(r.scale)⁻¹≤Z^B→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass s R 1 fixedBadMask 1 Ψ r.scale Z ξ/volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving))+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Ψ,hs,hn,hentry⟩:=original_comparison (ι:=ι) bΦ hbΦ
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Ψ,hs,hn,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  have hsource:=hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 Ψ r.scale r.scale_pos hV hK
  have hpos:=hentry s R r hr
  have hdom:=mul_le_mul_of_nonneg_left hsource
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (diagonalControl_nonneg r.profile))
  apply hpos.trans
  apply add_le_add _ le_rfl
  simpa only [mul_div_assoc, CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume] using hdom
end SevenEighths.CenteredMomentEnergyFixedRadialReduction

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.LowFixedRadialEntry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyLowFixedRadialEntry
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyOriginalSource
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentEnergyPhysicalEntry
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

omit [DecidableEq ι] in
lemma zero_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

theorem original_low_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(a b B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(ha:0<a)(hb:0≤b)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧0<Ctail ∧∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),∀he₁:s.W₁=W₁,∀he₂:s.W₂=W₂,
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      (∀i,s.hi i≤hi i) →∀(R:Ideal O)(r:Radial),
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume s≤Z^B → r.scale⁻¹≤Z^B →
      let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁;
      let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂;
      energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
        s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass (zeroInput s hz₁ hz₂) R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    bΦ hbΦ hi a b B ε ξ saving hhi ha hb hB hε hξ
  refine ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  dsimp only
  let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁
  let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂
  have hh:=hz.2 (zeroInput s hz₁ hz₂) W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  change energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
    s.P s.X₁ s.X₂ r.keep r.profile r.scale≤_+2*energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero,zeroInput_volume,zero_control] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_product_cap (b B ε:ℝ)(_hB:0≤B)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b →s.X₁*s.X₂≤Z^B →
      (zeroInput s hz₁ hz₂).Y₁≤1 ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(B+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hprod
  refine ⟨smallScale_le_one _,?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    _≤Z^B*Z^ε:=mul_le_mul hprod hconst (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le
    _=Z^(B+ε):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

omit [DecidableEq ι] in
theorem zero_comparison_first_log (b ε:ℝ)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → -ε≤Real.logb Z (zeroInput s hz₁ hz₂).Y₁ ∧
        Real.logb Z (zeroInput s hz₁ hz₂).Y₁≤0:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb
  change -ε≤Real.logb Z (smallScale s.b₁) ∧ Real.logb Z (smallScale s.b₁)≤0
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  have hlower:Z^(-ε)≤ smallScale s.b₁:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
    simpa only [smallScale,one_div] using one_div_le_one_div_of_le (by positivity) hconst
  refine ⟨?_,?_⟩
  · have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hlower
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  · have hh:=Real.logb_le_logb_of_le hZ (smallScale_pos s.b₁) (smallScale_le_one s.b₁)
    simpa only [Real.logb_one] using hh

end SevenEighths.CenteredMomentEnergyLowFixedRadialEntry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroGrowthReserve -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d loss defect xi saving ε:ℝ)
    (_hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+1)+loss+defect+xi≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+L≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBp:0<B:=by dsimp [B];positivity
  refine ⟨A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:max 1 s.radial.scale≤Z^s.width:=by
    apply max_le (Real.one_le_rpow hZ s.width_nonneg)
    rw [s.scale_eq]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    exact le_add_of_nonneg_right s.character_nonneg
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+loss+defect+xi))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+loss+defect+xi)):=by gcongr
      _=A^d*B*Z^(s.width+(d*(Bmask+Mcap+1)+loss+defect+xi)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+loss+defect+xi)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herr:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
        Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+L)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^s.width*Z^L):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add hreflect herr
    _=_:=by ring

theorem exists_growth_reserve (ε Mcap Bmask bΦ Loriginal:ℝ)
    (hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d L saving C:ℝ,0<d ∧ 0<L ∧ 0<saving ∧ 0<C ∧
      Loriginal≤L ∧ Mcap+Bmask+d+d≤L ∧
      ∀Z:ℝ,1≤Z→∀s:NaturalState Z Bmask bΦ,s.width≤Mcap→
      (s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+d+d+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          Z^(-2*saving)*max 1 s.radial.scale*Z^L)≤C*Z^(s.width+ε):=by
  let d:=ε/(8*(Bmask+Mcap+4))
  let L:=max Loriginal (Mcap+Bmask+d+d)+1
  let saving:=L+Bmask*d+2*Mcap*d+1
  have hd:0<d:=by dsimp [d];positivity
  have hL:0<L:=by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+d+d)]
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hmain:d*(Bmask+Mcap+1)+d+d+d≤ε:=by
    have heq:d*(Bmask+Mcap+4)=ε/8:=by
      dsimp only [d]
      field_simp
    nlinarith
  have herr:Bmask*d+Mcap*(2*d)-2*saving+L≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hbound⟩:=ledger_bound Mcap Bmask bΦ L d d d d saving ε hM hB hL.le hd hmain herr
  exact ⟨d,L,saving,C,hd,hL,hsave,hC,by dsimp only [L];linarith [le_max_left Loriginal (Mcap+Bmask+d+d)],
    by dsimp only [L];linarith [le_max_right Loriginal (Mcap+Bmask+d+d)],hbound⟩

end SevenEighths.CenteredMomentEnergyZeroGrowthReserve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroReferenceError -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReferenceError
open HeckeFamily ConcreteTraceCRT HeckeDyadic QuadraticInitialBound
open CenteredMomentCommonMaskEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceHomogeneousError
local notation "O"=>HeckeFamily.O

theorem short_energy_bound (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),Function.support (W:ℝ→ℂ)⊆Set.Iic b →
      ∀(χ:O→Character)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),0<X →0<K →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*diagonalControl Φ*max 1 K*X:=by
  obtain ⟨C,hC,h⟩:=natural_reference_error_homogeneous (∅:Finset (Fin 0)) b
    (fun _=>0) (fun _=>0) (by simp)
  refine ⟨C,hC,?_⟩
  intro W hs χ t X K Φ keep hX hK hΦ
  have hh:=h ∅ (Finset.Subset.refl _) W hs χ (fun _=>∅) (fun _ _=>0)
    (fun _=>1) t X K Φ keep hX hK (by simp) (by simp) (by simp) (by simp) hΦ
  simpa only [Finset.prod_empty,mul_one] using hh

end SevenEighths.CenteredMomentEnergyZeroReferenceError

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def rayCubeFamily (u : FreeRow) : RayQuotient.Characters M H→Character :=
  HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse

theorem canonical_probe_exists_ray_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤ s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,n,hn,hchoice⟩ := canonical_probe_exists_cube (ι:=RayQuotient.Characters M H)
    K e δ a b B ζ saving τ he he' hδ hδ' hζ hζ' hτ ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ,
    ProbeRayCharacterFamily.large_supported_twists_eventually M (1/100) (by norm_num)]
    with Z hZ hlarge
  intro η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨idx,grid,hlabel,hbins,herror⟩ := hchoice η Z hZ.1 hZ.2 T hT hdis length hl0 hl hpool W hWS hWB
    (rayCubeFamily M H hH)
  refine ⟨idx,grid,hlabel,hbins,?_,herror⟩
  intro u hu hcal
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hcal
  have hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1 :=
    hlarge u (mem_rowBand.mp hu).2.1 hs H hH
  refine ⟨hnp,?_,?_⟩
  · exact ProbeRayCharacterFamily.raw_twisted_conductor M H hH u
  · intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates S hS.prime η u
      (rayCubeFamily M H hH u) hnp' _).trans_lt (hbins u).2.2.2.2.1

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.DetectorMomentData -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

theorem momentData_product_raw (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData χ).character (momentElement u)) I=
      idealCoeff (χ.product (rawRow u)) I := by
  have he : idealCoeff ((momentData χ).character (momentElement u))=
      idealCoeff (χ.product (rawRow u)) := by
    apply hom_eq_of_primes
    intro P
    rw [momentData_coeff,idealCoeff_product,rawRow_coeff,fixedSourcePrincipal_prime]
    simp
  exact congrArg (fun f : Ideal O→*₀ℂ=>f I) he

theorem inverse_row_twist_moment_coeff (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((rawRow u).inverse.product χ) I=
      conj (idealCoeff ((momentData χ.inverse).character (momentElement u)) I) := by
  rw [momentData_product_raw,idealCoeff_product,idealCoeff_product,
    idealCoeff_inverse_conj,idealCoeff_inverse_conj,map_mul]
  simp only [starRingEnd_self_apply]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→RowData :=
  Sum.elim (fun b=>if b then momentData (fixedSourcePrincipal S hS)
    else momentData (η.inverse.excludePrimes S hS))
    (fun θ=>momentData (HeckeRayQuotient.character M H hH θ).inverse)

def sourceMomentReverse : Sum Bool (RayQuotient.Characters M H)→Bool :=
  Sum.elim (fun b=>!b) (fun _=>true)

theorem source_family_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) I=
      if sourceMomentReverse M H j then
        conj (idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I)
      else idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I := by
  rcases j with b|θ
  · cases b
    · simpa [sourceMomentReverse,sourceMomentData] using denominator_moment_coeff S hS hbad η u I
    · simpa [sourceMomentReverse,sourceMomentData] using numerator_moment_coeff S hS hbad u I
  · exact inverse_row_twist_moment_coeff (HeckeRayQuotient.character M H hH θ) u I
end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.DetectorBatch -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => HeckeFamily.O

def retainedProjection (R : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) : FreeRow :=
  if u∈R then u else u0

@[simp] theorem retainedProjection_of_mem (R : Finset FreeRow) (u0 u : FreeRow) (hu : u∈R) :
    retainedProjection R u0 u=u := by simp [retainedProjection,hu]

theorem retainedProjection_mem (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R) (u : FreeRow) :
    retainedProjection R u0 u∈R := by
  unfold retainedProjection
  split_ifs with hu
  · exact hu
  · exact h0

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def retainedSourceBatch {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (hw : ∀u∈R,SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) U a ε tstar T allowance i)
    (hrow : ∀u∈R,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0≤ mesh) (hb : 0<binWidth)
    (hwpos : ∀s∈slots,0<widths s) (hwmesh : ∀s∈slots,widths s≤ mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i where
  rows := R
  family := fun u=>sourceDetectorFamily S hS.prime η (retainedProjection R u0 u)
    (rayCubeFamily M H hH (retainedProjection R u0 u))
  witness := fun u=>hw (retainedProjection R u0 u) (retainedProjection_mem R u0 h0 u)
  row_norm := hrow
  data := sourceMomentData M H hH S hS.prime η
  reverse := sourceMomentReverse M H
  row_coeff := by
    intro u hu j I
    rw [retainedProjection_of_mem R u0 u hu]
    exact source_family_moment_coeff M H hH S hS.prime hS.bad η u j I
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hm
  binWidth_pos := hb
  widths_pos := hwpos
  widths_mesh := hwmesh
  supply := hsupply

lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdtop : d≤37/42)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsum : ∑j,ell j=1/6) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤ mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤ mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    norm_num at hn
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith

lemma physical_slot_scale {N : ℕ} (ell : Fin N→ℝ) (Z d : ℝ) (hZ : 0<Z) (hd : d≠0) (j : Fin N) :
    (Z^d)^(ell j/d)=Z^(ell j) := by
  rw [←Real.rpow_mul hZ.le]
  congr 1
  field_simp
end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.DetectorMomentGates -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve
open InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

def sourceMomentPeriod (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℕ:=
  ∏j:Sum Bool (RayQuotient.Characters M H),
    (baseCharacter (sourceMomentData M H hH S hS η j)).period

def sourceMomentConductorBound (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℝ:=
  1+∑j:Sum Bool (RayQuotient.Characters M H),
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)

theorem sourceMomentPeriod_ne_zero (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    sourceMomentPeriod M H hH S hS η≠0:=by
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>Nat.ne_of_gt (Character.period_pos _))

theorem sourceMomentPeriod_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    Ideal.span {(sourceMomentPeriod M H hH S hS η:O)}≤
      (baseCharacter (sourceMomentData M H hH S hS η j)).modulus:=by
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have hd:(baseCharacter (sourceMomentData M H hH S hS η j)).period∣
      sourceMomentPeriod M H hH S hS η:=Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨n,hn⟩:=hd
  rw [hn,Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Character.period_mem _)

theorem sourceMomentConductorBound_pos (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    0<sourceMomentConductorBound M H hH S hS η:=by
  unfold sourceMomentConductorBound
  positivity

theorem sourceMomentConductor_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
      sourceMomentConductorBound M H hH S hS η:=by
  have hh:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Sum Bool (RayQuotient.Characters M H))))=>
    (Nat.cast_nonneg (α:=ℝ) (baseCharacter (sourceMomentData M H hH S hS η k)).modulus.absNorm))
      (Finset.mem_univ j)
  unfold sourceMomentConductorBound
  linarith

theorem sourceMoment_deleted_base_gates (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    let q:=sourceMomentPeriod M H hH S hS η
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    ∀j:Sum Bool (RayQuotient.Characters M H),
      let χ:=(baseCharacter (sourceMomentData M H hH S hS η j)).excludePrimes
        (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (∀x,‖elementCharacter (idealCoeff χ).toMonoidHom x‖≤1) ∧
      FactorsModulo (fixedBaseConductor (deletedPeriod q))
        (elementCharacter (idealCoeff χ).toMonoidHom):=by
  dsimp only
  let q:=sourceMomentPeriod M H hH S hS η
  have hq:q≠0:=sourceMomentPeriod_ne_zero M H hH S hS η
  refine ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,?_⟩
  intro j
  exact (deleted_physical_base_gates _ q hq (sourceMomentPeriod_le M H hH S hS η j)).2.2

theorem sourceMoment_large_eventually (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀j:Sum Bool (RayQuotient.Characters M H),∀s:Slot,
        ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
          (Z^d)^(ell s/d):=by
  have ht:∀ᶠZ:ℝ in atTop,∀s:Slot,sourceMomentConductorBound M H hH S hS η<Z^(ell s):=by
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact (sourceMomentConductor_le M H hH S hS η j).trans (ht s)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ψ : Character) (m u : O) (reverse : Bool)
    (hrow : ∀n,elementCoeff ψ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (1*u) n)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then conj (idealCoeff ψ I) else idealCoeff ψ I)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hMm : M≤Ideal.span {m})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η m 1 u
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  rw [positiveSlotRow_eq_product η ψ m 1 u hrow _ _ _ _ P _ _ _ _ hX₁ hX₂ hP]
  simp only [norm_mul,norm_prod]
  rw [norm_of_oriented_coefficients χ ψ reverse hc false W₁ X₁ σ t hX₁,
    norm_of_oriented_coefficients χ ψ reverse hc false W₂ X₂ σ t hX₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_slot_conj M H η m u hmLam hMm (V i) (b i) (P i) (external i) (hP i) (hη i),RCLike.norm_conj]

theorem momentData_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then
      conj (idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
      else idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
    (hMm : M≤Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η ProbeHighRowFamily.rowMaskElement 1 u.val
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  apply source_plain_pair_norm M H η χ
    ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u))
    ProbeHighRowFamily.rowMaskElement u.val reverse _ hc (dvd_mul_left _ _) hMm
    W₁ W₂ V b P external X₁ X₂ σ t hX₁ hX₂ hP hη
  intro n
  simpa only [ProbeHighRowFamily.momentData,ProbeHighRowFamily.momentElement,one_mul] using
    (ProbeHighRowFamily.momentData η).character_spec (ProbeHighRowFamily.momentElement u) n

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryFiber -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def detectorPositiveRow (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) : ℂ :=
  positiveSlotRow η rowMaskElement 1 u.val
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (fun s : selected=>physicalSlotCoefficient η (F.profile s.val) (U^(F.widths s.val)) (F.external s.val))
    (fun s : selected=>U^(F.widths s.val)) 0 (U^F.m) (U^F.m)

theorem fiber_plain_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have hc := F.row_coeff u hu
  rw [hdata] at hc
  have he := momentData_plain_pair_norm M H η (F.family u F.label) u F.reverse hc hMm
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular)
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    (U^F.m) (U^F.m) σ t (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    (fun s=>Real.rpow_pos_of_pos hU _) (fun s=>hη s.val s.property)
  have hprod := Finset.prod_coe_sort selected (fun s=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val
    (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s))
  rw [hprod] at he
  simpa only [detectorPositiveRow,Fiber.physicalProduct,HeckeDetectorPhysicalSelection.physical,
    Finset.prod_coe_sort] using he

theorem fiber_plain_unmarked_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (j k : ℕ) (σ t : ℝ) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η ∅ j k σ t u‖^2 := by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    fiber_plain_energy_eq F η hdata hMm hU ∅ j k σ t (by simp)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma source_product_le_rowMask (S : Finset (Ideal O))
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) :
    (∏P∈S,P)≤Ideal.span {rowMaskElement} := by
  apply Ideal.dvd_iff_le.mp
  have hne : (Ideal.span {ConcretePrimeRowBridge.goodLambda}:Ideal O)≠Ideal.span {(2:O)} := by
    intro he
    have hh : CanonicalQuadraticSieve.badPrime false=CanonicalQuadraticSieve.badPrime true := he
    have hh := CanonicalQuadraticSieve.badPrime_injective hh
    cases hh
  have hd := Finset.prod_dvd_prod_of_subset CanonicalQuadraticSieve.fixedBadPrimes S (fun P : Ideal O=>P) hbad
  have he : (∏P∈CanonicalQuadraticSieve.fixedBadPrimes,P)=Ideal.span {rowMaskElement} := by
    change (∏P∈({Ideal.span {ConcretePrimeRowBridge.goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O)),P)=_
    rw [Finset.prod_pair hne]
    unfold rowMaskElement
    rw [←Ideal.span_singleton_mul_span_singleton]
    exact mul_comm _ _
  rwa [he] at hd

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentBase (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→Character :=
  Sum.elim (fun b=>if b then fixedSourcePrincipal S hS else η.inverse.excludePrimes S hS)
    (fun θ=>(HeckeRayQuotient.character M H hH θ).inverse)

lemma sourceMomentData_base (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (j : Sum Bool (RayQuotient.Characters M H)) :
    sourceMomentData M H hH S hS η j=momentData (sourceMomentBase M H hH S hS η j) := by
  rcases j with b|θ
  · cases b <;> rfl
  · rfl

theorem eventually_source_slots_coprime {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (ell : Fin N→ℝ) (hell : ∀i,0<ell i) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀d : ℝ,d≠0→∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b ((Z^d)^(ell i/d)),
        W ((P.absNorm:ℝ)/((Z^d)^(ell i/d)))≠0→
          IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
  have he : ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b (Z^(ell i)),W ((P.absNorm:ℝ)/(Z^(ell i)))≠0→
        IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_primePool_power_coprime (sourceMomentBase M H hH S hS η j)
      a (ell i) ha (hell i)] with Z hz
    exact hz M H
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with Z hz hZ
  intro j i d hd W b hs
  have heq : (Z^d)^(ell i/d)=Z^(ell i) := by
    rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]
  rw [heq]
  exact hz j i W b hs

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  exact mul_comm _ _

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal O} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

def fiberSector (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (θ : selected→RayQuotient.Characters M H) (u : FreeRow) : ℂ :=
  sectorValue M H hH (naturalRow η u.val u.property.1).character η 1
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>fun y=>conj (F.profile s.val y)) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>1-(F.external s.val).re)
    (fun s : selected=>-(F.external s.val).im) 0 (U^F.m) (U^F.m) θ

theorem detectorPositiveRow_sector {Slot : Type*}
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) (hU : 0<U) :
    detectorPositiveRow F η selected j k σ t u=
      averageWeight (ι:=selected) M H*∑θ : selected→RayQuotient.Characters M H,
        fiberSector hH F η selected j k σ t θ u := by
  have he:=natural_physical_product M H hH (naturalRow η u.val u.property.1) η 1 one_ne_zero
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    0 (U^F.m) (U^F.m) (by positivity) (fun _=>Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)] at he
  simpa only [detectorPositiveRow,rowMaskElement_eq_fixed,fiberSector] using he

theorem fiber_plain_sector_energy (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)≤
      ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
        ∑u∈F.rows,‖fiberSector hH F η selected j k σ t θ u‖^2 := by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  calc
    _≤∑u∈F.rows,∑θ : selected→RayQuotient.Characters M H,
        ‖averageWeight (ι:=selected) M H‖*‖fiberSector hH F η selected j k σ t θ u‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [detectorPositiveRow_sector hH F η selected j k σ t u hU]
      exact sector_average_energy M H _
    _= _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralSlots -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma row_phase_norm_one_of_not_dvd (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) :
    ‖idealRowHom u.val P.val‖=1 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg := supported_prime_data p hp (hspan.symm ▸ hs)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have he : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  rw [he]
  exact Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p u.val hg.1 hg.2 hu) (by decide)

theorem actual_central_unramified_error (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (4:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))+
      idealUnramifiedCorrection η u P x w z*star (idealRowHom u.val P.val)‖≤
        720*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact (rpow_le_half _ _ hQ (by rw [hz];norm_num)).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
    (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
      ((rpow_le_half _ _ hQ (by rw [hx,hz];linarith)).trans_lt (by norm_num))
  rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
  exact unramifiedSelected_central_error _ a e _ _ _ x w z hQ ha ha1 he he1
    (actualAPhase_norm_le_one η _)
    (PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη)
    (row_phase_norm_one_of_not_dvd u P hs hn) hx hw hz

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized -/

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_unramified_normalized (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖idealUnramifiedCorrection η u P x w z‖ ∧
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
      idealUnramifiedCorrection η u P x w z+star (idealRowHom u.val P.val)‖≤
        1440*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
  have hv := row_phase_norm_one_of_not_dvd u P hs hn
  have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
  constructor
  · exact unramifiedClosed_central_lower _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  · have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
    have hV : ‖coordV P.val.absNorm z‖<1 := by
      rw [coordV_norm _ hQ0]
      exact (rpow_le_half _ _ (by linarith) (by rw [hz];norm_num)).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
      (coordR_norm_le _ hQ0 _ x z hA).trans_lt
        ((rpow_le_half _ _ (by linarith) (by rw [hx,hz];linarith)).trans_lt (by norm_num))
    rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
    exact unramifiedSelected_central_quotient _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta hv hx hw hz
end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralSplit -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

def centralNormalizedSlot (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
    supportedCorrection η u P x w z

def repeatedRowPrime (u : FreeRow) (P : ProbePhysical.PrimeIdeal) : Prop :=
  P.val∣Ideal.span {u.val} ∧ 2≤ multiplicity (primaryGenerator P.val) u.val

def centralRegularError (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then 0 else
    centralNormalizedSlot η u P hs x w z+star (idealRowHom u.val P.val)

def centralRepeatedTerm (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then centralNormalizedSlot η u P hs x w z else 0

theorem centralNormalizedSlot_split (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=
      -star (idealRowHom u.val P.val)+centralRegularError η u P hs x w z+
        centralRepeatedTerm η u P hs x w z := by
  by_cases hp : repeatedRowPrime u P
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_left hp,row_phase_ramified u P hp.1,
      star_zero,neg_zero,zero_add]
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_right hp]
    ring

theorem central_actual_local_bounds (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖supportedCorrection η u P x w z‖ ∧
    ‖centralRegularError η u P hs x w z‖≤
      1440*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(1/2:ℝ)
        else (P.val.absNorm:ℝ)^(-(51/100:ℝ))) ∧
    ‖centralRepeatedTerm η u P hs x w z‖≤
      if repeatedRowPrime u P then 812*(P.val.absNorm:ℝ)^(1-w.re) else 0 := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  by_cases hd : P.val∣Ideal.span {u.val}
  · have hb := actual_central_ramified_normalized η u P hs hd (by linarith)
      a e x w z hsmall ha ha1 he he1 hx hw hz
    have hcorr : supportedCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
      simp [supportedCorrection,hs,hd]
    refine ⟨hcorr.symm ▸ hb.1,?_,?_⟩
    · by_cases hj : 2≤ multiplicity (primaryGenerator P.val) u.val
      · simp [centralRegularError,repeatedRowPrime,hd,hj]
        positivity
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        rw [centralRegularError,ite_eq_right hp,row_phase_ramified u P hd,star_zero,add_zero,ite_eq_left hd]
        have h := hb.2
        simp only [ite_eq_right hj,add_zero] at h
        have hn : ‖centralNormalizedSlot η u P hs x w z‖≤800*(P.val.absNorm:ℝ)^(1/2:ℝ) := by
          dsimp only [centralNormalizedSlot]
          rw [hcorr]
          have hm := mul_le_mul_of_nonneg_left h hQ0.le
          have hpow : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
            rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
          have hp2 : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-(1/2:ℝ))=
              (P.val.absNorm:ℝ)^(1/2:ℝ) := by
            conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
            rw [←Real.rpow_add hQ0];norm_num
          rw [←mul_assoc,hpow,one_mul] at hm
          rw [mul_left_comm (P.val.absNorm:ℝ) 800,hp2] at hm
          exact hm
        exact hn.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _))
    · by_cases hj : 2≤ multiplicity (primaryGenerator P.val) u.val
      · have hp : repeatedRowPrime u P := ⟨hd,hj⟩
        rw [centralRepeatedTerm,ite_eq_left hp,ite_eq_left hp]
        have h := hb.2
        rw [ite_eq_left hj] at h
        have hpow : (P.val.absNorm:ℝ)^(-(1/2:ℝ))≤(P.val.absNorm:ℝ)^(-w.re) := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          rw [hw];linarith
        have hn : (P.val.absNorm:ℝ)^(-1:ℝ)*‖centralNormalizedSlot η u P hs x w z‖≤
            812*(P.val.absNorm:ℝ)^(-w.re) := by
          dsimp only [centralNormalizedSlot];rw [hcorr]
          nlinarith
        have hm := mul_le_mul_of_nonneg_left hn hQ0.le
        have hi : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
          rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
        have heq : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-w.re)=
            (P.val.absNorm:ℝ)^(1-w.re) := by
          conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
          rw [←Real.rpow_add hQ0]; congr 1
        rw [←mul_assoc,hi,one_mul] at hm
        rw [mul_left_comm (P.val.absNorm:ℝ) 812,heq] at hm
        exact hm
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
  · have hb := actual_central_unramified_normalized η u P hs hd hη a e x w z hQ
      ha ha1 he he1 hx hw hz
    have hc : supportedCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
      simp [supportedCorrection,hs,hd]
    have hp : ¬repeatedRowPrime u P := fun h=>hd h.1
    refine ⟨hc.symm ▸ hb.1,?_,?_⟩
    · simpa only [centralRegularError,ite_eq_right hp,centralNormalizedSlot,hc,ite_eq_right hd] using hb.2
    · simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralRepeatedChoices -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedChoices
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => HeckeFamily.O

def activeChoices {k : ℕ} (u : FreeRow) (T : Fin k→Finset ProbePhysical.PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) : Finset (∀j,T j) :=
  Finset.univ.filter (fun P=>∀j,repeatedRowPrime u (P j).val ∧
    W j (((P j).val.val.absNorm:ℝ)/Y j)≠0)

lemma active_card_le_divisors {k : ℕ} (u : FreeRow) (T : Fin k→Finset ProbePhysical.PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) :
    (activeChoices u T W Y).card≤(IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card^k := by
  let U : Ideal O := Ideal.span {u.val}
  have hU : U≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  let f : activeChoices u T W Y→(Fin k→IdealMobiusDivisorSum.idealDivisors U) :=
    fun P j=>⟨(P.val j).val.val,(IdealMobiusDivisorSum.mem_idealDivisors hU).mpr
      (((Finset.mem_filter.mp P.property).2 j).1.1)⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g=>(g j).val) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hc

theorem active_card_subpower (N : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀k : ℕ,k≤N → ∀(u : FreeRow) (T : Fin k→Finset ProbePhysical.PrimeIdeal)
      (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      ((activeChoices u T W Y).card:ℝ)≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps := by
  let δ := eps/(N+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(max 1 D)^N,by positivity,?_⟩
  intro k hk u T W Y
  have hU : (Ideal.span {u.val}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hU1 : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hd := hdiv (Ideal.span {u.val}) hU
  have hcard : ((activeChoices u T W Y).card:ℝ)≤
      ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := by
    exact_mod_cast active_card_le_divisors u T W Y
  have hpow : D^k≤(max 1 D)^N :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hke : δ*k≤eps := by
    have hn : (k:ℝ)≤N := by exact_mod_cast hk
    have he : δ*(N+1)=eps := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := hcard
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ)^k := pow_le_pow_left₀ (by positivity) hd k
    _ = D^k*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(δ*k) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    _ ≤ _ := mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le hU1 hke)
      (by positivity) (by positivity)

lemma sum_products_restrict {k : ℕ} (η : Character) (u : FreeRow)
    (T : Fin k→Finset ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→CanonicalQuadraticSieve.Supported P.val)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) (x w z : ℂ) :
    (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hT j P.val P.property) x w z‖)=
    ∑P∈activeChoices u T W Y,∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u (P j).val (hT j (P j).val (P j).property) x w z‖ := by
  rw [Fintype.prod_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hp
  have hn : ¬∀j,repeatedRowPrime u (P j).val ∧ W j (((P j).val.val.absNorm:ℝ)/Y j)≠0 := by
    simpa only [activeChoices,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  by_cases hr : repeatedRowPrime u (P j).val
  · simp [hj hr]
  · simp [centralRepeatedTerm,hr]
end SevenEighths.ProbeCentralRepeatedChoices

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralRepeatedProduct -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss ProbeRowReflectedAllocation
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def rowCost (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : ℝ :=
  ((ProbeRowRadicalConductor.fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).absNorm)^(a-1/2+6*e)*
    ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)^(6*e+2*eps)*
    (3+T)^2*(presentationComplexity (rowCharacter S hS u) T)^eps

lemma rowCost_nonneg (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : 0≤ rowCost S hS u a e eps T := by
  unfold rowCost presentationComplexity HeckeLogarithmic.complexity
  positivity

lemma repeated_weight_bound (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e B Y : ℝ) (W : ℝ→ℂ) (x w z : ℂ)
    (hB : 0≤B) (hW : ∀t,‖W t‖≤B)
    (hQ : (480:ℝ)≤P.val.absNorm) (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hr : repeatedRowPrime u P) :
    ‖W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P hs x w z‖≤
      (812*B*(P.val.absNorm:ℝ)^z.re)*(P.val.absNorm:ℝ)^(-w.re) := by
  have hp : (0:ℝ)<P.val.absNorm := by linarith
  have hb := (central_actual_local_bounds η u P hs hη a e x w z hQ hsmall ha ha1 he he1 hx hw hz).2.2
  rw [ite_eq_left hr] at hb
  have hn : ‖(P.val.absNorm:ℂ)^(z-1)‖=(P.val.absNorm:ℝ)^(z.re-1) := by
    rw [show (P.val.absNorm:ℂ)=(((P.val.absNorm:ℝ):ℂ)) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  rw [norm_mul,norm_mul,hn]
  calc
    _ ≤ B*(P.val.absNorm:ℝ)^(z.re-1)*(812*(P.val.absNorm:ℝ)^(1-w.re)) := by
      gcongr
      exact hW _
    _ = _ := by
      calc
        _ = 812*B*((P.val.absNorm:ℝ)^(z.re-1)*(P.val.absNorm:ℝ)^(1-w.re)) := by ring
        _ = 812*B*(P.val.absNorm:ℝ)^(z.re-w.re) := by rw [←Real.rpow_add hp];congr 2;ring
        _ = _ := by rw [show z.re-w.re=z.re+(-w.re) by ring,Real.rpow_add hp];ring

theorem selected_repeated_product (e eps : ℝ) (he : 0<e) (he1 : e<1/1000)
    (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T a : ℝ) (i : ℕ),2<T → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T)<a+2*e →
    ∀(k : ℕ) (P : Fin k→ProbePhysical.PrimeIdeal) (hs : ∀j,Supported (P j).val),
      Function.Injective P → (∀j,IsCoprime (P j).val η.modulus) →
      (∀j,(480:ℝ)≤(P j).val.absNorm) →
      (∀j,198*((P j).val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∀j,repeatedRowPrime u (P j)) →
    ∀(B : ℝ) (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),0≤B → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,‖W j (((P j).val.absNorm:ℝ)/Y j)*((P j).val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u (P j) (hs j) x w z‖ ≤
        C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*
          ∏j,((P j).val.absNorm:ℝ)^(z.re-1/2) := by
  obtain ⟨C,hC,hbound⟩ := source_calibrated_reflected_allocation e eps he he1 heps
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T a i hT ha ha1 hbin k P hs hdis hη hQ hsmall hr B W Y hB hW x w z hx hw hz hwi
  obtain ⟨ψ,hle,hprim,hmask,hactive,hb⟩ := hbound S hS hmax hbad u hu
  have hi : Function.Injective (fun j=>(P j).val) := fun j l h=>hdis (Subtype.ext h)
  have hdiv (j : Fin k) := actual_multiplicity_divisor u (primaryGenerator (P j).val) (supported_primeGenerator_prime (P j) (hs j))
  have hspan (j : Fin k) : (Ideal.span {primaryGenerator (P j).val}:Ideal O)=(P j).val := span_primaryGenerator_of_supported (P j).val (hs j)
  have hb' := hb η twists T a i hT ha ha1 hbin k (fun j=>(P j).val) (fun j=>(P j).property) hi
    (fun j=>multiplicity (primaryGenerator (P j).val) u.val) (fun j=>(hr j).2)
    (fun j=>by have hd := (hdiv j).1;rw [hspan j] at hd;exact hd) w hw hwi
  let q : Fin k→ℝ := fun j=>(P j).val.absNorm
  have hq (j : Fin k) : 0<q j := by dsimp [q];have := hQ j;linarith
  have hp : (∏j,‖W j (q j/Y j)*((P j).val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u (P j) (hs j) x w z‖)≤
      (812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re)) := by
    have ht := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j (_:j∈Finset.univ)=>norm_nonneg _)
      (fun j (_:j∈Finset.univ)=>repeated_weight_bound η u (P j) (hs j) (hη j)
        a e B (Y j) (W j) x w z hB (hW j) (hQ j) (hsmall j) ha ha1 he he1.le hx hw hz (hr j))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using ht
  have hbc :
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,q j^(-w.re) ≤ C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)) := by
    convert hb' using 1 ; dsimp only [rowCost,q] ; ring
  have heq : (∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))=∏j,q j^(z.re-1/2) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [←Real.rpow_add (hq j)]
    congr 1
  calc
    _ ≤ ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ((812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re))) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ((812*B)^k*(∏j,q j^z.re))*(‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS u) w‖*∏j,q j^(-w.re)) := by ring
    _ ≤ ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left hbc (by positivity)
    _ = _ := by rw [show ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)))=
      C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*((∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))) by ring,heq]
end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralRepeatedSum -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedChoices
open ProbeSelectedPrimeSums
local notation "O" => HeckeFamily.O

theorem actual_repeated_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(k : ℕ),k≤N → ∀(T : Fin k→Finset ProbePhysical.PrimeIdeal)
      (hs : ∀j P,P∈T j→Supported P.val),
      (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j,(Y j)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hprod⟩ := selected_repeated_product e eps he he1 heps
  obtain ⟨D,hD,hcount⟩ := active_card_subpower N eps heps
  let A := annularPower c d (-(4/25:ℝ))
  let E := (max 1 (812*B*A))^N
  have hA : 0≤A := annularPower_nonneg c d _ hc
  have hE : 0<E := by dsimp [E];positivity
  refine ⟨D*C*E,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin k hk T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi
  let R := rowCost S hS u a e eps ((3*i+2:ℕ)*T0)
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  have hR : 0≤R := rowCost_nonneg _ _ _ _ _ _ _
  have hY0 (j : Fin k) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hYY : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hY0 j).le _)
  have hterm (P : ∀j,T j) (hP : P∈activeChoices u T W Y) :
      L*(∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
        centralRepeatedTerm η u (P j).val (hs j (P j).val (P j).property) x w z‖)≤
      C*E*R*∏j,(Y j)^(-(4/25:ℝ)) := by
    have hp := (Finset.mem_filter.mp hP).2
    have hb := hprod S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k
      (fun j=>(P j).val) (fun j=>hs j (P j).val (P j).property) (hdis P)
      (fun j=>hη j (P j).val (P j).property) (fun j=>hQ j (P j).val (P j).property)
      (fun j=>hsmall j (P j).val (P j).property) (fun j=>(hp j).1)
      B W Y hB hW x w z hx hw hz hwi
    have hpow : (∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2))≤A^k*∏j,(Y j)^(-(4/25:ℝ)) := by
      have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j _=>Real.rpow_nonneg (show (0:ℝ)≤(P j).val.val.absNorm by positivity) (-(4/25:ℝ)))
        (fun j (_:j∈Finset.univ)=>annular_rpow c d (Y j) ((P j).val.val.absNorm:ℝ) (-(4/25:ℝ)) hc hd (hY0 j)
          ((le_div_iff₀ (hY0 j)).mp (hWS j (hp j).2).1)
          ((div_le_iff₀ (hY0 j)).mp (hWS j (hp j).2).2))
      norm_num only [hz,show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num] at ⊢
      simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
    have hEbound : (812*B)^k*A^k≤E := by
      rw [←mul_pow]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (812*B*A)) k).trans
        (pow_le_pow_right₀ (le_max_left 1 _) hk)
    calc
      _ ≤ C*(812*B)^k*R*∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2) := hb
      _ ≤ C*(812*B)^k*R*(A^k*∏j,(Y j)^(-(4/25:ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C*((812*B)^k*A^k)*R*∏j,(Y j)^(-(4/25:ℝ)) := by ring
      _ ≤ _ := by gcongr
  rw [sum_products_restrict η u T hs W Y x w z,Finset.mul_sum]
  have hh := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply hh.trans
  calc
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps)*(C*E*R*∏j,(Y j)^(-(4/25:ℝ))) :=
      mul_le_mul_of_nonneg_right (hcount k hk u T W Y) (by positivity)
    _ = _ := by dsimp [R];ring
end SevenEighths.ProbeCentralRepeatedSum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralRepeatedSubset -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSubset
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedSum
local notation "O" => HeckeFamily.O

theorem actual_repeated_subset (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset ProbePhysical.PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀J : Finset (Fin N),
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j:J,(Y j.val)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := actual_repeated_sum N e eps c d B he he1 heps hc hd hB
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi J
  let k := Fintype.card J
  let E : J≃Fin k := Fintype.equivFin J
  let idx : Fin k→Fin N := fun j=>(E.symm j).val
  have hi : Function.Injective idx := fun j l h=>E.symm.injective (Subtype.ext h)
  have hk : k≤N := by
    dsimp [k]
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using J.card_le_univ
  have hd' (P : ∀j,T (idx j)) : Function.Injective (fun j=>(P j).val) := by
    intro j l heq
    change (P j).val=(P l).val at heq
    by_contra hne
    have hdiff : idx j≠idx l := fun h=>hne (hi h)
    exact Finset.disjoint_left.mp (hdis _ _ hdiff) (P j).property (by rw [heq];exact (P l).property)
  have hb := hmain S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k hk
    (fun j=>T (idx j)) (fun j P hP=>hs (idx j) P hP) hd'
    (fun j P hP=>hη (idx j) P hP) (fun j P hP=>hQ (idx j) P hP)
    (fun j P hP=>hsmall (idx j) P hP) (fun j=>W (idx j)) (fun j=>Y (idx j))
    (fun j=>hY (idx j)) (fun j=>hWS (idx j)) (fun j=>hW (idx j)) x w z hx hw hz hwi
  have hleft : (∏j:Fin k,∑P:T (idx j),‖W (idx j) ((P.val.val.absNorm:ℝ)/Y (idx j))*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs (idx j) P.val P.property) x w z‖)=
      ∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  have hright : (∏j:Fin k,(Y (idx j))^(-(4/25:ℝ)))=∏j:J,(Y j.val)^(-(4/25:ℝ)) :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  rw [hleft,hright] at hb
  exact hb
end SevenEighths.ProbeCentralRepeatedSubset

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralProduct -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def centralRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
    continuedCorrection S hS η u x w z

theorem calibratedTupleValue_central {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→ProbePhysical.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i,(480:ℝ)≤(P i).val.absNorm)
    (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hsmall : ∀i,198*((P i).val.absNorm:ℝ)^(-10*e)≤1/2) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z := by
  have hrestore := continuedCorrection_restore (4*e) S hS htail (Finset.univ.image P)
    (tupleOutside S P hPS) η u x w z (by rw [hx];linarith) (by rw [hz])
    (by rw [hw];linarith) (by rw [hx,hw];linarith)
  rw [Finset.prod_image hP.injOn] at hrestore
  have hn : (∏i,supportedCorrection η u (P i) x w z)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hz0
    have h := (central_actual_local_bounds η u (P i)
      (outside_prime_supported S hS.bad (P i) (hPS i)) (hη i) a e x w z
      (hQ i) (hsmall i) ha ha1 he he1 hx hw hz).1
    rw [hz0,norm_zero] at h
    norm_num at h
  rw [calibratedTupleValue_factor S hS hmax η u P hP hPS W Y x w z]
  unfold centralRowScalar centralNormalizedSlot
  rw [hrestore]
  simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib]
  field_simp

theorem calibrated_prime_slots_separate {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
        ∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val
            (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z := by
  calc
    _ = ∑P:(∀i,T i),centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i).val
            (outside_prime_supported S hS.bad (P i).val (hPS i (P i).val (P i).property)) x w z := by
      apply Finset.sum_congr rfl
      intro P _
      exact calibratedTupleValue_central S hS hmax η u (fun i=>(P i).val) (hdis P)
        (fun i=>hPS i (P i).val (P i).property) W Y a e x w z htail ha ha1 he he1 hx hw hz
        (fun i=>hQ i (P i).val (P i).property) (fun i=>hη i (P i).val (P i).property)
        (fun i=>hsmall i (P i).val (P i).property)
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum (fun i (P:T i)=>W i ((P.val.val.absNorm:ℝ)/Y i)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z)).symm

end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralCosts -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def centralRemainingScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

lemma centralRowScalar_split (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) :
    centralRowScalar S hS hmax η u x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      centralRemainingScalar S hS η u x w z := by
  unfold centralRowScalar centralRemainingScalar
  ring

theorem centralRemainingScalar_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S),FirstTail (4*e) S →
      ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤C*
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Ch,hCh,hh⟩ := continuedCorrection_first_subpower eps heps
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr*Ch,by positivity,?_⟩
  intro S hS hfirst η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hc := hh (4*e) S hS hfirst η u x w z
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith)
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold centralRemainingScalar
  rw [norm_mul,norm_mul]
  apply (mul_le_mul (mul_le_mul hl hrec (norm_nonneg _) (by linarith)) hc (norm_nonneg _)
    (mul_nonneg (by linarith) (mul_nonneg hCr.le (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _)))).trans
  exact le_of_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.PrimeRows.CentralExpansion -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def centralBranch (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : Fin 3→ℂ :=
  ![-star (idealRowHom u.val P.val),centralRegularError η u P hs x w z,
    centralRepeatedTerm η u P hs x w z]

theorem central_branch_sum (η : Character) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=∑b:Fin 3,centralBranch η u P hs x w z b := by
  simpa [centralBranch,Fin.sum_univ_three] using centralNormalizedSlot_split η u P hs x w z

theorem central_slots_branch_expansion {K : ℕ}
    (η : Character) (u : FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    (∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hT i P.val P.property) x w z)=
    ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralBranch η u P.val (hT i P.val P.property) x w z (b i) := by
  simp_rw [central_branch_sum,Finset.mul_sum]
  have hs (i : Fin K) :
      (∑P:T i,∑b:Fin 3,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b)=
      ∑b:Fin 3,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b := Finset.sum_comm
  simp_rw [hs]
  exact Fintype.prod_sum _

theorem calibrated_central_branch_expansion {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
      ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z (b i) := by
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hdis W Y a e x w z
    htail ha ha1 he he1 hx hw hz hQ hη hsmall]
  congr 1
  exact central_slots_branch_expansion η u T
    (fun i P hP=>outside_prime_supported S hS.bad P (hPS i P hP)) W Y x w z
end SevenEighths.ProbeHighRowFamily
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralBranchProduct -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralBranchProduct

theorem coupled_product_bound {ι : Type*} [Fintype ι]
    (L R : ℝ) (f g y : ι→ℝ) (hf : ∀i,0≤f i)
    (hsub : ∀J : Finset ι,L*(∏j ∈ J,g j)≤R*(∏j ∈ J,y j)) :
    L*(∏j : ι, (f j+g j))≤R*(∏j : ι, (f j+y j)) := by
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  calc
    _ = (∏j ∈ J,f j)*(L*∏j ∈ Finset.univ\J,g j) := by ring
    _ ≤ (∏j ∈ J,f j)*(R*∏j ∈ Finset.univ\J,y j) :=
      mul_le_mul_of_nonneg_left (hsub _) (Finset.prod_nonneg (fun j _=>hf j))
    _ = _ := by ring

theorem three_branch_bound {N : ℕ} (L R E : ℝ)
    (A B T : Fin N→ℂ) (y p : Fin N→ℝ)
    (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) (hy : ∀j,0≤y j) (hp : ∀j,1≤p j)
    (hA : ∀j,‖A j‖≤y j*p j) (hB : ∀j,‖B j‖≤y j*E)
    (hT : ∀J : Finset (Fin N),L*(∏j ∈ J,‖T j‖)≤R*(∏j ∈ J,y j)) :
    L*‖∏j : Fin N, (A j+B j+T j)‖≤R*(E+2)^N*(∏j : Fin N, y j)*(∏j : Fin N,p j) := by
  have hnorm : ‖∏j : Fin N, (A j+B j+T j)‖≤∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro j _
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hc := coupled_product_bound L R (fun j=>‖A j‖+‖B j‖) (fun j=>‖T j‖) y
    (fun j=>add_nonneg (norm_nonneg _) (norm_nonneg _)) hT
  have hpoint (j : Fin N) : (‖A j‖+‖B j‖)+y j≤y j*((E+2)*p j) := by
    have h := hp j
    have hp0 : 0≤p j := zero_le_one.trans h
    have he := mul_nonneg (show 0≤E+1 by linarith) (show 0≤p j-1 by linarith)
    have hm := mul_nonneg (hy j) he
    nlinarith [hA j,hB j]
  calc
    _ ≤ L*(∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖)) := mul_le_mul_of_nonneg_left hnorm hL
    _ ≤ R*(∏j : Fin N,((‖A j‖+‖B j‖)+y j)) := hc
    _ ≤ R*(∏j : Fin N, y j*((E+2)*p j)) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.prod_le_prod₀ (fun j _=>add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hy j)) (fun j _=>hpoint j)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring
end SevenEighths.ProbeCentralBranchProduct

end

end OAI

end

