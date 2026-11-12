module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part032
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part009
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailAggregate
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part031
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part033

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSourcePowerDescent -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourcePowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

def physicalFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  ![Cmain*Z^(2*δ+ε)*ηNorm*Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*
      profileMoment J₁*profileMoment J₂,
    Cexc*Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*K^(5/6:ℝ)*
      (loProduct*wlo*wlo)^(-2/3:ℝ),
    Cdiag*K*‖paperRadialFourier W 0‖,
    Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*K*Z^(-saving)]

lemma physicalFactors_nonneg (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ))
    (hm : 0≤Cmain) (he : 0≤Cexc) (hd : 0≤Cdiag) (ht : 0≤Ctail)
    (hZ : 0≤Z) (hK : 0≤K) (hη : 0≤ηNorm) (hl : 0≤loProduct) :
    ∀j,0≤physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
      loProduct wlo J₁ J₂ SΦ W j := by
  have hp1:=profileMoment_nonneg J₁
  have hp2:=profileMoment_nonneg J₂
  have hheight:=(heightEnvelope_pos t).le
  have hlo : 0≤loProduct*wlo*wlo := by nlinarith [mul_nonneg hl (sq_nonneg wlo)]
  have hs : 0≤SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  intro j
  fin_cases j <;> dsimp [physicalFactors] <;> positivity

theorem original_subsets_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondUniformSubsetSource.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=physicalFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
  have ha : ∀j,0≤a j := physicalFactors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    convert hh using 1
    dsimp [sourceCost,a,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondSourcePowerDescent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondFrozenPowerDescent -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondNonexceptionalScalar

theorem original_subsets_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondFrozenUniformSubset.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=physicalFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
  have ha : ∀j,0≤a j := physicalFactors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    convert hh using 1
    dsimp [sourceCost,a,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondFrozenPowerDescent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma choose_first_tail_order (B ξ saving:ℝ)(hB:0≤B)(hξ:0<ξ):
    ∃Adec:ℕ,∀(HN Z V Tsec:ℝ),1≤Z→0<V→V≤Z^B→0<Tsec→Tsec≤Z^B→
      V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹≤
        (1+Real.exp (2*HN))^2*Z^(-saving):=by
  obtain ⟨Adec,hAdec⟩:=exists_nat_ge ((4*B+saving)/(ξ/4))
  have horder:4*B-(ξ/4)*(Adec:ℝ)≤-saving:=by
    have hh:4*B+saving≤(Adec:ℝ)*(ξ/4):=(div_le_iff₀ (by linarith:0<ξ/4)).mp hAdec
    linarith
  refine ⟨Adec,?_⟩
  intro HN Z V Tsec hZ hV hVcap hT hTcap
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hk:=kernel_inverse_cap HN Z B Tsec hZ hB hT hTcap
  have hd:=reciprocal_cutoff_bound Z (ξ/4) Adec hz
  calc
    _≤(Z^B)^2*((1+Real.exp (2*HN))^2*(Z^B)^2)*Z^(-(ξ/4)*(Adec:ℝ)):=by
      apply mul_le_mul _ hd (by positivity) (by positivity)
      apply mul_le_mul (pow_le_pow_left₀ hV.le hVcap 2) hk
        (inv_nonneg.mpr (sq_nonneg _)) (by positivity)
    _=(1+Real.exp (2*HN))^2*Z^(4*B-(ξ/4)*(Adec:ℝ)):=by
      rw [←Real.rpow_mul_natCast hz.le]
      norm_num only [Nat.cast_ofNat]
      rw [show Z^(B*(2:ℝ))*((1+Real.exp (2*HN))^2*Z^(B*(2:ℝ)))*Z^(-(ξ/4)*(Adec:ℝ))=
        (1+Real.exp (2*HN))^2*(Z^(B*2)*Z^(B*2)*Z^(-(ξ/4)*(Adec:ℝ))) by ring]
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ horder) (sq_nonneg _)

omit [DecidableEq ι] in
theorem first_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_first_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=first_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn
    (fun I J _ _ E _=>(first_nominal_scale_le I J E K V hK).trans hnom) (by simpa using hZ.2)
  simp only [Real.rpow_one] at ht
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0< min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (mul_nonneg (Real.exp_pos HN).le hV.le)) hK.le).trans_eq
        (by ring)
    _=(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem local_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_first_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=local_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s R seed I‖)≤
      Cmass*plainControl s W₁ W₂*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn
    hnom (by simpa using hZ.2)
  simp only [Real.rpow_one] at ht
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0< min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*plainControl s W₁ W₂*V)^2*K*(Real.exp HN*V)*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (mul_nonneg (Real.exp_pos HN).le hV.le)) hK.le).trans_eq
        (by ring)
    _=(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)*(plainControl s W₁ W₂)^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailNatural -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem local_input_tail (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨S,C,hC,htail⟩ := local_input_tail_arbitrary_saving hi wlo whi (3*B) ξ saving
    hhi hwlo hwhi (by positivity) hξ
  refine ⟨S,C,hC,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hV hKi
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hV0 : 0<volume s.toData := volume_pos s
  have hVcap : volume s.toData≤Z^(3*B) := hV.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hTcap : (volume s.toData)^2/K≤Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV0.le hV 2) hKi (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  exact hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K _ hK hVcap hTcap le_rfl

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailSeed
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma paid_seed_power (Z Bseed saving seedNorm : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) :
    Z^(-(saving+Bseed))≤Z^(-saving)/seedNorm := by
  apply (le_div_iff₀ hs).mpr
  calc
    _≤Z^(-(saving+Bseed))*Z^Bseed :=
      mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by rw [←Real.rpow_add hZ];congr 1;ring

lemma paid_seed_term (Z Bseed saving seedNorm A : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) (hA : 0≤A) :
    A*Z^(-(saving+Bseed))≤A*Z^(-saving)/seedNorm := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (paid_seed_power Z Bseed saving seedNorm hZ hs hcap) hA

omit [DecidableEq ι] in
theorem second_input_tail_seed (hi : ι→ℝ) (wlo whi B Bseed ξ saving : ℝ)
    (hhi : ∀i,0≤hi i) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B) (hξ : 0<ξ) :
    ∃SΦ : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(s : Input ι)(W₁ W₂ : 𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(R seed : Ideal O)(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),
      seed≠0→(seed.absNorm:ℝ)≤Z^Bseed→
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K Tsec Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        Z^(-saving)/(seed.absNorm:ℝ) := by
  obtain ⟨SΦ,C,hC,hbound⟩ := second_input_tail_arbitrary_saving hi wlo whi B ξ
    (saving+Bseed) hhi hwlo hwhi hB hξ
  refine ⟨SΦ,C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hseed hseedcap hK hV hT hnom
  have hsn : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed)
  exact (hz.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R seed Φ K Tsec hK hV hT hnom).trans
    (paid_seed_term Z Bseed saving (seed.absNorm:ℝ) _ (zero_lt_one.trans hz.1) hsn hseedcap
      (by positivity))

end SevenEighths.CenteredMomentSourceInputTailSeed

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSourceSeededPowerDescent -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed

def seededFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo seedNorm : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  let a:=physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W
  ![a 0,a 1,a 2,a 3/seedNorm]

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*((τ q U χ).modulus.absNorm:ℝ)*dyadicScale (n 1)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondUniformSubsetSource.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondSourceSeededPowerDescent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondFrozenSeededPowerDescent -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    CenteredMomentSecondFrozenUniformSubset.original_subsets_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

end SevenEighths.CenteredMomentSecondFrozenSeededPowerDescent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondReferenceNormalization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondReferenceNormalization
open HeckeFamily CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondNonexceptionalScalar CenteredMomentSecondRadicalBudget
open CenteredMomentSectorLocalization CenteredMomentSecondSourcePowerDescent
open CenteredMomentSecondSourceSeededPowerDescent
local notation "O"=>HeckeFamily.O

def referenceEnvelope (qref:ℝ)(C D:Ideal O)(U:Finset (CommonIndex C D))(n:Fin 4→ℤ):ℝ:=
  (fixedFactor:ℝ)*qref*(∏P∈U,P.val).absNorm*
    (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm*dyadicScale (n 1)

lemma envelope_rescale (η:Character)(qref E:ℝ)(C D:Ideal O)
    (U:Finset (CommonIndex C D))(n:Fin 4→ℤ):
    (qref/(η.modulus.absNorm:ℝ)*E)*childEnvelope η C D U n=
      E*referenceEnvelope qref C D U n:=by
  have hq:(η.modulus.absNorm:ℝ)≠0:=by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot
  unfold childEnvelope referenceEnvelope
  field_simp

lemma paired_rescale (q qref E₁ E₂:ℝ)(hq:0<q)(hr:0≤qref):
    q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂))=qref*Real.sqrt (E₁*E₂):=by
  rw [show (qref/q*E₁)*(qref/q*E₂)=(qref/q)^2*(E₁*E₂) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (div_nonneg hr hq.le)]
  field_simp

lemma physicalFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo J₁ J₂ SΦ W=
    physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo J₁ J₂ SΦ W:=by
  funext j
  fin_cases j
  · dsimp [physicalFactors]
    have hh:=paired_rescale q qref E₁ E₂ hq hr
    calc
      _=Cmain*Z^(2*δ+ε)*(q*Real.sqrt ((qref/q*E₁)*(qref/q*E₂)))*
        CenteredMomentSecondWindowBudget.heightEnvelope t^(J₁+J₂)*
        CenteredMomentSecondWindowBudget.profileMoment J₁*CenteredMomentSecondWindowBudget.profileMoment J₂:=by ring
      _=_:=by rw [hh];ring
  all_goals rfl

lemma seededFactors_rescale (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo seed:ℝ)(J₁ J₂:ℕ)(SΦ:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hq:0<q)(hr:0≤qref):
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q
      (qref/q*E₁) (qref/q*E₂) r loProduct wlo seed J₁ J₂ SΦ W=
    seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t qref
      E₁ E₂ r loProduct wlo seed J₁ J₂ SΦ W:=by
  unfold seededFactors
  rw [physicalFactors_rescale Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t q qref E₁ E₂ r
    loProduct wlo J₁ J₂ SΦ W hq hr]

end SevenEighths.CenteredMomentSecondReferenceNormalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondFrozenReferenceSeededPowerDescent -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

theorem original_subsets_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenSeededPowerDescent.original_subsets_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hq:0<(s.η.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ s.η.modulus_ne_bot
  have hr:0≤qref/(s.η.modulus.absNorm:ℝ):=div_nonneg hqref.le hq.le
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap
    (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂)
    (mul_nonneg hr hE₁) (mul_nonneg hr hE₂)
  have hbound:=hh
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hleft q hq U n hn D0 hD hcap hs χ v b hb a ha)
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hright q hq U n hn D0 hD hcap hs χ v b hb a ha)
    r hX1 hX2 hY1 hY2
  rw [seededFactors_rescale Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ)
      J₁ J₂ Sf W hq hqref.le] at hbound
  exact hbound

end SevenEighths.CenteredMomentSecondFrozenReferenceSeededPowerDescent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstSeededGaussianPower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSeededGaussianPower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

open CenteredMomentAmplificationChildInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

omit [DecidableEq ι] in
lemma normalized_source_le_norm (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource s R seed W K≤
      ‖sourceGaussEnergy (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) (heightCoeff s.η s.t) W K‖/
          CenteredMomentAmplificationChildInput.volume s := by
  exact div_le_div_of_nonneg_right (Complex.re_le_norm _)
    (CenteredMomentAmplificationChildInput.volume_pos s).le

omit [DecidableEq ι] in
lemma allocated_source_le_norm (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource s C R seed B τ t W K≤
      ‖sourceGaussEnergy
        (finiteColumns (Fintype.piFinset (child s C R B τ t).pools))
        (coefficient (child s C R B τ t) (R*C) seed)
        (heightCoeff τ t) W K‖/CenteredMomentAmplificationChildInput.volume (child s C R B τ t) :=
  normalized_source_le_norm (child s C R B τ t) (R*C) seed W K

omit [DecidableEq ι] in
lemma active_error_source_le_norm (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v W K≤
      ‖sourceGaussEnergy
        (finiteColumns (Fintype.piFinset (errorInput s C R B τ t Q k Bp υ v).pools))
        (coefficient (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed)
        (heightCoeff υ v) W K‖/
          CenteredMomentAmplificationChildInput.volume (errorInput s C R B τ t Q k Bp υ v) :=
  normalized_source_le_norm (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed W K

theorem actual_subsets_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : Finset ι, ∀(s:Input T)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val) → (∀i,s.hi i=hi i.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    normalizedGaussSource s R0 seed W Kphys≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    CenteredMomentSecondFrozenReferenceSeededPowerDescent.original_subsets_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  exact (normalized_source_le_norm s R0 seed W Kphys).trans
    (hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
      E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2)

end SevenEighths.CenteredMomentFirstSeededGaussianPower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstNestedSeededGaussianPower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstNestedSeededGaussianPower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondNonexceptionalCost
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondNonexceptionalAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLiveBlock CenteredMomentSecondEnergySplit CenteredMomentActiveSource
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentSecondSectorColumns CenteredMomentSecondWindowSource
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialPointwise
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CenteredMomentExceptionalAmplitudePair
open CenteredMomentMobiusRegroup CenteredMomentRadialEligibleEnergy CenteredMomentSecondWindowBudget
open CenteredMomentSecondActivePhysicalDictionary
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open CenteredMomentSourceInputTailUniform EisensteinSchwartzPoisson

open CenteredMomentLogDyadic CenteredMomentSecondWindowSource
open MeasureTheory UniqueFactorizationMonoid CenteredMomentAllocatedDetectorAmplitude CenteredMomentCommonExceptionalCost

open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl

open CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedRatioScalar
open CenteredMomentSecondSourcePowerDescent CenteredMomentSourceInputTailSeed
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondNonexceptionalScalar
open CenteredMomentSecondReferenceNormalization

open CenteredMomentAmplificationChildInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstSeededGaussianPower CenteredMomentSecondFrozenRatioCost
open CenteredMomentSecondUniformSubsetSource

abbrev NestedIndex (α:Type*) := ΣT:Finset α,Finset T

def emptyIndex : NestedIndex ι := ⟨∅,∅⟩

theorem nested_source_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0 →
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      Cmain*Z^(2*δ+ε)*profileCost s*(s.η.modulus.absNorm:ℝ)*sourceRadius s*
        Real.sqrt (E₁*E₂)*heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/
          (seed.absNorm:ℝ)+
      Cdiag*Kphys*‖paperRadialFourier W 0‖*
        (2*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)*(∏i,s.M i))^2*
        (1+(∏i:T.2,hi i.val.val)*whi*whi)^(1+ε)*(volume s.toData)^ε/(seed.absNorm:ℝ)+
      Cexc*profileFactor Sprofile s p J Q Kc*
        Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)+
      Ctail*(plainControl s (p.profile 0) (p.profile 1))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys*Z^(-saving)  := by
  have hall (T : NestedIndex ι) := CenteredMomentSecondFrozenLiveDescent.original_source_descent
    wlo whi hwlo hwhi (fun i:T.2=>lo i.val.val) (fun i:T.2=>hi i.val.val) (fun i=>hhi i.val.val)
    W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  choose J Sp Sf hSp Cm Ce Cd Ct hCm hCe hCd hCt hbound using hall
  let J0 : ℕ := ∑T:NestedIndex ι,J T
  let Sp0 := Finset.univ.biUnion Sp
  let Sf0 := Finset.univ.biUnion Sf
  let Cm0 : ℝ := 1+∑T:NestedIndex ι,Cm T
  let Ce0 : ℝ := 1+∑T:NestedIndex ι,Ce T
  let Cd0 : ℝ := 1+∑T:NestedIndex ι,Cd T
  let Ct0 : ℝ := 1+∑T:NestedIndex ι,Ct T
  have sum_pos (f : NestedIndex ι→ℝ) (hf : ∀T,0≤f T) : 0<1+∑T:NestedIndex ι,f T := by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (NestedIndex ι)))=>hf T)
    linarith
  have sum_le (f : NestedIndex ι→ℝ) (hf : ∀T,0≤f T) (T : NestedIndex ι) : f T≤1+∑U:NestedIndex ι,f U := by
    have hh:=Finset.single_le_sum (fun U (_:U∈(Finset.univ:Finset (NestedIndex ι)))=>hf U) (Finset.mem_univ T)
    linarith
  refine ⟨J0,Sp0,Sf0,Finset.mem_biUnion.mpr ⟨emptyIndex,Finset.mem_univ _,hSp emptyIndex⟩,
    Cm0,Ce0,Cd0,Ct0,sum_pos Cm (fun T=>(hCm T).le),(sum_pos Ce hCe).le,
    sum_pos Cd (fun T=>(hCd T).le),sum_pos Ct (fun T=>(hCt T).le),?_⟩
  intro Q hQ hQt hQ72
  choose K hK hev using fun T=>hbound T Q hQ hQt hQ72
  let K0 : ℝ := 1+∑T:NestedIndex ι,K T
  refine ⟨K0,sum_pos K (fun T=>(hK T).le),?_⟩
  have heall : ∀ᶠ Z : ℝ in atTop, ∀T:NestedIndex ι,_ := Filter.eventually_all.mpr hev
  filter_upwards [heall] with Z hZ
  refine ⟨(hZ emptyIndex).1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=(hZ T).2 s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hsp : Sp T⊆Sp0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hsf : Sf T⊆Sf0 := fun x hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hj : J T≤J0 := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hcm:=sum_le Cm (fun T=>(hCm T).le) T
  have hce:=sum_le Ce hCe T
  have hcd:=sum_le Cd (fun T=>(hCd T).le) T
  have hct:=sum_le Ct (fun T=>(hCt T).le) T
  have hfactor:=factor_mono hsp s p hj Q (hK T).le (sum_le K (fun T=>(hK T).le) T)
  have hfn:=profileFactor_nonneg (Sp T) s p (J T) Q (K T) (hK T).le
  have hphi : (Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤Sf0.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := Seminorm.le_def.mp (Finset.sup_mono hsf) W
  have hz : 0≤Z := (hZ T).1.le.trans' zero_le_one
  have hp:=profileCost_nonneg s
  have hm1:=profileMoment_nonneg J₁
  have hm2:=profileMoment_nonneg J₂
  have he:=heightEnvelope_pos s.t
  have hsn : 0≤(seed.absNorm:ℝ) := by positivity
  have hvol:=CenteredMomentSourceInputTailUniform.volume_pos s
  have hc : 0≤(Sf T).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := apply_nonneg _ _
  have hCm0 : 0≤Cm0 := (sum_pos Cm (fun T=>(hCm T).le)).le
  have hCe0 : 0≤Ce0 := (sum_pos Ce hCe).le
  have hCd0 : 0≤Cd0 := (sum_pos Cd (fun T=>(hCd T).le)).le
  have hCt0 : 0≤Ct0 := (sum_pos Ct (fun T=>(hCt T).le)).le
  have hprodhi : 0≤∏i:T.2,hi i.val.val := Finset.prod_nonneg (fun i _=>hhi i.val.val)
  have hprodlo : 0≤∏i:T.2,s.lo i := Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  apply hh.trans
  gcongr

theorem nested_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (physicalFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    nested_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=physicalFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
  have ha : ∀j,0≤a j := physicalFactors_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    convert hh using 1
    dsimp [sourceCost,a,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

theorem nested_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*childEnvelope s.η q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩ :=
    nested_source_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ ε δ θ B ξ (saving+Bseed) hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 R0 seed hR0 hseed hseed0 hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  let a:=seededFactors Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ Sf W
  have hapos:=physicalFactors_nonneg Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) E₁ E₂ r (∏i,s.lo i) wlo J₁ J₂ Sf W
    hCm.le hCe hCd.le hCt.le (zero_le_one.trans hZ.1.le) hKphys.le (by positivity)
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le))
  have hseedpos : 0<(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed0)
  have ha : ∀j,0≤a j := by
    intro j
    fin_cases j
    · exact hapos 0
    · exact hapos 1
    · exact hapos 2
    · exact div_nonneg (hapos 3) hseedpos.le
  have hh': ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      sourceCost s Sp p J Q Kc ε (seed.absNorm:ℝ) a := by
    apply hh.trans
    have htail:=paid_seed_term Z Bseed saving (seed.absNorm:ℝ)
      (Ct*plainControl s (p.profile 0) (p.profile 1)^2*
        Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Kphys)
      (zero_lt_one.trans hZ.1) hseedpos hseedcap (by positivity)
    dsimp [sourceCost,a,seededFactors,physicalFactors]
    simp_rw [hhis]
    dsimp [mass, CenteredMomentAmplificationChildInput.volume,
      CenteredMomentExceptionalAmplitudePair.volume]
    ring_nf at htail ⊢
    linarith only [htail]
  exact hh'.trans (source_rhs s N b b₁ b₂ A hb hb₁ hb₂ hu hc
    (fun i=>by rw [hhis]; exact hhi i.val.val) hs1 hs2 hsb1 hsb2 hmass Sp p J Q Kc ε
    (seed.absNorm:ℝ) hKc.le hε.le (by positivity) a ha)

theorem nested_reference_seeded_power_descent (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    ‖sourceGaussEnergy S β (heightCoeff s.η s.t) W Kphys‖/volume s.toData≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    nested_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  have hq:0<(s.η.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ s.η.modulus_ne_bot
  have hr:0≤qref/(s.η.modulus.absNorm:ℝ):=div_nonneg hqref.le hq.le
  have hh:=hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap
    (qref/(s.η.modulus.absNorm:ℝ)*E₁) (qref/(s.η.modulus.absNorm:ℝ)*E₂)
    (mul_nonneg hr hE₁) (mul_nonneg hr hE₂)
  have hbound:=hh
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hleft q hq U n hn D0 hD hcap hs χ v b hb a ha)
    (by
      intro q hq U n hn D0 hD hcap hs χ v b hb a ha
      simpa only [envelope_rescale] using hright q hq U n hn D0 hD hcap hs χ v b hb a ha)
    r hX1 hX2 hY1 hY2
  rw [seededFactors_rescale Cm Ce Cd Ct Z ε δ θ B saving Kphys s.t
    (s.η.modulus.absNorm:ℝ) qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ)
      J₁ J₂ Sf W hq hqref.le] at hbound
  exact hbound

theorem actual_nested_subsets_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ):
    ∃J:ℕ,∃Sprofile SΦ:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧
      ∃Cmain Cexc Cdiag Ctail:ℝ,0<Cmain ∧ 0≤Cexc ∧ 0<Cdiag ∧ 0<Ctail ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃Kc:ℝ,0<Kc ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀T : NestedIndex ι, ∀(s:Input T.2)(p:Profiles wlo whi),(∀i,s.lo i=lo i.val.val) → (∀i,s.hi i=hi i.val.val) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀A:ℝ, s.upper≤b → Fintype.card T.2≤N → 0≤ s.b₁ → 0≤ s.b₂ →
      s.b₁≤b₁ → s.b₂≤b₂ → mass s≤A →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
      0≤ sourceRadius s → sourceRadius s≤Z^B →
      (s.η.modulus.absNorm:ℝ)≤Z^B → (R0.absNorm:ℝ)≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
    ∃τ:(q:ActiveLabel S β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
    (∀q U,Family s.η q.val.1 q.val.2
      (commonLabels_supported (activeSource S β) _ _ q.property).1
      (commonLabels_supported (activeSource S β) _ _ q.property).2 U (τ q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀Kphys Tsec:ℝ,0<Kphys → volume s.toData≤Z^B → Tsec≤Z^B →
      (volume s.toData)^2/Kphys≤Tsec →
      0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Z^B →
    ∀qref:ℝ,0<qref→∀E₁ E₂:ℝ,0≤E₁ → 0≤E₂ →
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.1,
      frozenCoefficient b.val q.val.1 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.1 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.1 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₁*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₁))→
    (∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:SourceBlocks q.val.1 q.val.2 U Kphys (frequencyRadius Tsec Z ξ) (sourceRadius s),
      physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false s.η χ₀ Q m q.val.1 q.val.2 U (frequencyRadius Tsec Z ξ)) W Kphys
        (fun i=>(n i:ℤ))≠0→
      ∀D0∈divisorPool Finset.univ (fun J:sectorPool q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).2.1 S=>(J:Ideal O)),
      (D0.absNorm:ℝ)≤ sourceRadius s/(q.val.2.absNorm:ℝ)→Squarefree D0→
      ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools q.val.2,
      frozenCoefficient b.val q.val.2 R0 s.ν s.W s.P≠0→
      ∀a∈(commonData (withHeight s (τ q U χ) v) q.val.2 R0 b).toSource.active D0,
      childEnergy (commonData (withHeight s (τ q U χ) v) q.val.2 R0 b)
        (canonicalRadial (τ q U χ) Q (fun i=>(n i:ℤ))) D0 a≤
          E₂*referenceEnvelope qref q.val.1 q.val.2 U (fun i=>(n i:ℤ))*
          (max 1 (1/retainedRatio (fun i=>(n i:ℤ))))^((1:ℝ)/6)*(1+‖v‖)^(2*J₂))→
    ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    normalizedGaussSource s R0 seed W Kphys≤
      (∑j, coefficients N b b₁ b₂ A Sprofile p J Q Kc s.t ε (seed.absNorm:ℝ)
        (seededFactors Cmain Cexc Cdiag Ctail Z ε δ θ B saving Kphys s.t
          qref E₁ E₂ r (∏i,s.lo i) wlo (seed.absNorm:ℝ) J₁ J₂ SΦ W) j *
        (CenteredMomentAmplificationChildInput.volume s)^(powers ε j))*mass s^2 := by
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hall⟩:=
    nested_reference_seeded_power_descent
      wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
        ε δ θ B Bseed ξ saving hε hδ hθ hB hξ
  refine ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Kc,hKc,hev⟩:=hall Q hQ hQt hQ72
  refine ⟨Kc,hKc,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N S β
  obtain ⟨τ,hfamily,hchild⟩:=hZ.2 T s p hlo hhis hP hw1 hw2 A hu hc hs1 hs2 hsb1 hsb2 hmass
    R0 seed hR0 hseed hseed0 hseedcap hH0 hH hη hR0N
  refine ⟨τ,hfamily,?_⟩
  intro χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
    E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2
  exact (normalized_source_le_norm s R0 seed W Kphys).trans
    (hchild χ₀ m hm hml hm2 Kphys Tsec hKphys hVcap hTcap hnom hR hRcap qref hqref
      E₁ E₂ hE₁ hE₂ hleft hright r hX1 hX2 hY1 hY2)

end SevenEighths.CenteredMomentFirstNestedSeededGaussianPower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputZeroUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceInputZeroUniform
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization EisensteinSchwartzPoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem first_input_zero_bound (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(_hwhi:0≤whi)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*(volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hbound⟩:=active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let L:=1+(∏i,hi i)*whi^2
  have hprod:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hL:0<L:=by dsimp [L];positivity
  refine ⟨4*C₀*L^(1+ε),by positivity,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  let β:=profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed
  have hc:coefficient s R seed=finiteColumnCoefficient (Fintype.piFinset s.pools) β:=by
    unfold coefficient;rw [he₁,he₂]
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hβ (v:Tuple ι):‖β v‖≤2*plainControl s W₁ W₂:=by
    have hb:=profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M W₁ W₂
      (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
      (fun i=>zero_le_one.trans (s.M_ge_one i)) (apply_nonneg _ _) (apply_nonneg _ _)
      s.W_bound (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
    exact hb.trans_eq (by dsimp [plainControl];ring)
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hN (v:Tuple ι)(hv:β v≠0):finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*V:=by
    have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
      s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
      (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv
    refine ⟨hp.1,hp.2.trans ?_⟩
    simp only [map_one,Nat.cast_one,one_mul,div_one]
    change (∏i,hi i)*whi*whi*(s.X₁*s.X₂)*(∏i,s.P i)≤_
    have hh:0≤V:=hV.le
    dsimp [L,V,volume] at *
    nlinarith
  rw [hc]
  by_cases hsmall:L*V<1
  · rw [zeroEnergy_eq_zero_of_subunit s.η m A s.t (Fintype.piFinset s.pools) β Φ K
      (L*V) hsmall (fun v _ hv=>hN v hv),norm_zero,zero_div]
    positivity
  have hb:=hbound (le_refl (Fintype.card ι)) s.η m A s.t (Fintype.piFinset s.pools) β Φ
    (L*V) K (2*plainControl s W₁ W₂) (le_of_not_gt hsmall) hK (by positivity)
    (fun v _ _=>hβ v) (fun I _ hI=>by
      obtain ⟨v,hv,hn,he⟩:=finiteColumnCoefficient_witness _ _ I hI
      rw [←he];exact (hN v hn).2)
  apply (div_le_div_of_nonneg_right hb hV.le).trans_eq
  have hp:(L*V)^(1+ε)/V=L^(1+ε)*V^ε:=by
    rw [Real.mul_rpow hL.le hV.le,Real.rpow_add hV,Real.rpow_one]
    field_simp
  change C₀*K*(2*plainControl s W₁ W₂)^2*‖paperRadialFourier Φ 0‖*(L*V)^(1+ε)/V=_
  calc
    _=4*C₀*(plainControl s W₁ W₂)^2*K*‖paperRadialFourier Φ 0‖*((L*V)^(1+ε)/V):=by ring
    _=_:=by rw [hp];ring

omit [DecidableEq ι] in
theorem first_input_zero_uniform (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        (volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hb⟩:=first_input_zero_bound hi wlo whi ε hhi hwlo hwhi hε
  obtain ⟨SΦ,D,hD,hd⟩:=paperRadialFourier_euler_source_weighted_bound 0 0
  refine ⟨SΦ,C₀*D,mul_pos hC₀ hD,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  have hf:‖paperRadialFourier Φ 0‖≤D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    simpa only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,pow_zero,one_mul,zero_mul] using
      hd Φ 0 le_rfl 0 le_rfl
  have hVp:0≤(volume s.toData)^ε:=Real.rpow_nonneg (volume_pos s).le _
  apply (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
  calc
    _≤C₀*(plainControl s W₁ W₂)^2*K*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        (volume s.toData)^ε:=by gcongr
    _=_:=by ring

omit [DecidableEq ι] in
theorem first_input_zero_capped (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→volume s.toData≤Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε:=by
  let δ:=ε/(B+1)
  have hδ:0<δ:=div_pos hε (by linarith)
  obtain ⟨SΦ,C,hC,hb⟩:=first_input_zero_uniform hi wlo whi δ hhi hwlo hwhi hδ
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ K hK
  have hp:(volume s.toData)^δ≤Z^ε:=by
    calc
      _≤(Z^B)^δ:=Real.rpow_le_rpow (volume_pos s).le hV hδ.le
      _=Z^(B*δ):=(Real.rpow_mul (zero_le_one.trans hZ) B δ).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by
        have hh:δ*(B+1)=ε:=by dsimp [δ];field_simp
        nlinarith)
  exact (hb s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

end SevenEighths.CenteredMomentSourceInputZeroUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputFirstRemainder -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstRemainder
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputZeroUniform CenteredMomentSourceInputFirstSectorTail
open CenteredMomentFirstEnergy EisensteinSchwartzPoisson
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
theorem original_first_remainder (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K-
        CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
          (volume s.toData) Z ξ‖/volume s.toData≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Cdiag,hCdiag,hdiag⟩:=first_input_zero_capped hi wlo whi B ε hhi hwlo hwhi hB hε
  obtain ⟨Stail,Ctail,hCtail,htail⟩:=local_input_tail hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hd:=hdiag Z hZ.1.le s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hVcap m A R seed Φ K hK.le
  have ht:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hVcap hKi
  rw [CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized
    s.η m A s.t hml hm2 (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed) Φ K (volume s.toData) Z ξ hK]
  rw [show ∀a b c:ℂ,a+b+c-b=a+c by intros;ring]
  exact ((div_le_div_of_nonneg_right (norm_add_le _ _) (volume_pos s).le).trans_eq
    (add_div _ _ _)).trans (add_le_add hd ht)

end SevenEighths.CenteredMomentSourceInputFirstRemainder

end

end OAI

end

