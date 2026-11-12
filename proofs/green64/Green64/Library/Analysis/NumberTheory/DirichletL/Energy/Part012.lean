module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part034
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part030
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part037
public import Green64.Library.OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part033
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part028
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part035

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularPower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularPower
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

theorem actual_original_subsets_annular_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(_hξ1:ξ≤1)(hreserve:0< reserve):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(B:actualAllocations src.pools C)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) →
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap)) →
    let input:=child src C R0 B τ t;
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ);
    let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j;
    let aerror:=fun (prime:elementPool P)(i:Fin 3)(_χ:RayCharacter)(j:Fin 4)=>
      Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
        deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j;
    childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile
      H0≤
      (∑j,sourceCoefficients P ((amplifierCap A 0 ξ+2*sigma)/(sigma/6)) amain aerror (powers εsrc) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  let Bcap:=readyBudget A Pcap
  have hBcap:0≤Bcap:=readyBudget_nonneg A Pcap hA hPcap
  have hAmp:0≤amplifierCap A 0 ξ:=by unfold amplifierCap;positivity
  obtain ⟨U,J,huniform⟩:=actual_original_subsets_amplified_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma referenceCost hsigma hξsmall referenceCost_ge_one
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,Zbase,hZbase,hm,he⟩:=huniform η₀ Q hQM hQ0 hQt hQ72
  have hall:=Filter.eventually_all.mpr (fun Aorig:Finset α=>
    eventually_original_subsets_power_amplification (Ω:=Aorig) M H hH fixedBadPrimes (Finset.Subset.refl _)
      sigma primeLoss (Pcap+A+1) Bseed (amplifierCap A 0 ξ) (max 1 bslot) eta 1 ξ reserve
      hsigma hPrimeLoss hAmp (by positivity) heta (by norm_num) hξ.le hreserve)
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss hAmp heta
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp
    (hall.and (hsepEvent.and (eventually_ge_atTop Zbase)))
  refine ⟨Cbound,hCbound,max Z₀ Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Z hZthreshold
  obtain ⟨hamp,hsepdata,hZZbase⟩:=
    hZ₀ Z ((le_max_left _ _).trans hZthreshold)
  have hZ:1<Z:=hZbase.trans_le hZZbase
  dsimp only
  have hbase:=hamp (∅:Finset α)
  refine ⟨hbase.2.1,hbase.2.2.1,?_⟩
  intro τ
  have hf (Aorig:Finset α):=(hamp Aorig).2.2.2 τ
  choose υ hυN henergy using hf
  refine ⟨υ,hυN,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC
    E hmod K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth
    hdrop hclip hsourceLower hreadym herrorPacket
  let input:=child src C R0 B τ t
  let delta:=frequencyLoss Z 32 ξ
  have hdelta:0≤delta:=frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le
  have hRC:(R0*C).absNorm=R0.absNorm*C.absNorm:=map_mul _ _ _
  have hRcommon:( (R0*C).absNorm:ℝ)≤Z^(Pcap+A+1):=by
    rw [hRC,Nat.cast_mul]
    calc
      _≤Z^Pcap*Z^(A+1):=mul_le_mul hRcap hNC (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
      _=Z^(Pcap+A+1):=by rw [←Real.rpow_add (by linarith:0<Z)];congr 1;ring
  have hmainlower:=main_minimum_lower src C R0 hC.1 B τ t Z hZ
  have hmain:=hm Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
    hreadym seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower _
    hmainlower.1 hmainlower.2.1 hmainlower.2.2.1 hmainlower.2.2.2
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))))
    (i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>Hcoef j*
      errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
      deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have haerror:∀prime i χ j,0≤aerror prime i χ j:=by
    intro prime i χ j
    apply mul_nonneg (hHcoef j)
    fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk]
    all_goals try unfold errorRadius errorCommonRadius
    all_goals positivity
  have hsupp:∀i,Function.support (input.W i)⊆Set.Iic (max 1 bslot):=by
    intro i x hx
    exact ((src.support i.val hx).2.trans (hhi i.val)).trans (le_max_right _ _)
  let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun i=>w i.val
  have hz:∀i,z i≤eta:=fun i=>hweta i.val
  have hlen:∀i,input.P i=Z^(z i):=fun i=>hmatch.scale i.val
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hsepdata
  have herror:∀prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))),
      ∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput input).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      childNormalizedGaussSource (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1))
        (R0*C) seed Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t
        CenteredMomentFirstAmplificationChoice.ballProfile
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))≤
      (∑j,aerror prime i χ j*(volume (child (activeInput input)
        ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t))^(powers εsrc j))*
        mass (child (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t)^2:=by
    intro prime i χ Bp
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    have hprime:prime.val≠0:=hd.1.ne_zero
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hsep z hz hlen hsupp
        (original input (R0*C) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*C) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=CenteredMomentFirstAmplificationChoice.errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυN Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have hvcap:=actual_error_reference_cap τ _ χ prime.val hprime (errorIndex i) hk Z hZ hN
    have hre:=herrorPacket prime i χ Bp
    rcases hre with hdead|hlive
    · change normalizedGaussSource _ _ _ _ _≤_
      apply (CenteredMomentFirstSecondInputGates.normalized_zero _ _ _ hdead _ _).le.trans
      exact mul_nonneg (Finset.sum_nonneg (fun j _=>mul_nonneg (haerror prime i χ j)
        (Real.rpow_nonneg (volume_pos _).le _))) (sq_nonneg _)
    · have hlower:=error_minimum_lower src C R0 hC.1 B τ t prime.val hprime
        (errorIndex i+1) Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t Z hZ
      have hprimeScale: sigma/6≤Real.logb Z (normValue prime.val):=by
        have hh:=Real.logb_le_logb_of_le hZ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/6)) (hdata _ hd.2.1).2.2.1
        simpa only [normValue,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
      have hh:=he Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
        w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
        hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
        K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
        prime.val hprime (errorIndex i) hk hprimeScale hcop Bp _ χ hN hvcap _ rfl
        hlive seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
        hcap hMdecl hMwidth hdrop hclip hsourceLower _
        hlower.1 hlower.2.1 hlower.2.2.1 hlower.2.2.2
      exact hh
  have hE:Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hann:=henergy Aorig (CenteredMomentCommonProfile.liveIndices B.val) input rfl hsupp z hz hlen
    (R0*C) seed (mul_ne_zero hR0 hC.1) hseedne hRcommon hseedcap
    (Real.logb Z (D.absNorm:ℝ)) (Real.logb Z (C.absNorm:ℝ)) C D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hE K (volume src) _
    hK (volume_pos src) (by simp only [one_mul];exact le_rfl) H0 hH0 houter hHcap
    amain aerror (powers εsrc) haerror (by simpa only [mul_one,nominalLog,input,amain,Hcoef,Kmain,mainRadius,paid,deficit,rmain,delta] using hmain)
    (by simpa only [mul_one,nominalLog,errorRadius,delta] using herror)
  apply hann.trans_eq
  rw [source_coefficients_identity _ _ _ (volume_pos input).le]
  dsimp only [normValue]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalAnnularPower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularLower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularLower
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentCanonicalFirst
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstAmplificationChoice
open CenteredMomentPrimeElements CenteredMomentSectorLocalization
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstChildProfileControl
open CenteredMomentSecondChildPowerBudget
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma parent_lower_ge {ι:Type*}[Fintype ι](s:Input ι)(Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤ s.X₁)(hX₂:Z^r≤ s.X₂)(hY₁:Z^r≤ s.Y₁)(hY₂:Z^r≤ s.Y₂):
    r≤parentLower s Z:=by
  have h (x:ℝ)(hx:Z^r≤x):r≤Real.logb Z x:=by
    have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r) hx
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  exact le_min (le_min (h _ hX₁) (h _ hX₂)) (le_min (h _ hY₁) (h _ hY₂))

lemma exceptional_cap_antitone (Z r s:ℝ)(hZ:1≤Z)(hrs:r≤ s):
    Z^(-2*max s 0/3)≤Z^(-2*max r 0/3):=by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hm:=max_le_max_right 0 hrs
  linarith

lemma main_powers_antitone (q Z K ell deficit paid saving r s:ℝ)
    (hZ:1≤Z)(hK:0≤K)(hrs:r≤ s):
    ∀j,mainPowers q Z K ell deficit paid saving s j≤ mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk,le_refl]
  exact mul_le_mul_of_nonneg_left (exceptional_cap_antitone Z r s hZ hrs) (Real.rpow_nonneg hK _)

lemma error_powers_antitone (p:O)(k:ℕ)(q Z K deficit paid saving r s:ℝ)
    (hZ:1≤Z)(hK:0≤K)(hrs:r≤ s):
    ∀j,errorPowers p k q Z K deficit paid saving s j≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk,le_refl]
  exact mul_le_mul_of_nonneg_left (exceptional_cap_antitone Z r s hZ hrs) (Real.rpow_nonneg hK _)

lemma source_coefficients_mono (P:Finset (Ideal O))(mainFactor:ℝ)(hf:0≤ mainFactor)
    (am bm:Fin 4→ℝ)(ae be:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (hm:∀j,am j≤bm j)(he:∀p i χ j,ae p i χ j≤be p i χ j):
    ∀j,sourceCoefficients P mainFactor am ae alpha j≤ sourceCoefficients P mainFactor bm be alpha j:=by
  intro j
  unfold sourceCoefficients
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (mul_le_mul_of_nonneg_left (hm j) hf)
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (CenteredMomentAmplificationErrorEnergy.localErrorCost_nonneg p (errorIndex i)))
  apply Finset.sum_le_sum
  intro χ _
  exact mul_le_mul_of_nonneg_right (he p i χ j)
    (Real.rpow_nonneg (pow_nonneg (by unfold normValue;positivity) _) _)

theorem actual_source_coefficients_lower {ι:Type*}[Fintype ι]
    (src:Input ι)(P:Finset (Ideal O))(C D:Ideal O)(E:Finset (CommonIndex C D))
    (K Z sigma delta reserve Mamp q deficit paid saving r:ℝ)
    (hZ:1<Z)(hsigma:0<sigma)(hMamp:0≤Mamp)
    (hX₁:Z^r≤ src.X₁)(hX₂:Z^r≤ src.X₂)(hY₁:Z^r≤ src.Y₁)(hY₂:Z^r≤ src.Y₂)
    (Hcoef:Fin 4→ℝ)(hH:∀j,0≤Hcoef j)(alpha:Fin 4→ℝ):
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Kerr:=fun p:elementPool P=>fun i:Fin 3=>errorRadius C D E K (volume src) Z sigma delta reserve p (errorIndex i+1);
    let oldr:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let newr:=r-Real.logb Z (C.absNorm:ℝ);
    ∀j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving oldr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (oldr-errorRemoval p Z (errorIndex i+1)) j) alpha j≤
    sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving newr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (newr-errorRemoval p Z (errorIndex i+1)) j) alpha j:=by
  dsimp only
  have hr:=parent_lower_ge src Z r hZ hX₁ hX₂ hY₁ hY₂
  apply source_coefficients_mono P _ (by positivity)
  · intro j
    exact mul_le_mul_of_nonneg_left (main_powers_antitone q Z _ _ _ _ _ _ _ hZ.le
      (by unfold mainRadius CenteredMomentAmplifiedRetainedRadius.mainCommonRadius;positivity)
      (sub_le_sub_right hr _) j) (hH j)
  · intro p i χ j
    exact mul_le_mul_of_nonneg_left (error_powers_antitone p (errorIndex i+1) q Z _ _ _ _ _ _ hZ.le
      (by unfold errorRadius CenteredMomentAmplifiedRetainedRadius.errorCommonRadius;positivity)
      (sub_le_sub_right (sub_le_sub_right hr _) _) j) (hH j)

theorem actual_high_annular_sum {ι:Type*}[Fintype ι]
    (src:Input ι)(P:Finset (Ideal O))(C D R:Ideal O)(E:Finset (CommonIndex C D))
    (B:actualAllocations src.pools C)(τ:Character)(t:ℝ)
    (K Z sigma delta reserve Mamp deficit paid saving Mwidth eps:ℝ)
    (hZ:1<Z)(hsigma:0<sigma)(hMamp:0≤Mamp)
    (hX₁:Z^(Mwidth/4)≤ src.X₁)(hX₂:Z^(Mwidth/4)≤ src.X₂)
    (hY₁:Z^(Mwidth/4)≤ src.Y₁)(hY₂:Z^(Mwidth/4)≤ src.Y₂)
    (Hcoef:Fin 4→ℝ)(hH:∀j,0≤Hcoef j):
    let input:=child src C R B τ t;
    let q:ℝ:=τ.modulus.absNorm;
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Kerr:=fun p:elementPool P=>fun i:Fin 3=>errorRadius C D E K (volume src) Z sigma delta reserve p (errorIndex i+1);
    let oldr:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let newr:=Mwidth/4-Real.logb Z (C.absNorm:ℝ);
    (∑j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving oldr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (oldr-errorRemoval p Z (errorIndex i+1)) j) (powers eps) j*
      (volume input)^(powers eps j))*mass input^2≤
    (∑j,sourceCoefficients P ((Mamp+2*sigma)/(sigma/6))
      (fun j=>Hcoef j*mainPowers q Z Kmain (sigma/3) deficit paid saving newr j)
      (fun p i _χ j=>Hcoef j*errorPowers p (errorIndex i+1) q Z (Kerr p i) deficit paid saving
        (newr-errorRemoval p Z (errorIndex i+1)) j) (powers eps) j*
      (volume input)^(powers eps j))*mass input^2:=by
  dsimp only
  have h:=actual_source_coefficients_lower src P C D E K Z sigma delta reserve Mamp
    (τ.modulus.absNorm:ℝ) deficit paid saving (Mwidth/4) hZ hsigma hMamp hX₁ hX₂ hY₁ hY₂
    Hcoef hH (powers eps)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_right (h j)
    (Real.rpow_nonneg (volume_pos _).le _))

end SevenEighths.CenteredMomentEnergyCanonicalAnnularLower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalLowColumn -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowColumn
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers

lemma source_mass_cap {ι:Type*}[Fintype ι](s:Input ι)(N:ℕ)(Mslot:ℝ)
    (hc:Fintype.card ι≤N)(hM:∀i,s.M i≤Mslot):mass s≤(max 1 Mslot)^N:=by
  calc
    _≤∏i:ι,max 1 Mslot:=by
      apply Finset.prod_le_prod₀
      · intro i _;exact zero_le_one.trans (s.M_ge_one i)
      · intro i _;exact (hM i).trans (le_max_right _ _)
    _=(max 1 Mslot)^Fintype.card ι:=by simp
    _≤_:=pow_le_pow_right₀ (le_max_left _ _) hc

lemma inherited_height_split (t height:ℝ)(J:ℕ)(hh:0≤height):
    (1+|t|+height)^J≤(1+height)^J*(1+|t|)^(2*J):=by
  have hbase:1+|t|+height≤(1+height)*(1+|t|):=by
    nlinarith [abs_nonneg t,mul_nonneg hh (abs_nonneg t)]
  calc
    _≤((1+height)*(1+|t|))^J:=pow_le_pow_left₀ (by positivity) hbase J
    _=(1+height)^J*(1+|t|)^J:=mul_pow _ _ _
    _≤_:=mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega:J≤2*J)) (by positivity)

theorem actual_admitted_subsets_low_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)(heps1:εsrc≤1):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(t:ℝ)(seed0:Ideal O),seed0∣C →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → 0≤Mdecl → Mdecl≤A →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hann⟩:=actual_original_subsets_annular_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers N lower upper εsrc hlower hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp:0≤Mamp:=by dsimp [Mamp,amplifierCap];positivity
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 Mslot)^(2*N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Z₀,hZ₀,hannZ⟩:=hann η₀ Q hQM hQ0 hQt hQ72
  let Ccolumn:=Cb*upper^N*avg*Ca*(max 1 Mslot)^(2*N)
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,Z₀,hZ₀,?_⟩
  intro Z hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hZpos:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hPne,hPcard,hfamily⟩:=hannZ Z hZZ
  dsimp only at hPne hPcard hfamily ⊢
  refine ⟨hPne,hPcard,?_⟩
  intro τ
  obtain ⟨υ,hυ,henergy⟩:=hfamily τ
  refine ⟨υ,hυ,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K H0 hK hH0 houter hHcap t seed0 hseed0 seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower hpackets
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let delta:=frequencyLoss Z 32 ξ
  let Bcap:=readyBudget A Pcap
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤ coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    exact henergy Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
      K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (hpackets B hB).1 (hpackets B hB).2
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hscalar:=actual_low_homogeneous_four_powers M H fixedBadPrimes (Finset.Subset.refl _)
    src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl A Mamp primeLoss
    hK (volume_pos src) hZ hsigma hεsrc.le hMdecl0 hMA hMdecl hlow hPrimeLoss.le hMamp hPcard hmod
    upper N hupper Hcoef hHcoef front (seed.absNorm:ℝ) (A+1)
    (CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    hfront hNseed heps1 hNC (fun j=>le_rfl) rmain rerror
  dsimp only at hscalar
  have hmass:=source_mass_cap src N Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 Mslot)^(2*N):=by
    calc
      _≤((max 1 Mslot)^N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ ref*(Cb*mass src^2*∑j,normalizedPower upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) N (powers εsrc j)):=hcommonBound
    _≤ ref*(Cb*mass src^2*((upper^N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ ref*(Cb*(max 1 Mslot)^(2*N)*((upper^N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring

end SevenEighths.CenteredMomentEnergyCanonicalLowColumn

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalHighColumn -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighColumn
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers

open CenteredMomentEnergyCanonicalLowColumn CenteredMomentEnergyCanonicalAnnularLower
open CenteredMomentEnergyFirstHighGaussianUniformPowers

theorem actual_admitted_subsets_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)(heps1:εsrc≤1):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(t:ℝ)(seed0:Ideal O),seed0∣C →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → 0≤Mdecl → Mdecl≤A →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤ src.X₁ → Z^(Mwidth/4)≤ src.X₂ →
    Z^(Mwidth/4)≤ src.Y₁ → Z^(Mwidth/4)≤ src.Y₂ →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hann⟩:=actual_original_subsets_annular_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers N lower upper εsrc hlower hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp:0≤Mamp:=by dsimp [Mamp,amplifierCap];positivity
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 Mslot)^(2*N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Z₀,hZ₀,hannZ⟩:=hann η₀ Q hQM hQ0 hQt hQ72
  let Ccolumn:=Cb*upper^N*avg*Ca*(max 1 Mslot)^(2*N)
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,Z₀,hZ₀,?_⟩
  intro Z hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hZpos:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hPne,hPcard,hfamily⟩:=hannZ Z hZZ
  dsimp only at hPne hPcard hfamily ⊢
  refine ⟨hPne,hPcard,?_⟩
  intro τ
  obtain ⟨υ,hυ,henergy⟩:=hfamily τ
  refine ⟨υ,hυ,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K H0 hK hH0 houter hHcap t seed0 hseed0 seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower hpackets
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let delta:=frequencyLoss Z 32 ξ
  let Bcap:=readyBudget A Pcap
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=Mwidth/4-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤ coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    have hann:=henergy Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
      K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (hpackets B hB).1 (hpackets B hB).2
    apply hann.trans
    exact actual_high_annular_sum src P C D R0 E B τ t
      K Z sigma delta reserve Mamp deficit paid saving Mwidth εsrc hZ hsigma hMamp
      hrawX₁ hrawX₂ hrawY₁ hrawY₂ Hcoef hHcoef
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hPsrc:∀i,1≤ src.P i:=by
    intro i
    rw [hmatch.scale i]
    exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i
    rw [hmatch.scale i,Real.logb_rpow hZpos hZ.ne']
  have hVcap:=CenteredMomentEnergyInputParentCapacity.original_volume_cap src Z κ Mdecl hZ hκsmall hPsrc
    (by simpa only [hlogs] using hcap)
  have hvolume:Real.logb Z (volume src)≤Mdecl:=by
    have hh:=Real.logb_le_logb_of_le hZ (volume_pos src) hVcap
    simpa only [Real.logb_rpow hZpos hZ.ne'] using hh
  have hscalar:=actual_high_homogeneous_four_powers M H fixedBadPrimes (Finset.Subset.refl _)
    src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl Mwidth A Mamp primeLoss
    hK (volume_pos src) hZ hsigma hεsrc.le hMdecl0 hMA hMwidth hwidthle hvolume hPrimeLoss.le hMamp hPcard hmod
    upper N hupper Hcoef hHcoef front (seed.absNorm:ℝ) (A+1)
    (CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    hfront hNseed heps1 hNC (fun j=>le_rfl)
  dsimp only at hscalar
  have hmass:=source_mass_cap src N Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 Mslot)^(2*N):=by
    calc
      _≤((max 1 Mslot)^N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ ref*(Cb*mass src^2*∑j,normalizedPower upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) N (powers εsrc j)):=hcommonBound
    _≤ ref*(Cb*mass src^2*((upper^N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ ref*(Cb*(max 1 Mslot)^(2*N)*((upper^N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring

end SevenEighths.CenteredMomentEnergyCanonicalHighColumn

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstRightAdmission -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstRightAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSecondInputGates CenteredMomentFirstSecondActiveErrorGates
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedRadiusLower CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentSectorLocalization
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceConductorCaps
open CenteredMomentEnergyInputParentCapacity CenteredMomentEnergyBands
open CenteredMomentEnergyAmplifiedChildWidth CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentActiveSource
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentRowNorm
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentFirstMixedRightTransport
local notation "O" => HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma main_radius_right (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) :
    columnMainRadius C D E K V Z σ δ reserve true =
      mainRadius D C (swapSubset C D E) K V Z σ δ reserve := by
  simp only [columnMainRadius, columnIdeal, oppositeIdeal, ite_true,
    mainRadius, swapSubset_generator, nominal_swap]

lemma error_radius_right (C D : Ideal O) (E : Finset (CommonIndex C D))
    (K V Z σ δ reserve : ℝ) (p : O) (k : ℕ) :
    columnErrorRadius C D E K V Z σ δ reserve true p k =
      errorRadius D C (swapSubset C D E) K V Z σ δ reserve p k := by
  simp only [columnErrorRadius, columnIdeal, oppositeIdeal, ite_true,
    errorRadius, swapSubset_generator, nominal_swap]

theorem eventually_right_main_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂,
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → 0 ≤ ξ → ξ ≤ 1 →
      0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ B : actualAllocations s.pools D, ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val D R s.ν s.W s.P ≠ 0 →
      let Km := mainRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve
      F.right.modulus = s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {(primeSubsetGenerator (fun P : CommonIndex D C => P.val)
          (swapSubset C D E)*activeConductor D C)} ∧
      Ready (child s D R B F.right t) (R*D) Km Z ξ (readyBudget A P) ∧
      (∀ I : Ideal O, coefficient (child s D R B F.right t) (R*D) innerL I ≠ 0 →
        lowerFactor N l a * volume (child s D R B F.right t) ≤ (I.absNorm : ℝ)) := by
  filter_upwards [eventually_main_packet N b b₁ b₂ l a A P hb hb₁ hb₂ hl ha hA hP] with Z hz
  refine ⟨hz.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1
    hreserve hsec rows W n hn hblock B t innerL hB
  dsimp only
  have hh := hz.2 s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F F.right (Or.inr rfl)
    K Csec Tsec σ ξ reserve hK hCsec hσ hξ hξ1 hreserve hsec rows W n hn hblock
    true B t hB
  refine ⟨right_modulus s.η C D hC E ξ₁ ξ₂ F, ?_,
    main_lower_support N l a hl ha s hc hs hW₁ hW₂ D R innerL B F.right t⟩
  have hr : Ready (child s D R B F.right t) (R*D)
      (columnMainRadius C D E K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve true)
      Z ξ (readyBudget A P) := hh.1
  rw [main_radius_right] at hr
  exact hr

theorem eventually_right_error_packet (N : ℕ) (b b₁ b₂ l a A P : ℝ)
    (hb : 1 ≤ b) (hb₁ : 1 ≤ b₁) (hb₂ : 1 ≤ b₂)
    (hl : 0 < l) (ha : 0 < a) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
      ∀ s : Input ι, Fintype.card ι ≤ N → Endpoints b b₁ b₂ s → l ≤ s.lower →
      (∀ x, s.W₁ x ≠ 0 → a ≤ x) → (∀ x, s.W₂ x ≠ 0 → a ≤ x) →
      ∀ κ : ℝ, 1/6 ≤ κ → (∀ i, 1 ≤ s.P i) →
      length Z s.X₁ + length Z s.X₂ + 6*κ*(∑ i, Real.logb Z (s.P i)) ≤ A →
      (s.η.modulus.absNorm : ℝ) ≤ Z^A →
      ∀ R seed0 : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z^P → Squarefree seed0 →
      ∀ C D : Ideal O, ∀ hC : Supported C, ∀ hD : Supported D,
      (C,D) ∈ CenteredMomentFirstSectors.commonLabels
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)))
        (CenteredMomentSourceRow.supportedColumns (activeSource
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0))) →
      ∀ E : Finset (CommonIndex C D), ∀ ξ₁ ξ₂ : RayCharacter,
      ∀ F : FixedPair s.η C D hC E ξ₁ ξ₂,
      ∀ K Csec Tsec σ ξ reserve : ℝ, 0 < K → 0 < Csec → 0 ≤ σ → σ ≤ 1 →
      0 ≤ ξ → ξ ≤ 1 → 0 ≤ reserve →
      Tsec ≤ Csec * firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E}) K (volume s) →
      ∀ rows : Finset O, ∀ W : 𝓢(ℝ,ℂ), ∀ n : Fin 4 → ℤ,
      Retained (frequencyRadius Tsec Z ξ) (n 1) →
      block s.η (fixedBadMask*idealGenerator R) 1 s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed0)
        C D hC hD E rows W (fun _ => logAnnulus) K
        (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) ≠ 0 →
      ∀ B : actualAllocations s.pools D, ∀ t : ℝ, ∀ innerL : Ideal O,
      frozenCoefficient B.val D R s.ν s.W s.P ≠ 0 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (Sbad : Finset (Ideal O)),
      fixedBadPrimes ⊆ Sbad →
      ∀ p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^(σ/3))),
      ∀ k : ℕ, k = 1 ∨ k = 6 ∨ k = 7 →
      (∀ i, ∀ I ∈ (activeInput (child s D R B F.right t)).slots i, IsCoprime (Ideal.span {p}) I) →
      ∀ Bp : actualAllocations (activeInput (child s D R B F.right t)).pools ((Ideal.span {p})^k),
      ∀ (χ : RayCharacter) (υ : Character) (v : ℝ),
      υ.modulus.absNorm ≤ radicalBound (childCharacter F.right χ) fixedBadMask p (errorMovingExponent (k-1)) →
      let d := errorInput s D R B F.right t (Ideal.span {p}) k Bp υ v
      let Re := (R*D)*(Ideal.span {p})^k
      let Ke := errorRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve p k
      F.right.modulus = s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {(primeSubsetGenerator (fun P : CommonIndex D C => P.val)
          (swapSubset C D E)*activeConductor D C)} ∧
      (((∀ I : Ideal O, coefficient d Re innerL I = 0) ∧ normalizedGaussSource d Re innerL ballProfile Ke = 0) ∨
      (Ready d Re Ke Z ξ (readyBudget A P) ∧
        (∀ I : Ideal O, coefficient d Re innerL I ≠ 0 →
          lowerFactor N l a * volume d ≤ (I.absNorm : ℝ)))) := by
  filter_upwards [eventually_active_error_ready N b b₁ b₂ 1 hb hb₁ hb₂ (by norm_num),
    eventual_parent_radius N b b₁ b₂ hb hb₁ hb₂,
    eventually_caps 1 (by norm_num)] with Z hready hradius hchars
  refine ⟨hready.1, ?_⟩
  intro ι _ _ s hc he hs hW₁ hW₂ κ hκ hPs hcapacity hη R seed0 hR hRN hseed
    C D hC hD hlabel E ξ₁ ξ₂ F K Csec Tsec σ ξ reserve hK hCsec hσ hσ1
    hξ hξ1 hreserve hsec rows W n hn hblock B t innerL hB M _ H Sbad hbad p hp k _hk
    hslot Bp χ υ v hυ
  dsimp only
  refine ⟨right_modulus s.η C D hC E ξ₁ ξ₂ F, ?_⟩
  let d := errorInput s D R B F.right t (Ideal.span {p}) k Bp υ v
  let Re := (R*D)*(Ideal.span {p})^k
  let Ke := errorRadius D C (swapSubset C D E) K (volume s) Z σ (frequencyLoss Z (32*Csec) ξ) reserve p k
  by_cases hdead : ∀ I : Ideal O, coefficient d Re innerL I = 0
  · exact Or.inl ⟨hdead, normalized_zero d Re innerL hdead ballProfile Ke⟩
  right
  have hlive : ∃ I : Ideal O, (original d Re innerL).beta I ≠ 0 := by
    simpa only [original_beta,not_forall] using hdead
  have hz := hready.1
  have hV := original_volume_cap s Z κ A hz hκ hPs hcapacity
  have hH := hradius.2 s hc he A hV
  have hz₁ := lower_profile_zero s.W₁ a ha hW₁
  have hz₂ := lower_profile_zero s.W₂ a ha hW₂
  have hcdata := actual_common_gates s R seed0 hseed hz₁ hz₂ C D hlabel
  have hCN := hcdata.2.2.2.2.2.1.trans hH
  have hJN : (D.absNorm : ℝ) ≤ Z^(A+1) := by
    exact hcdata.2.2.2.2.2.2.trans hH
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(σ/3)) Q hQ).2) p hp
  have hp0 : p ≠ 0 := hd.1.ne_zero
  have hQ : Ideal.span {p} ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hp0
  have hpupper := (pool_prime_log_range M H Sbad hbad Z σ hz p hp).2
  have hPN : ((Ideal.span {p}).absNorm : ℝ) ≤ Z^(σ/3) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hz.le hpupper
    rwa [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz) (normValue_pos p hp0)] at hh
  have ht := hchars.2 s.η C D hC E ξ₁ ξ₂ F A (A+1) hη hCN
  have hv : (υ.modulus.absNorm : ℝ) ≤ Z^(3*A+3+σ/3) := by
    have hh := ht.2.2 F.right υ (Or.inr rfl) χ p hp0 (errorMovingExponent (k-1)) (σ/3) hυ hPN
    simpa only [show A+2*(A+1)+σ/3+1 = 3*A+3+σ/3 by ring] using hh
  have hE : Ideal.span {primeSubsetGenerator (fun Q : CommonIndex C D => Q.val) E} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hne := first_block_active_rows_nonempty s.η (fixedBadMask*idealGenerator R) 1 s.t
    _ _ C D hC hD E rows W K n hblock
  have hrec := (active_row_reciprocals C D _ hE K (volume s) Z Csec Tsec ξ
    (Real.logb Z (C.absNorm : ℝ))
    (Real.logb Z (D.absNorm : ℝ)) σ reserve
    hK (volume_pos s) hz hCsec hσ hreserve hsec rows n hn hne p k).2
  have hKe : 0 < Ke := by
    dsimp [Ke,errorRadius,errorCommonRadius]
    positivity
  have hKeInv : Ke⁻¹ ≤ Z^(0 : ℝ) := by
    simpa only [Ke,errorRadius,swapSubset_generator,nominal_swap,nominalLog,Real.rpow_zero] using hrec
  have hr := hready.2 s hc he D R innerL B F.right t hR hB _ hQ k hslot Bp υ v Ke
    A 0 P (3*A+3+σ/3) ξ hKe hξ hz₁ hz₂ hV hKeInv hRN hv hlive
  exact ⟨ready_mono _ _ Ke Z ξ _ _ hz.le (error_exponent_le A P σ ξ hA hP hσ1 hξ1) hr,
    error_lower_support N l a hl ha s hc hs hW₁ hW₂ D R innerL B F.right t _ k Bp υ v⟩

end SevenEighths.CenteredMomentEnergyFirstRightAdmission

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalRightSourceColumn -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

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

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open CenteredMomentEnergyAmplifiedChildWidth
open CenteredMomentEnergyCanonicalAmplifiedUniform CenteredMomentEnergyAmplifierFamilyAdmission
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyFirstAnnularAdmission
open CenteredMomentEnergyFirstRawScaleAdmission CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open CenteredMomentEnergyCanonicalAnnularPower CenteredMomentEnergyCanonicalAmplifiedColumn
open CenteredMomentFirstCommonReferencePower CenteredMomentEnergyFirstLowHomogeneousPowers
open CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentEnergyFirstRightAdmission

theorem actual_original_right_low_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤ sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_low_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤ sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤ sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

theorem actual_original_right_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤ sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0< reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤ src.lower → src.upper≤upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤ sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤ src.X₁ → Z^(Mwidth/4)≤ src.X₂ →
    Z^(Mwidth/4)≤ src.Y₁ → Z^(Mwidth/4)≤ src.Y₂ →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=CenteredMomentEnergyCanonicalHighColumn.actual_admitted_subsets_high_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall hbeta hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤ sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤ sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

end SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤Bschedule)(ht:0≤ts)(hem:0≤em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤M)(hA:0≤A)(hB:0≤B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0<sigma ∧ sigma≤1 ∧ 0< r/4 ∧ r/4≤ sigma/4 ∧ r/4≤1 ∧
      0<sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0< maskEpsilon M B ε ∧ 0< mesh M B κ ε ∧
      mesh M B κ ε≤ sigma/12 ∧ 0≤ sigma/12 ∧ sigma/12<sigma/6 ∧
      0<2*sigma+1 ∧ 0≤A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0<sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤ reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(_hP:0≤P)(hB:0≤B)(hready:readyBudget A P≤B)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤ stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤ columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤M)(hB:0≤Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤Bmask):
    readyBudget A P≤CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤ count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end SevenEighths.CenteredMomentEnergyFirstSourceParameters

end

end OAI

end

