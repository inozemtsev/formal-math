module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part007

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / RowCompletion / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.InitialDensity -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SecondPassIntegration hiding O
open InitialMeanSquare hiding O
open CanonicalCubeSeparation
open CanonicalCoefficientClass (IsBaseRayTwist)
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)

theorem hasInitialCanonicalDensityAtRadius_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    HasInitialCanonicalDensityAtRadius χ S hbad := by
  intro deltaLoss hδ P A hA
  let base:=conjugateMonoid (normCharacter χ)
  have hbase : ∀u,‖base u‖≤1:=conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  obtain ⟨d,henergy⟩:=outsideLogEnergy_small_power S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels deltaLoss hδ A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hV₁ hV₂
  have hs₁ : ContDiff ℝ ∞ (orientedLogProfile true V₁):=Complex.conjCLE.contDiff.comp hVs₁
  have hb₁ : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hV₁ s
    intro hz
    exact hs (by simp [orientedLogProfile,hz])
  obtain ⟨C₁,hC₁,he₁⟩:=henergy (orientedLogProfile true V₁) hs₁ hb₁
  obtain ⟨C₂,hC₂,he₂⟩:=henergy (orientedLogProfile false V₂) hVs₂ hV₂
  obtain ⟨A',Vmax,hA',hVmax,hbV₁,hbV₂,hsV₁,hsV₂⟩:=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  let Ccan:=6*(C₁+C₂)*I₀^3
  let Cele:=initialElementaryConstant A' Vmax*I₀^3
  let C:=Ccan+Cele*Z₀^3+1
  have hCcan : 0≤Ccan:=by dsimp only [Ccan];positivity
  have hCele : 0≤Cele:=mul_nonneg (initialElementaryConstant_nonneg A' Vmax) (pow_nonneg hI₀ _)
  have hC : 0<C:=by dsimp only [C];positivity
  have hcanC : Ccan≤C:=by
    have hp : 0≤Cele*Z₀^3:=by positivity
    dsimp only [C]
    linarith
  have heleC : Cele*Z₀^3≤C:=by
    dsimp only [C]
    linarith
  let Cpool:=Real.exp (radiusIter A 3000)
  refine ⟨C,Cpool,max P 3,hC,Real.one_le_exp (radiusIter_nonneg A hA 3000),le_max_left _ _,?_⟩
  intro D Z X lengthScale K R ray T hZ hpool hX hL hK hXP hLP hKP hRP hmass hinv hT hout
  let p:=outsidePrime S D
  let hp:=outsidePrime_ne_zero S hbad D
  let hcop:=outsidePrime_coprime S hbad D
  let hg:=outsidePrime_good S hbad D
  let:=outsidePrime_maximal S hbad D
  let Ψ₁:=secondRayMinus base ray
  let Ψ₂:=secondRayPlus base ray
  let m:=primeSubsetGenerator (fun i=>Ideal.span {p i}) R
  let labels:=T.image Prod.fst
  have hmember : IsBaseRayTwist base base:=Or.inl rfl
  have hη : 0≤ canonicalDescentPadding deltaLoss:=(canonicalDescentPadding_budget deltaLoss hδ).1.le
  have hstate₁ := initialCanonicalState S D hbad base Ψ₁ (hmember.secondMinus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hstate₂ := initialCanonicalState S D hbad base Ψ₂ (hmember.secondPlus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hZδ : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hD : Real.exp (radiusIter A 3000)*Z^3≤D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ (le_max_right P 3)) (Real.exp_pos _).le).trans hpool
  have hlabels : ∀z∈T,z.1∈labels:=fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K:=fun z hz=>(hT z hz).2.2.2
  have hzero : ∀z∈T,z.2≠0:=fun z hz=>(hT z hz).2.2.1
  by_cases hlarge : Z₀≤Z
  · obtain ⟨hZgt,hZbig,hfixed⟩:=hthreshold Z hlarge
    have hleft (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₁ t) m labels (orientedLogProfile true V₁) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₁ D Z Ψ₁ m labels X lengthScale K t hstate₁ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₁ t) m labels
        (orientedLogProfile true V₁) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hright (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₂ t) m labels (orientedLogProfile false V₂) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₂ D Z Ψ₂ m labels X lengthScale K t hstate₂ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₂ t) m labels
        (orientedLogProfile false V₂) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hd:=densityChildEnergy_from_canonical_heights p hp hcop hg Finset.univ Ψ₁ Ψ₂ m T labels
      V₁ V₂ X lengthScale K ((C₁+C₂)*Z^deltaLoss) d (by linarith) (by linarith) (by positivity)
      hlabels hrows hzero hleft hright
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤_ at hd
    have hcan : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Ccan*Z^deltaLoss*(X*lengthScale)^2 := by
      convert hd using 1 ; dsimp only [Ccan,I₀] ; ring
    exact hcan.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcanC (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _))
  · have hKcap : K≤Z₀^3:=hstate₁.row_le_global.trans
      (pow_le_pow_left₀ (by linarith) (le_of_not_ge hlarge) 3)
    have hΨ₁ : ∀u,‖Ψ₁ u‖≤1:=fun u=>(secondRayMinus_norm_le base ray u).trans (hbase u)
    have hΨ₂ : ∀u,‖Ψ₂ u‖≤1:=fun u=>(secondRayPlus_norm_le base ray u).trans (hbase u)
    have hd:=initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X lengthScale K A' Vmax d (by linarith) hL hK hA' hVmax hbV₁ hbV₂ hsV₁ hsV₂
      (fun z hz=>⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩)
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Cele*K*(X*lengthScale)^2 at hd
    apply hd.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hKcap hCele).trans
      (heleC.trans (le_mul_of_one_le_right hC.le hZδ))

end CanonicalRowCompletion

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)

theorem initial_sector_transfer_radius
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀t,g t≠0→U t=1) (hgA : ∀t,g t≠0→|t|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃ (windows : Fin 7→ℝ→ℂ) (C Cₛ : ℝ),0≤C ∧ 0≤Cₛ ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : ActualEisensteinCubic.O→*ℂ) (m r : ActualEisensteinCubic.O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<H → 0<E → 0<V → 0<X → 0<K →
        (∀a,‖Ψ a‖≤1) → (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        ∃ B : Frequency→ℝ,
          (∀q,0≤B q) ∧
          (∀q,(1+H*K/(E^2*V^2*X^2))^N*B q≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S)
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H‖≤
          (C*H*elementNorm r/Z^2*‖secondRayCoefficient ray‖*(K*Real.exp 2)^ε)*
            (∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_sector_fixed_profiles
    U hUc hUs g g W A hA hU hU hgA hgA
  obtain ⟨Cw,hCw,hwbound⟩ := outerWindow_global_bound windows hwc (fun i => (hws i).continuous)
  have hM : 0≤A+2+1 := by linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := initial_source_uniform_transfer ε hε A₁ A₂ W windows
    (fun _ => A+2+1) (fun _ => hM) hwb N J
  refine ⟨windows,Cw*Cₐ,Cₛ,mul_nonneg hCw hCₐ.le,hCₛ,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m r ray s Z H E V X K hZ hH hE hV hX hK hΨ hs hk hz he hv hkap
  let R := H*K/(E^2*V^2*X^2)
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨b,hpoint,hbound⟩ := htrans R hR
  let B : Frequency→ℝ := fun q => ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b q‖
  refine ⟨B,fun q => norm_nonneg _,?_,?_⟩
  · intro q
    simpa only [B,R,tripleCoefficient,mul_assoc] using hpoint q.1 q.2.1 q.2.2
  · let T := s.image (sourceObservation p)
    have hT0 : ∀y∈T,y.1≠0 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact sourceRow_nonzero p x (hk x hx)
    have hTK : ∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K*Real.exp 2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hpos := elementNorm_pos _ (sourceRow_nonzero p x (hk x hx))
      have hl : Real.log (elementNorm (sourceObservation p x).1/K)≤2 :=
        (le_abs_self _).trans (hkap x hx)
      have hh := Real.exp_le_exp.mpr hl
      rw [Real.exp_log (div_pos hpos hK)] at hh
      have hh' := (div_le_iff₀ hK).mp hh
      simpa only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,mul_comm] using hh'
    let D := H*elementNorm r/Z^2*‖secondRayCoefficient ray‖
    have hD : 0≤D := by dsimp [D,elementNorm]; positivity
    have hweights : ∀x∈s,‖sourceWeight p hp hcop hg Ψ m ray Z H x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)‖≤D*Cw := by
      intro x hx
      exact mul_le_mul (sourceWeight_norm_fixed p hp hcop hg hinj hc Ψ m r ray Z H x
        (hs x hx) hZ hH.le (hΨ _) (hΨ _)) (hwbound _ _ _ _ _) (norm_nonneg _) hD
    have hh := hbound p hp hcop hg hinj r s T (sourceWeight p hp hcop hg Ψ m ray Z H) (D*Cw)
      (K*Real.exp 2) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r)
      (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K) X X
      (mul_nonneg hD hCw) (by positivity) hs (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hT0 hTK hweights
    rw [hid p hp hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap]
    convert hh using 1 ; dsimp [D,B,R,T] ; ring

end
section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

theorem initial_subbin_transfer_radius
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset ActualEisensteinCubic.O) (Z H M : ℝ) (j : SecondLogIndex)
        (s : Finset (SecondExpansionData ι)),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        s ⊆ secondLogSector p ∅ F K R Z M j →
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,hwb,ht⟩ :=
    initial_sector_transfer_radius U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j s hZ hH hΨ hsub
  dsimp only
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j (hsub hx))
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp (hsub hx)).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x (hsub hx)).1) (fun x hx => (hcoords x (hsub hx)).2.1)
    (fun x hx => (hcoords x (hsub hx)).2.2.1) (fun x hx => (hcoords x (hsub hx)).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end

section
open ActualEisensteinCubic
open SecondPassArithmetic

theorem initial_source_target_coprime
    {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
    (bad : Ideal ActualEisensteinCubic.O) (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (s : Finset (SecondExpansionData ι)) :
    ∀z∈sourceIdealTarget (s.image (sourceObservation p)),IsCoprime z.1 bad := by
  intro z hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
  change IsCoprime (Ideal.span {(sourceObservation p x).2}) bad
  rw [sourceLabel_span]
  exact (IsCoprime.prod_left (fun i _=>hbad i)).mul_left
    (IsCoprime.prod_left (fun i _=>hbad i))

end

open MeasureTheory
open scoped BigOperators Classical ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem HasInitialCanonicalDensityAtRadius.retained_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) (A : ℝ) (hA : 0≤A) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
        outsideCanonicalDensity χ S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by
  obtain ⟨J,hJ⟩ := hcan η hη 20 A hA
  refine ⟨J,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨Cc,Cpool,E,hCc,hCpool,hPE,hcanonical⟩ := hJ V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hVrad₁ hVrad₂
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z0,hZ0,hthreshold⟩ := initial_large_threshold a b (initialExcludedNorm S) ν
    (initialExcludedNorm_ge_one S) hν
  let Ce := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  let K0 := initialPolynomialCap a b*Z0^17*Real.exp 2
  let C := Cc+Ce*(K0+1)+1
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hcap := initialPolynomialCap_ge_one a b
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCcC : Cc ≤ C := by dsimp [C]; nlinarith
  have hCeC : Ce ≤ C := by dsimp [C]; nlinarith
  have hCeKC : Ce*K0 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,Cpool,E,hC,hCpool,hPE,?_⟩
  intro D Z R ray j T hZ hpool hR hj hrad hT hTc
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let lengthScale := initialLogLabel j
  let Kr := secondLogK j*Real.exp 2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hB := primeProductNorm_ge_one p hp R
  have hBpos := zero_lt_one.trans_le hB
  have hX : 0 < X := initialLogColumn_pos Z _ j hZp hBpos
  have hL : 1 ≤ lengthScale := initialLogLabel_ge_one j
  have hKr : 1 ≤ Kr := one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hZη : 1 ≤ Z^η := Real.one_le_rpow hZ hη.le
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hΨ₁ : ∀ z,‖secondRayMinus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayMinus_norm_le Ψ ray z).trans (hΨ z)
  have hΨ₂ : ∀ z,‖secondRayPlus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayPlus_norm_le Ψ ray z).trans (hΨ z)
  have hTb : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ Kr := by
    intro z hz
    exact ⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩
  have promote (d : ℝ) (hd : d ≤ C)
      (he : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ d*(X*lengthScale)^2) :
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^η*(X*lengthScale)^2 :=
    he.trans (mul_le_mul_of_nonneg_right (hd.trans (le_mul_of_one_le_right hC.le hZη)) (sq_nonneg _))
  by_cases hzlarge : Z0 ≤ Z
  · have hgeom := initial_large_bin_geometry p hp Finset.univ R a b Z σ θ ν (initialExcludedNorm S)
      j hZ (initialExcludedNorm_ge_one S) hR hj hσ hmargin (hthreshold Z hzlarge) hrad
    dsimp only at hgeom
    by_cases hxlarge : 1 ≤ X
    · exact (hcanonical D Z X lengthScale Kr R ray T hZ hpool hxlarge hL hKr
        hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hT hTc).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcC (Real.rpow_nonneg hZp.le _)) (sq_nonneg _))
    · have hKL : Kr ≤ lengthScale := initial_subunit_row_le_label Z X lengthScale Kr
        (initialExcludedNorm S*primeProductNorm p R) ((1 : ℝ)/20) hZ (le_of_not_ge hxlarge)
        (zero_le_one.trans hL) (zero_le_one.trans hKr)
        (one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hB)
        (by norm_num) (by simpa only [Kr,X,lengthScale,neg_div] using hgeom.2.2.2.2.2)
      apply promote Ce hCeC
      exact initial_subunit_density_bound p hp hcop hg (outsidePrime_odd S hbad D)
        (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hKL hA hVmax hV₁ hV₂ hs₁ hs₂ hTb
  · have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
    have hkr : Kr ≤ K0 := by
      have hbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
        (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
      have hcapZ := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
      have hpow : Z^17 ≤ Z0^17 := pow_le_pow_left₀ hZp.le (le_of_not_ge hzlarge) 17
      calc
        Kr ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
          mul_le_mul_of_nonneg_right (hbin.trans hcapZ) (Real.exp_pos _).le
        _ ≤ K0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hcap)) (Real.exp_pos _).le
    apply promote (Ce*Kr) ((mul_le_mul_of_nonneg_left hkr hCe).trans hCeKC)
    exact initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hA hVmax hV₁ hV₂ hs₁ hs₂ hTb

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.retained_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ θ ν η : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hcop := outsidePrime_coprime S hbad D
      let hg := outsidePrime_good S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z (initialErrorWindow a b) j))
            G G W H‖ else 0) ≤ C*H*Z^(35*η) := by
  obtain ⟨J,hJ⟩ := HasInitialCanonicalDensityAtRadius.retained_density χ S hbad hcan a b σ θ ν η hσ hν hη hmargin
    (initialErrorWindow a b+2+1) (by unfold initialErrorWindow; positivity)
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,hwb,ht⟩ :=
    initial_subbin_transfer_radius U hUc hUs g W (initialErrorWindow a b) hM hU hgs η hη 0 (2*J)
  obtain ⟨Ce,Cpool,E,hCe,hCpool,hPE,henergy⟩ := hJ (windows 5) (windows 6) (hwc 5) (hwc 6) (hws 5) (hws 6) (hwb 5) (hwb 6)
  obtain ⟨Cl,hCl,hlog⟩ := initial_row_log_budget η (initialPolynomialCap a b) hη (initialPolynomialCap_ge_one a b)
  let C0 := Ct*Real.exp 4*Ce*Cs*initialRayMass*Cl
  have hray := initialRayMass_nonneg
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1,Cpool,E,by linarith,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hKmax : 1 ≤ Kmax := initialErrorRowBound_ge_one a b Z H hZ hH
  let B : SecondRayIndex → Finset (OutsidePrimeIndex S D) → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  let d := H*Real.exp 4*(Ce*Z^η)*Cs*(Kmax*Real.exp 2)^η
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
      (hR : R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M))
      (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
      (hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ) :
      initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j) ≤
        d/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
    have hT := initial_squarefree_target_geometry p hp hg (outsidePrime_odd S hbad D)
      Finset.univ R K Z M j
    have hTe : ∀ z ∈ sourceIdealTarget ((s R j).image (sourceObservation p)),
        Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧ z.2 ≠ 0 ∧
        ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
      intro z hz
      exact ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩
    have hTc := initial_source_target_coprime p (∏P∈S,P)
      (CanonicalRowCompletion.outside_pool_coprime_excluded S D hbad hSp) (s R j)
    have he := henergy D Z R ray j _ hZ hpool hR hj hlow hTe hTc
    have he' :
        densityChildEnergy p hp hcop hg Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (1*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (sourceIdealTarget ((s R j).image (sourceObservation p)))
          (windows 5) (windows 6) (initialLogColumn Z (primeProductNorm p R) j)
          (initialLogColumn Z (primeProductNorm p R) j) (2*J) ≤
          (Ce*Z^η)*(initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j)^2 := by
      simpa only [outsideCanonicalDensity,one_mul] using he
    exact initial_bin_cost_uniform p hp hcop hg Finset.univ R Ψ 1 ray K Z H M Kmax η Cs
      (Ce*Z^η) hZp hHp hKmax hη.le hCs (by positivity) j hj windows (B ray R j) (2*J) 0
      (hB ray R j).1 (hB ray R j).2.1 he'
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖ else 0) ≤
      Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (initial_harmonic_aggregation p (outsidePrime_injective S hbad D) Finset.univ
        (Z*Real.exp M) Kmax d hd
        (fun ray R j => if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j)
          else 0) (by
          intro ray R hR j hj
          split_ifs with hlow
          · exact hterm ray R hR j hj hlow
          · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
            positivity)) hCt)
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hlow
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialSquarefreeBinCost,s,G,B] ; ring
    · simp
  have hlogBound := hlog Z (Z*Real.exp M) Kmax hZ (by positivity) (zero_lt_one.trans_le hKmax)
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
  calc
    _ ≤ Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := hsum
    _ = (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*
        ((Kmax*Real.exp 2)^η*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by dsimp [d]; ring
    _ ≤ (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*(Cl*Z^(34*η)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = C0*H*Z^(35*η) := by
      rw [show 35*η=η+34*η by ring,Real.rpow_add hZp]
      dsimp [C0]
      ring
    _ ≤ (C0+1)*H*Z^(35*η) := by
      gcongr
      linarith

end InitialMeanSquare

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.ThetaDensity -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem HasInitialCanonicalDensityAtRadius.nonzero_source_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hg := outsidePrime_good S hbad D
      let hinj := outsidePrime_injective S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
        W H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ C*H*Z^ε := by
  let η := min 1 (ε/100)
  let ν := (σ-(1 : ℝ)/20)/3
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 35*η ≤ ε := by
    have hh : η ≤ ε/100 := min_le_right _ _
    linarith
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hmargin : ν+ν ≤ σ-(1 : ℝ)/20 := by dsimp [ν]; linarith
  obtain ⟨Cl,Cpool,E,hCl,hCpool,hPE,hlow⟩ := HasInitialCanonicalDensityAtRadius.retained_source χ S hbad hSp hcan U hUc hUs g W
    a b σ ν ν η hU hgs hσ0 hν hη hmargin
  obtain ⟨Ch,hCh,hhigh⟩ := initial_high_radial_source U hUc hUs g W a b ν 1 η hU hgs hν hη hη1
  refine ⟨Cl+Ch,Cpool,E,by positivity,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let hinj := outsidePrime_injective S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  let f := fun (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖
  let Lsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if initialRadial Z H (primeProductNorm p R) j ≤ Z^ν then f ray R j else 0
  let Hsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if Z^ν < initialRadial Z H (primeProductNorm p R) j then f ray R j else 0
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hL : Lsum ≤ Cl*H*Z^(35*η) := hlow D Z hZ hpool
  have hHi : Hsum ≤ Ch*Z^(-(1 : ℝ)) :=
    hhigh p hp hcop hg hinj (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D)
      Finset.univ Ψ 1 Z H hZ hH hΨ (fun _ R j => s R j) (fun _ _ _ => Finset.filter_subset _ _)
  have hrow : ∀ R ∈ (Finset.univ : Finset (OutsidePrimeIndex S D)).powerset,
      ∀ x ∈ secondSupportedSector p Finset.univ K R Z M,elementNorm (sourceObservation p x).1 ≤ Kmax := by
    intro R hR x hx
    exact initialErrorRowBound_valid p hp Finset.univ R a b Z H hZp hHp x hx
  have htotal := initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj
    (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D) Finset.univ Ψ 1 g W
    Z H M Kmax hZp hgs K hrow
  have hpart : (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j)=Lsum+Hsum := by
    dsimp only [Lsum,Hsum]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : initialRadial Z H (primeProductNorm p R) j ≤ Z^ν
    · rw [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · rw [ite_eq_right hh,ite_eq_left (lt_of_not_ge hh),zero_add]
  have hpower : Z^(35*η) ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hsmall : Z^(-(1 : ℝ)) ≤ H*Z^ε := by
    have h1 : Z^(-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)
    exact h1.trans (one_le_mul_of_one_le_of_one_le hH (Real.one_le_rpow hZ hε.le))
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j := htotal
    _ = Lsum+Hsum := hpart
    _ ≤ Cl*H*Z^(35*η)+Ch*Z^(-(1 : ℝ)) := add_le_add hL hHi
    _ ≤ Cl*H*Z^ε+Ch*(H*Z^ε) := add_le_add
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hCl.le hHp.le))
      (mul_le_mul_of_nonneg_left hsmall hCh.le)
    _ = (Cl+Ch)*H*Z^ε := by ring

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_of_canonical_density_at_radius {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : HasInitialCanonicalDensityAtRadius χ S hbad)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset ActualEisensteinCubic.O,
      (∀ z ∈ T,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T,z ≠ 0) →
      (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2) ≤ C*Z*(Z^(1+σ))*Z^ε := by
  let g0 := initialLogProfile W a b ha hs hW
  let g := conjugateProfile g0
  let M := initialErrorWindow a b
  have hM : 0 ≤ M := by dsimp [M,initialErrorWindow]; positivity
  have hg0 : ∀ t,g0 t ≠ 0 → |t| ≤ M := initialLogProfile_support W a b ha hs hW
  have hg : ∀ t,g t ≠ 0 → |t| ≤ M := conjugateProfile_support_bound g0 M hg0
  obtain ⟨U,hUc,hUs,hUeq,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  have hU : ∀ t,g t ≠ 0 → U t=1 := fun t ht => hUeq t (hg t ht)
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := HasInitialCanonicalDensityAtRadius.nonzero_source_bound χ S hbad hSp hcan
    U hUc hUs g rowMajorant a b σ ε hU hg hσ hε
  obtain ⟨Ce,hCe,herrors⟩ := outside_mean_square_source_with_errors W a b ha hs hW
  refine ⟨Cs+Ce,by positivity,?_⟩
  intro D Z hZ hD T hT hT0
  let Db : ℕ := max D ⌈Cpool*Z^E⌉₊
  have hDDb : D ≤ Db := le_max_left _ _
  have hpool : Cpool*Z^E ≤ (Db : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right D ⌈Cpool*Z^E⌉₊)
  have hDb : b*Z ≤ (Db : ℝ) := hD.trans (by exact_mod_cast hDDb)
  let p := outsidePrime S Db
  let hp := outsidePrime_ne_zero S hbad Db
  let hg := outsidePrime_good S hbad Db
  let hinj := outsidePrime_injective S hbad Db
  let := outsidePrime_maximal S hbad Db
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let G := fun V => normalizedColumn p (fun T => g0 (columnLog p Z T)) V
  let MS := ∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S Db) (outsideIdealsUpTo_ne_bot S Db)
    (outside_good S Db hbad) χ (fun n => W (n/Z)) z‖^2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hεZ : 1 ≤ Z^ε := Real.one_le_rpow hZ hε.le
  have he := herrors χ S Db hbad hSp Z H hZp hHp hDb T hT hT0
  have hsrc := hsource Db Z hZ hpool
  have hstar : (fun V => star (G V)) =
      (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) := by
    funext V
    exact star_normalizedColumn p g0 Z V
  have hsrc' :
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ Cs*H*Z^ε := by
    rw [hstar]
    exact hsrc
  change MS/Z ≤
    ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
      rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖+Ce*H-‖G ∅‖^2 at he
  have herr : Ce*H ≤ Ce*H*Z^ε := le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεZ
  have hnorm : MS/Z ≤ (Cs+Ce)*H*Z^ε := by
    nlinarith [sq_nonneg ‖G ∅‖]
  have hfinal := (div_le_iff₀ hZp).mp hnorm
  have hMS : (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)=MS := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [outside_row_cutoff_stable S hbad hDDb χ W b Z hZp (fun t ht => (hs ht).2) hD z]
  rw [hMS]
  convert hfinal using 1 ; dsimp only [H] ; ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion

theorem outside_mean_square_of_theta_models {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1:ℝ)/20<σ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ∀T : Finset ActualEisensteinCubic.O,
      (∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^(1+σ)) →
      (∀z∈T,z≠0) →
      (∑z∈T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n=>W (n/Z)) z‖^2)≤C*Z*(Z^(1+σ))*Z^ε :=
  outside_mean_square_of_canonical_density_at_radius χ S hbad hSp
    (hasInitialCanonicalDensityAtRadius_of_theta χ S hSp hbad ρ q levelBound hρ hq hlevel hmodels)
    W a b ha hs hW σ ε hσ hε

end InitialMeanSquare

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

lemma cuspBarrierField_local_model (p : SpatialCoordinates) (hp : 0<p 2) :
    (cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun _ => 1)) ∨
    ∃x : FullCuspClasses,1< rowHeight (fullCuspRow x) p ∧
      cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun q => 1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)) := by
  by_cases hx : ∃x : FullCuspClasses,1< rowHeight (fullCuspRow x) p
  · obtain ⟨x,hx⟩ := hx
    refine Or.inr ⟨x,hx,?_⟩
    have hc := (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt
    filter_upwards [hc.eventually_const_lt hx,(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq hpos
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=_
    rw [fullCuspProfileField_eq _ q hpos,fullCuspProfileSum_eq_single _
      (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) _ x
        (by rwa [←fullCuspRow_height x q hpos]),←fullCuspRow_height x q hpos]
  · left
    obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
    have hsmall : ∀ᶠq in 𝓝 p,∀x∈T,rowHeight (fullCuspRow x) q<2 := by
      rw [eventually_all_finset]
      intro x hxT
      apply (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt.eventually_lt_const
      have hn : rowHeight (fullCuspRow x) p≤1 := not_lt.mp (fun h => hx ⟨x,h⟩)
      linarith
    filter_upwards [hT,hsmall] with q hq hqT
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=1
    have hz : ∀x : FullCuspClasses,cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)=0 := by
      intro x
      apply cuspBarrierProfile_zero 2 3 (by norm_num)
      by_cases hmem : x∈T
      · exact (hqT x hmem).le
      · exact (hq x hmem).le.trans (by norm_num)
    simp only [fullCuspProfileField,hz,tsum_zero,add_zero]

lemma cuspBarrierProfile_log_derivative_bound :
    ∃D : ℝ,0≤D ∧ ∀v : ℝ,1<v→
      |v*deriv (cuspBarrierProfile 2 3) v|≤D*(1+cuspBarrierProfile 2 3 v) := by
  have hd := (contDiff_infty_iff_deriv.mp (cuspBarrierProfile_smooth 2 3)).2.continuous
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 3)).image hd.abs).bddAbove
  let D := max 1 (3*max C 0)
  have hD : 0≤D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨D,hD,fun v hv => ?_⟩
  by_cases hhigh : 3<v
  · have he : cuspBarrierProfile 2 3 =ᶠ[𝓝 v] (fun x => x-1) := by
      filter_upwards [Ioi_mem_nhds hhigh] with x hx
      rw [cuspBarrierProfile,cuspTransition_one 2 3 x (by norm_num) hx.le,one_mul]
    have hder : deriv (cuspBarrierProfile 2 3) v=1 := by rw [he.deriv_eq]; simp
    rw [hder,mul_one,abs_of_pos (by linarith),he.self_of_nhds]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 (3*max C 0)) (show 0≤v by linarith)
    dsimp only [D]
    nlinarith
  · have hCv : |deriv (cuspBarrierProfile 2 3) v|≤ max C 0 :=
      (hC (Set.mem_image_of_mem _ (show v∈Set.Icc (1:ℝ) 3 from ⟨hv.le,not_lt.mp hhigh⟩))).trans (le_max_left _ _)
    have h1 : |v*deriv (cuspBarrierProfile 2 3) v|≤3*max C 0 := by
      rw [abs_mul,abs_of_pos (by linarith)]
      exact mul_le_mul (not_lt.mp hhigh) hCv (abs_nonneg _) (by positivity)
    have hphi := cuspBarrierProfile_nonneg 2 3 (by norm_num) (by norm_num) v
    exact (h1.trans (le_max_right _ _)).trans (by nlinarith)

lemma cuspBarrierField_scaled_deriv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j) (p j)‖≤
        D*cuspBarrierField 2 3 p := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierProfile_log_derivative_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [Function.update_eq_self] using ((continuous_axis_update p j).continuousAt (x := p j)).tendsto
  rcases cuspBarrierField_local_model p hp with hz | ⟨x,hx,he⟩
  · have hzCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p] (fun _ => (1:ℂ)) :=
      hz.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have hzC := hzCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)] (fun _ => (1:ℂ)) at hzC
    rw [hzC.deriv_eq,deriv_const,mul_zero,norm_zero,hz.self_of_nhds,mul_one]
    exact hD
  · have heCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p]
        (fun q => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℝ):ℂ)) :=
      he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have heC := heCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)]
      (fun t => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) (Function.update p j t)):ℝ):ℂ)) at heC
    rw [heC.deriv_eq]
    simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [deriv_const_add]
    have hpF := (rowProfile_axis_derivatives (fun v => (cuspBarrierProfile 2 3 v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspBarrierProfile_smooth 2 3).contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) p hp j).1
    change ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℂ)) p j) (p j)‖≤_
    rw [hpF.deriv,cast_profile_deriv _ ((cuspBarrierProfile_smooth 2 3).differentiable (by simp))]
    have hid : (p 2:ℂ)*(((deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ)*
        (rowHeight (fullCuspRow x) p:ℂ)*(rowLogD (fullCuspRow x) p j:ℂ))=
        ((p 2*rowLogD (fullCuspRow x) p j:ℝ):ℂ)*
        ((rowHeight (fullCuspRow x) p*deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ) := by
      push_cast
      ring
    rw [hid,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (abs_nonneg _) (rowLogD_hyperbolic_bound _ (fullCuspRow_ne_zero x) p hp j)).trans
    rw [he.self_of_nhds]
    exact hbound _ hx

lemma kernelBarrier_scaled_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierField_scaled_deriv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  let f : EuclideanSpatial→ℂ := fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)
  have hf : ∀q,0<q 2→ ContDiffAt ℝ ∞ f q := fun q hq =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) q hq)
  have he : ∀q : SpatialCoordinates,0<q 2→ f (WithLp.toLp 2 q)=(cuspBarrierField 2 3 q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq 2 3 (WithLp.toLp 2 q) hq)
  have ha := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤_
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,ha.deriv_eq]
  change _≤D*cuspBarrier 2 3 (euclideanToHyperbolic p)
  rw [cuspBarrier_euclidean_eq 2 3 p hp]
  exact hbound p.ofLp hp j

lemma kernelBarrier_scaled_real_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      |p 2*fderiv ℝ (fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)) p
        (euclideanCoordinateVector j)|≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := kernelBarrier_scaled_fderiv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have hphi := (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have he := (Complex.ofRealCLM.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  have hh := hbound p hp j
  change ‖(p 2:ℂ)*fderiv ℝ (Complex.ofRealCLM ∘ (fun q => cuspBarrier 2 3 (euclideanToHyperbolic q))) p
      (euclideanCoordinateVector j)‖≤_ at hh
  rw [he] at hh
  simpa only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,←Complex.ofReal_mul,
    Complex.norm_real,Real.norm_eq_abs] using! hh

lemma kernelExhaustionProfile_euler_bounded :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀v : ℝ,|v*deriv (kernelExhaustionProfile n) v|≤C := by
  obtain ⟨C,hC,hbound⟩ := cuspTransition_euler_bounded 1 2 (by norm_num)
  refine ⟨C,hC,fun n v => ?_⟩
  let c : ℝ := (n:ℝ)+1
  have hc : c≠0 := by dsimp [c]; positivity
  have hd := (hasDerivAt_const v (1:ℝ)).sub
    (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/c)).hasDerivAt.comp v
      ((hasDerivAt_id v).div_const c))
  change HasDerivAt (kernelExhaustionProfile n) (0-deriv (cuspTransition 1 2) (v/c)*(1/c)) v at hd
  rw [hd.deriv]
  have he : v*(0-deriv (cuspTransition 1 2) (v/c)*(1/c))= -(v/c*deriv (cuspTransition 1 2) (v/c)) := by ring
  rw [he,abs_neg]
  exact hbound (v/c)

lemma kernelExhaustionCutoff_scaled_fderiv_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤C := by
  obtain ⟨D,hD,hgrad⟩ := kernelBarrier_scaled_real_fderiv_bound
  obtain ⟨B,hB,hprofile⟩ := kernelExhaustionProfile_euler_bounded
  refine ⟨D*B,mul_nonneg hD hB,fun n p hp j => ?_⟩
  let phi : EuclideanSpatial→ℝ := fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)
  have hphi : DifferentiableAt ℝ phi p :=
    (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have hP := ((kernelExhaustionProfile_smooth n).differentiable (by simp) (phi p)).hasDerivAt
  have hd := (hP.ofReal_comp.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  change ‖(p 2:ℂ)*fderiv ℝ ((fun v => (kernelExhaustionProfile n v:ℂ)) ∘ phi) p
    (euclideanCoordinateVector j)‖≤D*B
  rw [hd]
  change ‖(p 2:ℂ)*((fderiv ℝ phi p (euclideanCoordinateVector j):ℝ) •
    ((deriv (kernelExhaustionProfile n) (phi p):ℝ):ℂ))‖≤D*B
  rw [Complex.real_smul,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    |p 2*(fderiv ℝ phi p (euclideanCoordinateVector j)*deriv (kernelExhaustionProfile n) (phi p))|
      = |p 2*fderiv ℝ phi p (euclideanCoordinateVector j)| *|deriv (kernelExhaustionProfile n) (phi p)| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (D*phi p)*|deriv (kernelExhaustionProfile n) (phi p)| :=
      mul_le_mul_of_nonneg_right (hgrad p hp j) (abs_nonneg _)
    _ = D*|phi p*deriv (kernelExhaustionProfile n) (phi p)| := by
      rw [abs_mul,abs_of_nonneg (le_trans zero_le_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) _))]
      ring
    _ ≤ D*B := mul_le_mul_of_nonneg_left (hprofile n (phi p)) hD

lemma kernelExhaustionCutoff_fderiv_eventually_zero (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,
      fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p=0 := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  have he := hn.comp_tendsto hc
  have heC : (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) =ᶠ[𝓝 p]
      (fun _ => (1:ℂ)) := he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
  rw [heC.fderiv_eq]
  simp

lemma kernelExhaustionCutoff_energy_density_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→
      (∑j : Fin 3,‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖^2)≤C := by
  obtain ⟨D,hD,hbound⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*D^2,by positivity,fun n p hp => ?_⟩
  calc
    _ ≤ ∑j : Fin 3,D^2 := Finset.sum_le_sum (fun j hj =>
      (sq_le_sq₀ (norm_nonneg _) hD).mpr (hbound n p hp j))
    _ = 3*D^2 := by simp

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SixthPowerAverage
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def totientDensity (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  ∏ P ∈ primeSupport I, (1-(1:ℂ)/(Ideal.absNorm P:ℂ))

theorem idealSupport_card (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (idealSupport F I).card=(primeSupport I).card := by
  rw [primeSupport,←idealSupport_image_eq_factors F hI]
  exact (Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.val_injective h)).symm

theorem idealSupport_density (F : Finset (Ideal ActualEisensteinCubic.O)) {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) :
    (∏ i ∈ idealSupport F I, (1-(1:ℂ)/(Ideal.absNorm i.val:ℂ)))=totientDensity I := by
  rw [totientDensity, primeSupport, ←idealSupport_image_eq_factors F hI,
    Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

theorem idealSexticRow_sixth_mask
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=
      rowCoprimeMask (fun i : primePool F => i.val) (idealSupport F I) b := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  exact finiteSquarefreeRow_sixth_power _ _ _ _

theorem idealSexticRow_sixth_radial_summable
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (I : Ideal ActualEisensteinCubic.O) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Summable (fun b : ActualEisensteinCubic.O => idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
  have hs : Summable (fun b : ActualEisensteinCubic.O => V (‖eisEmbedding b‖^2/Y)) := by
    simpa only [scaledRadialTest_apply] using
      (actual_eisenstein_summable_norm (scaledRadialTest V Y hY)).of_norm
  simp_rw [idealSexticRow_sixth_mask]
  convert hs.indicator {b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} using 1
  funext b
  by_cases hb : ∃i∈idealSupport F I,b∈i.val
  · rw [Set.indicator_of_notMem (show b∉{b : ActualEisensteinCubic.O | ¬∃i∈idealSupport F I,b∈i.val} from fun hn=>hn hb)]
    simp only [rowCoprimeMask,ite_eq_left hb,zero_mul]
  · rw [Set.indicator_of_mem hb]
    simp only [rowCoprimeMask,ite_eq_right hb,one_mul]

theorem idealSexticRow_sixth_average
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      (Y:ℂ)*paperRadialFourier V 0*totientDensity I+
      maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  simp_rw [idealSexticRow_sixth_mask]
  rw [masked_principal_radial_poisson_zero_split _ Subtype.val_injective _ V Y hY,
    idealSupport_density F hI]

theorem idealRowSum_sixth_average {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    (∑'b : ActualEisensteinCubic.O, V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))=
      (Y:ℂ)*paperRadialFourier V 0*
        (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I)+
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y := by
  have he (b : ActualEisensteinCubic.O) : V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)=
      ∑I∈F,(baseChangeWeight χ I*W (Ideal.absNorm I))*
        (idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y)) := by
    rw [idealRowSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun I _ =>
    (idealSexticRow_sixth_radial_summable F hF hg I V Y hY).mul_left _)]
  simp_rw [tsum_mul_left]
  rw [show (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      ∑'b : ActualEisensteinCubic.O,idealSexticRow F hF hg I (b^6)*V (‖eisEmbedding b‖^2/Y))=
      ∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        ((Y:ℂ)*paperRadialFourier V 0*totientDensity I+
          maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y) by
    apply Finset.sum_congr rfl
    intro I hI
    rw [idealSexticRow_sixth_average F hF hg hI V Y hY]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem sixth_average_remainder_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F => i.val) (idealSupport F I) V Y‖≤
      ∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
  let : ∀i : primePool F,(i.val).IsMaximal := primePool_maximal F hF
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  have hr := maskedPrincipalRemainder_uniform (fun i : primePool F=>i.val)
    (idealSupport F I) V Y hY
  rw [idealSupport_card F hI] at hr
  rw [norm_mul,norm_mul]
  calc
    _≤(1*‖W (Ideal.absNorm I)‖)*((2:ℝ)^(primeSupport I).card*pvControl V) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (baseChangeWeight_norm_le_one χ I) (norm_nonneg _))
        hr (norm_nonneg _) (by positivity)
    _=_ := by ring

theorem sixth_power_fiber_card (s : Finset ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) :
    (s.filter (fun b=>b^6=z)).card≤6 := by
  calc
    _≤(Polynomial.nthRoots 6 z).toFinset.card := by
      apply Finset.card_le_card
      intro b hb
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_nthRoots (by norm_num : 0<6)).mpr (Finset.mem_filter.mp hb).2)
    _≤(Polynomial.nthRoots 6 z).card := Multiset.toFinset_card_le _
    _≤6 := Polynomial.card_nthRoots 6 z

theorem sixth_power_average_cauchy (s : Finset ActualEisensteinCubic.O) (V A : ActualEisensteinCubic.O→ℂ)
    (hV : ∀b∈s,‖V b‖≤1) :
    ‖∑b∈s,V b*A (b^6)‖^2≤
      6*s.card*∑z∈s.image (fun b=>b^6),‖A z‖^2 := by
  have hc := DescentWeightedCauchy.weighted_cauchy_sq s V (fun b=>A (b^6)) (fun _=>1)
  simp only [star_one,mul_one,norm_one,one_pow,mul_one] at hc
  have hp := DescentWeightedCauchy.weighted_energy_pushforward s (s.image (fun b=>b^6))
    (fun b=>b^6) V A (fun _=>6) (fun b hb=>Finset.mem_image.mpr ⟨b,hb,rfl⟩) (by
      intro z hz
      calc
        _≤∑b∈s with b^6=z,(1:ℝ) := Finset.sum_le_sum (fun b hb=>hV b (Finset.mem_filter.mp hb).1)
        _=(s.filter (fun b=>b^6=z)).card := by simp
        _≤6 := by exact_mod_cast sixth_power_fiber_card s z)
  have hv : (∑b∈s,‖V b‖)≤ s.card := by
    simpa using Finset.sum_le_sum (fun b hb=>hV b hb)
  apply hc.trans
  calc
    _≤(∑z∈s.image (fun b=>b^6),6*‖A z‖^2)*(s.card:ℝ) :=
      mul_le_mul hp hv (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
        (Finset.sum_nonneg (fun _ _=>by positivity))
    _=_ := by rw [←Finset.mul_sum]; ring

end SixthPowerAverage

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Mellin.SixthPowerAverage -/

section

namespace OAI

noncomputable section

namespace SixthPowerAverage

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Metric
open EisensteinSchwartzPoisson

theorem exists_averaging_test :
    ∃V : 𝓢(ℝ,ℂ),
      (∀x,‖V x‖≤1) ∧
      (Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1) ∧
      V 0=0 ∧ paperRadialFourier V 0≠0 := by
  let f : ContDiffBump ((3:ℝ)/4) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let g : ℝ→ℂ := fun x=>(f x:ℂ)
  have hgs : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp f.contDiff
  have hsupport : Function.support g⊆Set.Icc ((1:ℝ)/2) 1 := by
    intro x hx
    have hf : f x≠0 := by simpa only [g,Function.mem_support,ne_eq,Complex.ofReal_eq_zero] using hx
    have hh : |x-(3:ℝ)/4|<1/4 := by
      have hi : x∈Function.support (f:ℝ→ℝ) := hf
      rw [f.support_eq] at hi
      simpa only [Metric.mem_ball,Real.dist_eq,f] using hi
    exact ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  let V : 𝓢(ℝ,ℂ) := hgc.toSchwartzMap hgs
  have hz : V 0=0 := by
    by_contra h
    have hh := (hsupport h).1
    norm_num at hh
  refine ⟨V,?_,hsupport,hz,?_⟩
  · intro x
    change ‖(f x:ℂ)‖≤1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg f.nonneg]
    exact f.le_one
  · rw [paperRadialFourier_zero_eq_halfline]
    have he : (∫x : ℝ in Set.Ioi 0,(V x))=∫x : ℝ,(f x:ℂ) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_contra hn
      have hp := (hsupport hn).1
      simp only [Set.mem_Ioi,not_lt] at hx
      linarith
    rw [he,integral_complex_ofReal]
    apply mul_ne_zero
    · apply div_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
      · exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3))
    · have hfint : Integrable (f:ℝ→ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      have hfpos : 0 < ∫x : ℝ,f x := by
        apply (integral_pos_iff_support_of_nonneg f.nonneg' hfint).mpr
        rw [f.support_eq]
        exact measure_ball_pos volume _ f.rOut_pos
      exact_mod_cast hfpos.ne'

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge

lemma prime_coprime_span_iff (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (b : ActualEisensteinCubic.O) : IsCoprime P (Ideal.span {b}) ↔ b∉P := by
  rw [Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.IsMaximal)).not_le_iff_codisjoint,
    Ideal.span_singleton_le_iff_mem]

lemma squarefree_sixth_row_coprime
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    {I : Ideal ActualEisensteinCubic.O} (hI : I∈F) (hsq : Squarefree I)
    (b : ActualEisensteinCubic.O) :
    idealSexticRow F hF hg I (b^6)=if IsCoprime I (Ideal.span {b}) then 1 else 0 := by
  let : ∀i : primePool F,(i.val).IsMaximal:=primePool_maximal F hF
  have hc : IsCoprime I (Ideal.span {b}) ↔ ¬∃i∈idealSupport F I,b∈i.val := by
    conv_lhs => rw [←idealSupport_product_eq F hI hsq]
    rw [IsCoprime.prod_left_iff]
    simp only [prime_coprime_span_iff,not_exists,not_and]
  rw [idealSexticRow_sixth_mask,hc]
  by_cases hn : ∃i∈idealSupport F I,b∈i.val <;> simp [rowCoprimeMask,hn]

theorem idealRowSum_sixth_eq_coprime_sum {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (b : ActualEisensteinCubic.O) :
    idealRowSum F hF hg χ W (b^6)=
      ∑I∈F with IsCoprime I (Ideal.span {b}),baseChangeWeight χ I*W (Ideal.absNorm I) := by
  rw [idealRowSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · rw [squarefree_sixth_row_coprime F hF hg hI hsq b]
    split_ifs <;> simp
  · rw [ConcretePrimeRowBridge.baseChangeWeight_zero_of_not_squarefree χ I hsq]
    simp

end

section

open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O

def averagingRows (Y : ℝ) : Finset ActualEisensteinCubic.O := rowNormDisk ⌊Y⌋₊

theorem mem_averagingRows {Y : ℝ} {b : ActualEisensteinCubic.O} (hY : 0≤Y) :
    b∈averagingRows Y ↔ b≠0 ∧ ‖eisEmbedding b‖^2≤Y := by
  rw [averagingRows,mem_rowNormDisk]
  have hz : 0<Ideal.absNorm (Ideal.span {b}:Ideal ActualEisensteinCubic.O) ↔ b≠0 := by
    rw [Nat.pos_iff_ne_zero,ne_eq,Ideal.absNorm_eq_zero_iff,Ideal.span_singleton_eq_bot]
  rw [hz,Nat.le_floor_iff hY,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem averagingRows_card (Y : ℝ) (hY : 1≤Y) :
    ((averagingRows Y).card:ℝ)≤128*Y :=
  DescentFiberCost.finite_element_count_real _ Y hY
    (fun b hb=>(mem_averagingRows (by linarith)).mp hb |>.2)

theorem averagingRows_power_norm (Y : ℝ) (hY : 1≤Y)
    {z : ActualEisensteinCubic.O} (hz : z∈(averagingRows Y).image (fun b=>b^6)) :
    z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Y^6 := by
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hz
  have hh:=(mem_averagingRows (by linarith : (0:ℝ)≤Y)).mp hb
  refine ⟨pow_ne_zero _ hh.1,?_⟩
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_pow,norm_pow,
    ←pow_mul,show (6:ℕ)*2=2*6 by omega,pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hh.2 _

theorem average_tsum_eq_finite (V : 𝓢(ℝ,ℂ))
    (hV : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 0<Y) (A : ActualEisensteinCubic.O→ℂ) :
    (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6))=
      ∑b∈averagingRows Y,V (‖eisEmbedding b‖^2/Y)*A (b^6) := by
  apply tsum_eq_sum
  intro b hb
  have hz : V (‖eisEmbedding b‖^2/Y)=0 := by
    by_contra hv
    apply hb
    apply (mem_averagingRows hY.le).mpr
    refine ⟨?_,?_⟩
    · intro he
      simp only [he,map_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0),zero_div,hV0] at hv
      exact hv trivial
    · exact (div_le_one hY).mp (hV hv).2
  rw [hz,zero_mul]

theorem average_tsum_cauchy (V : 𝓢(ℝ,ℂ))
    (hV : ∀x,‖V x‖≤1)
    (hs : Function.support (V:ℝ→ℂ)⊆Set.Icc ((1:ℝ)/2) 1)
    (hV0 : V 0=0) (Y : ℝ) (hY : 1≤Y) (A : ActualEisensteinCubic.O→ℂ) :
    ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*A (b^6)‖^2≤
      768*Y*∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2 := by
  rw [average_tsum_eq_finite V hs hV0 Y (by linarith) A]
  apply (sixth_power_average_cauchy _ _ _ (fun b hb=>hV _)).trans
  have hc:=averagingRows_card Y hY
  nlinarith [Finset.sum_nonneg (s:=(averagingRows Y).image (fun b=>b^6))
    (fun z _=>sq_nonneg ‖A z‖)]

theorem average_remainder_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {q : ℕ}
      (F : Finset (Ideal ActualEisensteinCubic.O)) (_hF : ∀I∈F,I≠⊥)
      (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
      (V : 𝓢(ℝ,ℂ)) (Y lengthScale G : ℝ),0<Y → 1≤lengthScale → 0≤G →
      (∀n,‖W n‖≤G) → (∀I∈F,W (Ideal.absNorm I)≠0→(Ideal.absNorm I:ℝ)≤lengthScale) →
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤
      C*G*pvControl V*lengthScale^(1+ε) := by
  obtain ⟨C,hC,hp⟩:=SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro q F hF χ W V Y lengthScale G hY hL hG hW hnorm
  apply (sixth_average_remainder_bound F hF χ W V Y hY).trans
  let T:=F.filter (fun I=>W (Ideal.absNorm I)≠0)
  have he : (∑I∈F,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V)=
      ∑I∈T,‖W (Ideal.absNorm I)‖*(2:ℝ)^(primeSupport I).card*pvControl V := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I hI hn
    have hz : W (Ideal.absNorm I)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hz,norm_zero,zero_mul]
  have hc : (T.card:ℝ)≤128*lengthScale :=
    DescentFiberCost.finite_ideal_count_real T lengthScale hL
      (fun I hI=>hF I (Finset.mem_filter.mp hI).1)
      (fun I hI=>hnorm I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2)
  rw [he]
  calc
    _≤∑I∈T,G*(C*lengthScale^ε)*pvControl V := by
      apply Finset.sum_le_sum
      intro I hI
      have hh:=Finset.mem_filter.mp hI
      have hb:=(hp I (hF I hh.1)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm I hh.1 hh.2) hε.le) hC.le)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hW _) hb (by positivity) hG) (pvControl_nonneg V)
    _=(T.card:ℝ)*(G*(C*lengthScale^ε)*pvControl V) := by simp
    _≤128*lengthScale*(G*(C*lengthScale^ε)*pvControl V) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (pvControl_nonneg V))
    _=(128*C)*G*pvControl V*lengthScale^(1+ε) := by
      rw [Real.rpow_add (by linarith : (0:ℝ)<lengthScale),Real.rpow_one]
      ring

theorem totient_sum_normalized_bound {q : ℕ}
    (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀I∈F,I≠⊥)
    (hg : ∀I∈F,∀P∈UniqueFactorizationMonoid.normalizedFactors I,goodLambda∉P)
    (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ)
    (V : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y) :
    Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*totientDensity I‖≤
      ‖∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6)‖+
      ‖∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
        maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖ := by
  have he:=idealRowSum_sixth_average F hF hg χ W V Y hY
  have hh:=norm_sub_le (∑'b : ActualEisensteinCubic.O,V (‖eisEmbedding b‖^2/Y)*idealRowSum F hF hg χ W (b^6))
    (∑I∈F,baseChangeWeight χ I*W (Ideal.absNorm I)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y)
  rw [he,add_sub_cancel_right,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY] at hh
  rwa [←he] at hh

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open InitialMeanSquare
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion

theorem outside_totient_moebius_bound {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ‖∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨V,hV,hVs,hV0,hVhat⟩:=exists_averaging_test
  obtain ⟨Cm,hCm,hm⟩:=outside_mean_square_of_theta_models χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ((1:ℝ)/10) (2*ε) (by norm_num) (by positivity)
  simp only [show (1:ℝ)+1/10=11/10 by norm_num] at hm
  obtain ⟨Ce,hCe,he⟩:=average_remainder_small_power ε hε
  have hWc : HasCompactSupport W := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  let Ws : 𝓢(ℝ,ℂ):=hWc.toSchwartzMap hW
  let G : ℝ:=SchwartzMap.seminorm ℝ 0 0 Ws
  let B : ℝ:=max 1 b
  let Err : ℝ:=Ce*G*pvControl V*B^(1+ε)
  let Avg : ℝ:=Real.sqrt (768*Cm)
  let C : ℝ:=(Avg+Err)/‖paperRadialFourier V 0‖
  have hG : 0≤G:=apply_nonneg _ _
  have hB : 1≤B:=le_max_left _ _
  have hErr : 0≤Err:=mul_nonneg (mul_nonneg (mul_nonneg hCe.le hG) (pvControl_nonneg V)) (by positivity)
  have hAvg : 0<Avg:=Real.sqrt_pos.mpr (by positivity)
  have hhat : 0<‖paperRadialFourier V 0‖:=norm_pos_iff.mpr hVhat
  refine ⟨C,div_pos (by linarith) hhat,?_⟩
  intro D Z hZ hD
  have hZp : 0<Z:=by linarith
  let Y : ℝ:=Z^((11:ℝ)/60)
  have hY : 1≤Y:=Real.one_le_rpow hZ (by norm_num)
  have hYp : 0<Y:=by linarith
  let F:=outsideIdealsUpTo S D
  let A : ActualEisensteinCubic.O→ℂ:=idealRowSum F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z))
  have hYpow : Y^6=Z^((11:ℝ)/10) := by
    dsimp only [Y]
    rw [←Real.rpow_mul_natCast hZp.le]
    norm_num
  have hms : (∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2)≤
      Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε) := by
    apply hm D Z hZ hD
    · intro z hz
      have hn:=(averagingRows_power_norm Y hY hz).2
      simpa only [hYpow,show (1:ℝ)+1/10=11/10 by norm_num] using hn
    · intro z hz
      exact (averagingRows_power_norm Y hY hz).1
  have havg2:= (average_tsum_cauchy V hV hVs hV0 Y hY A).trans
    (mul_le_mul_of_nonneg_left hms (by positivity : 0≤768*Y))
  have heq : 768*Y*(Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε))=
      (Avg*Z^((137:ℝ)/120+ε))^2 := by
    dsimp only [Y,Avg]
    rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤768*Cm),←Real.rpow_mul_natCast hZp.le]
    calc
      _ = (768*Cm)*(Z^((11:ℝ)/60)*Z^(1:ℝ)*Z^((11:ℝ)/10)*Z^(2*ε)) := by rw [Real.rpow_one];ring
      _ = (768*Cm)*Z^((11:ℝ)/60+1+11/10+2*ε) := by
        rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
      _ = _ := by congr 2 ; ring
  rw [heq] at havg2
  have havg : ‖∑'z : ActualEisensteinCubic.O,V (‖eisEmbedding z‖^2/Y)*A (z^6)‖≤
      Avg*Z^((137:ℝ)/120+ε) := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havg2
  have herr : ‖∑I∈F,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤Err*Z^(1+ε) := by
    have hbZ : 1≤B*Z:=by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hZ)]
    have hh:=he F (outsideIdealsUpTo_ne_bot S D) χ (fun n=>W (n/Z)) V Y (B*Z) G hYp hbZ hG
      (fun n=>Ws.norm_le_seminorm ℝ (n/Z)) (by
        intro I hI hn
        have hh:=(hs hn).2
        exact ((div_le_iff₀ hZp).mp hh).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hZp.le))
    calc
      _≤Ce*G*pvControl V*(B*Z)^(1+ε):=hh
      _=Err*Z^(1+ε):=by rw [Real.mul_rpow (by linarith : 0≤B) hZp.le];dsimp only [Err];ring
  have hexponent : Z^(1+ε)≤Z^((137:ℝ)/120+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hmain:=totient_sum_normalized_bound F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z)) V Y hYp
  have hbound : Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
      (Avg+Err)*Z^((137:ℝ)/120+ε) := by
    apply hmain.trans
    have := add_le_add havg (herr.trans (mul_le_mul_of_nonneg_left hexponent hErr))
    simpa only [add_mul] using this
  have hzexp : Z^((137:ℝ)/120+ε)=Y*Z^((23:ℝ)/24+ε) := by
    dsimp only [Y]
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (mul_pos hYp hhat)).mp
  apply hbound.trans_eq
  rw [hzexp]
  dsimp only [C]
  field_simp [hhat.ne']

end

section

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open IdealMobiusDivisorSum hiding O
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare

def weightedMoebius {q : ℕ} (χ : DirichletCharacter ℂ q) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  baseChangeWeight χ I*totientDensity I

def outsideWeight {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : Ideal ActualEisensteinCubic.O→ℂ :=
  FiniteSFactor.outsideWeight S (weightedMoebius χ)

def weightedCoeff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : ℕ→ℂ :=
  FiniteSFactor.outsideCoeff S (weightedMoebius χ)

theorem totientDensity_norm_le_one (I : Ideal ActualEisensteinCubic.O) : ‖totientDensity I‖≤1 := by
  rw [totientDensity,norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP
    exact norm_nonneg _
  · intro P hP
    have hN : (2:ℝ)≤Ideal.absNorm P:=by exact_mod_cast IdealDivisorBound.support_norm_two_le hP
    have hNp : (0:ℝ)<Ideal.absNorm P:=by linarith
    have he : (1-(1:ℂ)/(Ideal.absNorm P:ℂ))=((1-1/(Ideal.absNorm P:ℝ):ℝ):ℂ) := by push_cast;rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    · exact sub_le_self _ (by positivity)
    · have hi : (1:ℝ)/(Ideal.absNorm P:ℝ)≤1 := (div_le_one hNp).mpr (by linarith)
      linarith

theorem weightedMoebius_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (I : Ideal ActualEisensteinCubic.O) : ‖weightedMoebius χ I‖≤1 := by
  rw [weightedMoebius,norm_mul]
  exact (mul_le_mul (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ I)
    (totientDensity_norm_le_one I) (norm_nonneg _) zero_le_one).trans_eq (mul_one _)

@[simp] theorem weightedMoebius_zero {q : ℕ} (χ : DirichletCharacter ℂ q) :
    weightedMoebius χ (0:Ideal ActualEisensteinCubic.O)=0 := by
  change ((UniqueFactorizationMonoid.moebius (0:Ideal ActualEisensteinCubic.O):ℂ)*
    χ (Ideal.absNorm (0:Ideal ActualEisensteinCubic.O)))*totientDensity 0=0
  rw [UniqueFactorizationMonoid.moebius_zero,Int.cast_zero,zero_mul,zero_mul]

theorem outsideWeight_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (I : Ideal ActualEisensteinCubic.O) :
    ‖outsideWeight χ S I‖≤1 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_norm_le_one χ I
  · simp

@[simp] theorem outsideWeight_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) :
    outsideWeight χ S (0:Ideal ActualEisensteinCubic.O)=0 := by
  unfold outsideWeight FiniteSFactor.outsideWeight
  split_ifs
  · exact weightedMoebius_zero χ
  · rfl

@[simp] theorem weightedCoeff_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) : weightedCoeff χ S 0=0 := by
  unfold weightedCoeff FiniteSFactor.outsideCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hz:=Ideal.absNorm_eq_zero_iff.mp (FiniteSFactor.mem_fiber.mp hI)
  change outsideWeight χ S I=0
  rw [hz]
  exact outsideWeight_zero χ S

theorem weightedCoeff_norm_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (n : ℕ) : ‖weightedCoeff χ S n‖≤128*n := by
  by_cases hn : n=0
  · subst n
    simp
  have hn1 : (1:ℝ)≤n:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hc:=DescentFiberCost.finite_ideal_count_real (FiniteSFactor.fiber n) n hn1 (by
      intro I hI hz
      have hh:=FiniteSFactor.mem_fiber.mp hI
      rw [hz] at hh
      simp only [Ideal.absNorm_bot] at hh
      exact hn hh.symm) (by
      intro I hI
      exact_mod_cast (FiniteSFactor.mem_fiber.mp hI).le)
  calc
    _≤∑I∈FiniteSFactor.fiber n,‖outsideWeight χ S I‖:=norm_sum_le _ _
    _≤∑I∈FiniteSFactor.fiber n,(1:ℝ):=Finset.sum_le_sum (fun I hI=>outsideWeight_norm_le_one χ S I)
    _=(FiniteSFactor.fiber n).card:=by simp
    _≤128*n:=hc

theorem weightedCoeff_LSeriesSummable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (weightedCoeff χ S) s := by
  apply LSeriesSummable_of_isBigO_rpow hs
  apply Asymptotics.IsBigO.of_bound 128
  filter_upwards [] with n
  simpa only [show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.norm_natCast]
    using weightedCoeff_norm_bound χ S n

theorem weightedCoeff_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (n : ℕ) (hn : n∉Finset.Icc 1 D) : weightedCoeff χ S n*W ((n:ℝ)/Z)=0 := by
    by_cases hn0 : n=0
    · subst n
      simp
    · have hnD : D<n := by simp only [Finset.mem_Icc] at hn;omega
      have hz : W ((n:ℝ)/Z)=0 := by
        by_contra hw
        have hh:=(div_le_iff₀ hZ).mp (hW _ hw)
        have hl : (D:ℝ)<n:=by exact_mod_cast hnD
        linarith
      rw [hz,mul_zero]
  have hh : HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)/Z))
      (∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  have he:=outsideIdealSum_eq_outsideCoeff_sum S D (weightedMoebius χ)
    (fun n=>W ((n:ℝ)/Z))
  change _=(∑n∈Finset.Icc 1 D,weightedCoeff χ S n*W ((n:ℝ)/Z)) at he
  rw [←he] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only [weightedMoebius]
  ring

theorem ideal_weighted_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (b Z : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I) := by
  have ht (I : Ideal ActualEisensteinCubic.O) (hI : I∉outsideIdealsUpTo S D) :
      outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)=0 := by
    by_cases hI0 : I=0
    · rw [hI0,outsideWeight_zero,zero_mul]
    by_cases hg : ∀P∈S,¬P∣I
    · have hz : W ((Ideal.absNorm I:ℝ)/Z)=0 := by
        by_contra hn
        apply hI
        refine mem_outsideIdealsUpTo.mpr ⟨?_,?_,hg⟩
        · exact Nat.one_le_iff_ne_zero.mpr (fun hh=>hI0 (Ideal.absNorm_eq_zero_iff.mp hh))
        · exact_mod_cast ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
      rw [hz,mul_zero]
    · simp [outsideWeight,FiniteSFactor.outsideWeight,hg]
  have hh : HasSum (fun I : Ideal ActualEisensteinCubic.O=>outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z))
      (∑I∈outsideIdealsUpTo S D,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)) :=
    hasSum_sum_of_ne_finset_zero ht
  convert hh using 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [outsideWeight,FiniteSFactor.outsideWeight,ite_eq_left (mem_outsideIdealsUpTo.mp hI).2.2,weightedMoebius]
  ring

end

open scoped BigOperators Classical SchwartzMap ContDiff Topology
open Filter Asymptotics MeasureTheory
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
open InitialMeanSquare CompactMellinBridge

def weightedCompactSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (t : ℝ) : ℂ :=
  ∑'n : ℕ,weightedCoeff χ S n*W ((n:ℝ)*t)

theorem weightedCompactSum_hasSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ)
    (hW : ∀x,2≤x→W x=0) (t : ℝ) (ht : 0<t) :
    HasSum (fun n : ℕ=>weightedCoeff χ S n*W ((n:ℝ)*t)) (weightedCompactSum χ S W t) := by
  obtain ⟨N,hN⟩:=exists_nat_gt (2/t)
  have hz (n : ℕ) (hn : n∉Finset.range N) : weightedCoeff χ S n*W ((n:ℝ)*t)=0 := by
    have hNn : N≤n:=by simpa only [Finset.mem_range,not_lt] using hn
    have htwo : 2≤(n:ℝ)*t := by
      have hh:=(div_lt_iff₀ ht).mp hN
      exact hh.le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hNn) ht.le)
    rw [hW _ htwo,mul_zero]
  exact (summable_of_ne_finset_zero hz).hasSum

theorem weightedCompactSum_inv_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) (D : ℕ) (hD : b*Z≤D) :
    weightedCompactSum χ S W Z⁻¹=
      ∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I := by
  simpa only [weightedCompactSum,div_eq_mul_inv] using
    (weightedCoeff_hasSum χ S W b Z hZ hW D hD).tsum_eq

theorem weightedCompactSum_eq_ideal_tsum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (W : ℝ→ℂ) (Z b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0→x≤b) :
    weightedCompactSum χ S W Z⁻¹=
      ∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z) := by
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZ hW _ hD,
    (ideal_weighted_hasSum χ S W b Z hZ hW _ hD).tsum_eq]

theorem weightedCompactSum_isBigO_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹)=O[atTop]
      (fun Z : ℝ=>Z^((23:ℝ)/24+ε)) := by
  obtain ⟨C,hC,hbound⟩:=outside_totient_moebius_bound χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ε hε
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with Z hZ
  have hZp : 0<Z:=by linarith
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [weightedCompactSum_inv_eq χ S W Z b hZp (fun x hx=>(hs hx).2) _ hD,
    Real.norm_of_nonneg (Real.rpow_nonneg hZp.le _)]
  exact hbound _ Z hZ hD

theorem weightedCompactMellin_analytic_of_theta {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (ε : ℝ) (hε : 0<ε) :
    AnalyticOnNhd ℂ
      (fun s : ℂ=>mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23:ℝ)/24+ε<s.re} := by
  have hf:=weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx))
  have hlocal:=weighted_sum_inv_locallyIntegrableOn_pos (weightedCoeff χ S) W
    (weightedCompactSum χ S W) hW (fun x hx=>hs x (Or.inr hx)) hf
  have hzero:=weighted_sum_zero_near_small_D (weightedCoeff χ S) (weightedCoeff_zero χ S) W
    (weightedCompactSum χ S W) (fun x hx=>hs x (Or.inr hx)) hf
  have hsup : Function.support W⊆Set.Icc (1:ℝ) 2 := by
    intro x hx
    have h1 : 1<x:=by by_contra hh;exact hx (hs x (Or.inl (le_of_not_gt hh)))
    have h2 : x<2:=by by_contra hh;exact hx (hs x (Or.inr (le_of_not_gt hh)))
    exact ⟨h1.le,h2.le⟩
  exact ShortDraftMellin.inverse_mellin_analytic _ _ hlocal
    (weightedCompactSum_isBigO_of_theta χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
      W 1 2 (by norm_num) hsup hW ε hε) hzero

theorem weightedCompactMellin_eq_series {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀) (S : Finset (Ideal ActualEisensteinCubic.O))
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0)
    (s : ℂ) (hRe : 2<s.re) :
    mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s)=
      mellin W s*LSeries (weightedCoeff χ S) s := by
  have hls:=weightedCoeff_LSeriesSummable χ S s hRe
  exact mellin_weighted_sum (weightedCoeff χ S) W (weightedCompactSum χ S W) s
    (weightedCoeff_zero χ S) (weightedCompactSum_hasSum χ S W (fun x hx=>hs x (Or.inr hx)))
    (weighted_term_integrable _ (weightedCoeff_zero χ S) W s (compact_weight_mellin_convergent W hW hs s))
    (weighted_terms_fubini _ (weightedCoeff_zero χ S) W s hls) hls

theorem weightedCompactMellin_analytic {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) :
    AnalyticOnNhd ℂ
      (fun s : ℂ=>mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))
      {s : ℂ | (23:ℝ)/24<s.re} := by
  intro s hsRe
  have he : 0<(s.re-(23:ℝ)/24)/2:=by change (23:ℝ)/24<s.re at hsRe;linarith
  apply weightedCompactMellin_analytic_of_theta χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W hW hs _ he s
  change (23:ℝ)/24+(s.re-23/24)/2<s.re
  change (23:ℝ)/24<s.re at hsRe
  linarith

theorem ideal_totient_moebius_bound {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z →
      ‖∑'I : Ideal ActualEisensteinCubic.O,outsideWeight χ S I*W ((Ideal.absNorm I:ℝ)/Z)‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨C,hC,hbound⟩:=outside_totient_moebius_bound χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ε hε
  refine ⟨C,hC,?_⟩
  intro Z hZ
  have hZp : 0<Z:=by linarith
  have hD : b*Z≤(⌈b*Z⌉₊:ℝ):=Nat.le_ceil _
  rw [(ideal_weighted_hasSum χ S W b Z hZp (fun x hx=>(hs hx).2) _ hD).tsum_eq]
  exact hbound _ Z hZ hD

end SixthPowerAverage

end

end OAI

end

