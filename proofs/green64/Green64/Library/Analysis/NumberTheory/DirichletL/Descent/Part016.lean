module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part013

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailAggregate -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_parent_tail_aggregate_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height : ℝ)(R : Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_rapid Jmax Lcap tau saving hLcap htau
  let N : ℝ := (Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)
  have hN : 0<N := by dsimp [N];positivity
  refine ⟨s,(32*512)*N*C,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  let B := C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving)
  have hsum : (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖)
      ≤N*(2:ℝ)^slots.card*B := by
    calc
      _ ≤ ∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_J∈slots.powerset,B := by
        apply Finset.sum_le_sum
        intro ray hr
        apply Finset.sum_le_sum
        intro core hc₀
        apply Finset.sum_le_sum
        intro J hJ
        exact hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m ray core w slots J lists a
          (Finset.mem_powerset.mp hJ) hslots ha hΨ hw om lo hi hlo hs X M Y Z height R
          hX hhi hZ hY hscale hy hyi hXcap hsource hextra hb₁ hb₂ hactive hcommon hquot hR
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        dsimp [N]
        ring
  apply (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤(32*512)*(2:ℝ)^slots.card)).trans_eq
  have he : ((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card := by
    rw [←pow_mul,pow_mul']
    norm_num
  dsimp [B]
  calc
    _ = (32*512)*N*C*((2:ℝ)^slots.card)^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by ring
    _ = _ := by rw [he]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailPhysical -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseWholePriorityRetainedSource FirstCauchyArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem global_physical_tail_rapid (Jmax : ℕ) (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃(s : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
    ∀{ι σ : Type*}[DecidableEq ι][DecidableEq σ]
      (p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Jo : ℕ),Jo≤Jmax → ∀(extra : CubeCoordinates ι→Finset ι)(pool : Finset ι)
      (source : Finset (Source ι Jo))(negative : Bool)(Ψ : O→*ℂ)(m : O)
      (w : Source ι Jo→ℂ)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) → (∀x∈source,‖w x‖≤1) →
      ∀(om : 𝓢(ℝ,ℂ))(lo hi : ℝ)(hlo : 0<lo)(hs : Function.support om⊆Set.Icc lo hi)
      (X M Y Z height kappa eta : ℝ)(R : Finset ι→Finset ι→ℝ),
      kappa+(9/2:ℝ)*eta≤Lcap →
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
      (∀x∈source,SourceValid p x) → (∀x∈source,extra x.cube⊆x.cube.support) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap) →
      (∀x∈source,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.firstCommon≤Z^Lcap) →
      (∀x∈source,primeProductNorm p x.quotientSupport≤Z^Lcap) →
      (∀x∈source,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      (Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*((32*512)*(2:ℝ)^slots.card*
      (∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
        coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
        priorityTailParent p hg hp hinj extra pool negative
          (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a (principalWindow om lo hi hlo hs negative height) X Y R y‖))≤
      C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving) := by
  obtain ⟨s,C,hC,hbound⟩ := global_parent_tail_aggregate_rapid Jmax Lcap tau (saving+Lcap) hLcap htau
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height kappa eta R hkappa hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hbound p hp hg hinj hcop hc Jo hJo extra pool source negative Ψ m w slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y Z height R hX hhi hZ hY hscale hy hyi hXcap
    hsource hextra hb₁ hb₂ hactive hcommon hquot hR
  have he : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^(kappa+(9/2:ℝ)*eta) := by
    rw [Real.rpow_add hz,Real.rpow_def_of_pos hz ((9/2:ℝ)*eta)]
    congr 2
    ring
  have hP : Z^kappa*Real.exp ((9/2:ℝ)*(eta*Real.log Z))≤Z^Lcap := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ hkappa
  apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans
  calc
    _ ≤ Z^Lcap*(C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
      (SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-(saving+Lcap))) :=
      mul_le_mul_of_nonneg_right hP (by positivity)
    _ = _ := by
      have he₂ : Z^Lcap*Z^(-(saving+Lcap))=Z^(-saving) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = C*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
          (SchwartzMap.seminorm ℝ 0 0 om)^2*(Z^Lcap*Z^(-(saving+Lcap))) := by ring
        _ = _ := by rw [he₂]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityZero -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
def globalPriorityZeroAggregate
    (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a V X Y R (parent p x)‖

theorem global_priority_zero_aggregate (ε:ℝ)(hε:0<ε):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X→hi≤Real.exp M→1≤Y→(∀G E,0≤R G E)→
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative t) X Y R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Y*(X*Real.exp M)^(1+ε)*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=priority_zero_parent_uniform ε hε
  obtain ⟨Cb,hCb,hmass⟩:=global_priority_weighted_branch ε hε
  refine ⟨s,Cb*Cp,mul_pos hCb hCp,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs X M Y t R hX hhi hY hR
  let B:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*
    Y*(X*Real.exp M)^(1+ε)
  have hB:0≤B:=by dsimp [B];positivity
  have hh:=hmass p hp hg hcop original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB
    (fun ray core J x=>‖priorityZeroParent p hg extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y R (parent p x)‖)
    (by intros;positivity)
    (fun ray core J hJ x hx=>hprincipal p hp hg hinj hcop extra pool negative
      (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots J lists a hslots ha
      (fun u=>(firstCoreTwist_norm_le negative _ Ψ core u).trans (hΨ u))
      om lo hi hlo hs X M Y t R hX hhi hY hR (parent p x))
  convert hh using 1 <;> dsimp only [globalPriorityZeroAggregate,B] ; ring
end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityZeroPhysical -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_zero_physical (ε:ℝ)(hε:0<ε)(Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (Jo:ℕ),Jo≤Jmax→∀(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
      (original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)(negative:Bool)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (Z M r ell V delta A B Ractive j t eta tau window pi height:ℝ)(R:Finset ι→Finset ι→ℝ),
      1≤Z→0≤ell+eta→0≤B→0≤j→
      ε*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*ε*(2*ell+B+t+4*eta)≤pi+eta/2→
      (∀x∈original,SourceValid p x)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(B+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(t+eta))→
      (∀x∈original,extra x.cube⊆x.cube.support)→
      hi≤Real.exp window→1≤Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)→(∀G E,0≤R G E)→
      (Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative height) (Z^(r-A-B-t))
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+ε))*
        Z^(r+3*ell+V+17*eta+tau+pi):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=global_priority_zero_aggregate ε hε
  obtain ⟨Cm,hCm,hmass⟩:=original_physical_weighted_source Jmax dsmall hdsmall
  refine ⟨s,Cp*Cm,mul_pos hCp hCm,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs Z M r ell V delta A B Ractive j t eta tau window pi height R
    hZ hell hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot hextra hhi hY hR
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let P:=Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let Q:=Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2
  have hP:0≤P:=by dsimp [P];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have he:=mul_le_mul_of_nonneg_left (hprincipal p hp hg hinj hcop extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs (Z^(r-A-B-t)) window
    (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) height R (by positivity) hhi hY hR) hP
  have hm:=hmass p hp hinj Jo hJo original Z M r ell V delta A B Ractive j t eta tau ε window pi
    hZ hell hε.le hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot extra negative hextra
  have hsupp(x:Source ι Jo):wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x:=by
    simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
  simp_rw [hsupp] at he
  apply he.trans
  calc
    _=Q*(physicalPrincipalFactor Z M r ell V delta A B Ractive j t eta tau ε window*
      ∑x∈original,(primeProductNorm p (principalSupport extra negative x))^(2*ε)):=by
      dsimp [Q,P,physicalPrincipalFactor];ring
    _≤Q*(Cm*Real.exp (window*(1+ε))*Z^(r+3*ell+V+17*eta+tau+pi)):=mul_le_mul_of_nonneg_left hm hQ
    _= _:=by dsimp [Q];ring
end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullBranches -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_slice_full_tail
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖ := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (le_refl _))

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullAggregate -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InverseMomentGlobalPriorityTail
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
def globalPriorityOriginalEnergy (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x)).re

def globalPriorityTailAggregate (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) original negative J lists,
      coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
      priorityTailParent p hg hp hinj extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
        m slots J lists a V X Y R y‖

theorem global_priority_three_branches
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t;
    globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y≤
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityRetainedAggregate p hg hp hcop extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityTailAggregate p hg hp hinj extra pool original w negative Ψ m slots lists a V X Y R:=by
  dsimp only
  unfold globalPriorityOriginalEnergy globalPriorityZeroAggregate globalPriorityRetainedAggregate globalPriorityTailAggregate
  rw [←mul_add,←mul_add]
  simp only [←Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro core hcore
  apply Finset.sum_le_sum
  intro J hJ
  have hb:=global_priority_slice_full_tail p hg hp hcop hinj hc hpr extra pool original w negative Ψ m
    ray core slots J lists a om lo hi hlo hs X t Y hX hY R
  dsimp only at hb
  rw [original_paired_tail p hg hp hinj]
  exact (Complex.re_le_norm _).trans hb
end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredStep -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_filtered_physical_step
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤ cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤ cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_aggregate (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have hz:0<Z:=zero_lt_one.trans hZ
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have hzbound : _ ≤ Cz'*Z^(r+3*ell+V+17*eta+tau+pi):=hzn.trans (by dsimp [Cz'];gcongr)
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add hzbound hrbound) htbound)
end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredStepUniform -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_filtered_physical_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤ cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤ cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    global_priority_filtered_aggregate_uniform_types  om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  obtain ⟨sz,Cz,hCz,hzero⟩:=global_priority_zero_physical εmass hεmass Jmax dsmall hdsmall
  obtain ⟨st,Ct,hCt,htail⟩:=global_physical_tail_rapid Jmax Lcap tau saving hLcap htau
  let Cz':=Cz*(4:ℝ)^K*(sz.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+εmass))
  let Ct':=Ct*(4:ℝ)^K*(st.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2
  refine ⟨C,Cbin,Cz',Ct',hC,hCbin,by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hh:=hdata 1 1 ∅ (Finset.empty_subset _)
  obtain ⟨_,hρ,hL,hZ,hX,hY,heta,hbin,_,_,_,_,_,_,hΨall,_,_,_,_,_,_,_,hYe,hXe,hLe,_,hZ2,_,_,_,_,_,_,_⟩:=hh
  have hz:0<Z:=zero_lt_one.trans hZ
  have haall:∀i∈slots,∀q∈lists i,‖a i q‖≤1:=by
    have hh':=hdata 1 1 slots (Finset.Subset.refl _)
    exact hh'.1
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  have hzn:=hzero p hp hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport Z M r ell V delta Acol Bfirst Ractive j tcount eta tau window pi t cutoff
    hZ.le hell hBfirst hj hcost hvalid hcube₁ hcube₂ hactive hcommon hquotient hextra hhi (by rwa [←hYe]) hrad
  rw [←hXe,←hYe] at hzn
  have hzbound : _ ≤ Cz'*Z^(r+3*ell+V+17*eta+tau+pi):=hzn.trans (by dsimp [Cz'];gcongr)
  have htn:=htail p hp hg hinj hcop hc Jo hJo extra pool original negative Ψ m w slots lists a
    hdisj haall hΨall hw om lo hi hlo hsupport X window Y Z t
    (firstKappa M r ell V delta Acol Bfirst Ractive) eta cutoff hPcap hX hhi hZ.le hY hscale hy hyi hx
    hvalid hextra hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hcutoff
  have htbound : _ ≤ Ct'*Z^(-saving):=htn.trans (by dsimp [Ct'];gcongr)
  have hrbound:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hhib hslots hA hdata
  have hb:=global_priority_three_branches p hg hp hcop hinj hc hpr extra pool original w negative Ψ m slots lists a
    om lo hi hlo hsupport X t Y hX hY cutoff
  have hP:0≤Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)):=by positivity
  have hb':=mul_le_mul_of_nonneg_left hb hP
  simp only [mul_add] at hb'
  exact hb'.trans (add_le_add (add_le_add hzbound hrbound) htbound)
end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.FirstGlobalParents -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def ofOriginal (k : FirstOriginalOuter ι) : Source ι 0 where
  cube := k.1
  firstCommon := k.2.1
  firstDivisor := k.2.2
  quotientSupport := ∅
  oldAssigned := Fin.elim0

def toOriginal (x : Source ι 0) : FirstOriginalOuter ι :=
  ⟨x.cube,⟨x.firstCommon,x.firstDivisor⟩⟩

omit [DecidableEq ι] in
@[simp] theorem toOriginal_ofOriginal (k : FirstOriginalOuter ι) :
    toOriginal (ofOriginal k)=k := by cases k with | mk b k => cases k; rfl

omit [DecidableEq ι] in
@[simp] theorem toOriginal_fill (x : Source ι 0) (D : Finset ι) :
    toOriginal (fillFirstQuotient x D)=toOriginal x := rfl

omit [DecidableEq ι] in
theorem ofOriginal_injective : Function.Injective (ofOriginal (ι:=ι)) :=
  Function.LeftInverse.injective toOriginal_ofOriginal

omit [DecidableEq ι] in
theorem ofOriginal_toOriginal (x : Source ι 0) :
    ofOriginal (toOriginal x)=eraseFirstQuotient x := by
  apply Source.ext <;> try rfl
  exact funext (fun i=>Fin.elim0 i)

omit [DecidableEq ι] in

theorem fill_ofOriginal_injective : Function.Injective
    (fun q : FirstOriginalOuter ι × Finset ι=>fillFirstQuotient (ofOriginal q.1) q.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [toOriginal_fill,toOriginal_ofOriginal] using congrArg toOriginal h
  · exact congrArg Source.quotientSupport h

def originalOuterSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (Source ι 0) :=
  (firstOriginalOuter pool Q).image ofOriginal

theorem originalOuterSource_empty (pool : Finset ι) (Q : Finset (ι→₀ℕ)) :
    ∀x∈originalOuterSource pool Q,x.quotientSupport=∅ := by
  intro x hx
  obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
  rfl

theorem sum_originalOuterSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (H : Source ι 0→A) :
    (∑x∈originalOuterSource pool Q,H x)=∑k∈firstOriginalOuter pool Q,H (ofOriginal k) := by
  exact Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)

def originalSelector (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (x : Source ι 0) (D : Finset ι) : ℂ := selector (toOriginal x) D

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) (D : Finset ι) :
    originalSelector selector (ofOriginal k) D=selector k D := by
  simp only [originalSelector,toOriginal_ofOriginal]

omit [DecidableEq ι] in
@[simp] theorem originalSelector_ofOriginal_fun (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (k : FirstOriginalOuter ι) : originalSelector selector (ofOriginal k)=selector k :=
  funext (originalSelector_ofOriginal selector k)

def originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) : Finset (Source ι 0) :=
  globalParentSource (originalOuterSource pool Q) pool (originalSelector selector)

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i

theorem originalParentSource_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,SourceValid p x := by
  intro x hx
  obtain ⟨k,hk,D,hD,hs,rfl⟩:=(mem_originalParentSource pool Q selector x).mp hx
  exact original_fill_valid p pool Q k hk D

theorem sum_originalParentSource {A : Type*} [AddCommMonoid A]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→A) :
    (∑x∈originalParentSource pool Q selector,H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset.filter (fun D=>selector k D≠0),
        H (fillFirstQuotient (ofOriginal k) D) := by
  rw [originalParentSource,sum_globalParentSource _ _ _ (originalOuterSource_empty pool Q),
    sum_originalOuterSource]
  simp only [originalSelector_ofOriginal]

theorem signed_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,selector (toOriginal x) x.quotientSupport*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        selector k D*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem real_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (H : Source ι 0→ℝ) :
    (∑x∈originalParentSource pool Q selector,‖selector (toOriginal x) x.quotientSupport‖*H x)=
      ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
        ‖selector k D‖*H (fillFirstQuotient (ofOriginal k) D) := by
  rw [sum_originalParentSource]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector k D=0 <;> simp [toOriginal,ofOriginal,fillFirstQuotient,hs]

theorem original_supports (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (k : FirstOriginalOuter ι)
    (hk : k∈firstOriginalOuter pool Q) :
    k.1.leftExponent∈Q ∧ k.1.rightExponent∈Q ∧
      k.1.support⊆pool ∧ k.2.1⊆pool ∧ k.2.2⊆pool := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  have hb' := (mem_reopenedCubeFamily Q k.1).mp hb
  have hs := reopenedCubeFamily_support pool Q hQ k.1 hb
  have hc : k.2.1⊆pool := (Finset.mem_powerset.mp hC).trans Finset.sdiff_subset
  refine ⟨hb'.1,hb'.2.1,hs,hc,?_⟩
  exact (Finset.mem_powerset.mp hE).trans (Finset.union_subset hc
    ((Finset.filter_subset _ _).trans hs))

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem original_principal_extra (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) :
    ∀x∈originalParentSource pool Q selector,
      cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit ⊆ x.cube.support := by
  intro x hx
  exact Finset.filter_subset _ _

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem original_parent_data (k : FirstOriginalOuter ι) (D : Finset ι) :
    (parent p (fillFirstQuotient (ofOriginal k) D)).cube=k.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstCommon=k.2.1 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).firstDivisor=k.2.2 ∧
    (parent p (fillFirstQuotient (ofOriginal k) D)).quotient=sourceIdeal p D :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem original_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈assignedParents p (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (assignedParents p (originalParentSource pool Q selector) negative J lists) expansion) :=
  assigned_family_conditions p hp _ (originalParentSource_valid p pool Q selector)
    negative J lists expansion hE

theorem original_whole_assigned_conditions (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (0+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀y∈wholeAssignedParents p
      (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
        x.cube.leftBit x.cube.rightBit)
      (originalParentSource pool Q selector) negative J lists,
      ∀x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily
      (wholeAssignedParents p
        (fun x=>cubePrincipalSupport x.cube.support x.cube.leftExponent x.cube.rightExponent
          x.cube.leftBit x.cube.rightBit)
        (originalParentSource pool Q selector) negative J lists) expansion) :=
  whole_assigned_family_conditions p hp _ _ (originalParentSource_valid p pool Q selector)
    (original_principal_extra pool Q selector) negative J lists expansion hE

variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_priority_slice
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (ray : RayCharacter×RayCharacter)
    (core : FirstCoreIndex) (H : Source ι 0→ℂ) :
    (∑x∈originalParentSource pool Q selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑k∈firstOriginalOuter pool Q,∑D∈pool.powerset,
      (priorityOuter p hg k.1 negative Ψ m (selector k) ray core D:ℂ)*
        H (fillFirstQuotient (ofOriginal k) D) := by
  have h:=global_original_priority_slice p hg (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) negative Ψ m ray core H
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

theorem original_second_energy_source
    (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (extra : CubeCoordinates ι→Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (om : ℝ→ℂ) (X t Y : ℝ) :
    (∑k∈firstOriginalOuter pool Q,
      firstWholePrioritySecondEnergy p hp hg hinj pool k.1 k.2.1 (extra k.1)
        negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
        slots lists a (selector k) om X t Y)=
    (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,
      ∑J∈slots.powerset,(∑x∈originalParentSource pool Q selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re := by
  have h:=global_second_energy_source p hg hp hinj (originalOuterSource pool Q) pool
    (originalSelector selector) (originalOuterSource_empty pool Q) extra negative Ψ m
    slots lists a om X t Y
  rw [sum_originalOuterSource] at h
  simp only [originalSelector_ofOriginal_fun] at h
  simpa only [originalParentSource,originalSelector,toOriginal,eraseFirstQuotient,ofOriginal] using h

end SevenEighths.InverseFirstGlobalParents

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalCanonicalEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_canonical_to_original_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑x∈outer,firstCanonicalSecondEnergy p hp hg hinj pool x.cube x.firstCommon
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      (fun U=>primeMark slots lists a (extra x.cube∪U)) (selector x) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool (globalParentSource outer pool selector)
      (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun x hx=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool x.cube x.firstCommon (extra x.cube)
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      slots lists a (selector x) om X t Y hY))
  exact le_of_eq (global_second_energy_source p hg hp hinj outer pool selector houter extra
    negative Ψ m slots lists a om X t Y)

theorem original_canonical_to_global_priority
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈firstOriginalOuter pool Q,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalParents.originalParentSource pool Q selector)
      (fun x=>(‖selector (InverseFirstGlobalParents.toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  apply le_trans (Finset.sum_le_sum (fun k hk=>
    first_actual_second_whole_cube_priority p hp hg hinj hc pool k.1 k.2.1 (extra k.1)
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      slots lists a (selector k) om X t Y hY))
  exact le_of_eq (InverseFirstGlobalParents.original_second_energy_source p hg hp hinj pool Q
    selector extra negative Ψ m slots lists a om X t Y)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def outerNorms (p : ι→O) (x : FirstOriginalOuter ι) : Fin 5→ℝ :=
  ![‖eisEmbedding (aLabel p x.1.support x.1.rightBit)‖^2,
    ‖eisEmbedding (aLabel p x.1.support x.1.leftBit)‖^2,
    primeProductNorm p x.2.1,
    ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2,
    primeProductNorm p (cubeActiveSupport x.1.support
      (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)]

def outerGate (p : ι→O) (k : SourceIndex) (x : FirstOriginalOuter ι) : Prop :=
  ∀i : Fin 5,dyadIndex (outerNorms p x i)=k i.castSucc

def outerCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :=
  (firstOriginalOuter pool Q).filter (outerGate p k)

def parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) :=
  (originalParentSource pool Q (fun x=>commonSelector p (selector x) l)).filter
    (fun x=>outerGate p k (toOriginal x))

theorem mem_parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (x : Source ι 0) : x∈parentCell p pool Q selector k l ↔
    ∃o∈outerCell p pool Q k,∃D∈pool.powerset,
      commonSelector p (selector o) l D≠0 ∧ fillFirstQuotient (ofOriginal o) D=x := by
  simp only [parentCell,outerCell,Finset.mem_filter,mem_originalParentSource]
  constructor
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hg⟩
    exact ⟨o,⟨ho,by simpa using hg⟩,D,hD,hs,rfl⟩
  · rintro ⟨o,⟨ho,hg⟩,D,hD,hs,rfl⟩
    exact ⟨⟨o,ho,D,hD,hs,rfl⟩,by simpa using hg⟩

def originalNorms (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) : Fin 6→ℝ :=
  sourceNorms (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2)
    (fun y=>y.2.2) x

lemma originalNorms_outer (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (i : Fin 5) : originalNorms p x i.castSucc=outerNorms p x.1 i := by
  fin_cases i <;> rfl

lemma originalNorms_frequency (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) :
    originalNorms p x 5=‖eisEmbedding x.2.2‖^2 := rfl

theorem sourceCell_outer (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    x.1∈outerCell p pool Q k := by
  obtain ⟨hs,hk⟩:=Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp hs).1,?_⟩
  intro i
  simpa only [sourceIndex,originalNorms_outer] using congrFun hk i.castSucc

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerNorms_ge_one (x : FirstOriginalOuter ι) : ∀i,1≤outerNorms p x i := by
  intro i
  fin_cases i
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · change 1≤‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) :
    ∀i,1≤originalNorms p x i := by
  have hf:=((mem_firstRetainedSource p labels x.1.1 Y x.2).mp (Finset.mem_sigma.mp hx).2).2
  have hn : x.2.2≠0 := (Finset.mem_erase.mp hf).1
  intro i
  fin_cases i
  · exact outerNorms_ge_one p hp x.1 0
  · exact outerNorms_ge_one p hp x.1 1
  · exact outerNorms_ge_one p hp x.1 2
  · exact outerNorms_ge_one p hp x.1 3
  · exact outerNorms_ge_one p hp x.1 4
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceCell_frequency (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    dyadScale (k 5)≤‖eisEmbedding x.2.2‖^2 ∧
      ‖eisEmbedding x.2.2‖^2≤2*dyadScale (k 5) := by
  have h:=sourceCell_ratios (originalNorms p) _ (source_norms_ge_one p hp pool Q labels Y) k x hx 5
  exact ⟨by simpa only [originalNorms_frequency,one_mul] using (le_div_iff₀ (dyadScale_pos _)).mp h.1,
    by simpa only [originalNorms_frequency] using (div_le_iff₀ (dyadScale_pos _)).mp h.2⟩

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerGate_dyads (k : SourceIndex) (x : FirstOriginalOuter ι) (hx : outerGate p k x) :
    ∀i : Fin 5,dyadScale (k i.castSucc)≤outerNorms p x i ∧
      outerNorms p x i≤2*dyadScale (k i.castSucc) := by
  intro i
  have h:=dyadIndex_bounds _ (outerNorms_ge_one p hp x i)
  rw [hx i] at h
  exact ⟨h.1,h.2.le⟩

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma commonSelector_norm (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤‖selector D‖ := by
  unfold commonSelector
  split_ifs <;> simp

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_common_dyads (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι)
    (hlive : commonSelector p selector l D≠0) :
    dyadScale l≤primeProductNorm p D ∧ primeProductNorm p D≤2*dyadScale l := by
  have he : dyadIndex (primeProductNorm p D)=l := by
    by_contra h
    exact hlive (by simp [commonSelector,h])
  have h:=dyadIndex_bounds _ (primeProductNorm_ge_one p hp D)
  rw [he] at h
  exact ⟨h.1,h.2.le⟩

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
lemma sourceIdeal_norm (D : Finset ι) : (Ideal.absNorm (sourceIdeal p D):ℝ)=primeProductNorm p D := by
  simp only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm]

omit [∀i,(Ideal.span {p i}).IsMaximal] in

theorem parentCell_cube_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z ell eta : ℝ)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  exact reopenedCubeFamily_cube_norms p Q _ hQ o.1
    ((mem_firstOriginalOuter pool Q o).mp (Finset.mem_filter.mp ho).1).1

def dyadicExponent (Z : ℝ) (n : ℕ) : ℝ := Real.logb Z (dyadScale n)

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta) (n : ℕ)
    (hq : dyadScale n≤q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤q ∧ q≤Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_norm_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (∀i : Fin 5,Z^dyadicExponent Z (k i.castSucc)≤outerNorms p (toOriginal x) i ∧
      outerNorms p (toOriginal x) i≤Z^(dyadicExponent Z (k i.castSucc)+eta)) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)=primeProductNorm p x.quotientSupport ∧
    Z^dyadicExponent Z l≤(Ideal.absNorm (parent p x).quotient:ℝ) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)≤Z^(dyadicExponent Z l+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  have hg := outerGate_dyads p hp k o (Finset.mem_filter.mp ho).2
  have hd := live_common_dyads p hp (selector o) l D hs
  simp only [toOriginal_fill,toOriginal_ofOriginal]
  refine ⟨fun i=>dyad_power_bounds Z eta _ hZ h2 _ (hg i),sourceIdeal_norm p D,?_⟩
  change Z^dyadicExponent Z l≤(Ideal.absNorm (sourceIdeal p D):ℝ) ∧
    (Ideal.absNorm (sourceIdeal p D):ℝ)≤Z^(dyadicExponent Z l+eta)
  rw [sourceIdeal_norm]
  exact dyad_power_bounds Z eta _ hZ h2 l hd

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_ideal_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (Z^dyadicExponent Z (k 2)≤primeProductNorm p x.firstCommon ∧
      primeProductNorm p x.firstCommon≤Z^(dyadicExponent Z (k 2)+eta)) ∧
    (Z^dyadicExponent Z (k 3)≤(Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ)≤Z^(dyadicExponent Z (k 3)+eta)) ∧
    (Z^dyadicExponent Z (k 4)≤(Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ)
        ≤Z^(dyadicExponent Z (k 4)+eta)) := by
  have h:=(parentCell_norm_bounds p hp pool Q selector k l Z eta hZ h2 x hx).1
  refine ⟨h 2,?_,?_⟩
  · simpa [sourceIdeal_norm,outerNorms,toOriginal,primeSubsetGenerator_norm_eq_productNorm] using h 3
  · simpa [sourceIdeal_norm,outerNorms,toOriginal] using h 4

def jNorm (p : ι→O) (x : FirstOriginalOuter ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.1.support (fun i=>x.1.leftExponent i+x.1.rightExponent i)
    x.1.leftBit x.1.rightBit)‖^2

def labelParentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :=
  (parentCell p pool Q selector k l).filter (fun x=>dyadIndex (jNorm p (toOriginal x))=j)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem labelParentCell_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈labelParentCell p pool Q selector k l j) :
    x∈parentCell p pool Q selector k l ∧
    Z^dyadicExponent Z j≤jNorm p (toOriginal x) ∧
      jNorm p (toOriginal x)≤Z^(dyadicExponent Z j+eta) := by
  obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hx
  have hn : 1≤jNorm p (toOriginal x) :=
    EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  have hd:=dyadIndex_bounds _ hn
  rw [hj] at hd
  exact ⟨hm,dyad_power_bounds Z eta _ hZ h2 j ⟨hd.1,hd.2.le⟩⟩

theorem raw_column_exponent (Z r : ℝ) (hZ : 1<Z) (a b c : ℕ) :
    Z^r/(dyadScale a*dyadScale b*dyadScale c)=
      Z^(r-dyadicExponent Z a-dyadicExponent Z b-dyadicExponent Z c) := by
  simp only [Real.rpow_sub (show 0<Z by linarith),rpow_dyadicExponent Z hZ]
  simp only [div_div]

theorem columnScales_exponents (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    columnScales k l (Z^r) (Z^r)=rawScales k l
      (Z^(r-dyadicExponent Z (k 0)-dyadicExponent Z (k 2)-dyadicExponent Z l))
      (Z^(r-dyadicExponent Z (k 1)-dyadicExponent Z (k 2)-dyadicExponent Z l)) := by
  simp only [columnScales,raw_column_exponent Z r hZ]

theorem columnScales_products (Z r : ℝ) (k : SourceIndex) (l : ℕ) :
    let s:=columnScales k l (Z^r) (Z^r)
    s 0*s 2*s 5*s 7=Z^r ∧ s 1*s 2*s 5*s 8=Z^r :=
  ⟨columnScales_left k l _ _,columnScales_right k l _ _⟩

theorem sourceCell_parent (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (l : ℕ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (D : Finset ι) (hD : D⊆pool) (hs : commonSelector p (selector x.1) l D≠0) :
    fillFirstQuotient (ofOriginal x.1) D∈parentCell p pool Q selector k l :=
  (mem_parentCell p pool Q selector k l _).mpr
    ⟨x.1,sourceCell_outer p pool Q labels Y k x hx,D,Finset.mem_powerset.mpr hD,hs,rfl⟩

theorem outerCell_eq_of_first_five (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k k' : SourceIndex) (h : ∀i : Fin 5,k i.castSucc=k' i.castSucc) :
    outerCell p pool Q k=outerCell p pool Q k' := by
  ext x
  simp only [outerCell, Finset.mem_filter, outerGate, h]

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_selector_norm_le_one (selector : Finset ι→ℂ)
    (hs : ∀D,‖selector D‖≤1) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤1 := (commonSelector_norm p selector l D).trans (hs D)

include hp in

theorem sourceCell_actual_ratios
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
    (selector C₁ C₂ : (Σ _ : FirstOriginalOuter ι,Ideal O×O)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j≠0) :
    ∀i,actualOuterRatios p (outerNorms p x.1 0) (outerNorms p x.1 1)
      (outerNorms p x.1 2) (outerNorms p x.1 4)
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  exact actual_original_cell_ratios p hp hg _ selector C₁ C₂
    (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2) (fun y=>y.2.2)
    (source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end SevenEighths.InverseFirstGlobalCaps

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstLiveNorms -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_norm_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L B:ℝ)
    (hB:0≤B)(hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels:∀I∈labels,I≠0)(hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    (∀i:Fin 6,originalNorms p x i≤(![L,L,L,L*B^2,B^2,Y]:Fin 6→ℝ) i) ∧
      primeProductNorm p j.2.1≤L ∧ InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
  obtain ⟨ha₁,ha₂,hcommon,hquot⟩:=original_live_profile_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K L hW x hx j hn
  obtain ⟨ho,hfreq⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hb,hC,hD⟩:=(mem_firstOriginalOuter pool Q x.1).mp ho
  obtain ⟨hf,hrow⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hfreq
  have hcube:=reopenedCubeFamily_cube_norms p Q B hQ x.1.1 hb
  have hsup:=cube_whole_support_dyad p hp x.1.1 B hB hcube.1 hcube.2
  have hdiv:primeProductNorm p x.1.2.2≤L*B^2:=by
    calc
      _≤primeProductNorm p (x.1.2.1∪cubePrincipalSupport x.1.1.support x.1.1.leftExponent
          x.1.1.rightExponent x.1.1.leftBit x.1.1.rightBit):=
        primeProductNorm_mono p hp (Finset.mem_powerset.mp hD)
      _≤primeProductNorm p x.1.2.1*primeProductNorm p x.1.1.support:=by
        apply (primeProductNorm_union_le_mul p hp _ _).trans
        exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _))
          (primeProductNorm_pos p hp _).le
      _≤L*B^2:=mul_le_mul hcommon hsup (primeProductNorm_pos p hp _).le
        ((primeProductNorm_pos p hp _).le.trans hcommon)
  have hactive:activeNorm p x≤B^2:=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hsup
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hf)
  have hh0:x.2.2≠0:=(Finset.mem_erase.mp hrow).1
  have hh:=((mem_nonzeroChildFrequencyBall _ hE Y x.2.2).mp hrow).2
  have hfreqnorm:‖eisEmbedding x.2.2‖^2≤Y:=
    (element_norm_le_of_dvd (mul_ne_zero hE hh0) (dvd_mul_left x.2.2 _)).trans hh
  have hj:InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
    have hd:=jLabel_dvd_cube_product p x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
      x.1.1.leftBit x.1.1.rightBit x.1.1.support_pos
    have hnorm:=element_norm_le_of_dvd
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _)) hd
    simp only [map_mul,norm_mul,mul_pow] at hnorm
    exact hnorm.trans ((mul_le_mul hcube.1 hcube.2 (sq_nonneg _) hB).trans_eq (pow_two B).symm)
  refine ⟨?_,hquot,hj⟩
  intro i
  fin_cases i
  · exact ha₁
  · exact ha₂
  · exact hcommon
  · simpa [originalNorms,InverseMomentFirstChildWindows.sourceNorms,divisorElement,
      primeSubsetGenerator_norm_eq_productNorm] using hdiv
  · exact hactive
  · exact hfreqnorm

end SevenEighths.InverseMomentFirstLiveCaps

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstDyadicRadius -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]

def firstDyadicExponent (Z x:ℝ):ℝ:=dyadicExponent Z (dyadIndex x)

theorem first_dyadic_bounds (Z eta x:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x):
    0≤firstDyadicExponent Z x ∧ Z^firstDyadicExponent Z x≤x ∧ x≤Z^(firstDyadicExponent Z x+eta):=by
  have hd:=dyadIndex_bounds x hx
  have he:=dyad_power_bounds Z eta x hZ hbin (dyadIndex x) ⟨hd.1,hd.2.le⟩
  refine ⟨?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [Real.rpow_zero,firstDyadicExponent,rpow_dyadicExponent Z hZ]
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

def firstDyadicRadius (p:ι→O)(b:CubeCoordinates ι)(C D:Finset ι)
    (Z M r ell V eta tau:ℝ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (firstDyadicExponent Z (primeProductNorm p D))
    (firstDyadicExponent Z (primeProductNorm p C))
    (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau)

def firstDyadicPhysicalCutoff (p:ι→O)(b:CubeCoordinates ι)(C:Finset ι)(I:Ideal O)
    (Z M r ell V eta tau:ℝ)(D:Finset ι):Finset O:=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (firstDyadicRadius p b C D Z M r ell V eta tau)

theorem first_dyadic_radius_global_cap
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι)(C D:Finset ι)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (h₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)):
    firstDyadicRadius p b C D Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hC:=first_dyadic_bounds Z eta (primeProductNorm p C) hZ hbin (primeProductNorm_ge_one p hp C)
  have hd:=first_dyadic_bounds Z eta (primeProductNorm p D) hZ hbin (primeProductNorm_ge_one p hp D)
  have hj:=first_dyadic_bounds Z eta (‖eisEmbedding (jLabel p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) hZ hbin
    (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _))
  have hs:=cube_whole_support_dyad p hp b (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) h₁ h₂
  have hn:primeProductNorm p D≤Z^(firstDyadicExponent Z (primeProductNorm p C)+2*ell+3*eta):=by
    calc
      _≤primeProductNorm p (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):=
        primeProductNorm_mono p hp hD
      _≤primeProductNorm p C*primeProductNorm p b.support:=
        (primeProductNorm_union_le_mul p hp _ _).trans
          (mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _)) (primeProductNorm_pos p hp _).le)
      _≤Z^(firstDyadicExponent Z (primeProductNorm p C)+eta)*(Z^(ell+eta))^2:=
        mul_le_mul hC.2.2 hs (primeProductNorm_pos p hp _).le (Real.rpow_nonneg hz.le _)
      _=_:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
        congr 1
        norm_num
        ring
  have hde:= (Real.rpow_le_rpow_left_iff hZ).mp (hd.2.1.trans hn)
  unfold firstDyadicRadius firstPhysicalHeight
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith [hC.1,hj.1]

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstDyadicTail -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_first_dyadic_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
    (hMm:0≤Mmax) (hFm:0≤Fmax) (heta:0≤eta) (htau:0<tau) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (weights:σ→ι→ℂ)
      (extra₁ extra₂:CubeCoordinates ι→Finset ι)
      (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (Z M r ell V Γ G₁ G₂:ℝ),
      1<Z → 2≤Z^eta → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤ r → r+3*ell+V≤Fmax →
      0≤Γ → 0≤G₁ → 0≤G₂ →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta)) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
          (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*65536*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hbin hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
    hadm hb₁ hb₂ hI0 hIF ha hslots hw he₁ he₂ ht₁ ht₂ hs₁ hs₂
  have hz:0<Z:=zero_lt_one.trans hZ
  let B:=Z^(ell+eta)
  let L:=Z^(r+eta)
  let E:=65536*(Cm*(B^2*L)*G₁)*(Cm*(B^2*L)*G₂)*
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving')
  have hB:1≤B:=Real.one_le_rpow hZ.le (by linarith)
  have hL:0<L:=Real.rpow_pos_of_pos hz _
  have hE:0≤E:=by dsimp [E,B,L];positivity
  have hextra (extra:CubeCoordinates ι→Finset ι) (he:∀b∈bs,extra b⊆b.support)
      (b:CubeCoordinates ι) (hb:b∈bs):primeProductNorm p (extra b)≤B^2:=
    (primeProductNorm_mono p hp (he b hb)).trans
      (cube_whole_support_dyad p hp b B (zero_le_one.trans hB) (hb₁ b hb) (hb₂ b hb))
  have hlocal (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels)
      (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
        (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
        (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
        (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:1≤x):x≤Z^(firstDyadicExponent Z x+eta):=
      (first_dyadic_bounds Z eta x hZ hbin hx).2.2
    have hlower (x:ℝ) (hx:1≤x):Z^(firstDyadicExponent Z x-eta)≤x:=by
      exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : firstDyadicExponent Z x-eta≤firstDyadicExponent Z x)).trans
        (first_dyadic_bounds Z eta x hZ hbin hx).2.1
    have hjpos:0<‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (firstDyadicExponent Z (primeProductNorm p C))
      (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>firstDyadicExponent Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_ge_one p hp D)) (hlower _ (primeProductNorm_ge_one p hp C))
      (hlower _ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)))
    simpa only [firstLocalPhysicalTail,firstDyadicPhysicalCutoff,firstDyadicRadius,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)
    hB hL (Real.one_le_rpow hZ.le (by linarith)) hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2) hlocal
  apply he.trans
  have hexp:B^9*L^4*Z^(V+eta)*Z^(-saving')≤Z^(-saving):=by
    dsimp [B,L]
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [saving']
    norm_num
    linarith
  have hm:=mul_le_mul_of_nonneg_left hexp
    (show 0≤Ca*65536*Cm^2*Ct*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) from by positivity)
  convert hm using 1
  · dsimp only [E]
    norm_num
    ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstDyadicOriginalBranches -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight SecondPassIntegration FourierBridge
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_zero_tail
    (om:𝓢(ℝ,ℂ))(b Mmax Fmax eta tau saving eps:ℝ)
    (hs:∀y,om y≠0→y≤b)(hMm:0≤Mmax)(hFm:0≤Fmax)(heta:0≤eta)(htau:0<tau)(heps:0<eps):
    ∃Czero Ctail:ℝ,0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta:ℝ),
      1<Z→2≤Z^eta→0≤M→M≤Mmax→0≤ell→0≤V→ (-eta≤ r) → (r+3*ell+V≤Fmax)→0≤Γ→b≤Z^eta→
      (∀u,‖Ψ u‖≤1)→(∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖weights i q‖≤1)→
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let mark:=fun (v:ι→₀ℕ) U=>primeMark slots lists weights (v.support∪U);
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualZero p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M))‖≤
          Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta)) ∧
      ‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualTail p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (firstDyadicPhysicalCutoff p q C I Z M r ell V eta tau))‖≤Ctail*Γ^2*Z^(-saving):=by
  obtain ⟨Cz,hCz,hzero⟩:=original_first_zero_physical eps heps
  obtain ⟨s,Ct,hCt,htail⟩:=full_first_dyadic_marked_rapid_tail Mmax Fmax eta tau saving hMm hFm heta htau
  let G:=SchwartzMap.seminorm ℝ 0 0 om
  let Cz':=Cz*G^2*‖paperRadialFourier rowMajorant 0‖
  let Ct':=Ct*G^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)
  refine ⟨Cz',Ct',by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ hbin hM hMmax hell hV hr hF hΓ hb hΨ hQ hn hlabels hβ hslots hw W mark
  have hz:0<Z:=zero_lt_one.trans hZ
  have hG:0≤G:=apply_nonneg _ _
  have hW:∀U,‖W (primeProductNorm p U)‖≤G:=by
    intro U
    simp only [W,normTwistedSource,norm_mul,logPhase_norm,one_mul]
    exact om.norm_le_seminorm ℝ _
  have hsupport:∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta):=by
    intro U hU
    have hnon:om (primeProductNorm p U/Z^r)≠0:=by
      intro hh
      exact hU (by simp [W,normTwistedSource,hh])
    have hle:primeProductNorm p U≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
    apply hle.trans
    calc
      b*Z^r≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  have hzero':=hzero p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights W rowMajorant
    Z M r ell V eta Γ G hZ (by linarith) (by linarith) hΓ hG hΨ hQ hn hlabels hβ hslots hw hW hsupport
  have hcb:=reopenedCubeFamily_cube_norms p Q _ hQ
  have htail':=htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    Ψ Ψ m m slots lists weights (fun q=>q.rightExponent.support) (fun q=>q.leftExponent.support)
    (fun _ U=>W (primeProductNorm p U)) (fun _ U=>W (primeProductNorm p U)) rowMajorant Z M r ell V
    (Γ^2) G G hZ hbin hM hMmax hell hV hr hF (sq_nonneg _) hG hG hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun q hq=>(hcb q hq).1) (fun q hq=>(hcb q hq).2)
    hn hlabels (fun q hq C _ I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ q hq C I hI)
    hslots hw (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hsupport) (fun _ _=>hsupport)
  constructor
  · simpa only [mark,Finset.union_comm,Cz',G,mul_assoc,mul_left_comm,mul_comm] using hzero'
  · simpa only [mark,reopenedPhysicalSourceSum,Ct',pow_two,mul_assoc,mul_left_comm,mul_comm] using htail'

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileParents -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]

lemma originalChildEnergy_eq_caps (hp : ∀i,p i≠0)
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) :
    originalChildEnergy p hp hg hinj pool Q k l negative Ψ m mark omega T t Y=
      ∑x∈InverseFirstGlobalCaps.outerCell p pool Q k,
        firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
          (mark (if negative then x.1.rightExponent else x.1.leftExponent))
          (commonSelector p (fun _=>1) l) omega T t Y := by
  rw [originalChildEnergy,originalOuterCell_eq_caps]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def refinedOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (gate : FirstOriginalOuter ι→Prop) : Finset (FirstOriginalOuter ι) :=
  (originalOuterCell p pool Q k).filter gate

def refinedSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) : Finset (OriginalIndex ι) :=
  (sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k).filter
      (fun x=>gate x.1 ∧ firstOriginalWeight p β cutoff x.1 x.2≠0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedSource_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) :
    refinedSource p pool Q labels β cutoff Y k gate⊆sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k :=
  Finset.filter_subset _ _

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_weight_frequency (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (x : OriginalIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2≠0) :
    x.2.2∈reopenedPhysicalCutoff p x.1.1 x.2.1 (cutoff x.1.1 x.1.2.1 x.2.1) x.1.2.2 := by
  by_contra hh
  exact hx (by simp [firstOriginalWeight,hh])

theorem refined_source_radius (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ysource Ychild : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop)
    (hn : ∀I∈labels,I≠0)
    (hcut : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Ychild) :
    refinedSource p pool Q labels β cutoff Ysource k gate⊆
      firstGlobalRetainedSource p (refinedOuter p pool Q k gate) (fun _=>labels) (fun x=>x.1) Ychild := by
  intro x hx
  obtain ⟨hxcell,hgate,hweight⟩ := Finset.mem_filter.mp hx
  have hxold := original_cell_subset p pool Q labels Ysource k hxcell
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxold
  have hm := (mem_firstRetainedSource p labels x.1.1 Ysource x.2).mp hf
  have houter : x.1∈refinedOuter p pool Q k gate := Finset.mem_filter.mpr ⟨ho,hgate⟩
  have hE := firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hn x.2.1 hm.1)
  apply Finset.mem_sigma.mpr
  refine ⟨houter,(mem_firstRetainedSource p labels x.1.1 Ychild x.2).mpr ⟨hm.1,?_⟩⟩
  apply Finset.mem_erase.mpr
  refine ⟨(Finset.mem_erase.mp hm.2).1,?_⟩
  apply (mem_childFrequencyBall _ hE Ychild x.2.2).mpr
  exact ((mem_childFrequencyBall _ hE _ x.2.2).mp
    (original_weight_frequency p β cutoff x hweight)).trans (hcut x.1 houter x.2.1 hm.1)

def labelGate (j : ℕ) (x : FirstOriginalOuter ι) : Prop :=
  InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedOuter_label (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (j : ℕ) :
    refinedOuter p pool Q k (labelGate p j)=
      (InverseFirstGlobalCaps.outerCell p pool Q k).filter
        (fun x=>InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j) := by
  rw [refinedOuter,originalOuterCell_eq_caps]
  ext x
  simp [labelGate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def refinedChildEnergy (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (gate : FirstOriginalOuter ι→Prop) (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) : ℝ :=
  ∑x∈refinedOuter p pool Q k gate,
    firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
      (mark (if negative then x.1.rightExponent else x.1.leftExponent))
      (commonSelector p (fun _=>1) l) omega T t Y

def refinedCellRows (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
    (refinedSource p pool Q labels β cutoff Y k gate)
    pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) W₁ W₂ Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s

theorem original_refined_cell_physical_budget (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ : ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) :
    ∃(omega₁ omega₂ : 𝓢(ℝ,ℂ))(lo hi : ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁ : ℝ→ℂ) ∧ HasCompactSupport (omega₂ : ℝ→ℂ) ∧
      tsupport (omega₁ : ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂ : ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀(ε : ℝ),0<ε→∀(Aker J : ℕ),∃ Cprofile Kpush : ℝ,0≤Cprofile ∧ 0<Kpush ∧
    ∀{ι : Type*}[DecidableEq ι](p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
      (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Γ Ysource Y : ℝ)
      (_hΨ : ∀u,‖Ψ u‖≤1) (_hΓ : 0≤Γ) (_hY : 0<Y)
      (_hsf : ∀I∈labels,Squarefree I) (_hn : ∀I∈labels,I≠0)
      (_hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop)
      (_hcutoff : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Y)
      (T₁ T₂ K theta L : ℝ)
      (_hT₁ : 0<T₁) (_hT₂ : 0<T₂) (_hK : 0<K) (_hL : 0≤L)
      (Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta : ℝ)
      (_hB : 0≤Benergy) (_hZ : 0<Z)
      (_hscale : rawScales k l T₁ T₂=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
      (_hLe : L=eta*Real.log Z)
      (_hleft : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate true Ψ m mark omega₁ T₁
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
      (_hright : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate false Ψ m mark omega₂ T₂
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Ysource (rawScales k l T₁ T₂)‖≤
        ((Γ^2*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖-theta‖)^InverseClippingProfiles.momentOrder J*
          (1+‖theta‖)^InverseClippingProfiles.momentOrder J)/
          (1+K*(rawScales k l T₁ T₂) 6/((rawScales k l T₁ T₂) 3*(rawScales k l T₁ T₂) 4*
            ((rawScales k l T₁ T₂) 5)^2*T₁*T₂))^Aker)) := by
  obtain ⟨w₁,w₂,U,M₀,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,hM,hUc,hUs,hwin⟩ :=
    original_cell_windows g₁ g₂ m₁ m₂ 1 (fun _=>0) hm₁ hm₂ hg₁ hg₂ (fun _=>le_rfl)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro ε hε Aker J
  obtain ⟨Cprofile,Kpush,hC,hKp,he⟩ := actual_first_original_subset_physical_budget
    ε hε U g₁ g₂ Φ M₀ (fun _=>0) m₁ m₂ 1
    hM (fun _=>le_rfl) hUs hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hC,hKp,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Ysource Y hΨ hΓ hY hsf hn hβ
    k l gate hcutoff T₁ T₂ K theta L hT₁ hT₂ hK hL Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hB hZ hscale hLe hleft hright
  let source := refinedSource p pool Q labels β cutoff Ysource k gate
  have hgates := hwin p hp hg pool Q labels Ysource (coefficient p hp hcop hg Ψ m mark true)
    (coefficient p hp hcop hg Ψ m mark false) k l T₁ T₂ (fun _=>0) 1 1 (-theta) theta
    hT₁ hT₂ (by intro i;simp) le_rfl le_rfl le_rfl le_rfl
  have hb := he p hp hg hinj hcop hc hpr pool (refinedOuter p pool Q k gate) (fun x=>x.1) (fun x=>x.2.1)
    Ψ Ψ m m (divisorElement p) (fun x=>mark x.1.rightExponent) (fun x=>mark x.1.leftExponent)
    (fun _=>commonSelector p (fun _=>1) l) (fun _=>labels) (firstOriginalWeight p β cutoff) (Γ^2) Y
    hΨ hΨ (sq_nonneg _) hY (fun _ _=>hsf) (fun _ _=>hn)
    (fun x hx=>original_weight_bound p pool Q labels β cutoff Γ Y hΓ hβ x (original_outer_cell_subset p pool Q k (Finset.mem_filter.mp hx).1))
    w₁ w₂ (fun _=>0) 1 1 (-theta) theta (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    K L hK (rawScales k l T₁ T₂) (rawScales_pos k l T₁ T₂ hT₁ hT₂)
    source (refined_source_radius p hp pool Q labels β cutoff Ysource Y k gate hn hcutoff)
    (fun x hx=>original_source_positive p hp pool Q labels Ysource x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (by intro i;simp) le_rfl le_rfl le_rfl le_rfl hL
    (fun x hx=>hgates.1 x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hgates.2.1 x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hgates.2.2 x (Finset.mem_filter.mp hx).1)
    Benergy hB Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe
    (by simpa [refinedChildEnergy,rawScales] using hleft)
    (by simpa [refinedChildEnergy,rawScales] using hright)
  unfold refinedCellRows
  unfold SevenEighths.InverseMomentFirstOriginalProfile.coefficient SevenEighths.InverseMomentFirstOriginalProfile.weight
  simpa [source,rawScales] using hb

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveIdentity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_refined_cell_profile_identity (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    let source := refinedSource p pool Q labels β cutoff Y k gate
    (∑x∈source,∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) l j.2.1*
      sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>normTwistedSource om theta (y/X)) Φ K x j)=
    refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y s := by
  intro source
  let W₁ := fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X))
  let W₂ := fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)
  have he := original_family_profiles p hp hg source pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) om a b ha hsom Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K X theta
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s hs
    (by intro x hx;have hh:=original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp (refinedSource_subset p pool Q labels β cutoff Y k gate hx)).1
        exact ⟨hh.1,hh.2.1,hh.2.2.1⟩) hX hleft hright
  change _=firstFamilyPhysicalRows p hg source pool _ _ _ _ _ _ Φ _ _ _ _ K _ _ s
  rw [←he]
  have hl : s 0*s 2*s 5*s 7≠0 := hleft.trans_ne (ne_of_gt hX)
  have hr : s 1*s 2*s 5*s 8≠0 := hright.trans_ne (ne_of_gt hX)
  simp only [firstFamilyPhysicalRows,firstBlockedPhysicalRows,sourceSummand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hl,mul_div_cancel₀ _ hr]
  ring

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLivePartition -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

abbrev JointKey := SourceIndex × ℕ × ℕ

def jointKey (x : OriginalIndex ι) (j : FirstCommonIndex ι) : JointKey :=
  (sourceIndex (originalNorms p) x,dyadIndex (primeProductNorm p j.2.1),
    dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))

def liveJointKeys (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) : Finset JointKey :=
  ((S×ˢfirstCommonIndices pool).filter (fun x=>term x.1 x.2≠0)).image
    (fun x=>jointKey p x.1 x.2)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma sum_live_joint_cells (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices pool,term x j)=
      ∑k∈liveJointKeys p S pool term,∑x∈S,∑j∈firstCommonIndices pool,
        if jointKey p x j=k then term x j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : term x j=0
  · simp [hz]
  · have hk : jointKey p x j∈liveJointKeys p S pool term :=
      Finset.mem_image.mpr ⟨(x,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [hk]

lemma sourceSummand_zero_of_weight (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2=0) :
    sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j=0 := by
  simp [sourceSummand,weight,retainedCubeWeight,hx]

lemma joint_cell_eq_refined (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (k : JointKey) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    (∑x∈S,∑j∈firstCommonIndices pool,if jointKey p x j=k then term x j else 0)=
      ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
        ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  simp only [refinedSource,sourceCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : firstOriginalWeight p β cutoff x.1 x.2=0
  · have ht : ∀j,term x j=0 := fun j=>sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hw
    simp [ht,hw]
  · by_cases hs : sourceIndex (originalNorms p) x=k.1
    · by_cases hj : dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)=k.2.2
      · simp [jointKey,hs,hj,labelGate,hw,Prod.ext_iff,commonSelector,ite_mul]
      · simp [jointKey,hs,hj,labelGate,Prod.ext_iff]
    · simp [jointKey,hs,Prod.ext_iff]

theorem original_retained_joint_partition (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s=
      ∑k∈liveJointKeys p S pool term,
        ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
          ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  rw [original_retained_sum p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s hs,
    sum_live_joint_cells p S pool term]
  apply Finset.sum_congr rfl
  intro k hk
  exact joint_cell_eq_refined p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y k

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

