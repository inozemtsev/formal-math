module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part029
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part018
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part025
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part026
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part028
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part030

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalRows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_physical_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_original_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN H hβ hHD R Kphys hKphys n rK
  have hrK:0< rK:=div_pos (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
    (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
  have hh:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN (dyadicScale (n 2)) (dyadicScale (n 3))
    (dyadicScale_pos _) (dyadicScale_pos _) H hβ hHD R
    (fun _=>Real.log (secondEffectiveScale C D A Kphys/dyadicScale (n 0)))
    (fun z=>Real.log (normValue z/dyadicScale (n 1))) rK hrK
  change (1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤_ at hh
  have ho:0≤outerScalar C D Kphys n:=by unfold outerScalar; positivity
  have hno:0≤normalizer C D U:=(normalizer_pos C D hC U).le
  rw [physicalBlock_eq s.η s.t S β C D hC hD U R rows hn W Kphys hKphys n,
    norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ho,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hno]
  calc
    _=(outerScalar C D Kphys n*normalizer C D U)*
        ((1+rK)^decay*‖normalizedBlock s.η s.t S β C D hC hD U R rows W Kphys n‖):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hh (mul_nonneg ho hno)

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalDyadic -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_dyadic_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      (1+rK)^decay*‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖≤
        outerScalar C D Kphys n*normalizer C D U*
          (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_physical_exceptional_block wlo whi hwlo hwhi lo hi W decay ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n rK
  rw [physicalBlock_dyadic_rows s.η s.t S β C D hC hD U R rows W Kphys n]
  exact hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ (dyadicRows rows n)
    (fun z hz=>dyadicRows_nonzero rows n z hz)
    (fun χ z hz=>hex₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hex₂ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₁ χ z (dyadicRows_subset rows n hz))
    (fun χ z hz=>hcond₂ χ z (dyadicRows_subset rows n hz))
    χ₀ hcop hη m hm hml hm2 (fun z hz=>hex z (dyadicRows_subset rows n hz))
    1 (Real.logb Z (dyadicScale (n 1))) (by norm_num)
    (fun z hz=>by simpa only [one_mul] using dyadicRows_power_cap rows n Z hZ.1 z hz)
    H hβ hHD R Kphys hKphys n

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildProfileControl
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonRadialPointwise CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mass (s : Input ι) : ℝ := ∏ i,s.M i

omit [DecidableEq ι] in
lemma mass_one (s : Input ι) : 1≤ mass s :=
  Finset.one_le_prod₀ (fun i _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma mass_nonneg (s : Input ι) : 0≤ mass s := zero_le_one.trans (mass_one s)

omit [DecidableEq ι] in
lemma child_mass (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : mass (child s C R B τ t)≤ mass s := by
  change (∏i:liveIndices B.val,s.M i.val)≤∏i,s.M i
  rw [Finset.prod_coe_sort]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)

omit [DecidableEq ι] in
lemma child_card (B : CenteredMomentAddedZeroUniform.Tuple ι) :
    Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa using Finset.card_le_card (Finset.subset_univ (liveIndices B))

omit [DecidableEq ι] in
lemma slot_control_bound (s : Input ι) (b : ℝ) (hb : 1≤b) (hu : s.upper≤b) :
    slotControl s.toData≤(128*b)^Fintype.card ι*mass s^2 := by
  have hpoint (i : ι) : max 1 (128*max 0 (s.hi i)*s.M i)≤(128*b)*s.M i := by
    apply max_le
    · have hM:=s.M_ge_one i
      nlinarith
    · apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (s.M_ge_one i))
      exact mul_le_mul_of_nonneg_left (max_le (by linarith) ((s.upper_ge i).trans hu)) (by norm_num)
  have hp:=Finset.prod_le_prod₀ (fun i (_:i∈Finset.univ)=>by positivity)
    (fun i (_:i∈Finset.univ)=>hpoint i)
  calc
    slotControl s.toData=mass s*(∏i,max 1 (128*max 0 (s.hi i)*s.M i)):=rfl
    _≤ mass s*(∏i,(128*b)*s.M i):=mul_le_mul_of_nonneg_left hp (mass_nonneg s)
    _=(128*b)^Fintype.card ι*mass s^2:=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
      unfold mass
      ring

omit [DecidableEq ι] in
lemma profile_cost_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileCost s≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*A^2)*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have hm2:=pow_le_pow_left₀ (mass_nonneg s) hm 2
  have h:=mul_le_mul hm2 hp (by positivity) (sq_nonneg A)
  have h':=(mul_le_mul_of_nonneg_right h
    (show 0≤2*(max 1 s.b₁*max 1 s.b₂)*mass s^2 by positivity))
  convert h' using 1 <;> simp only [profileCost,Data.profileFactor,mass]; ring

omit [DecidableEq ι] in
lemma exceptional_slot_bound (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    slotControl s.toData^2*frozenProfile s^2≤
      ((128*b)^N)^2*(b^N)^2*A^4*mass s^2 := by
  have hb0:0≤b:=zero_le_one.trans hb
  have hp : (max 1 s.upper)^Fintype.card ι≤b^N :=
    (pow_le_pow_left₀ (by positivity) (max_le hb hu) _).trans (pow_le_pow_right₀ hb hc)
  have h128 : (1:ℝ)≤128*b := by linarith
  have hs : slotControl s.toData≤(128*b)^N*mass s^2 :=
    (slot_control_bound s b hb hu).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h128 hc) (sq_nonneg _))
  have hf : frozenProfile s≤ mass s*b^N :=
    mul_le_mul_of_nonneg_left hp (mass_nonneg s)
  have h:=mul_le_mul (pow_le_pow_left₀ (slotControl_nonneg _) hs 2)
    (pow_le_pow_left₀ (frozenProfile_nonneg s) hf 2) (sq_nonneg _) (sq_nonneg _)
  calc
    _≤((128*b)^N*mass s^2)^2*(mass s*b^N)^2:=h
    _=((128*b)^N)^2*(b^N)^2*mass s^4*mass s^2:=by ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg s) hm 4) (by positivity))
      (sq_nonneg _)

omit [DecidableEq ι] in
theorem twice_controls (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileCost d≤(2*(max 1 s.b₁*max 1 s.b₂)*b^N*mass s^2)*mass d^2 ∧
    slotControl d.toData^2*frozenProfile d^2≤
      ((128*b)^N)^2*(b^N)^2*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤ mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact ⟨profile_cost_bound d N b (mass s) hb hu hn hm,
    exceptional_slot_bound d N b (mass s) hb hu hn hm⟩

def exceptionalConstant (N : ℕ) (b : ℝ) (J : ℕ) (Q : Ideal O) (K : ℝ) : ℝ :=
  K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2*
    ((128*b)^N)^2*(b^N)^2

omit [DecidableEq ι] in
lemma exceptional_factor_bound {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Q : Ideal O) (K : ℝ)
    (hK : 0≤K) (s : Input ι) (N : ℕ) (b A : ℝ)
    (hb : 1≤b) (hu : s.upper≤b) (hc : Fintype.card ι≤N) (hm : mass s≤A) :
    profileFactor S s p J Q K≤exceptionalConstant N b J Q K*
      p.control S^2*(1+‖s.t‖)^(2*J)*A^4*mass s^2 := by
  have h:=exceptional_slot_bound s N b A hb hu hc hm
  let F:=K*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
    (1+2*Real.pi)^(4*J)*p.control S^2*(1+‖s.t‖)^(2*J)*
    (∫u:ℝ,(1+‖u‖)^J*‖CenteredMomentHeckeColumnWindow.columnDensity
      CenteredMomentLogDyadic.logAnnulus CenteredMomentLogDyadic.logAnnulus_compact
      CenteredMomentLogDyadic.logAnnulus_smooth u‖)^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hh:=mul_le_mul_of_nonneg_left h hF
  convert hh using 1 <;> simp only [profileFactor,exceptionalConstant,F] <;> ring

omit [DecidableEq ι] in
theorem twice_exceptional_factor {wlo whi : ℝ}
    (S : Finset (ℕ×ℕ)) (p : Profiles wlo whi) (J : ℕ) (Qfix : Ideal O) (K : ℝ)
    (hK : 0≤K) (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hu : s.upper≤b) (hc : Fintype.card ι≤N)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    profileFactor S d p J Qfix K≤exceptionalConstant N b J Qfix K*
      p.control S^2*(1+‖v‖)^(2*J)*mass s^4*mass d^2 := by
  let d:=twiceChild s C R B τ t Q k Bp υ v
  have hm : mass d≤ mass s :=
    (child_mass (child s C R B τ t) (Q^k) (R*C) Bp υ v).trans
      (child_mass s C R B τ t)
  have hn : Fintype.card (liveIndices Bp.val)≤N :=
    (child_card Bp.val).trans ((child_card B.val).trans hc)
  exact exceptional_factor_bound S p J Qfix K hK d N b (mass s) hb hu hn hm

end SevenEighths.CenteredMomentFirstChildProfileControl

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstDivisorSupport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorSupport
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentSecondDivisorSupport CenteredMomentChildAssembly
open CenteredMomentHeckeColumnWindow
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

lemma right_coefficient_zero (s : OriginalData ι) (C D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (a : columns C D hD.1 s.columns→ℂ) (I : columns C D hD.1 s.columns) :
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun I=>coefficient η m 1 t s.beta D I*a I) χ I=0 := by
  unfold divisorCoefficient
  rw [element_span]
  split_ifs with hd
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (column_supported C D hD.1 s.columns I).1 s.beta H hβ hn hd)
    simp only [coefficient,hz,zero_mul]
  · rfl

theorem rightWindowChild_zero (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild s η m t C D hC hD E χ L θ X V z=0 := by
  unfold rightWindowChild gaussPolynomial
  dsimp only
  simp only [right_coefficient_zero s C D hD H hβ L hL η m t χ,
    zero_mul,Finset.sum_const_zero]

theorem signed_right_window_filter (s : OriginalData ι) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (Ds : Finset (Ideal O)) (rows : Finset O)
    (F : Ideal O→O→ℂ) :
    (∑L∈Ds,∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)))=
      ∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ∑z∈rows,F L z*star (rightWindowChild s η m t C D hC hD E χ L θ X V (-z)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hl : (L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl]
    simp only [rightWindowChild_zero s C D hC hD E H hβ L (lt_of_not_ge hl),star_zero,
      mul_zero,Finset.sum_const_zero]

theorem supported_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(Ds : Finset (Ideal O))(D : Ideal O)(H : ℝ),H/(D.absNorm:ℝ)≤Z^B →
      (∑L∈Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Ds D H hcap
  exact hz.2 _ (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hcap)

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

theorem input_commonEnergy_zero (s : Input ι) (R seed D : Ideal O) (hD : Supported D)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy (original s R seed) D hD τ t L W K=0 :=
  commonEnergy_zero (original s R seed) D hD _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL τ t W K

theorem input_rightWindowChild_zero (s : Input ι) (R seed C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (L : Ideal O)
    (hL : CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)<L.absNorm)
    (η : Character) (m : O) (t : ℝ) (χ : RayCharacter)
    (θ X : ℝ) (V : ℝ→ℂ) (z : O) :
    rightWindowChild (original s R seed) η m t C D hC hD E χ L θ X V z=0 :=
  rightWindowChild_zero (original s R seed) C D hC hD E _
    (fun I hi=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s R seed I hz₁ hz₂ hi).2)
    L hL η m t χ θ X V z

end SevenEighths.CenteredMomentFirstDivisorSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstDivisorCommonBound -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstDivisorCommonBound
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
local notation "O"=>ActualEisensteinCubic.O

def pairMajorant {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑i∈S,∑j∈S,b i*b j*‖∑'z:O,(gaussRow (a i) (ha i) z*star (gaussRow (a j) (ha j) z))*
    W (‖eisEmbedding z‖^2/K)‖

lemma pairMajorant_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℝ) (hb : ∀i∈S,0≤b i)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤pairMajorant S a ha b W K :=
  Finset.sum_nonneg (fun i hi=>Finset.sum_nonneg (fun j hj=>
    mul_nonneg (mul_nonneg (hb i hi) (hb j hj)) (norm_nonneg _)))

lemma gaussEnergy_pair_bound {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (b : α→ℝ)
    (hc : ∀i∈S,‖c i‖≤b i) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (gaussEnergy S a ha c W K).re≤pairMajorant S a ha b W K := by
  apply (Complex.re_le_norm _).trans
  rw [gaussEnergy_expand S a ha c W K hK]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  simp only [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (hc i hi) (hc j hj) (norm_nonneg _) ((norm_nonneg _).trans (hc i hi)))
    (norm_nonneg _)

variable {ι : Type*} [Fintype ι]

def coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  pairMajorant Finset.univ (sourceGenerator (residualPool C hC.1 s.columns))
    (sourceGenerator_supported _) (fun I:supportedColumns (residualPool C hC.1 s.columns)=>
      ‖if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (C*I) else 0‖) W K

lemma coarse_nonneg (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : 0≤ coarse s C hC L W K :=
  pairMajorant_nonneg _ _ _ _ (fun _ _=>norm_nonneg _) _ _

lemma commonEnergy_coarse (s : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (τ : Character) (v : ℝ) :
    (commonEnergy s C hC τ v L W K).re≤ coarse s C hC L W K := by
  apply gaussEnergy_pair_bound _ _ _ _ _ _ W K hK
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one τ v I
      (Finset.mem_filter.mp I.property).2.1)

universe u

theorem actual_supported_annular_block (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        (∑ L∈(divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b})).filter
            (fun L=>(L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
            (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  let live (L : Ideal O) : Prop := (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ)
  let U := CenteredMomentFirstAnnularMajorant.profile
  let H := dyadicScale (n 1)
  let active (L : Ideal O) : Prop := live L ∧ (UniqueFactorizationMonoid.moebius L:ℂ)≠0
  let F₁ (L : Ideal O) := if active L then E₁/(L.absNorm:ℝ) else coarse s C hC L U H
  let F₂ (L : Ideal O) := if active L then E₂/(L.absNorm:ℝ) else if live L then coarse s D hD L U H else 0
  have hF₁ (L : Ideal O) : 0≤F₁ L := by
    dsimp only [F₁]; split_ifs
    · exact div_nonneg hE₁ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
  have hF₂ (L : Ideal O) : 0≤F₂ L := by
    dsimp only [F₂]; split_ifs
    · exact div_nonneg hE₂ (Nat.cast_nonneg _)
    · exact coarse_nonneg _ _ _ _ _ _
    · exact le_rfl
  have hh:=hbound η s t C D hC hD hCD E rows K hK n F₁ F₂
    (fun L _=>hF₁ L) (fun L _=>hF₂ L)
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₁,ite_eq_left hl] using hleft L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · apply (commonEnergy_coarse s C hC L U H (dyadicScale_pos _) _ v).trans
        rw [show F₁ L=coarse s C hC L U H from ite_eq_right hl]
        exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _)
          (one_le_pow₀ (by linarith [norm_nonneg v])))
    (by
      intro L hL χ v
      by_cases hl:active L
      · simpa only [F₂,ite_eq_left hl] using hright L hL hl.1 (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hl.2) χ v
      · by_cases hc:live L
        · apply (commonEnergy_coarse s D hD L U H (dyadicScale_pos _) _ v).trans
          simp only [F₂,ite_eq_right hl,ite_eq_left hc]
          exact le_mul_of_one_le_right (coarse_nonneg _ _ _ _ _ _) (one_le_pow₀ (by linarith [norm_nonneg v]))
        · rw [commonEnergy_zero s D hD Hsource hβ L (lt_of_not_ge hc)]
          simp only [F₂,ite_eq_right hl,ite_eq_right hc,Complex.zero_re,zero_mul,le_refl])
  let Ds:=divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})
  have he : (∑L∈Ds,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
      (windowBudget J₁ t (F₁ L)*windowBudget J₂ t (F₂ L))) =
      (∑L∈Ds.filter live,‖(UniqueFactorizationMonoid.moebius L:ℂ)‖/(L.absNorm:ℝ))*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
    rw [Finset.sum_mul,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hμ:(UniqueFactorizationMonoid.moebius L:ℂ)=0
    · simp only [hμ,norm_zero,zero_mul,zero_div,ite_self]
    · by_cases hl:live L
      · have ha:active L:=⟨hl,hμ⟩
        simp only [F₁,F₂,ite_eq_left ha,live,ite_eq_left hl]
        rw [CenteredMomentSecondHarmonicBudget.paired_divisor J₁ J₂ t E₁ E₂ _ (Nat.cast_nonneg _)]
        ring
      · have ha:¬active L:=fun hh=>hl hh.1
        simp only [F₂,ite_eq_right ha,live,ite_eq_right hl,windowBudget,Real.sqrt_zero,zero_mul,mul_zero]
  exact hh.trans_eq (by rw [he]; ring)

theorem actual_supported_annular_harmonic (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ)
    (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ Cbound : ℝ, 0<Cbound ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ Hsource : ℝ,(∀I,s.beta I≠0→(I.absNorm:ℝ)≤Hsource) →
    Hsource/(D.absNorm:ℝ)≤Z^B → ∀ E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₁/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), (L.absNorm:ℝ)≤Hsource/(D.absNorm:ℝ) → Squarefree L → ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (E₂/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*Z^δ*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
  obtain ⟨Cb,hCb,hbound⟩:=actual_supported_annular_block W decay J₁ J₂
  obtain ⟨Cm,hCm,hmass⟩:=supported_harmonic_mass B δ hB hδ
  refine ⟨(Cb+1)*Cm,mul_pos (by linarith) hCm,?_⟩
  filter_upwards [hmass] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n Hsource hβ hcap E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n Hsource hβ E₁ E₂ hE₁ hE₂ hleft hright
  have hm:=hZ.2 (divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
    (fun b=>Ideal.span {element C D hD.1 s.columns b})) D Hsource hcap
  have hW : 0≤windowBudget J₁ t E₁*windowBudget J₂ t E₂ :=
    mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)
  have hz : 0≤Z^δ := Real.rpow_nonneg ((zero_lt_one.trans hZ.1).le) _
  calc
    _ ≤ _ := hh
    _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*(Cm*Z^δ)*
        (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by
      gcongr
    _ ≤ _ := by
      have hc : Cb≤Cb+1 := by linarith
      calc
        _ = ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cb*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by ring
        _ ≤ ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*(Cb+1)*Cm*Z^δ*
          (windowBudget J₁ t E₁*windowBudget J₂ t E₂) := by gcongr
        _ = _ := by ring

end SevenEighths.CenteredMomentFirstDivisorCommonBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstErrorAllocationPower -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstErrorAllocationPower
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentFirstChildProfileControl
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma child_mass_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    mass (child s (Q^k) R B τ t)=mass s := by
  change (∏i:liveIndices B.val,s.M i.val)=∏i,s.M i
  rw [Finset.prod_coe_sort,prime_slots_live s Q hQ k hslot B]

lemma allocations_card (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) :
    Fintype.card (actualAllocations s.pools (Q^k))≤k+1 := by
  simpa only [Fintype.card_coe] using actual_amplification_allocations_card s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩)

theorem power_sum_eq (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)=
    Fintype.card (actualAllocations s.pools (Q^k))*
      (volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  simp_rw [child_volume s Q hQ k hslot,child_mass_eq s Q hQ k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

theorem power_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ) (α : ℝ) :
    (∑B:actualAllocations s.pools (Q^k),
      volume (child s (Q^k) R B (τ B) (t B))^α*mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(volume s/(Q.absNorm:ℝ)^k)^α*mass s^2 := by
  rw [power_sum_eq s Q hQ.ne_zero k hslot R τ t α]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) α)
  exact_mod_cast allocations_card s Q hQ k hslot

theorem budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    ((k+1:ℕ):ℝ)*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  simp_rw [child_volume s Q hQ.ne_zero k hslot,child_mass_eq s Q hQ.ne_zero k hslot]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs : 0≤∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j) :=
    Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _))
  have hc : (Fintype.card (actualAllocations s.pools (Q^k)):ℝ)≤k+1 := by
    exact_mod_cast allocations_card s Q hQ k hslot
  calc
    _≤((k:ℝ)+1)*((∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hs (sq_nonneg _))
    _=_ := by push_cast;ring

theorem error_budget_sum_le (s : Input ι) (Q : Ideal O) (hQ : Prime Q) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (τ : actualAllocations s.pools (Q^k)→Character)
    (t : actualAllocations s.pools (Q^k)→ℝ)
    (n : ℕ) (a α : Fin n→ℝ) (ha : ∀j,0≤a j) :
    (∑B:actualAllocations s.pools (Q^k),
      (∑j,a j*volume (child s (Q^k) R B (τ B) (t B))^(α j))*
        mass (child s (Q^k) R B (τ B) (t B))^2)≤
    8*(∑j,a j*(volume s/(Q.absNorm:ℝ)^k)^(α j))*mass s^2 := by
  apply (budget_sum_le s Q hQ k hslot R τ t n a α ha).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg (fun j _=>mul_nonneg (ha j)
      (Real.rpow_nonneg (div_nonneg (volume_pos s).le (pow_nonneg (Nat.cast_nonneg _) k)) _)))
  rcases hk with rfl|rfl|rfl <;> norm_num

end SevenEighths.CenteredMomentFirstErrorAllocationPower

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedPowerBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentFirstAmplifiedPowerBudget
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentSectorLocalization CenteredMomentOriginalChildEnergy
open CenteredMomentFirstScale
open CenteredMomentChildRows CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily

open CenteredMomentFirstAnnularInput CenteredMomentFirstErrorAllocationPower
theorem eventually_input_power_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ s : Input ι,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec xi reserve hsigma hloss hM hb hgap hC hxi hreserve,
    eventually_dyadic_amplification.{0} M H hH Sbad hbad sigma loss BR Bs Mmax b eta
      hsigma hloss hM hgap] with Z hz hpz
  obtain ⟨hZ,hP,hcard,hfam⟩:=hz
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hpz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η
  obtain ⟨τ,hN,henergy⟩:=hfam η
  refine ⟨τ,hN,?_⟩
  intro s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec hK hX hsec
    H0 hH0 houter hcap amain aerror α haerr hmain herr
  have he:=henergy s hsη hsupp z hz hlen R seed hR0 hs0 hR hs d cLog I J E hE K X Tsec
    hK hX hsec H0 hH0 houter hcap
  apply he.trans
  have hpweight:0≤56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ):=by positivity
  have hmweight:0≤(Mmax+2*sigma)/(sigma/6):=by positivity
  have herror: ∀p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∀i:Fin 3,
      (∑χ:RayCharacter,∑B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          R seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
            (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1)))≤
      (errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
        (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
          CenteredMomentFirstChildProfileControl.mass s^2:=by
    intro p i
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) p.val p.property
    have hcop:∀j,∀Q∈(activeInput s).slots j,IsCoprime (Ideal.span {p.val}) Q:=by
      exact original_slot_coprime (original s R seed).active Z sigma b eta hZ.le hb hsep z hz hlen
        hsupp (original s R seed).active_slot
        (fun j Q hQ=>s.prime j Q ((original s R seed).active_subset _ hQ))
        (Ideal.span {p.val}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hq:Prime (Ideal.span {p.val}):=(hdata _ hd.2.1).1
    calc
      _≤∑χ:RayCharacter,((errorIndex i+1+1:ℕ):ℝ)*
          (∑j,aerror p i χ j*(volume (activeInput s)/
            ((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
              CenteredMomentFirstChildProfileControl.mass (activeInput s)^2:=by
        apply Finset.sum_le_sum
        intro χ hχ
        apply le_trans (Finset.sum_le_sum (fun B _=>herr p i χ B))
        exact budget_sum_le (activeInput s) (Ideal.span {p.val}) hq (errorIndex i+1) hcop R
          (fun _=>τ p i χ) (fun _=>s.t) 4 (aerror p i χ) α (haerr p i χ)
      _=_:=by
        simp only [CenteredMomentFirstChildProfileControl.mass,activeInput]
        push_cast
        rw [←Finset.sum_mul,←Finset.mul_sum]
        congr 2
        ring
  calc
    _≤(56/((primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          ((∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)+
          ∑p:elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))),∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
            ((errorIndex i+2:ℝ)*(∑χ:RayCharacter,∑j,aerror p i χ j*
              (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j))*
                CenteredMomentFirstChildProfileControl.mass s^2)):=by
      apply mul_le_mul_of_nonneg_left _ hpweight
      apply add_le_add (mul_le_mul_of_nonneg_left hmain hmweight)
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (herror p i)
        (mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i)))
    _=_:=by
      simp only [←mul_assoc,←Finset.sum_mul]
      ring

theorem eventually_original_subsets_power_amplification {Ω : Type*} [Fintype Ω]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ η : Character,
      ∃ τ : (A:Finset Ω) → (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (A:Finset Ω) (p : elementPool P) i χ,(τ A p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ A:Finset Ω,∀ s : Input A,s.η=η →
          (∀ i,Function.support (s.W i)⊆Set.Iic b) →
          ∀ (z : A→ℝ),(∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
          ∀ (R seed : Ideal O),R≠0 → seed≠0 → (R.absNorm:ℝ)≤Z^BR → (seed.absNorm:ℝ)≤Z^Bs →
          ∀ (d cLog : ℝ),∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (H0 : ℝ),0<H0 → H0≤4*frequencyRadius Tsec Z xi → 8*H0≤Z^Mmax →
          ∀ (amain:Fin 4→ℝ) (aerror:elementPool P→Fin 3→RayCharacter→Fin 4→ℝ)
            (α:Fin 4→ℝ), (∀p i χ j,0≤aerror p i χ j)→
          (normalizedGaussSource s R seed ballProfile
            (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
              (frequencyLoss Z (32*Csec) xi) reserve)≤
                (∑j,amain j*(volume s)^(α j))*CenteredMomentFirstChildProfileControl.mass s^2)→
          (∀p:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
            ∀B:actualAllocations (activeInput s).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
                R seed B (τ A p i χ) s.t ballProfile
                (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                  (frequencyLoss Z (32*Csec) xi) reserve p (errorIndex i+1))≤
                (∑j,aerror p i χ j*(volume (child (activeInput s)
                  ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t))^(α j))*
                  CenteredMomentFirstChildProfileControl.mass (child (activeInput s)
                    ((Ideal.span {p.val})^(errorIndex i+1)) R B (τ A p i χ) s.t)^2)→
          normalizedGaussSource s R seed CenteredMomentFirstAnnularMajorant.profile H0≤
            (56/(P.card:ℝ))*CenteredMomentFirstChildProfileControl.mass s^2*
              (((Mmax+2*sigma)/(sigma/6))*(∑j,amain j*(volume s)^(α j))+
                ∑p:elementPool P,∑i:Fin 3,
                  (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*(errorIndex i+2:ℝ)*
                    ∑χ:RayCharacter,∑j,aerror p i χ j*
                      (volume s/((Ideal.span {p.val}).absNorm:ℝ)^(errorIndex i+1))^(α j)) := by
  have hall:=Filter.eventually_all.mpr (fun A:Finset Ω=>
    eventually_input_power_amplification (ι:=A) M H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec xi reserve
      hsigma hloss hM hb hgap hC hxi hreserve)
  filter_upwards [hall] with Z hz
  have hbase:=hz (∅:Finset Ω)
  refine ⟨hbase.1,hbase.2.1,hbase.2.2.1,?_⟩
  intro η
  have hf (A:Finset Ω):=(hz A).2.2.2 η
  choose τ hN he using hf
  exact ⟨τ,hN,he⟩

end SevenEighths.CenteredMomentFirstAmplifiedPowerBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstReferenceBlock -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentGaussEnergy
open CenteredMomentFirstDivisorSupport CenteredMomentChildAssembly
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSecondWindowBudget
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentMobiusRegroup
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalAnnularCommonBound
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedWindow CenteredMomentFirstWindowBudgets
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O

theorem actual_reference_block (W:𝓢(ℝ,ℂ)) (decay J₁ J₂:ℕ)
    (B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃Cb:ℝ,0<Cb ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type*}[Fintype ι][DecidableEq ι],∀s:Input ι,∀R seed:Ideal O,
    ∀a₁ a₂:ℝ,0<a₁→0<a₂→
    (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀E:Finset (CommonIndex C D),∀ξ₁ ξ₂:RayCharacter,
    ∀F:FixedPair s.η C D hC E ξ₁ ξ₂,∀rows:Finset O,∀K:ℝ,0<K→∀n:Fin 4→ℤ,
    sourceRadius s/(D.absNorm:ℝ)≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
    let V:=volume s;
    let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z);
    let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z);
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) C hC (fixedPair s.η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 (original s R seed).columns))
      (fun b=>Ideal.span {element C D hD.1 (original s R seed).columns b}),
      (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) D hD (fixedPair s.η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))→
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay*
      ‖block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
        (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
        K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))‖/V≤
      Cb*Z^δ*(‖inactiveWeight C D E‖*(Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*
        fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
      (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j)):=by
  obtain ⟨Cb,hCb,hev⟩:=CenteredMomentFirstDivisorCommonBound.actual_supported_annular_harmonic
    W decay J₁ J₂ B δ hB hδ
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ C D hC hD hCD E ξ₁ ξ₂ F rows K hK n hcap EL ER hEL hER
    V refL refR hleft hright
  have hz:0≤Z:=zero_le_one.trans hZ.1.le
  have hcb:0≤Cb:=hCb.le
  have hf:0≤fixedPresentationCost:=fixedPresentationCost_pos.le
  have hprodlo:0≤∏i,s.lo i:=Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)
  have hV:0<V:=volume_pos s
  have hRL:0≤ refL:=by dsimp [refL]; positivity
  have hRR:0≤ refR:=by dsimp [refR]; positivity
  have hLE:∀i:Fin 4,0≤ refL*EL i:=fun i=>mul_nonneg hRL (hEL i)
  have hRE:∀i:Fin 4,0≤ refR*ER i:=fun i=>mul_nonneg hRR (hER i)
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  have hb:=hZ.2 s.η (original s R seed) s.t C D hC hD hCD E rows K hK n
    (sourceRadius s) (fun I hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)
    hcap (∑i,refL*EL i) (∑i,refR*ER i)
    (Finset.sum_nonneg (fun i _=>hLE i)) (Finset.sum_nonneg (fun i _=>hRE i)) hleft hright
  have hw:=windowBudget_pair_sum Finset.univ Finset.univ (fun i=>refL*EL i) (fun i=>refR*ER i)
    (fun i _=>hLE i) (fun i _=>hRE i) J₁ J₂ s.t
  have hb':=hb.trans (mul_le_mul_of_nonneg_left hw (by positivity))
  by_cases hn:block s.η (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns
      (original s R seed).beta C D hC hD E rows W (fun _=>logAnnulus)
      K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))=0
  · simp only [hn,norm_zero,mul_zero,zero_div]
    have he:0≤∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (EL i)*windowBudget J₂ s.t (ER j):=
      Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>mul_nonneg
        (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
    positivity
  · have href:=original_four_budget_reference s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
      (fixedBadMask*idealGenerator R) 1 s.t (original s R seed).columns C D hC hD hCD E
      ξ₁ ξ₂ F rows W (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
      (dyadicScale (n 2)) (dyadicScale (n 3)) (Real.log 4) Z EL ER J₁ J₂ s.t hK
      (dyadicScale_pos _) (dyadicScale_pos _) hZ.1 hEL hER
      (fun _ x hx=>by
        have hh:=logAnnulus_support hx
        exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩) hn
    have hh:=div_le_div_of_nonneg_right hb' hV.le
    have hscale:0≤Cb*Z^δ:=by positivity
    have hmul:=mul_le_mul_of_nonneg_left href hscale
    calc
      _ ≤ _ := hh
      _ = Cb*Z^δ*(‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖/V*
          (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ s.t (refL*EL i)*windowBudget J₂ s.t (refR*ER j))) := by ring
      _ ≤ _ := by convert hmul using 1 <;> (try dsimp [refL,refR,V,volume,CenteredMomentExceptionalAmplitudePair.volume]) ; ring

end SevenEighths.CenteredMomentFirstReferenceBlock

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCanonicalPair -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalCanonicalPair
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow CenteredMomentExceptionalWindowHeight
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentCommonExceptionalCanonicalWindow CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=actual_canonical_common_window lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentSecondExceptionalCanonicalPair

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalOriginalBlock -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalOriginalBlock
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound CenteredMomentSecondExceptionalCanonicalPair
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤ sourceBudget s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0< rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,hJ⟩:=actual_canonical_original_pair lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentSecondExceptionalOriginalBlock

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalBudget
open HeckeFamily CanonicalQuadraticSieve CompletedGauss UniqueFactorizationMonoid
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondPhysicalLedger
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalSourceShell CenteredMomentCommonExceptionalCost
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentForcing CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma profileMass_self (s:Input ι)(p:Tests)(J:ℕ):
    profileMass s.toData s.toData p p J=
      p.heightWeight s.t^(2*J)*slotControl s.toData^2*volume s.toData:=by
  have hs:volume s.toData=Real.sqrt (volume s.toData)*Real.sqrt (volume s.toData):=by
    nlinarith [Real.sq_sqrt (volume_pos s.toData).le]
  unfold profileMass
  rw [show 2*J=J+J by omega,pow_add]
  conv_rhs => rw [hs]
  ring

lemma count_power (Z h f e:ℝ)(hZ:1<Z)(hh:0<h)(hf:0<f):
    Z^((Real.logb Z h-4*Real.logb Z f)/6+e)=
      h^(1/6:ℝ)/f^(2/3:ℝ)*Z^e:=by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show (Real.logb Z h-4*Real.logb Z f)/6+e=
    Real.logb Z h*(1/6)-Real.logb Z f*(2/3)+e by ring,
    Real.rpow_add hz,Real.rpow_sub hz,Real.rpow_mul hz.le,Real.rpow_mul hz.le,
    Real.rpow_logb hz (ne_of_gt hZ) hh,Real.rpow_logb hz (ne_of_gt hZ) hf]

def profileFactor (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card)*(1+2*Real.pi)^(4*J)*
    p.heightWeight s.t^(2*J)*slotControl s.toData^2*frozenProfile s^2*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

omit [DecidableEq ι] in
lemma profileFactor_nonneg (s:Input ι)(p:Tests)(J:ℕ)(Q:Ideal O)(K:ℝ)(hK:0≤K):
    0≤profileFactor s p J Q K:=by
  unfold profileFactor
  have hp:0≤p.heightWeight s.t:=by unfold Tests.heightWeight; positivity
  positivity

lemma sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(U:Finset (CommonIndex C D))(K Z ε δ θ r h:ℝ)
    (hZ:1<Z)(hh:0<h):
    sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z h)=
      profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      (h^(1/6:ℝ)/(forcingNorm C D U)^(2/3:ℝ)*volume s.toData^2/
        ((C.absNorm:ℝ)*D.absNorm)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold sourceBudget
  simp only [forcingNorm] at hf ⊢
  rw [Real.one_rpow, mul_one]
  rw [show (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+2*ε+δ-
      max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0=
      (Real.logb Z h-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
        (2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0) by ring,
    count_power Z h (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val) (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ) _ hZ hh hf,profileMass_self]
  unfold profileFactor
  ring

theorem central_sourceBudget_exact (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)
    (hC:Supported C)(_hD:Supported D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys:ℝ)(n:Fin 4→ℤ)(hZ:1<Z):
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))=
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      centralPhysicalCost C D U Kphys (volume s.toData) n/
      ((Ideal.absNorm (∏P:CommonIndex C D,P.val):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  have hp:=common_product_pos C D hC Finset.univ
  have hpow:(forcingNorm C D U)^(2/3:ℝ)=
      (forcingNorm C D U)^(1/3:ℝ)*(forcingNorm C D U)^(1/3:ℝ):=by
    rw [←Real.rpow_add hf];congr 1;ring
  rw [sourceBudget_exact s p J Q C D hC U K Z ε δ θ r _ hZ (dyadicScale_pos _),hpow]
  unfold centralPhysicalCost
  field_simp

end SevenEighths.CenteredMomentSecondExceptionalBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalOriginalBlock CenteredMomentSecondExceptionalBudget
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

lemma column_power_saving (Z c d θ:ℝ) (hZ:1<Z) (hc:1≤ c) (hd:1≤d) (hθ:θ≤1/3) :
    (c*d)^θ*Z^(-(Real.logb Z c+Real.logb Z d)/3)≤1 := by
  have hc0:0<c:=zero_lt_one.trans_le hc
  have hd0:0<d:=zero_lt_one.trans_le hd
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:-(Real.logb Z c+Real.logb Z d)/3=Real.logb Z (c*d)*(-1/3):=by
    rw [Real.logb_mul hc0.ne' hd0.ne'];ring
  rw [he,Real.rpow_mul hz.le,Real.rpow_logb hz (ne_of_gt hZ) (mul_pos hc0 hd0),
    ←Real.rpow_add (mul_pos hc0 hd0)]
  have hcd:1≤ c*d:=by nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hcd (by linarith : θ+ -1/3≤0)).trans_eq
    (Real.rpow_zero _)

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

theorem original_budget_physical_saving_full
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

lemma column_cap_ledger (c d r:ℝ)(hc:0≤ c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  have hmin:0≤ min c d:=le_min hc hd
  have hc':min c d≤ c:=min_le_left _ _
  have hd':min c d≤d:=min_le_right _ _
  by_cases hr:0≤ r
  · rw [max_eq_left hr]
    by_cases hm:r≤ min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤ r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤ max (r-min c d) 0:=le_max_right _ _
    linarith

theorem original_budget_physical_saving
    (s:Input ι)(p:Tests)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)(hθ:θ≤1/3)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  have hcol:=column_power_saving Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ hZ hc hd hθ
  let A:ℝ:=profileFactor s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hA:0≤A:=mul_nonneg (profileFactor_nonneg s p J Q K hK) (Real.rpow_nonneg (by linarith) _)
  have hv:=volume_pos s.toData
  have hE:0≤E:=by dsimp [E];positivity
  have hnum:A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n≤A*E:=by
    calc
      _≤A*((C.absNorm:ℝ)*D.absNorm)^θ*
          (E*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
        exact mul_le_mul_of_nonneg_left hcost (mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
      _=A*E*(((C.absNorm:ℝ)*D.absNorm)^θ*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by ring
      _≤A*E*1:=mul_le_mul_of_nonneg_left hcol (mul_nonneg hA hE)
      _=A*E:=mul_one _
  rw [central_sourceBudget_exact s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*((C.absNorm:ℝ)*D.absNorm)^θ*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right hnum (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentSecondExceptionalPhysicalSaving

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaving -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve UniqueFactorizationMonoid IdealMobiusDivisorSum
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalPhysicalSaving
open CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalAllowance
open CenteredMomentRankinRadical
local notation "O"=>HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem original_budget_physical_saving_full
    {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Kphys a:ℝ)(n:Fin 4→ℤ)(hK:0≤K)(hZ:1<Z)
    (hKphys:0<Kphys)(ha:0<a)
    (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (R:ℝ)(rows:Finset O)(hrows:∀z∈rows,z≠0)(W:𝓢(ℝ,ℂ))
    (hlower:∀I:Ideal O,β I≠0→a*volume s.toData≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W Kphys n≠0) :
    (1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    profileFactor Sprofile s p J Q K*
      Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*
      ((volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ))*
      Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
      (Ideal.absNorm (commonRadical C D):ℝ) := by
  have hp:0<(Ideal.absNorm (commonRadical C D):ℝ):=by
    rw [←common_ideal_product]
    exact common_product_pos C D hC Finset.univ
  have hf:=forcingNorm_ge_one C D hC U
  have hfp:1≤(forcingNorm C D U)^(1/3:ℝ):=Real.one_le_rpow hf (by norm_num)
  have hcost:=original_block_physical_cost η t S β C D hC hD hCD U R rows hrows W Kphys n
    hKphys (volume s.toData) a Z (volume_pos s.toData) ha hZ hlower hne
  let A:ℝ:=profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ
  let E:ℝ:=(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
    Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)
  have hA:0≤A:=mul_nonneg
    (mul_nonneg (profileFactor_nonneg Sprofile s p J Q K hK) (Real.rpow_nonneg (by linarith) _))
    (Real.rpow_nonneg (by positivity) _)
  have hv:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hE:0≤E:=by dsimp [E];positivity
  rw [central_sourceBudget_exact Sprofile s p J Q C D hC hD U K Z ε δ θ r Kphys n hZ,
    common_ideal_product]
  change A*centralPhysicalCost C D U Kphys (volume s.toData) n/
    ((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ))≤_
  calc
    _≤A*E/((Ideal.absNorm (commonRadical C D):ℝ)*(forcingNorm C D U)^(1/3:ℝ)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hA)
        (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _))
    _≤A*E/(Ideal.absNorm (commonRadical C D):ℝ):=by
      apply div_le_div_of_nonneg_left (mul_nonneg hA hE) hp
      nlinarith
    _= _:=by dsimp [A,E];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQSaved -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤_:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 ; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalSaved -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_saved_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)*
          Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_dyadic_exceptional_block wlo whi hwlo hwhi lo hi W 1 ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  let F:=physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n
  by_cases hne:F=0
  · change ‖F‖/_≤_
    rw [hne,norm_zero,zero_div]
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hz:0≤Z:=(zero_lt_one.trans hZ.1).le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    positivity
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD R Kphys hKphys n
  let rK:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hd:0<1+rK:=by
    have h0:=dyadicScale_pos (n 0)
    have h1:=dyadicScale_pos (n 1)
    have h2:=dyadicScale_pos (n 2)
    have h3:=dyadicScale_pos (n 3)
    dsimp [rK]; positivity
  have hp':‖F‖≤outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK):=by
    apply (le_div_iff₀ hd).mpr
    simpa only [pow_one,mul_comm] using hp
  have hs:=original_budget_physical_saving_full Sprofile s p J Q C D hC hD hCD U K Z ε δ θ r Kphys a n
    hK.le hZ.1 hKphys ha s.η s.t S β R rows hn W hlower hne
  calc
    _≤(outerScalar C D Kphys n*normalizer C D U*
      (Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1))))/(1+rK))/
      volume s.toData:=div_le_div_of_nonneg_right hp' (volume_pos s.toData).le
    _=Ck*((1/volume s.toData)*outerScalar C D Kphys n*normalizer C D U*
      sourceBudget Sprofile s p J Q C D U K Z ε δ θ r 1 (Real.logb Z (dyadicScale (n 1)))/(1+rK)):=by ring
    _≤_:=by
      convert mul_le_mul_of_nonneg_left hs hCk using 1 ; ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCommonSaving -/

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSecondExceptionalCommonSaving
open CenteredMomentSecondExceptionalPhysicalSaving
lemma common_weight_bound (Z c d θ B ε δ r:ℝ)(hZ:1<Z)(hc:1≤ c)(hd:1≤d)
    (hθ:0≤θ)(hC:c≤Z^B)(hD:d≤Z^B):
    Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*(c*d)^θ*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)≤
        Z^(2*ε+δ+2*B*θ-2*max r 0/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hcd:0≤ c*d:=mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hd)
  have hpow:(c*d)^θ≤Z^(2*B*θ):=by
    calc
      _≤(Z^B*Z^B)^θ:=Real.rpow_le_rpow hcd
        (mul_le_mul hC hD (zero_le_one.trans hd) (Real.rpow_nonneg hz.le _)) hθ
      _=Z^(2*B*θ):=by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1;ring
  have hl:=column_cap_ledger (Real.logb Z c) (Real.logb Z d) r
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  calc
    _≤Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*Z^(2*B*θ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3):=by gcongr
    _=Z^((2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)+2*B*θ-
      (Real.logb Z c+Real.logb Z d)/3):=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1;ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end SevenEighths.CenteredMomentSecondExceptionalCommonSaving

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalUniform -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_uniform_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      (C.absNorm:ℝ)≤Z^B → (D.absNorm:ℝ)≤Z^B → primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀a:ℝ,0<a → (∀I:Ideal O,β I≠0→a*volume s.toData≤(I.absNorm:ℝ)) →
      ∀(R Kphys:ℝ),0<Kphys → ∀n:Fin 4→ℤ,
      ‖physicalBlock s.η s.t S β C D hC hD U R rows W Kphys n‖/volume s.toData≤
        Ck*(profileFactor Sprofile s p J Q K*
          Z^(2*ε+δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
          (Ideal.absNorm (commonRadical C D):ℝ)) :=by
  obtain ⟨J,Sprofile,hSprofile,Ck,hCk,hkernel⟩:=actual_saved_exceptional_block wlo whi hwlo hwhi lo hi W ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hkernel Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hNC hND hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hs:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex H hβ hHD a ha hlower R Kphys hKphys n
  have hc:1≤(C.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hb:=common_weight_bound Z (C.absNorm:ℝ) (D.absNorm:ℝ) θ B ε δ r hZ.1 hc hd hθ.le hNC hND
  let F:=Ck*profileFactor Sprofile s p J Q K*(volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)/
    (Ideal.absNorm (commonRadical C D):ℝ)
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:0≤volume s.toData:=(volume_pos s.toData).le
    dsimp only [F]
    positivity
  apply hs.trans
  calc
    _=F*(Z^(2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
      ((C.absNorm:ℝ)*D.absNorm)^θ*Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3)):=by
      dsimp only [F];ring
    _≤F*Z^(2*ε+δ+2*B*θ-2*max r 0/3):=mul_le_mul_of_nonneg_left hb hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondExceptionalSourceCaps -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace SevenEighths.CenteredMomentSecondExceptionalSourceCaps
open HeckeFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondExceptionalFamilyUniform
local notation "O" => HeckeFamily.O

theorem eventually_source_caps :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(η:Character)(R0:Ideal O)(H R B:ℝ),
      0≤B → 0≤H → 0≤R → (η.modulus.absNorm:ℝ)≤Z^B →
      (R0.absNorm:ℝ)≤Z^B → H≤Z^B → R≤Z^B →
      H≤Z^(5*B+1) ∧
      (expandedFactor η:ℝ)*R0.absNorm*H^2*(4*R)≤Z^(5*B+1) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (4*fixedExpandedCost)] with Z hZ hfixed
  refine ⟨hZ,?_⟩
  intro η R0 H R B hB hH hR hη hR0 hHN hRN
  have hz:0<Z:=zero_lt_one.trans hZ
  have hH2:H^2≤(Z^B)^2:=pow_le_pow_left₀ hH hHN 2
  have hbig:B≤5*B+1:=by linarith
  refine ⟨hHN.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hbig),?_⟩
  rw [expandedFactor_real]
  calc
    _=(4*fixedExpandedCost)*(η.modulus.absNorm:ℝ)*R0.absNorm*H^2*R:=by ring
    _≤Z*(Z^B)*(Z^B)*(Z^B)^2*(Z^B):=by gcongr
    _=Z^(5*B+1):=by
      rw [show (Z^B)^2=Z^B*Z^B by ring]
      calc
        _=Z^(1:ℝ)*Z^B*Z^B*(Z^B*Z^B)*Z^B:=by rw [Real.rpow_one]
        _=Z^(5*B+1):=by
          repeat rw [←Real.rpow_add hz]
          congr 1
          ring

end SevenEighths.CenteredMomentSecondExceptionalSourceCaps

end

end OAI

end

