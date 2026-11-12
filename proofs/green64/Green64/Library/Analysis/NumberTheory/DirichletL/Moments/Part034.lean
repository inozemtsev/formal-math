module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part018
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part033
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part025
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part030
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part028
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part013
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part032

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part034

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstSourceReduction -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSourceReduction
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputFirstRemainder CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy
open CenteredMomentActiveSource (activeSource)
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def physicalMass (s:Input ι)(R seed:Ideal O)(m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ:=
  let β:=coefficient s R seed
  let T:=activeSource (finiteColumns (Fintype.piFinset s.pools)) β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s R seed m A s.t T p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

 theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K‖/volume s.toData≤
      physicalMass s R seed m A Φ K Z ξ/volume s.toData+
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_norm s R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (volume s.toData) Z ξ hK
  change ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
      (volume s.toData) Z ξ‖≤physicalMass s R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K)
    (CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K (volume s.toData) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (volume_pos s).le
  linarith

end SevenEighths.CenteredMomentFirstSourceReduction

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalActiveDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalActiveDictionary
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
open CenteredMomentFirstPhysicalSource CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

theorem columns_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β : Ideal O→ℂ) :
    columns C D hD (activeSource S β)=
      (columns C D hD S).filter (fun I=>β (D*I)≠0) := by
  ext I
  simp only [columns,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

theorem element_value (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (I : columns C D hD S) :
    element C D hD S I=CompletedGauss.primaryGenerator (I:Ideal O) := rfl

theorem column_sum_active (C D : Ideal O) (hD : D≠0) (S : Finset (Ideal O))
    (β f : Ideal O→ℂ) (hf : ∀I,β (D*I)=0→f I=0) :
    (∑I∈columns C D hD (activeSource S β),f I)=∑I∈columns C D hD S,f I := by
  rw [columns_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : β (D*I)=0
  · simp only [hi,ne_eq,not_true_eq_false,ite_false,hf I hi]
  · simp only [hi,ne_eq,not_false_eq_true,ite_true]

theorem column_pair_sum_active (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (f : Ideal O→Ideal O→ℂ)
    (hl : ∀I J,β (C*I)=0→f I J=0) (hr : ∀I J,β (D*J)=0→f I J=0) :
    (∑I∈columns C C hC (activeSource S β),∑J∈columns C D hD (activeSource S β),f I J)=
      ∑I∈columns C C hC S,∑J∈columns C D hD S,f I J := by
  simp_rw [column_sum_active C D hD S β _ (fun J h=>hr _ J h)]
  apply column_sum_active C C hC S β
  intro I hi
  exact Finset.sum_eq_zero (fun J hJ=>hl I J hi)

lemma primary_supported (I : Ideal O) (hI : Supported I) :
    Supported (Ideal.span {CompletedGauss.primaryGenerator I}) := by
  rw [primary_span_supported I hI]
  exact hI

def physicalTerm (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) : ℂ :=
  if hI : Supported I then if hJ : Supported J then
    let na:=CompletedGauss.primaryGenerator I
    let nb:=CompletedGauss.primaryGenerator J
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    if IsCoprime I J then
      (tripleRow na nb r (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) e *
      ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
      tripleFourier na nb r
        (supported_element_ne_zero _ (primary_supported I hI))
        (supported_element_ne_zero _ (primary_supported J hJ))
        (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (primary_supported I hI))
        (supportedModulusCharacter nb (primary_supported J hJ))⁻¹ (activeFunction C D hC) h)*
      (coefficient η m A t β C I*star (coefficient η m A t β D J))*
      windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
        (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
      EisensteinSchwartzPoisson.paperRadialFourier W
        (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
    else 0
  else 0 else 0

theorem physicalTerm_zero_left (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hi : β (C*I)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hi,zero_mul,mul_zero]
  split_ifs <;> rfl

theorem physicalTerm_zero_right (η : Character) (m A : O) (t : ℝ) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (h : O) (I J : Ideal O) (hj : β (D*J)=0) :
    physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J=0 := by
  simp only [physicalTerm,coefficient,hj,zero_mul,star_zero,mul_zero]
  split_ifs <;> rfl

theorem block_eq_ideal_sums (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      inactiveWeight C D E * ∑h∈rows,
        ∑I∈columns C C hC.1 S,∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
  unfold block
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _=∑I:columns C C hC.1 S,∑J:columns C D hD.1 S,
        physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [physicalTerm,dite_eq_left (column_supported C C hC.1 S I),
        dite_eq_left (column_supported C D hD.1 S J),element]
      rfl
    _=_ := by
      simp_rw [Finset.sum_coe_sort]
      exact Finset.sum_coe_sort (columns C C hC.1 S)
        (fun I=>∑J∈columns C D hD.1 S,
          physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J)

theorem block_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  rw [block_eq_ideal_sums,block_eq_ideal_sums]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact column_pair_sum_active C D hC.1 hD.1 S β
    (physicalTerm η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h)
    (fun I J hi=>physicalTerm_zero_left η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hi)
    (fun I J hj=>physicalTerm_zero_right η m A t β C D hC E W V K K₀ H₀ A₀ B₀ h I J hj)

theorem block_active_ne_zero_iff (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block η m A t (activeSource S β) β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 ↔
      block η m A t S β C D hC hD E rows W V K K₀ H₀ A₀ B₀≠0 := by
  rw [block_active]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _
open CenteredMomentCommonRadialData CenteredMomentFirstRetainedNorm
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentLogDyadic

theorem original_dyadic_block_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    block s.η m A t (activeSource S β) β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))=
    block s.η m A t S β C D hC hD E rows W
      (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  apply block_active

theorem original_sector_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sector s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sector
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  apply block_active

theorem original_sectorMass_active (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t
        (activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed))
        C D hC hD W K X Z ξ=
      sectorMass s R seed m A t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_active]

theorem original_retained_full_sectorMass [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ := by
  dsimp only
  apply (original_retained_norm s R seed hz₁ hz₂ m A t S W K X Z ξ hK).trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ W K X Z ξ

theorem active_sectorMass_sum (s : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    let T:=activeSource S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t T p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ)=
    ∑p:commonLabels (supportedColumns T) (supportedColumns T),
      sectorMass s R seed m A t S p.val.1 p.val.2
        (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K X Z ξ := by
  dsimp only
  apply Finset.sum_congr rfl
  intro p hp
  exact original_sectorMass_active s R seed m A t S _ _ _ _ Φ K X Z ξ

theorem physicalMass_full_source [DecidableEq ι] (s : Input ι) (R seed : Ideal O)
    (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ := by
  exact active_sectorMass_sum s R seed m A s.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)) Φ K
    (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ

theorem normalized_physicalMass_full_source [DecidableEq ι] (s : Input ι)
    (R seed : Ideal O) (m A : O) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed m A Φ K Z ξ /
        CenteredMomentExceptionalAmplitudePair.volume s.toData=
      let S:=CenteredMomentSourceMass.finiteColumns (Fintype.piFinset s.pools)
      let β:=CenteredMomentOriginalCommonHarmonic.coefficient s R seed
      let T:=activeSource S β
      (∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s R seed m A s.t S p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
          (CenteredMomentExceptionalAmplitudePair.volume s.toData) Z ξ) /
        CenteredMomentExceptionalAmplitudePair.volume s.toData := by
  exact congrArg (fun x:ℝ=>x/CenteredMomentExceptionalAmplitudePair.volume s.toData)
    (physicalMass_full_source s R seed m A Φ K Z ξ)

end SevenEighths.CenteredMomentFirstPhysicalActiveDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalOriginalMask -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalOriginalMask
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstMaskedFamily CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonSupport
open CenteredMomentFirstRetainedNorm CenteredMomentFirstSourceReduction
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma original_coefficient (s : Input ι) (R seed C I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    CenteredMomentFirstPhysicalSource.coefficient s.η (fixedBadMask*idealGenerator R) 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I =
    CenteredMomentFirstPhysicalSource.coefficient s.η fixedBadMask 1 t
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) C I := by
  unfold CenteredMomentFirstPhysicalSource.coefficient
  by_cases h : CenteredMomentOriginalCommonHarmonic.coefficient s R seed (C*I)=0
  · simp [h]
  · have hc : IsCoprime I R :=
      (beta_coprime (original s R seed) (C*I) h).of_mul_left_right
    have hw := rowWeight_mask_factor s.η (idealGenerator R) I hI t
    change CenteredMomentHeckeExpansion.rowWeight s.η (fixedBadMask*idealGenerator R) 1 1 t I =
      idealMask (idealGenerator R) I * CenteredMomentHeckeExpansion.rowWeight s.η fixedBadMask 1 1 t I at hw
    rw [hw]
    simp only [idealMask, span_idealGenerator, hc, ite_true, one_mul]

omit [DecidableEq ι] in
theorem original_block (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (W : 𝓢(ℝ,ℂ))
    (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η (fixedBadMask*idealGenerator R) 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ =
    block s.η fixedBadMask 1 t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀ := by
  unfold block
  apply congrArg (fun z : ℂ => inactiveWeight C D E * z)
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [original_coefficient s R seed C a (column_supported C C hC.1 S a) t,
    original_coefficient s R seed D b (column_supported C D hD.1 S b) t]

omit [DecidableEq ι] in
lemma original_sector (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sector s R seed (fixedBadMask*idealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sector s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sector
  simp_rw [original_block]

omit [DecidableEq ι] in
lemma original_sectorMass (s : Input ι) (R seed : Ideal O) (t : ℝ)
    (S : Finset (Ideal O)) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed (fixedBadMask*idealGenerator R) 1 t S C D hC hD W K X Z ξ =
    sectorMass s R seed fixedBadMask 1 t S C D hC hD W K X Z ξ := by
  unfold sectorMass
  simp_rw [original_block]

omit [DecidableEq ι] in
theorem original_physicalMass (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
    physicalMass s R seed fixedBadMask 1 W K Z ξ := by
  unfold physicalMass
  simp_rw [original_sectorMass]

end SevenEighths.CenteredMomentFirstPhysicalOriginalMask

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalZeroRadius -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalZeroRadius
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstRetainedNorm
open CenteredMomentFirstSourceReduction CenteredMomentCommonSupport
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

omit [DecidableEq ι] in
lemma coefficient_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0) (I : Ideal O) :
    CenteredMomentOriginalCommonHarmonic.coefficient s R seed I=0 := by
  by_contra h
  obtain ⟨hI,hN⟩ := original_column_norm s R seed I h₁ h₂ h
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  linarith

omit [DecidableEq ι] in
lemma block_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ) :
    block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W V K K₀ H₀ A₀ B₀=0 := by
  simp [block,CenteredMomentFirstPhysicalSource.coefficient,coefficient_zero s R seed h₁ h₂ hH]

omit [DecidableEq ι] in
lemma sectorMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (t : ℝ) (S : Finset (Ideal O)) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) :
    sectorMass s R seed m A t S C D hC hD W K X Z ξ=0 := by
  unfold sectorMass
  simp only [block_zero s R seed h₁ h₂ hH,norm_zero,Finset.sum_const_zero]

omit [DecidableEq ι] in
theorem physicalMass_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (m A : O) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed m A W K Z ξ=0 := by
  unfold physicalMass
  simp only [sectorMass_zero s R seed h₁ h₂ hH,Finset.sum_const_zero]

omit [DecidableEq ι] in
theorem sourceGaussEnergy_zero (s : Input ι) (R seed : Ideal O)
    (h₁ : s.W₁ 0=0) (h₂ : s.W₂ 0=0) (hH : sourceRadius s≤0)
    (S : Finset (Ideal O)) (f : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed) f W K=0 := by
  simp [sourceGaussEnergy,gaussEnergy,gaussPolynomial,coefficient_zero s R seed h₁ h₂ hH]

end SevenEighths.CenteredMomentFirstPhysicalZeroRadius

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceSource
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstRetainedNorm
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstSourceReduction
open CenteredMomentFirstInactiveRadicalMass CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev SourceBlocks (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):=
  Blocks (effectiveScale p.val.1 p.val.2 E K) (localRadius s R seed K Z ξ p E)
    (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)

def originalBlock (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):ℂ:=
  block s.η (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    p.val.1 p.val.2
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).1
    (commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property).2 E
    (retainedRows (localRadius s R seed K Z ξ p E) 1) W (fun _=>logAnnulus)
    K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3))

def radicalWeight (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):ℝ:=
  CenteredMomentFirstInactiveRadicalMass.inactiveWeight p.val.1 p.val.2 E 0/
    ((commonRadical p.val.1 p.val.2).absNorm:ℝ)

omit [DecidableEq ι] in
lemma radicalWeight_nonneg (s:Input ι)(R seed:Ideal O)(p:Labels s R seed)
    (E:Finset (CommonIndex p.val.1 p.val.2)):0≤ radicalWeight s R seed p E:=
  div_nonneg (inactiveWeight_nonneg _ _ _ _) (Nat.cast_nonneg _)

lemma physicalMass_eq_sum (s:Input ι)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(K Z ξ:ℝ):
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ=
      ∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖:=by
  rw [physicalMass_full_source]
  rfl

theorem original_block_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀W:𝓢(ℝ,ℂ),∀K A:ℝ,0<K→0≤A→volume s.toData≤Z^B→K⁻¹≤Z^B→
    (∀p:Labels s R seed,∀E∈inactiveSubsets p.val.1 p.val.2,
      ∀n:SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E)→
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ/
      volume s.toData≤A*(C₀*Z^ε/(seed.absNorm:ℝ)) := by
  obtain ⟨Cd,hCd,hd⟩:=original_input_local_blocks_subpower hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cm,hCm,hm⟩:=actual_inactive_radical_mass (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ),eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hd hZ hfixed
  intro s R seed hs hs0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hblock
  have hZ1:1≤Z:=by linarith
  have hcap:=input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hZ1 hfixed hV
  have hmass:=hm Z hZ seed hs hs0
    (finiteColumns (Fintype.piFinset s.pools)) (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI=>original_column_mask s R seed I hI)
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2.trans hcap) 0 (le_refl _)
  have hf:∀p E,0≤ radicalWeight s R seed p E:=radicalWeight_nonneg s R seed
  have hsector (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈inactiveSubsets p.val.1 p.val.2):
      (∑n:SourceBlocks s R seed K Z ξ p E,‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData)≤
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E := by
    have hp:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hcard:=hd s hhi hb₁ hb₂ hH p.val.1 p.val.2 hp.1.1 hp.2.1 E K hK hV hKi
    change (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)≤Cd*Z^(ε/2) at hcard
    calc
      _≤∑_n:SourceBlocks s R seed K Z ξ p E,A*radicalWeight s R seed p E:=
        Finset.sum_le_sum (fun n _=>hblock p E hE n)
      _ = (Fintype.card (SourceBlocks s R seed K Z ξ p E):ℝ)*(A*radicalWeight s R seed p E) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (Cd*Z^(ε/2))*(A*radicalWeight s R seed p E) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (hf p E))
      _ = _ := (mul_assoc _ _ _).symm
  rw [physicalMass_eq_sum]
  simp only [Finset.sum_div]
  calc
    _≤∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        (Cd*Z^(ε/2)*A)*radicalWeight s R seed p E:=by
      apply Finset.sum_le_sum;intro p _
      exact Finset.sum_le_sum (fun E hE=>hsector p E hE)
    _=(Cd*Z^(ε/2)*A)*(∑p:Labels s R seed,∑E∈inactiveSubsets p.val.1 p.val.2,
        radicalWeight s R seed p E):=by simp_rw [←Finset.mul_sum]
    _≤(Cd*Z^(ε/2)*A)*(Cm*Z^(ε/2)/(seed.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _=_ := by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith : 0<Z)];congr 1;ring]
      ring

end SevenEighths.CenteredMomentFirstReferenceSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

universe u
namespace SevenEighths.CenteredMomentEnergyFirstAnnularAdmission
open HeckeFamily ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstExtractedLedger
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
lemma source_dyad_retained (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Retained (localRadius s R seed K Z ξ p E) (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  exact ((mem_retainedIndices _ _).mp hn).1

omit [DecidableEq ι] in
lemma source_dyad_gt_one (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):1<dyadicScale (n 1):=by
  have hn: (n 1:ℤ)∈retainedIndices (localRadius s R seed K Z ξ p E):=(n 1).property
  obtain ⟨q,hq,hweight⟩:=((mem_retainedIndices _ _).mp hn).2
  exact hq.trans_lt ((dyadicWeight_support (n 1)) hweight).2

omit [DecidableEq ι] in
lemma source_nominal_positive (s:Input ι)(R seed:Ideal O)(K:ℝ)(hK:0<K)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    0<firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData):=by
  have he:=Ideal.span_singleton_eq_bot.not.mpr
    (primeSubsetGenerator_ne_zero (fun P:CommonIndex p.val.1 p.val.2=>P.val) E)
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using he
  exact firstNominalScale_pos _ _ _ hE K _ hK (volume_pos s.toData)

omit [DecidableEq ι] in
lemma source_nominal_span (s:Input ι)(R seed:Ideal O)(K:ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2)):
    firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData)=
      firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (volume s.toData):=by rw [primeSubsetGenerator,span_idealGenerator]

def amplifierCap (A D ξcap:ℝ):ℝ:=3*max A D+ξcap/2+1

omit [DecidableEq ι] in
theorem source_amplifier_packet (A D ξcap Z:ℝ)(hZ:32≤Z)
    (s:Input ι)(R seed:Ideal O)(K ξ:ℝ)(hK:0<K)(hξ:ξ≤ξcap)
    (hV:volume s.toData≤Z^A)(hKi:K⁻¹≤Z^D)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
    0<Tsec ∧ 0<dyadicScale (n 1) ∧
      dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
      8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
      Tsec≤1*firstNominalScale p.val.1 p.val.2
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
        K (volume s.toData):=by
  have hz:1≤Z:=by linarith
  have hzpos:0<Z:=by linarith
  have hfreq:=retained_scale_le _ (n 1) (source_dyad_retained s R seed K Z ξ p E n)
  have hV':volume s.toData≤Z^(max A D):=hV.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _))
  have hKi':K⁻¹≤Z^(max A D):=hKi.trans
    (Real.rpow_le_rpow_of_exponent_le hz (le_max_right _ _))
  have hrad:=local_frequency_radius_cap p.val.1 p.val.2 E K (volume s.toData) Z
    (max A D) ξ hK (volume_pos s.toData).le hz hV' hKi'
  have hrad':localRadius s R seed K Z ξ p E≤Z^(3*max A D+ξcap/2):=by
    apply hrad.trans
    exact Real.rpow_le_rpow_of_exponent_le hz (by linarith)
  refine ⟨source_nominal_positive s R seed K hK p E,dyadicScale_pos _,hfreq,?_,?_⟩
  · calc
      _≤32*Z^(3*max A D+ξcap/2):=by linarith
      _≤Z*Z^(3*max A D+ξcap/2):=
        mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hzpos.le _)
      _=Z^(amplifierCap A D ξcap):=by
        unfold amplifierCap
        rw [Real.rpow_add_one hzpos.ne']
        ring
  · rw [one_mul]
    exact (source_nominal_span s R seed K p E).le

omit [DecidableEq ι] in
lemma source_frequency_ledger (s:Input ι)(R seed:Ideal O)(K Z ξ:ℝ)(hK:0<K)(hZ:1<Z)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
    (n:SourceBlocks s R seed K Z ξ p E):
    Real.logb Z (dyadicScale (n 1))≤
      Real.logb Z (firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData))+
        frequencyLoss Z 1 ξ:=by
  apply retained_first_dyad_enclosure _ Z 1 _ ξ hZ (by norm_num) _ (n 1)
    (source_dyad_retained s R seed K Z ξ p E n)
  rw [one_mul,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (source_nominal_positive s R seed K hK p E)]

theorem fixed_endpoint_radius (N:ℕ)(upper b₁ b₂ A Z:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂)(hZ:32≤Z)
    (hfixed:upper^N*b₁*b₂≤Z)
    (s:Input ι)(hN:Fintype.card ι≤N)
    (hhi:∀i,|s.hi i|≤upper)(hs₁:|s.b₁|≤b₁)(hs₂:|s.b₂|≤b₂)
    (hV:volume s.toData≤Z^A):sourceRadius s≤Z^(A+1):=by
  apply input_radius_cap (fun _:ι=>upper) b₁ b₂ A Z s hhi hs₁ hs₂ (by linarith) _ hV
  have hpow:upper^(Fintype.card ι)≤upper^N:=pow_le_pow_right₀ hu hN
  simpa only [Finset.prod_const,Finset.card_univ] using
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hb₁) hb₂).trans hfixed

theorem eventually_source_admission (N:ℕ)(upper b₁ b₂ A D ξcap:ℝ)
    (hu:1≤upper)(hb₁:0≤b₁)(hb₂:0≤b₂):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(α:Type u)[Fintype α][DecidableEq α],∀s:Input α,Fintype.card α≤N →
      (∀i,|s.hi i|≤upper) → |s.b₁|≤b₁ → |s.b₂|≤b₂ →
      ∀(R seed:Ideal O)(K ξ:ℝ),0<K → ξ≤ξcap →
      volume s.toData≤Z^A → K⁻¹≤Z^D →
      sourceRadius s≤Z^(A+1) ∧
      ∀(p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
        (n:SourceBlocks s R seed K Z ξ p E),
      let Tsec:=firstNominalScale p.val.1 p.val.2 (∏P∈E,P.val) K (volume s.toData);
      0<Tsec ∧ 1<dyadicScale (n 1) ∧
        dyadicScale (n 1)≤4*frequencyRadius Tsec Z ξ ∧
        8*dyadicScale (n 1)≤Z^(amplifierCap A D ξcap) ∧
        Tsec≤1*firstNominalScale p.val.1 p.val.2
          (Ideal.span {primeSubsetGenerator (fun P:CommonIndex p.val.1 p.val.2=>P.val) E})
          K (volume s.toData):=by
  filter_upwards [eventually_ge_atTop (32:ℝ),eventually_ge_atTop (upper^N*b₁*b₂)] with Z hZ hf
  refine ⟨by linarith,?_⟩
  intro α _ _ s hN hhi hs₁ hs₂ R seed K ξ hK hξ hV hKi
  refine ⟨fixed_endpoint_radius N upper b₁ b₂ A Z hu hb₁ hb₂ hZ hf s hN hhi hs₁ hs₂ hV,?_⟩
  intro p E n
  have hh:=source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi p E n
  exact ⟨hh.1,source_dyad_gt_one s R seed K Z ξ p E n,hh.2.2⟩

end SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstReferenceEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstReferenceEnergy
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceBlock
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy CenteredMomentChildAssembly
open CenteredMomentCommonSupport CenteredMomentMobiusRegroup CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

abbrev supported (s:Input ι)(R seed:Ideal O)(p:Labels s R seed):=
  commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property

def ColumnBounds (s:Input ι)(R seed:Ideal O)(Z:ℝ)(J₁ J₂:ℕ)(EL ER:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ):Prop:=
  let C:=p.val.1; let D:=p.val.2; let h:=supported s R seed p
  let F:=fixedPair s.η C D h.1 E 1 1
  let V:=volume s.toData
  let refL:=(F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)
  let refR:=(F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) C h.1 (fixedPair s.η C D h.1 E χ χ).left v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refL*EL i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₁)) ∧
  (∀L∈divisorPool (Finset.univ:Finset (columns C D h.2.1 (original s R seed).columns))
    (fun b=>Ideal.span {element C D h.2.1 (original s R seed).columns b}),
    (L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ)→Squarefree L→∀χ:RayCharacter,∀v:ℝ,
    (commonEnergy (original s R seed) D h.2 (fixedPair s.η C D h.1 E χ χ).right v L
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      ((∑i,refR*ER i)/(L.absNorm:ℝ))*(1+‖v‖)^(2*J₂))

def pairedBudget (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):ℝ:=
  ∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (EL i)*windowBudget J₂ t (ER j)
lemma pairedBudget_nonneg (J₁ J₂:ℕ)(t:ℝ)(EL ER:Fin 4→ℝ):0≤pairedBudget J₁ J₂ t EL ER:=
  Finset.sum_nonneg (fun _i _=>Finset.sum_nonneg (fun _j _=>mul_nonneg
    (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))

def sourceFactor (s:Input ι)(a₁ a₂ K:ℝ):ℝ:=
  (Real.exp (Real.log 4)/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm:ℝ)
omit [DecidableEq ι] in
lemma sourceFactor_nonneg (s:Input ι)(a₁ a₂ K:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)(hK:0<K):
    0≤ sourceFactor s a₁ a₂ K:=by
  have hlo:0<∏i,s.lo i:=Finset.prod_pos (fun i _=>s.lo_pos i)
  have hf:=fixedPresentationCost_pos
  unfold sourceFactor
  positivity

theorem actual_physical_mass (W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)(hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→
      ∀a₁ a₂ K:ℝ,0<a₁→0<a₂→0<K→
      (∀x,s.W₁ x≠0→a₁≤x)→(∀x,s.W₂ x≠0→a₂≤x)→
      volume s.toData≤Z^B→K⁻¹≤Z^B→∀EL ER:Fin 4→ℝ,(∀i,0≤EL i)→(∀i,0≤ER i)→
      (∀p:Labels s R seed,∀E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀n:SourceBlocks s R seed K Z ξ p E,
        CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n≠0→ ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val))→
      physicalMass s R seed fixedBadMask 1 W K Z ξ/volume s.toData≤
        C*Z^ε/(seed.absNorm:ℝ)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER:=by
  obtain ⟨Cs,hCs,hsum⟩:=original_block_sum hi b₁ b₂ B ξ (ε/2) hB hξ (by linarith)
  obtain ⟨Cb,hCb,hblock⟩:=actual_reference_block W 0 J₁ J₂ (B+1) (ε/2) (by linarith) (by linarith)
  refine ⟨Cs*Cb,mul_pos hCs hCb,?_⟩
  filter_upwards [hsum,hblock,eventually_ge_atTop ((∏i,hi i)*b₁*b₂)] with Z hsum hblock hfixed
  intro s R seed hseed hseed0 hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hs₁ hs₂ hV hKi EL ER hEL hER hcol
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hh:=hs₁ 0 hn;linarith
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hh:=hs₂ 0 hn;linarith
  by_cases hH:0<sourceRadius s
  case neg =>
    rw [CenteredMomentFirstPhysicalZeroRadius.physicalMass_zero s R seed hz₁ hz₂ (le_of_not_gt hH)]
    simp only [zero_div]
    have hsF:=sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
    have hsP:=pairedBudget_nonneg J₁ J₂ s.t EL ER
    have hZpos:0<Z:=zero_lt_one.trans hblock.1
    positivity
  let A:=Cb*Z^(ε/2)*sourceFactor s a₁ a₂ K*pairedBudget J₁ J₂ s.t EL ER
  have hA:0≤A:=mul_nonneg (mul_nonneg (mul_nonneg hCb.le (Real.rpow_nonneg (by linarith [hblock.1]) _))
    (sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK)) (pairedBudget_nonneg _ _ _ _ _)
  have hcap:=CenteredMomentFirstPhysicalDyadicCount.input_radius_cap hi b₁ b₂ B Z s hhi hb₁ hb₂ hblock.1.le hfixed hV
  have hpblock (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))
      (hE:E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2)
      (n:SourceBlocks s R seed K Z ξ p E):
      ‖CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E:=by
    by_cases hne:CenteredMomentFirstReferenceSource.originalBlock s R seed W K Z ξ p E n=0
    · rw [hne,norm_zero,zero_div]
      exact mul_nonneg hA (radicalWeight_nonneg s R seed p E)
    have hp:=supported s R seed p
    have hg:=actual_common_gates s R seed hseed hz₁ hz₂ p.val.1 p.val.2 p.property
    have hND:1≤(p.val.2.absNorm:ℝ):=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
    have hcapD:sourceRadius s/(p.val.2.absNorm:ℝ)≤Z^(B+1):=
      (div_le_self hH.le hND).trans hcap
    have hh:=hblock.2 s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂ p.val.1 p.val.2 hp.1 hp.2 hg.2.2.1 E 1 1
      (fixedPair s.η p.val.1 p.val.2 hp.1 E 1 1) (retainedRows (localRadius s R seed K Z ξ p E) 1)
      K hK (fun i => (n i).val) hcapD EL ER hEL hER (hcol p E hE n hne).1 (hcol p E hE n hne).2
    simp only [pow_zero,one_mul] at hh
    convert hh using 1 <;>
      simp only [CenteredMomentFirstReferenceSource.originalBlock,A,sourceFactor,pairedBudget,radicalWeight,
        CenteredMomentFirstInactiveRadicalMass.inactiveWeight,Real.rpow_zero,div_one,
        CenteredMomentFirstPhysicalSource.inactiveWeight, CenteredMomentAmplificationChildInput.original,
        CenteredMomentFirstAmplificationChoice.OriginalData.columns,
        CenteredMomentFirstAmplificationChoice.OriginalData.beta,
        CenteredMomentFirstAmplificationChoice.OriginalData.profile,
        CenteredMomentOriginalCommonHarmonic.coefficient,
        CenteredMomentAmplificationChildInput.volume,
        CenteredMomentExceptionalAmplitudePair.volume] ; ring
  have hh:=hsum s R seed hseed hseed0 hz₁ hz₂ hhi hb₁ hb₂ hH W K A hK hA hV hKi hpblock
  rw [CenteredMomentFirstPhysicalOriginalMask.original_physicalMass] at hh
  calc
    _≤_:=hh
    _=_:=by
      rw [show Z^ε=Z^(ε/2)*Z^(ε/2) by rw [←Real.rpow_add (by linarith [hblock.1]:0<Z)];congr 1;ring]
      dsimp [A]
      ring

end SevenEighths.CenteredMomentFirstReferenceEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstColumnPairing -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstColumnPairing
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildInput CenteredMomentGaussEnergy
open CenteredMomentFirstMixedAllowance CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentSecondRetainedAggregate CenteredMomentChildAssembly
open CenteredMomentFirstNonexceptionalWeightSum
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma fixed_pair_moduli (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(χ:RayCharacter):
    (fixedPair η C D hC E χ χ).left.modulus=(fixedPair η C D hC E 1 1).left.modulus ∧
    (fixedPair η C D hC E χ χ).right.modulus=(fixedPair η C D hC E 1 1).right.modulus:=by
  constructor
  · rw [(fixedPair η C D hC E χ χ).left_modulus,
      (fixedPair η C D hC E 1 1).left_modulus]
  · rw [(fixedPair η C D hC E χ χ).right_modulus,
      (fixedPair η C D hC E 1 1).right_modulus]

lemma reference_sum (ref seed front Z:ℝ)(loss:Fin 4→ℝ)(v:ℝ)(J:ℕ):
    (ref/seed)*(front*∑j:Fin 4,Z^(loss j))*(1+|v|)^(2*J)=
      ((∑j:Fin 4,ref*(front*Z^(loss j)))/seed)*(1+‖v‖)^(2*J):=by
  rw [Real.norm_eq_abs]
  simp only [←Finset.mul_sum]
  ring

omit [DecidableEq ι] in
theorem column_bounds_of_reference_sums
    (s:Input ι)(R seed:Ideal O)(Z:ℝ)(Jleft Jright:ℕ)
    (frontLeft frontRight:ℝ)(lossLeft lossRight:Fin 4→ℝ)
    (p:Labels s R seed)(E:Finset (CommonIndex p.val.1 p.val.2))(n:Fin 4→ℤ)
    (hleft:∀L:Ideal O,(L.absNorm:ℝ)≤ sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.1 (supported s R seed p).1
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).left.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.1.absNorm:ℝ))^2*Z^(allowance p.val.1 p.val.2 Z)/(L.absNorm:ℝ))*
          (frontLeft*∑j:Fin 4,Z^(lossLeft j))*(1+|v|)^(2*Jleft))
    (hright:∀L:Ideal O,(L.absNorm:ℝ)≤ sourceRadius s/(p.val.2.absNorm:ℝ)→
      Squarefree L→∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy (original s R seed) p.val.2 (supported s R seed p).2
        (fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
        (((fixedPair s.η p.val.1 p.val.2 (supported s R seed p).1 E χ χ).right.modulus.absNorm:ℝ)*
            (CenteredMomentExceptionalAmplitudePair.volume s.toData/(p.val.2.absNorm:ℝ))^2*Z^(allowance p.val.2 p.val.1 Z)/(L.absNorm:ℝ))*
          (frontRight*∑j:Fin 4,Z^(lossRight j))*(1+|v|)^(2*Jright)):
    ColumnBounds s R seed Z Jleft Jright
      (fun j=>frontLeft*Z^(lossLeft j)) (fun j=>frontRight*Z^(lossRight j)) p E n:=by
  constructor
  · intro L _ hcap hL χ v
    have hh:=hleft L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).1] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)
  · intro L _ hcap hL χ v
    have hh:=hright L hcap hL χ v
    rw [(fixed_pair_moduli s.η p.val.1 p.val.2 (supported s R seed p).1 E χ).2] at hh
    exact hh.trans_eq (reference_sum _ _ _ _ _ _ _)

end SevenEighths.CenteredMomentEnergyFirstColumnPairing

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstPhysicalNormalization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentFirstReferenceEnergy CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource

lemma window_pair_le (J₁ J₂ : ℕ) (t L R H : ℝ) (hH : 0 ≤ H)
    (hL : L ≤ H) (hR : R ≤ H) :
    windowBudget J₁ t L * windowBudget J₂ t R ≤
      H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hs : Real.sqrt L * Real.sqrt R ≤ H := by
    calc
      _ ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul (Real.sqrt_le_sqrt hL) (Real.sqrt_le_sqrt hR)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = H := Real.mul_self_sqrt hH
  have hp := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ by
      exact mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos t).le _)
        (profileMoment_nonneg _)) (profileMoment_nonneg _))
  convert hp using 1 <;> simp only [windowBudget, pow_add] <;> ring

theorem pairedBudget_le_cap (J₁ J₂ : ℕ) (t H : ℝ) (EL ER : Fin 4 → ℝ)
    (hH : 0 ≤ H) (hL : ∀ i, EL i ≤ H) (hR : ∀ j, ER j ≤ H) :
    pairedBudget J₁ J₂ t EL ER ≤
      16 * H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hh : pairedBudget J₁ J₂ t EL ER ≤
      ∑ _i : Fin 4, ∑ _j : Fin 4,
        H * heightEnvelope t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
      window_pair_le J₁ J₂ t (EL i) (ER j) H hH (hL i) (hR j)))
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num
  ring

theorem pairedBudget_le_powers (J₁ J₂ : ℕ) (t Z F Mdecl M₀ ell : ℝ)
    (lossL lossR EL ER : Fin 4 → ℝ) (hZ : 1 ≤ Z) (hF : 0 ≤ F)
    (hL : ∀ i, EL i ≤ F * Z ^ (Mdecl - M₀ + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^ (Mdecl - M₀ + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    pairedBudget J₁ J₂ t EL ER ≤
      16 * F * Z ^ (Mdecl - M₀ + ell) * heightEnvelope t ^ (J₁ + J₂) *
        profileMoment J₁ * profileMoment J₂ := by
  have hcap := pairedBudget_le_cap J₁ J₂ t (F * Z ^ (Mdecl - M₀ + ell)) EL ER
    (mul_nonneg hF (Real.rpow_nonneg (by linarith) _))
    (fun i => (hL i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hellL i])) hF))
    (fun j => (hR j).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hellR j])) hF))
  simpa only [mul_assoc] using hcap

theorem physical_power_identity (Z K q Mdecl ell : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hq : 0 < q) :
    K * q * Z ^ (Mdecl - (Real.logb Z K + Real.logb Z q) + ell) =
      Z ^ (Mdecl + ell) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hKq : K * q = Z ^ (Real.logb Z K + Real.logb Z q) := by
    rw [Real.rpow_add hz, Real.rpow_logb hz hZ.ne' hK, Real.rpow_logb hz hZ.ne' hq]
  rw [hKq, ← Real.rpow_add hz]
  congr 1
  ring

lemma character_power_identity (η : Character) (Z K Mdecl ell : ℝ)
    (hZ : 1 < Z) (hK : 0 < K) :
    K * (η.modulus.absNorm : ℝ) *
      Z ^ (Mdecl - (Real.logb Z K + Real.logb Z (η.modulus.absNorm : ℝ)) + ell) =
      Z ^ (Mdecl + ell) := by
  apply physical_power_identity Z K _ Mdecl ell hZ hK
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

lemma heightEnvelope_le (t : ℝ) :
    heightEnvelope t ≤ (1 + 2 * Real.pi) ^ 2 * (1 + ‖t‖) := by
  unfold heightEnvelope
  nlinarith [norm_nonneg t, Real.pi_pos, mul_nonneg (norm_nonneg t) Real.pi_pos.le]

lemma heightEnvelope_pow_le (J : ℕ) (t : ℝ) :
    heightEnvelope t ^ J ≤ (1 + 2 * Real.pi) ^ (2 * J) * (1 + ‖t‖) ^ J := by
  have hh := pow_le_pow_left₀ (heightEnvelope_pos t).le (heightEnvelope_le t) J
  simpa only [mul_pow, ← pow_mul] using hh

def normalizationConstant (lowerProduct : ℝ) : ℝ :=
  16 * (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost

lemma normalizationConstant_pos (lowerProduct : ℝ) (hlower : 0 < lowerProduct) :
    0 < normalizationConstant lowerProduct := by
  unfold normalizationConstant
  exact mul_pos (mul_pos (by norm_num) (div_pos (Real.exp_pos _) hlower))
    fixedPresentationCost_pos

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sourceFactor_pairedBudget_le (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (J₁ J₂ : ℕ)
    (lossL lossR EL ER : Fin 4 → ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hK : 0 < K) (hZ : 1 < Z) (hF : 0 ≤ F)
    (hsupport : lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂)
    (hL : ∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      normalizationConstant lowerProduct * F * Z ^ (Mdecl + ell) *
        heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hbudget := pairedBudget_le_powers J₁ J₂ s.t Z F Mdecl
    (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) ell
    lossL lossR EL ER hZ.le hF hL hR hellL hellR
  have hsource := sourceFactor_nonneg s a₁ a₂ K ha₁ ha₂ hK
  have hden := div_le_div_of_nonneg_left (Real.exp_pos (Real.log 4)).le hlower hsupport
  have hmass : 0 ≤ (s.η.modulus.absNorm : ℝ) := Nat.cast_nonneg _
  have hpresent := fixedPresentationCost_pos.le
  have hsource' : sourceFactor s a₁ a₂ K ≤
      (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost * K *
        (s.η.modulus.absNorm : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden hpresent) hK.le) hmass
  have hbound := (mul_le_mul_of_nonneg_left hbudget hsource).trans
    (mul_le_mul_of_nonneg_right hsource'
      (show 0 ≤ 16 * F * Z ^
          (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + ell) *
          heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ by
        have hp₁ := profileMoment_nonneg J₁
        have hp₂ := profileMoment_nonneg J₂
        have hh := (heightEnvelope_pos s.t).le
        have hz := zero_lt_one.trans hZ
        positivity))
  apply hbound.trans_eq
  dsimp [normalizationConstant]
  have hid := character_power_identity s.η Z K Mdecl ell hZ hK
  calc
    _ = (16 * (Real.exp (Real.log 4) / lowerProduct) * fixedPresentationCost) * F *
        (K * (s.η.modulus.absNorm : ℝ) * Z ^
          (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + ell)) *
        heightEnvelope s.t ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by ring
    _ = _ := by rw [hid]

def polynomialConstant (lowerProduct : ℝ) (J₁ J₂ : ℕ) : ℝ :=
  normalizationConstant lowerProduct * (1 + 2 * Real.pi) ^ (2 * (J₁ + J₂))

lemma polynomialConstant_pos (lowerProduct : ℝ) (J₁ J₂ : ℕ)
    (hlower : 0 < lowerProduct) : 0 < polynomialConstant lowerProduct J₁ J₂ := by
  exact mul_pos (normalizationConstant_pos lowerProduct hlower) (pow_pos (by positivity) _)

omit [DecidableEq ι] in
theorem sourceFactor_pairedBudget_polynomial (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (J₁ J₂ : ℕ)
    (lossL lossR EL ER : Fin 4 → ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hK : 0 < K) (hZ : 1 < Z) (hF : 0 ≤ F)
    (hsupport : lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂)
    (hL : ∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i))
    (hR : ∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j))
    (hellL : ∀ i, lossL i ≤ ell) (hellR : ∀ j, lossR j ≤ ell) :
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      polynomialConstant lowerProduct J₁ J₂ * F * Z ^ (Mdecl + ell) *
        (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  have hh := sourceFactor_pairedBudget_le lowerProduct hlower s a₁ a₂ K Z F Mdecl ell
    J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hsupport hL hR hellL hellR
  have hm₁ := profileMoment_nonneg J₁
  have hm₂ := profileMoment_nonneg J₂
  have hconst := (normalizationConstant_pos lowerProduct hlower).le
  have hz := zero_lt_one.trans hZ
  apply hh.trans
  calc
    _ ≤ normalizationConstant lowerProduct * F * Z ^ (Mdecl + ell) *
        ((1 + 2 * Real.pi) ^ (2 * (J₁ + J₂)) * (1 + ‖s.t‖) ^ (J₁ + J₂)) *
        profileMoment J₁ * profileMoment J₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (heightEnvelope_pow_le (J₁ + J₂) s.t)
          (by positivity)) hm₁) hm₂
    _ = _ := by unfold polynomialConstant; ring

theorem uniform_source_normalization (lowerProduct : ℝ) (hlower : 0 < lowerProduct)
    (J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] [DecidableEq ι],
    ∀ (s : Input ι) (a₁ a₂ K Z F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ),
    0 < a₁ → 0 < a₂ → 0 < K → 1 < Z → 0 ≤ F →
    lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
    (∀ i, EL i ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
    (∀ j, ER j ≤ F * Z ^
      (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
    (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
    sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER ≤
      C * F * Z ^ (Mdecl + ell) * (1 + ‖s.t‖) ^ (J₁ + J₂) *
        profileMoment J₁ * profileMoment J₂ := by
  refine ⟨polynomialConstant lowerProduct J₁ J₂,
    polynomialConstant_pos lowerProduct J₁ J₂ hlower, ?_⟩
  intro ι _ _ s a₁ a₂ K Z F Mdecl ell lossL lossR EL ER ha₁ ha₂ hK hZ hF hs hL hR heL heR
  exact sourceFactor_pairedBudget_polynomial lowerProduct hlower s a₁ a₂ K Z F Mdecl ell
    J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hs hL hR heL heR

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentFirstSourceReduction
open CenteredMomentFirstReferenceSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceMass CenteredMomentFirstNonexceptionalWeightSum
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_physical_mass_of_columnBounds (W : 𝓢(ℝ, ℂ)) (J₁ J₂ : ℕ)
    (hi : ι → ℝ) (b₁ b₂ B ξ ε lowerProduct : ℝ)
    (hB : 0 ≤ B) (hξ : 0 ≤ ξ) (hε : 0 < ε) (hlower : 0 < lowerProduct) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ s : Input ι, ∀ R seed : Ideal HeckeFamily.O,
      Squarefree seed → seed ≠ 0 → (∀ i, |s.hi i| ≤ hi i) → |s.b₁| ≤ b₁ → |s.b₂| ≤ b₂ →
      ∀ a₁ a₂ K : ℝ, 0 < a₁ → 0 < a₂ → 0 < K →
      lowerProduct ≤ (∏ i, s.lo i) * a₁ * a₂ →
      (∀ x, s.W₁ x ≠ 0 → a₁ ≤ x) → (∀ x, s.W₂ x ≠ 0 → a₂ ≤ x) →
      CenteredMomentExceptionalAmplitudePair.volume s.toData ≤ Z ^ B → K⁻¹ ≤ Z ^ B →
      ∀ (F Mdecl ell : ℝ) (lossL lossR EL ER : Fin 4 → ℝ), 0 ≤ F →
      (∀ i, 0 ≤ EL i) → (∀ j, 0 ≤ ER j) →
      (∀ i, EL i ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossL i)) →
      (∀ j, ER j ≤ F * Z ^
        (Mdecl - (Real.logb Z K + Real.logb Z (s.η.modulus.absNorm : ℝ)) + lossR j)) →
      (∀ i, lossL i ≤ ell) → (∀ j, lossR j ≤ ell) →
      (∀ p : Labels s R seed, ∀ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∀ n : SourceBlocks s R seed K Z ξ p E,
        originalBlock s R seed W K Z ξ p E n ≠ 0 →
          ColumnBounds s R seed Z J₁ J₂ EL ER p E (fun i => (n i).val)) →
      physicalMass s R seed CenteredMomentSecondHeightFamily.fixedBadMask 1 W K Z ξ /
          CenteredMomentExceptionalAmplitudePair.volume s.toData ≤
        C * F * Z ^ (Mdecl + ell + ε) / (seed.absNorm : ℝ) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂ := by
  obtain ⟨Cb, hCb, hbound⟩ := actual_physical_mass W J₁ J₂ hi b₁ b₂ B ξ ε hB hξ hε
  refine ⟨Cb * polynomialConstant lowerProduct J₁ J₂,
    mul_pos hCb (polynomialConstant_pos lowerProduct J₁ J₂ hlower), ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with Z hbound hZ
  intro s R seed hseed hseed₀ hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK hsupport hs₁ hs₂ hV hKi
    F Mdecl ell lossL lossR EL ER hF hEL hER hL hR heL heR hcols
  have hphysical := hbound s R seed hseed hseed₀ hhi hb₁ hb₂ a₁ a₂ K ha₁ ha₂ hK
    hs₁ hs₂ hV hKi EL ER hEL hER hcols
  have hnormal := sourceFactor_pairedBudget_polynomial lowerProduct hlower s a₁ a₂ K Z
    F Mdecl ell J₁ J₂ lossL lossR EL ER ha₁ ha₂ hK hZ hF hsupport hL hR heL heR
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hp : 0 ≤ Cb * Z ^ ε / (seed.absNorm : ℝ) := by positivity
  calc
    _ ≤ Cb * Z ^ ε / (seed.absNorm : ℝ) * sourceFactor s a₁ a₂ K *
        pairedBudget J₁ J₂ s.t EL ER := hphysical
    _ = (Cb * Z ^ ε / (seed.absNorm : ℝ)) *
        (sourceFactor s a₁ a₂ K * pairedBudget J₁ J₂ s.t EL ER) := by ring
    _ ≤ (Cb * Z ^ ε / (seed.absNorm : ℝ)) *
        (polynomialConstant lowerProduct J₁ J₂ * F * Z ^ (Mdecl + ell) *
          (1 + ‖s.t‖) ^ (J₁ + J₂) * profileMoment J₁ * profileMoment J₂) :=
      mul_le_mul_of_nonneg_left hnormal hp
    _ = _ := by
      rw [show Z ^ (Mdecl + ell + ε) = Z ^ (Mdecl + ell) * Z ^ ε from
        Real.rpow_add hz (Mdecl + ell) ε]
      ring

end SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SuccessorPaidParameters -/

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSuccessorPaidParameters
open CenteredMomentFirstSecondLossParameters

def edge (epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh : ℝ) : ℝ :=
  epsChild+epsRemove+2*delta+epsilon+delta2+delta1/6+kappa*mesh+7*theta/3

def exceptional (sigma deltafr epsilon delta B theta : ℝ) : ℝ :=
  3*sigma+5*deltafr/6+2*epsilon+2*delta+2*(5*B+1)*theta

def diagonal (sigma delta reserve epsilon A : ℝ) : ℝ :=
  2*sigma+delta+reserve+epsilon*A

lemma paid_normalization (Z shortening allowance paid : ℝ) (hZ : 0<Z) :
    Z^(-shortening-allowance)*Z^(shortening+paid)=Z^(paid-allowance) := by
  rw [←Real.rpow_add hZ]
  congr 1
  ring

lemma paid_normalization_with_ratio (Z shortening allowance paid ratio : ℝ)
    (hZ : 0<Z) :
    Z^(-shortening-allowance)*(Z^(shortening+paid)*ratio^((1:ℝ)/6))=
      Z^(paid-allowance)*ratio^((1:ℝ)/6) := by
  rw [←mul_assoc,paid_normalization Z shortening allowance paid hZ]

theorem actual_paid_error_reference
    (ρ υ : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (p : HeckeFamily.O) (hp : p≠0) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6)
    (Z V C allowance paid : ℝ) (hZ : 1<Z) (hV : 0<V) (hC : 0<C)
    (hυ : υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter ρ χ)
      CenteredMomentSecondHeightFamily.fixedBadMask p
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent n)) :
    (V/C)*CenteredMomentAmplificationErrorEnergy.localErrorCost p n*
      (υ.modulus.absNorm:ℝ)*(V/C/(CenteredMomentSectorLocalization.normValue p)^(n+1))*
      Z^(CenteredMomentFirstAmplificationChoice.errorRemoval p Z (n+1)+paid)/
      ((ρ.modulus.absNorm:ℝ)*(V/C)^2*Z^allowance)≤
      CenteredMomentFirstSourceConductorCaps.rayCost*Z^(paid-allowance) := by
  have hh:=CenteredMomentFirstMixedMainError.actual_main_error_reference
    ρ υ χ p hp n hn Z V C allowance
    (Z^(CenteredMomentFirstAmplificationChoice.errorRemoval p Z (n+1)+paid))
    hZ hV hC (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hυ
  apply hh.trans_eq
  rw [mul_assoc,paid_normalization Z _ allowance paid (zero_lt_one.trans hZ)]

lemma declared_parent_deficit (actual declared loss : ℝ) (h : actual≤declared) :
    actual+(declared-actual)/6+loss≤declared+loss := by linarith

lemma paired_declared_parent (actual declared left right loss : ℝ)
    (h : actual≤declared)
    (hl : left≤(declared-actual)/6+loss)
    (hr : right≤(declared-actual)/6+loss) :
    actual+(left+right)/2≤declared+loss := by linarith

lemma mesh_cost (kappa reserve : ℝ) (hk : 0≤kappa) (hr : 0≤ reserve) :
    kappa*(reserve/(kappa+1))≤ reserve := by
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<kappa+1)).mpr
  nlinarith

theorem simultaneous_parameters (Mcap B kappa epsilonTarget : ℝ)
    (hM : 0≤Mcap) (hB : 0≤B) (hk : 0≤kappa) (he : 0<epsilonTarget) :
    ∃ sigma reserve mesh : ℝ,
      0<sigma ∧ sigma≤1 ∧ sigma≤epsilonTarget/1000 ∧
      0< reserve ∧ 0< mesh ∧ mesh≤ reserve ∧ kappa*mesh≤ reserve ∧
      20*reserve≤ sigma/2 ∧
      Mcap<(depth Mcap sigma:ℝ)*sigma/2 ∧
      (∀ epsChild epsRemove delta epsilon delta1 delta2 theta,
        epsChild≤ reserve → epsRemove≤ reserve → delta≤ reserve → epsilon≤ reserve →
        delta1≤ reserve → delta2≤ reserve → theta≤ reserve →
        (depth Mcap sigma:ℝ)*edge epsChild epsRemove delta epsilon delta1 delta2 theta kappa mesh
          ≤epsilonTarget/16) ∧
      (∀ deltafr epsilon delta theta,
        deltafr≤ reserve → epsilon≤ reserve → delta≤ reserve → theta≤ reserve →
        exceptional sigma deltafr epsilon delta B theta≤epsilonTarget/16) ∧
      (∀ delta other epsilon A,
        delta≤ reserve → other≤ reserve → 0≤epsilon → epsilon≤ reserve → A≤Mcap →
        diagonal sigma delta other epsilon A≤epsilonTarget/16) := by
  let sigma : ℝ := min 1 (epsilonTarget/1000)
  have hs : 0<sigma := lt_min (by norm_num) (by positivity)
  have hs1 : sigma≤1 := min_le_left _ _
  have hse : sigma≤epsilonTarget/1000 := min_le_right _ _
  let n := depth Mcap sigma
  let L : ℝ := (n:ℝ)+Mcap+10*B+30
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg _
  have hL : 0<L := by dsimp [L]; positivity
  let reserve : ℝ := min (sigma/100) (epsilonTarget/(1000*L))
  have hr : 0< reserve := lt_min (by positivity) (by positivity)
  have hrs : reserve≤ sigma/100 := min_le_left _ _
  have hre : reserve≤epsilonTarget/(1000*L) := min_le_right _ _
  have hbudget : reserve*(1000*L)≤epsilonTarget := (le_div_iff₀ (by positivity)).mp hre
  have hnres : (n:ℝ)*reserve≤epsilonTarget/1000 := by
    have hx : (n:ℝ)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hbRes : (10*B+20)*reserve≤epsilonTarget/1000 := by
    have hx : (10*B+20)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  have hmRes : (Mcap+2)*reserve≤epsilonTarget/1000 := by
    have hx : (Mcap+2)*reserve≤L*reserve := mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr.le
    nlinarith
  let mesh : ℝ := reserve/(kappa+1)
  have hm : 0< mesh := by dsimp [mesh]; positivity
  have hmr : mesh≤ reserve := by
    dsimp [mesh]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm : kappa*mesh≤ reserve := mesh_cost kappa reserve hk hr.le
  refine ⟨sigma,reserve,mesh,hs,hs1,hse,hr,hm,hmr,hkm,by linarith,
    depth_covers Mcap sigma hs,?_,?_,?_⟩
  · intro ec er d e d1 d2 t hec her hd he hd1 hd2 ht
    have hedge : edge ec er d e d1 d2 t kappa mesh≤10*reserve := by
      unfold edge
      linarith
    have hp := mul_le_mul_of_nonneg_left hedge hn
    change (n:ℝ)*edge ec er d e d1 d2 t kappa mesh≤epsilonTarget/16
    nlinarith
  · intro df e d t hdf he hd ht
    have htheta : 2*(5*B+1)*t≤2*(5*B+1)*reserve :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    unfold exceptional
    nlinarith
  · intro d other e A hd ho he0 he hA
    have hmul : e*A≤ reserve*Mcap := (mul_le_mul_of_nonneg_left hA he0).trans
      (mul_le_mul_of_nonneg_right he hM)
    unfold diagonal
    nlinarith

end SevenEighths.CenteredMomentSuccessorPaidParameters

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.WidthSchedule -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyWidthSchedule
open CenteredMomentSuccessorPaidParameters CenteredMomentFirstSecondLossParameters

def amplification (ε:ℝ):ℝ := min 1 (ε/16000)
def count (M ε:ℝ):ℕ := depth M (amplification ε)
def scale (M B ε:ℝ):ℝ := (count M ε:ℝ)+M+10*B+30
def reserve (M B ε:ℝ):ℝ :=
  min (amplification ε/100) (ε/(1000000*scale M B ε))
def mesh (M B κ ε:ℝ):ℝ := reserve M B ε/(κ+1)
def width (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε/16+(k:ℝ)*amplification ε/2
def loss (M B ε:ℝ)(k:ℕ):ℝ := reserve M B ε+64*(k:ℝ)*reserve M B ε

theorem bounds (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<amplification ε ∧ amplification ε≤1 ∧ amplification ε≤ε/16000 ∧
    0< reserve M B ε ∧ 0< mesh M B κ ε ∧ mesh M B κ ε≤ reserve M B ε ∧
    κ*mesh M B κ ε≤ reserve M B ε ∧
    20*reserve M B ε≤amplification ε/2 ∧
    M<width M B ε (count M ε) ∧
    loss M B ε (count M ε)≤ε/1000 :=by
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hs1:amplification ε≤1:=min_le_left _ _
  have hse:amplification ε≤ε/16000:=min_le_right _ _
  have hn:0≤(count M ε:ℝ):=Nat.cast_nonneg _
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hrs:reserve M B ε≤amplification ε/100:=min_le_left _ _
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL:(count M ε:ℝ)≤ scale M B ε:=by unfold scale;linarith
  have h1L:1≤ scale M B ε:=by unfold scale;linarith
  have hnR:(count M ε:ℝ)*reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR:reserve M B ε≤ε/1000000:=by
    have hh:=mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm:0< mesh M B κ ε:=by unfold mesh;positivity
  have hmr:mesh M B κ ε≤ reserve M B ε:=by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm:κ*mesh M B κ ε≤ reserve M B ε:=mesh_cost κ _ hκ hr.le
  have hw:M<width M B ε (count M ε):=by
    have hd:=depth_covers M (amplification ε) hs
    change M<(count M ε:ℝ)*amplification ε/2 at hd
    unfold width
    linarith
  refine ⟨hs,hs1,hse,hr,hm,hmr,hkm,by linarith,hw,?_⟩
  unfold loss
  linarith

lemma reserve_cost (M B ε c:ℝ)(hM:0≤M)(hB:0≤B)(hε:0<ε)
    (hc:c≤ scale M B ε):c*reserve M B ε≤ε/1000000:=by
  have hL:0<scale M B ε:=by unfold scale;positivity
  have hs:0<amplification ε:=lt_min (by norm_num) (by positivity)
  have hr:0< reserve M B ε:=lt_min (by positivity) (by positivity)
  have hre:reserve M B ε≤ε/(1000000*scale M B ε):=min_le_right _ _
  have hp:reserve M B ε*(1000000*scale M B ε)≤ε:=
    (le_div_iff₀ (by positivity)).mp hre
  have hh:=mul_le_mul_of_nonneg_right hc hr.le
  nlinarith

theorem one_time_losses (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (df es d theta other A:ℝ)(hdf:df≤ reserve M B ε)(hes:es≤ reserve M B ε)
    (hd:d≤ reserve M B ε)(ht:theta≤ reserve M B ε)(ho:other≤ reserve M B ε)
    (he0:0≤es)(hA:A≤M):
    exceptional (amplification ε) df es d B theta≤ε/1000 ∧
      diagonal (amplification ε) d other es A≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hs:=hb.2.2.1
  have hr:=hb.2.2.2.1
  have hx:=reserve_cost M B ε (10*B+7) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have hy:=reserve_cost M B ε (M+2) hM hB hε (by unfold scale;linarith [Nat.cast_nonneg (α:=ℝ) (count M ε)])
  have htheta:=mul_le_mul_of_nonneg_left ht (show 0≤2*(5*B+1) by positivity)
  have hmul:es*A≤ reserve M B ε*M:=
    (mul_le_mul_of_nonneg_left hA he0).trans (mul_le_mul_of_nonneg_right hes hM)
  constructor
  · unfold exceptional
    nlinarith
  · unfold diagonal
    nlinarith

lemma mesh_lt_prime_width (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    mesh M B κ ε<amplification ε/6:=by
  have h:=bounds M B κ ε hM hB hκ hε
  have hp:=h.1
  have hm:=h.2.2.2.2.2.1
  have hr:=h.2.2.2.2.2.2.2.1
  linarith

lemma width_zero (M B ε:ℝ):width M B ε 0=reserve M B ε/16:=by simp [width]
lemma loss_zero (M B ε:ℝ):loss M B ε 0=reserve M B ε:=by simp [loss]
lemma width_succ (M B ε:ℝ)(k:ℕ):
    width M B ε (k+1)-amplification ε/2=width M B ε k:=by
  simp only [width,Nat.cast_add,Nat.cast_one]
  ring
lemma loss_succ (M B ε:ℝ)(k:ℕ):
    loss M B ε (k+1)=loss M B ε k+64*reserve M B ε:=by
  simp only [loss,Nat.cast_add,Nat.cast_one]
  ring

lemma child_band (M B ε parent child:ℝ)(k:ℕ)
    (hp:parent≤width M B ε (k+1))(hc:child≤parent-amplification ε/2):
    child≤width M B ε k:=by
  rw [←width_succ M B ε k]
  linarith

lemma loss_le_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤ count M ε):loss M B ε k≤ε/1000:=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hk':(k:ℝ)≤(count M ε:ℝ):=by exact_mod_cast hk
  apply le_trans _ hb.2.2.2.2.2.2.2.2.2
  unfold loss
  gcongr

lemma next_paid_loss (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other:ℝ)
    (her:er≤ reserve M B ε)(hd:d≤ reserve M B ε)(he:e≤ reserve M B ε)
    (hd1:d1≤ reserve M B ε)(hd2:d2≤ reserve M B ε)(ht:theta≤ reserve M B ε)
    (ho:other≤50*reserve M B ε):
    loss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+other≤
      loss M B ε (k+1):=by
  have hb:=bounds M B κ ε hM hB hκ hε
  have hr:=hb.2.2.2.1
  have hm:=hb.2.2.2.2.2.2.1
  rw [loss_succ]
  unfold edge
  linarith

theorem actual_removal_path {ι:Type*}[DecidableEq ι]
    (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0<κ)(hε:0<ε)
    (n:ℕ)(J:Fin n→Finset ι)(w:Fin n→ι→ℝ)(x y state:Fin n→ℝ)
    (hw:∀k,∀i∈J k,0≤w k i)(hm:∀k,∀i∈J k,w k i≤ mesh M B κ ε):
    ∃R:Fin n→Finset ι,(∀k,R k⊆J k) ∧
      (∀k,R k=J k ∨ x k+y k+6*κ*(∑i∈J k\R k,w k i)≤ state k) ∧
      (∑k,κ*(∑i∈R k,w k i))≤
        (∑k,CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6)+
          (n:ℝ)*reserve M B ε:=by
  have hb:=bounds M B κ ε hM hB hκ.le hε
  have hmesh:=hb.2.2.2.2.1
  have hcost:=hb.2.2.2.2.2.2.1
  choose R hR hcap hpay using fun k=>CenteredMomentLiveCapacity.removal_excess_cost
    (J k) (w k) (x k) (y k) (state k) κ (mesh M B κ ε) hκ hmesh.le (hw k) (hm k)
  refine ⟨R,hR,hcap,?_⟩
  calc
    _≤∑k,(CenteredMomentLiveCapacity.excess (J k) (w k) (x k) (y k) (state k) κ/6+
        reserve M B ε):=Finset.sum_le_sum (fun k _=>(hpay k).trans (by linarith))
    _=_:=by rw [Finset.sum_add_distrib];simp

end SevenEighths.CenteredMomentEnergyWidthSchedule

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.WidthRanges -/

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyProfiles CenteredMomentEnergyWidthSchedule

def step (M B L:ℝ):ℝ:=4*(L+M+B+4)
def range (M B L:ℝ):ℕ→ℝ
  | 0=>max 1 L
  | n+1=>step M B (range M B L n)
def sourceCap (M B L:ℝ)(n:ℕ):ℝ:=10*(range M B L n+M+B+1)
def finalSourceCap (M B L ε:ℝ):ℝ:=sourceCap M B L (count M ε)
def fineMesh (M B L κ ε:ℝ):ℝ:=mesh M (finalSourceCap M B L ε) κ ε

lemma range_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ range M B L n:=by
  induction n with
  | zero=>exact zero_le_one.trans (le_max_left _ _)
  | succ n ih=>simp only [range,step];positivity

lemma range_mono (M B L:ℝ)(hM:0≤M)(hB:0≤B):Monotone (range M B L):=by
  apply monotone_nat_of_le_succ
  intro n
  have hh:=range_nonneg M B L hM hB n
  simp only [range,step]
  linarith

lemma range_original (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):L≤ range M B L n:=by
  exact (le_max_right (1:ℝ) L).trans (range_mono M B L hM hB (Nat.zero_le n))

lemma step_admits (M B L rho d e:ℝ)(hM:0≤M)(hB:0≤B)(hL:0≤L)
    (hrho:rho≤1)(hd:d≤1)(he:e≤1):
    L≤ step M B L ∧ M+B+rho/100+1≤ step M B L ∧
    max L (M+B+2*d)+1≤ step M B L ∧
    2*L+e≤ step M B L ∧
    2*(max L (M+B+2*d)+1)+e≤ step M B L:=by
  have hmax:max L (M+B+2*d)≤L+M+B+2:=by
    apply max_le <;> linarith
  unfold step
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma range_envelope (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):
    range M B L n≤(8:ℝ)^n*(max 1 L+M+B+4):=by
  induction n with
  | zero=>simp only [range,pow_zero,one_mul];linarith
  | succ n ih=>
    have hp:1≤(8:ℝ)^n:=one_le_pow₀ (by norm_num)
    have ha:0≤ max 1 L:=zero_le_one.trans (le_max_left _ _)
    have hm:M+B+4≤(8:ℝ)^n*(max 1 L+M+B+4):=by
      have hh:=mul_le_mul_of_nonneg_right hp (show 0≤ max 1 L+M+B+4 by positivity)
      simp only [one_mul] at hh
      linarith
    simp only [range,step,pow_succ]
    nlinarith

lemma ready_exponent_le (M B L A D P q e xi:ℝ)(n:ℕ)
    (hM:0≤M)(hB:0≤B)
    (hA:A≤2*range M B L n+M+1)(hD:D≤1)(hP:P≤B)
    (hq:q≤4*range M B L n+3*M+4)(he:e≤1)(hxi:xi≤1):
    CenteredMomentFirstSecondInputGates.exponent A D P q e xi≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold CenteredMomentFirstSecondInputGates.exponent sourceCap
  apply max_le
  · linarith
  apply max_le
  · linarith
  apply max_le <;> linarith

lemma sourceCap_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(n:ℕ):0≤ sourceCap M B L n:=by
  have hr:=range_nonneg M B L hM hB n
  unfold sourceCap
  positivity

lemma fineMesh_pos (M B L κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε):
    0<fineMesh M B L κ ε:=by
  exact (bounds M (finalSourceCap M B L ε) κ ε hM
    (sourceCap_nonneg M B L hM hB _) hκ hε).2.2.2.2.1

lemma support_step (a b:ℝ)(ha:0<a)(n:ℕ):
    0<lower a b (n+1) ∧ lower a b (n+1)=lower a b n/max 1 b:=
  ⟨lower_pos a b ha _,rfl⟩

end SevenEighths.CenteredMomentEnergyWidthRanges

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedAllowance
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentSuccessorPaidParameters
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

def reference (q V C Z allowance:ℝ):ℝ:=q*(V/C)^2*Z^allowance

def mainCores (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*q*(V/C)*Z^(ell+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*(V/C)^((1:ℝ)/3)*Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*Kmain*(V/C)^eps/reference q V C Z allowance,
    (V/C)*Kmain*Z^(-saving)/reference q V C Z allowance]

def errorCores (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):Fin 4→ℝ:=
  ![(V/C)*localErrorCost p (k-1)*q*Z^(errorMoving p Z k)*
      (V/C/(normValue p)^k)*Z^(errorRemoval p Z k+deficit/6+paid)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*(V/C/(normValue p)^k)^((1:ℝ)/3)*
      Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3)/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*(V/C/(normValue p)^k)^eps/reference q V C Z allowance,
    (V/C)*localErrorCost p (k-1)*Kerror*Z^(-saving)/reference q V C Z allowance]

def lossVector (sigma delta reserve paid eps Mcap saving:ℝ):Fin 4→ℝ:=
  ![paid,3*sigma/2+5*(delta+reserve)/6,
    2*sigma+delta+reserve+eps*Mcap,2*sigma+delta+reserve-saving]

def averagedCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(H main:Fin 4→ℝ)
    (error:elementPool P→Fin 3→Ray→Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*H j*main j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)

lemma actual_valuation_mass : (∑i:Fin 3,16*(errorIndex i+2:ℝ)^2)=1872 := by
  norm_num [Fin.sum_univ_succ,errorIndex]

theorem actual_error_average (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (f:elementPool P→Fin 3→Ray→ℝ)(E:ℝ)(_hE:0≤E)
    (hf:∀p i χ,f p i χ≤E):
    (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
        1872*(Fintype.card Ray:ℝ)*E := by
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hc:Fintype.card (elementPool P)=P.card:=by
    rw [Fintype.card_coe,elementPool_card P hp hbad]
  have hh:(∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,f p i χ)≤
      ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*∑χ:Ray,E:=by
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _=>hf p i χ)) (by positivity)
  apply (mul_le_mul_of_nonneg_left hh (by positivity:0≤1/(P.card:ℝ))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [←Finset.sum_mul,actual_valuation_mass,hc]
  field_simp

lemma main_paid_core (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    Z^(-ell)*mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0≤
      Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have he:mainCores q V C Z allowance Kmain ell deficit paid eps saving r 0=
      Z^(ell+deficit/6+paid-allowance):=by
    dsimp [mainCores,reference]
    rw [Real.rpow_sub hz]
    field_simp
  rw [he,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

lemma error_paid_core (p:O)(hp:p≠0)(k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7)
    (q V C Z allowance Kerror deficit paid eps saving r:ℝ)
    (hq:0<q)(hV:0<V)(hC:0<C)(hZ:1<Z)(hB:0≤allowance)(hdef:0≤deficit):
    errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0≤Z^(deficit+paid) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hx:0<V/C:=div_pos hV hC
  have hpv:=normValue_pos p hp
  have hw:=actual_error_weight p hp Z hZ k hk
  have hs:localErrorCost p (k-1)*Z^(errorMoving p Z k)≤1:=by
    have hh:=mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hz.le (errorMoving p Z k))
    rw [←Real.rpow_add hz,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have he:errorCores p k q V C Z allowance Kerror deficit paid eps saving r 0=
      (localErrorCost p (k-1)*Z^(errorMoving p Z k))*Z^(deficit/6+paid-allowance):=by
    dsimp [errorCores,reference]
    rw [Real.rpow_sub hz,show errorRemoval p Z k+deficit/6+paid=
      errorRemoval p Z k+(deficit/6+paid) by ring,Real.rpow_add hz,errorRemoval_power p hp Z hZ k]
    field_simp
  rw [he]
  calc
    _≤1*Z^(deficit/6+paid-allowance):=mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hz.le _)
    _≤Z^(deficit+paid):=by rw [one_mul];apply Real.rpow_le_rpow_of_exponent_le hZ.le;linarith

theorem actual_main_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤ sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hr:0< mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve:=by unfold mainCommonRadius;positivity
  have havg:Z^(-sigma/3)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hZ.le (by linarith)
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=main_paid_core (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod hK hV
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          4*sigma/3+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [mainCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod
    have hc0:0≤ mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 2:=by
      dsimp [mainCores,reference];positivity
    apply (mul_le_mul_of_nonneg_right havg hc0).trans
    rw [one_mul]
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_main_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [mainCores,reference] ; ring
    have ht':=mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hz.le (-sigma/3))
    apply ht'.trans
    calc
      _≤1*(Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          2*sigma+delta+reserve)*Z^(-saving)):=mul_le_mul_of_nonneg_right havg (by positivity)
      _≤_:=by
        rw [one_mul,←Real.rpow_add hz]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        dsimp [lossVector]
        linarith

theorem actual_error_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving r Mdecl Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤ sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))(hbad:fixedBadPrimes⊆Sbad)
    (p:O)(hp:p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k:ℕ)(hk:k=1 ∨ k=6 ∨ k=7):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k;
    ∀j:Fin 4,errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving r j≤
      Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hpdata:=elementPool_data _ (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0:p≠0:=hpdata.1.ne_zero
  have hr:0<errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k:=by unfold errorCommonRadius;positivity
  have hA:Real.logb Z V≤Mdecl:=by linarith
  have hAcap:Real.logb Z V≤Mcap:=hA.trans hcap
  intro j
  fin_cases j
  · have hh:=error_paid_core p hp0 k hk (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
        (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_reference η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve r hZ hmod M H Sbad hbad p hp k hk hK hV
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 1≤
        Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))/6+
          3*sigma/2+5*(delta+reserve)/6):=by
      convert hh using 1 ; dsimp [errorCores,reference] ; ring
    apply ht.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve eps hK hV hZ heps hmod p hp0 k hk
    apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    have he:=mul_le_mul_of_nonneg_left hAcap heps
    linarith
  · have hh:=actual_error_diagonal η τ C D hC hD hCD E K V Z sigma delta reserve 0 hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht:=mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    have hcore:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving r 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [errorCores,reference] ; ring
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

def sourceCoefficients (P:Finset (Ideal O))(mainFactor:ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):Fin 4→ℝ:=fun j=>
  (56/(P.card:ℝ))*(mainFactor*amain j+
    ∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))

lemma shortened_power (V q:ℝ)(k:ℕ)(alpha:ℝ)(hV:0≤V)(hq:0≤q):
    (V/q^k)^alpha=V^alpha*(q^k)^(-alpha):=by
  rw [Real.div_rpow hV (pow_nonneg hq k),Real.rpow_neg (pow_nonneg hq k),div_eq_mul_inv]

theorem source_coefficients_identity (P:Finset (Ideal O))(mainFactor V:ℝ)(hV:0≤V)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ):
    (∑j:Fin 4,sourceCoefficients P mainFactor amain aerror alpha j*V^(alpha j))=
    (56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
      ∑p:elementPool P,∑i:Fin 3,(16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
        (errorIndex i+2:ℝ)*∑χ:Ray,∑j:Fin 4,aerror p i χ j*
          (V/(normValue p)^(errorIndex i+1))^(alpha j)) := by
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  let f:=fun (j:Fin 4) (p:elementPool P) (i:Fin 3) (χ:Ray)=>
    16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
      (aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)
  have hswap:(∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ)=
      ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  calc
    _=(56/(P.card:ℝ))*∑j:Fin 4,
        (mainFactor*amain j*V^(alpha j)+
          (∑p:elementPool P,∑i:Fin 3,16*(errorIndex i+2:ℝ)^2*localErrorCost p (errorIndex i)*
            ∑χ:Ray,aerror p i χ j*((normValue p)^(errorIndex i+1))^(-alpha j))*V^(alpha j)):=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      unfold sourceCoefficients
      ring
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑j:Fin 4,∑p:elementPool P,∑i:Fin 3,∑χ:Ray,f j p i χ):=by
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.mul_sum,mul_assoc]
      · simp only [f,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    _=(56/(P.card:ℝ))*(mainFactor*(∑j:Fin 4,amain j*V^(alpha j))+
        ∑p:elementPool P,∑i:Fin 3,∑χ:Ray,∑j:Fin 4,f j p i χ):=by rw [hswap]
    _=_:=by
      congr 2
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [shortened_power V (normValue p) _ _ hV (hnorm _)]
      dsimp [f]
      ring

theorem averaged_coefficients_bound (P:Finset (Ideal O))(hne:P.Nonempty)
    (hp:∀Q∈P,Prime Q)(hbad:∀Q∈P,Q∉fixedBadPrimes)
    (Z ell primeLoss mainFactor:ℝ)(hZ:1<Z)(hloss:0≤primeLoss)
    (hfactor:0≤ mainFactor)(hcard:Z^(ell-primeLoss)≤(P.card:ℝ))
    (H main loss:Fin 4→ℝ)(error:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hH:∀j,0≤H j)(hm:∀j,Z^(-ell)*main j≤Z^(loss j))
    (he:∀p i χ j,error p i χ j≤Z^(loss j)):
    ∀j,averagedCoefficients P mainFactor H main error j≤
      56*(mainFactor+1872*(Fintype.card Ray:ℝ))*H j*Z^(loss j+primeLoss) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hn:(0:ℝ)<P.card:=by exact_mod_cast hne.card_pos
  have hinv:(1/(P.card:ℝ))≤Z^(-ell+primeLoss):=by
    have hh:=one_div_le_one_div_of_le (Real.rpow_pos_of_pos hz _) hcard
    simpa [one_div,←Real.rpow_neg hz.le,neg_sub,sub_eq_add_neg,add_comm] using hh
  intro j
  have hm':main j≤Z^(ell+loss j):=by
    have hh:=mul_le_mul_of_nonneg_left (hm j) (Real.rpow_nonneg hz.le ell)
    rw [←mul_assoc,←Real.rpow_add hz,add_neg_cancel,Real.rpow_zero,one_mul,
      ←Real.rpow_add hz] at hh
    exact hh
  have hmain:(1/(P.card:ℝ))*main j≤Z^(loss j+primeLoss):=by
    calc
      _≤(1/(P.card:ℝ))*Z^(ell+loss j):=mul_le_mul_of_nonneg_left hm' (by positivity)
      _≤Z^(-ell+primeLoss)*Z^(ell+loss j):=mul_le_mul_of_nonneg_right hinv (by positivity)
      _=Z^(loss j+primeLoss):=by rw [←Real.rpow_add hz];congr 1;ring
  have herr:=actual_error_average P hne hp hbad (fun p i χ=>H j*error p i χ j)
    (H j*Z^(loss j)) (mul_nonneg (hH j) (Real.rpow_nonneg hz.le _)) (fun p i χ=>mul_le_mul_of_nonneg_left (he p i χ j) (hH j))
  have hl:Z^(loss j)≤Z^(loss j+primeLoss):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have herr':(1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
      16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)≤
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss)):=
    herr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (hH j)) (by positivity))
  calc
    _=56*(mainFactor*H j*((1/(P.card:ℝ))*main j)+
      (1/(P.card:ℝ))*(∑p:elementPool P,∑i:Fin 3,
        16*(errorIndex i+2:ℝ)^2*∑χ:Ray,H j*error p i χ j)):=by
      unfold averagedCoefficients;ring
    _≤56*(mainFactor*H j*Z^(loss j+primeLoss)+
      1872*(Fintype.card Ray:ℝ)*(H j*Z^(loss j+primeLoss))):=by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hmain (mul_nonneg hfactor (hH j))) herr') (by norm_num)
    _=_:=by ring

theorem actual_low_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving rmain;
    let error:=fun (p:elementPool P) (i:Fin 3) (χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (rerror p i χ);
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    rmain Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      (rerror p i χ) Mdecl Mcap hK hV hZ hs.le heps hM hcap hactual hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

theorem source_normalized_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(alpha:Fin 4→ℝ)(amain:Fin 4→ℝ)
    (aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
        (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor (fun _=>1)
        (fun j=>(V/C)*amain j*(V/C)^(alpha j)/reference q V C Z allowance)
        (fun p i χ j=>(V/C)*localErrorCost p (errorIndex i)*aerror p i χ j*
          (V/C/(normValue p)^(errorIndex i+1))^(alpha j)/reference q V C Z allowance) j := by
  have hx:0<V/C:=div_pos hV hC
  have hnorm:∀p:O,0≤normValue p:=by intro p;unfold normValue;positivity
  intro j
  have hden:reference q V C Z allowance≠0:=by unfold reference;positivity
  have he:CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*((V/C)*sourceCoefficients P mainFactor amain aerror alpha j*
        (V/C)^(alpha j)/reference q V C Z allowance):=by
    unfold CenteredMomentFirstCommonReferencePower.normalizedPower reference
    rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_neg hZ.le]
    field_simp
  rw [he]
  congr 1
  unfold sourceCoefficients averagedCoefficients
  simp only [one_mul]
  simp only [shortened_power (V/C) _ _ _ hx.le (hnorm _)]
  simp only [div_eq_mul_inv,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul]
  ring_nf

theorem eventually_prime_average_gates
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (Sbad:Finset (Ideal O))(sigma primeLoss:ℝ)(hs:0<sigma)(hloss:0<primeLoss):
    ∀ᶠ Z:ℝ in Filter.atTop,1<Z ∧
      (primePool M H Sbad (1/2) 1 (Z^(sigma/3))).Nonempty ∧
      Z^(sigma/3-primeLoss)≤(primePool M H Sbad (1/2) 1 (Z^(sigma/3))).card := by
  filter_upwards [eventually_actual_pool_card M H hH Sbad (sigma/3) primeLoss (by positivity) hloss,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_,hc⟩
  apply Finset.card_pos.mp
  exact_mod_cast (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3-primeLoss)).trans_le hc

lemma source_coefficients_nonneg (P:Finset (Ideal O))(mainFactor:ℝ)(hmain:0≤ mainFactor)
    (amain:Fin 4→ℝ)(aerror:elementPool P→Fin 3→Ray→Fin 4→ℝ)(alpha:Fin 4→ℝ)
    (ha:∀j,0≤amain j)(he:∀p i χ j,0≤aerror p i χ j):
    ∀j,0≤ sourceCoefficients P mainFactor amain aerror alpha j := by
  intro j
  have hc:∀p:O,∀n:ℕ,0≤localErrorCost p n:=by
    intro p n
    have hn:0≤normValue p:=by unfold normValue;positivity
    unfold localErrorCost
    split <;> positivity
  unfold sourceCoefficients
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg hmain (ha j))
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (mul_nonneg (by positivity) (hc p (errorIndex i)))
  apply Finset.sum_nonneg
  intro χ _
  exact mul_nonneg (he p i χ j) (Real.rpow_nonneg (by unfold normValue;positivity) _)

def mainPowers (q Z Kmain ell deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(ell+deficit/6+paid),Kmain^((5:ℝ)/6)*Z^(-2*max r 0/3),Kmain,Kmain*Z^(-saving)]

def errorPowers (p:O)(k:ℕ)(q Z Kerror deficit paid saving r:ℝ):Fin 4→ℝ:=
  ![q*Z^(errorMoving p Z k)*Z^(errorRemoval p Z k+deficit/6+paid),
    Kerror^((5:ℝ)/6)*Z^(-2*max r 0/3),Kerror,Kerror*Z^(-saving)]

lemma main_core_power (q V C Z allowance Kmain ell deficit paid eps saving r:ℝ):
    ∀j,mainCores q V C Z allowance Kmain ell deficit paid eps saving r j=
      (V/C)*mainPowers q Z Kmain ell deficit paid saving r j*
        (V/C)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [mainCores,mainPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

lemma error_core_power (p:O)(k:ℕ)(q V C Z allowance Kerror deficit paid eps saving r:ℝ):
    ∀j,errorCores p k q V C Z allowance Kerror deficit paid eps saving r j=
      (V/C)*localErrorCost p (k-1)*errorPowers p k q Z Kerror deficit paid saving r j*
        (V/C/(normValue p)^k)^(CenteredMomentSecondChildPowerBudget.powers eps j)/reference q V C Z allowance := by
  intro j
  fin_cases j <;> simp [errorCores,errorPowers,CenteredMomentSecondChildPowerBudget.powers] <;> ring

theorem actual_power_reference_identity (P:Finset (Ideal O))(mainFactor b V C q Z allowance eps:ℝ)
    (N:ℕ)(H:Fin 4→ℝ)(Kmain ell deficit paid saving rmain:ℝ)
    (Kerror rerror:elementPool P→Fin 3→Ray→ℝ)
    (hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P) (i:Fin 3) (χ:Ray) (j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    ∀j,CenteredMomentFirstCommonReferencePower.normalizedPower b V C q Z allowance eps
      (sourceCoefficients P mainFactor amain aerror alpha j) N (alpha j)=
      C^eps*(b^N)^(alpha j)*averagedCoefficients P mainFactor H
        (mainCores q V C Z allowance Kmain ell deficit paid eps saving rmain)
        (fun p i χ=>errorCores p (errorIndex i+1) q V C Z allowance (Kerror p i χ)
          deficit paid eps saving (rerror p i χ)) j := by
  dsimp only
  intro j
  rw [source_normalized_identity P mainFactor b V C q Z allowance eps N _ _ _ hV hC hq hZ j]
  congr 1
  unfold averagedCoefficients
  simp only [one_mul]
  rw [main_core_power]
  congr 2
  · ring
  · apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    rw [error_core_power]
    simp only [Nat.add_sub_cancel]
    ring

end SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget
open CenteredMomentSourceLiveColumn
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma main_coefficients_nonneg (q Z K ell deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤ mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

lemma error_coefficients_nonneg (p:O)(k:ℕ)(q Z K deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

theorem common_annular_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤ s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(H0 Z allowance:ℝ),0<H0→0<Z→
    ∀(P:Finset (Ideal O))(mainFactor:ℝ)(H:Fin 4→ℝ),0≤ mainFactor→(∀j,0≤H j)→
    ∀(Kmain ell deficit paid saving rmain:ℝ),0≤Kmain→
    ∀(Kerror rerror:elementPool P→Fin 3→Ray→ℝ),(∀p i χ,0≤Kerror p i χ)→
    let q:ℝ:=τ.modulus.absNorm;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,sourceCoefficients P mainFactor amain aerror (powers ε) j*
          (volume (child s C R B τ t))^(powers ε j))*
          CenteredMomentFirstChildProfileControl.mass (child s C R B τ t)^2)→
    (commonEnergy (original s R seed) C hC τ t L CenteredMomentFirstAnnularMajorant.profile H0).re≤
      reference q (volume s) (C.absNorm:ℝ) Z allowance*
        (Cb*CenteredMomentFirstChildProfileControl.mass s^2*
          ∑j,(C.absNorm:ℝ)^ε*(b^N)^(powers ε j)*
            averagedCoefficients P mainFactor H
              (mainCores q (volume s) (C.absNorm:ℝ) Z allowance Kmain ell deficit paid ε saving rmain)
              (fun p i χ=>errorCores p (errorIndex i+1) q (volume s) (C.absNorm:ℝ)
                Z allowance (Kerror p i χ) deficit paid ε saving (rerror p i χ)) j):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_reference_powers N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L H0 Z allowance hH0 hZ
    P mainFactor H hmain hH Kmain ell deficit paid saving rmain hKmain Kerror rerror hKerror
  dsimp only
  intro hchildren
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hNC:0<(C.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hC.1
  have hcoeff:=source_coefficients_nonneg P mainFactor hmain
    (fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain ell deficit paid saving rmain j)
    (fun p i χ j=>H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror p i χ) deficit paid saving (rerror p i χ) j) (powers ε)
    (fun j=>mul_nonneg (hH j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZ.le hKmain j))
    (fun p i χ j=>mul_nonneg (hH j) (error_coefficients_nonneg _ _ _ _ _ _ _ _ _
      hq.le hZ.le (hKerror p i χ) j))
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L
    CenteredMomentFirstAnnularMajorant.profile H0 Z allowance hH0 hZ
    (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 _ (powers ε)
    hcoeff (powers_nonneg ε hε.le) hchildren
  apply hh.trans_eq
  unfold reference
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact actual_power_reference_identity P mainFactor b (volume s) (C.absNorm:ℝ)
    (τ.modulus.absNorm:ℝ) Z allowance ε N H Kmain ell deficit paid saving rmain Kerror rerror
    (volume_pos s) hNC hq hZ j

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentSecondSourceSeededPowerDescent
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondWindowBudget
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O

def fixedFactors (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ)):Fin 4→ℝ:=
  ![Cm*Z^(2*delta+epsilon)*cost*Ebase*heightEnvelope t^(J+J)*profileMoment J*profileMoment J,
    Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ),
    Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖,
    Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W/seed]

lemma coefficients_mul {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed (fun j=>f j*g j) j=
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j*g j:=by
  intro j
  fin_cases j <;> simp [CenteredMomentSecondChildPowerBudget.coefficients] <;> ring

lemma coefficients_mono {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ)
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤K)(hseed:0≤ seed)
    (hfg:∀j,f j≤g j):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j≤
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed g j:=by
  have h0:=hfg 0
  have h1:=hfg 1
  have h2:=hfg 2
  have h3:=hfg 3
  intro j
  fin_cases j <;> simp only [CenteredMomentSecondChildPowerBudget.coefficients, Fin.isValue, Matrix.cons_val,  Fin.reduceFinMk]
  · gcongr
  · have he:0≤CenteredMomentFirstChildProfileControl.exceptionalConstant N upper J Q K:=by
      unfold CenteredMomentFirstChildProfileControl.exceptionalConstant
      positivity
    gcongr
  · gcongr
  · gcongr

theorem seeded_factors_main (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
    ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (_hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤ radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    ∀j,seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W j≤
      fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j*
        mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hEp:0≤Ebase*Z^(ell+deficit/6+paid):=mul_nonneg hE (Real.rpow_nonneg hZ.le _)
  have hsqrt:Real.sqrt ((Ebase*Z^(ell+deficit/6+paid))*(Ebase*Z^(ell+deficit/6+paid)))=
      Ebase*Z^(ell+deficit/6+paid):=by rw [←pow_two,Real.sqrt_sq hEp]
  have hneg:(loProduct*wlo*wlo)^(-2/3:ℝ)≤loFloor^(-2/3:ℝ):=
    Real.rpow_le_rpow_of_nonpos hlo hloProduct (by norm_num)
  intro j
  fin_cases j
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk,hsqrt]
    exact le_of_eq (by ring)
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_sub hZ]
    have hbase:0≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)/Z^(2*max r 0/3)*radius^(5/6:ℝ):=by positivity
    have hh:=mul_le_mul_of_nonneg_left hneg hbase
    have hpow:Z^(-2*max r 0/3)=(Z^(2*max r 0/3))⁻¹:=by
      rw [show -2*max r 0/3=-(2*max r 0/3) by ring,Real.rpow_neg hZ.le]
    convert hh using 1 <;> (try rw [hpow]) <;> ring
  · simp [seededFactors,physicalFactors,fixedFactors,mainPowers,mul_comm,mul_left_comm,mul_assoc]
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    exact le_of_eq (by ring)

lemma fixedFactors_nonneg (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hZ:0≤Z)
    (hcost:0≤ cost)(hE:0≤Ebase)(hlo:0≤loFloor)(hseed:0≤ seed):
    ∀j,0≤fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j:=by
  have hh:0≤heightEnvelope t:=(heightEnvelope_pos t).le
  have hp:=profileMoment_nonneg J
  have hc:0≤Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  intro j
  fin_cases j <;> simp only [fixedFactors,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

theorem main_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤ seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤ radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W) j≤
      H j*mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hh:=coefficients_mono N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _
    hu hb1 hb2 hK hseed
    (seeded_factors_main Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed J Sf W hCm hCe hZ hE hradius hlo hloProduct)
  intro j
  exact (hh j).trans_eq (coefficients_mul N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _ j)

theorem error_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (profiles:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)(prime:O)(k:ℕ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤ seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤ radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t
        (cost*q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k))
        E E r loProduct wlo seed J J Sf W) j≤
      H j*errorPowers prime k q Z radius deficit paid saving r j:=by
  dsimp only
  have hh:=main_coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix
    Cm Ce Cd Ct Z epsilon delta theta B saving radius t
    (q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k)) cost Ebase
    (CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k) deficit paid r
    loProduct wlo loFloor seed J Sf W hu hb1 hb2 hK hseed hCm hCe hZ hE hradius hlo hloProduct
  intro j
  have hid:mainPowers (q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k)) Z radius
      (CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k) deficit paid saving r j=
      errorPowers prime k q Z radius deficit paid saving r j:=by
    fin_cases j <;> rfl
  have hhj:=hh j
  rw [hid] at hhj
  simpa only [mul_assoc] using hhj

end SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

end

end OAI

end

