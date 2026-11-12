module

public import Green64.Library.OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening
public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent
public import Green64.Library.OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight -/

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

lemma fullCuspHeight_le_barrier (x : FullCuspClasses) (w : HyperbolicSpace) :
    fullCuspHeight x w≤ max 3 (cuspBarrier 2 3 w) := by
  by_cases hx : fullCuspHeight x w≤3
  · exact hx.trans (le_max_left _ _)
  · have he : cuspBarrier 2 3 w=fullCuspHeight x w := by
      rw [cuspBarrier,fullCuspProfileSum_eq_single _
        (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) w x (by linarith),
        cuspBarrierProfile,cuspTransition_one 2 3 _ (by norm_num) (by linarith),one_mul]
      ring
    exact he ▸ le_max_right _ _

lemma cosetHeight_le_barrier (r : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight r w≤ max 3 (cuspBarrier 2 3 w) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    change cosetHeight (cosetOf M) w≤ max 3 (cuspBarrier 2 3 w)
    rw [cosetHeight_cosetOf]
    exact fullCuspHeight_le_barrier (fullCuspOf M.1) w

lemma kernel_compact_seed_height_bound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    ∃B : ℝ,a≤B ∧ 3≤B ∧ ∀q∈S,kernelQuotientBarrier 2 3 q≤B := by
  obtain ⟨B,hB⟩ := (hS.image (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num)).continuous).bddAbove
  refine ⟨max a (max 3 B),le_max_left _ _,(le_max_left 3 B).trans (le_max_right _ _),?_⟩
  intro q hq
  exact (hB (Set.mem_image_of_mem _ hq)).trans ((le_max_right 3 B).trans (le_max_right _ _))

def kernelSeedHeightBound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) : ℝ :=
  Classical.choose (kernel_compact_seed_height_bound a S hS)

lemma kernelSeedHeightBound_spec (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    a≤kernelSeedHeightBound a S hS ∧ 3≤kernelSeedHeightBound a S hS ∧
      ∀q∈S,kernelQuotientBarrier 2 3 q≤kernelSeedHeightBound a S hS :=
  Classical.choose_spec (kernel_compact_seed_height_bound a S hS)

def compactSeedTransition (a b B : ℝ) : C(Set.Icc a B,ℂ) :=
  ⟨fun v => (cuspTransition a b (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    ((cuspTransition_contDiff a b).continuous.comp continuous_subtype_val)⟩

def compactSeedProfile (a b B : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a B,ℂ) :=
  compactSeedTransition a b B * NormedSpace.exp (s • compactLogProfile a B ha)

lemma compactSeedProfile_entire (a b B : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactSeedProfile a b B ha) :=
  (differentiable_const _).mul (differentiable_exp_smul_const ℂ (compactLogProfile a B ha))

lemma compactSeedProfile_apply (a b B : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a B) :
    compactSeedProfile a b B ha s v=cuspSeedProfile a b s v := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a B ha)
  change (NormedSpace.exp (s • compactLogProfile a B ha)) v=
    NormedSpace.exp ((s • compactLogProfile a B ha) v) at he
  change (cuspTransition a b (v:ℝ):ℂ)*(NormedSpace.exp (s • compactLogProfile a B ha)) v=_
  rw [he,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,cuspSeedProfile,
    positiveHeightPower,logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]

lemma compactHeightProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (s : ℂ) (v : ℝ) (hv : v≤B) :
    compactHeightProfile a B hB (compactSeedProfile a b B ha s) v=cuspSeedProfile a b s v := by
  by_cases hva : a≤v
  · rw [compactHeightProfile,Set.indicator_of_mem (show v∈Set.Icc a B from ⟨hva,hv⟩),
      Set.projIcc_of_mem hB ⟨hva,hv⟩,compactSeedProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem (by simp [Set.mem_Icc,hva]),
      cuspSeedProfile,cuspTransition_zero a b v hab (le_of_not_ge hva)]
    simp

lemma kernelCompactProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (hthree : 3≤B) (s : ℂ) (q : KernelQuotient) (hq : kernelQuotientBarrier 2 3 q≤B) :
    kernelCompactProfile a B hB (compactSeedProfile a b B ha s) q=kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a B hB (compactSeedProfile a b B ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedProfile a b s) w
    unfold cuspCutoffCorrection
    apply tsum_congr
    intro r
    unfold cuspCutoffTerm
    rw [compactHeightProfile_seed a b B ha hab hB s _
      ((cosetHeight_le_barrier r w).trans (max_le hthree hq))]

def kernelLocalSeedL2 (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (s : ℂ) : KernelQuotientL2 :=
  kernelMassRestrictionCLM S hS.measurableSet
    (compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1
      (compactSeedProfile a b (kernelSeedHeightBound a S hS) ha s))

lemma kernelLocalSeedL2_entire (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) : Differentiable ℂ (kernelLocalSeedL2 S hS a b ha) := by
  exact (kernelMassRestrictionCLM S hS.measurableSet).differentiable.comp
    ((compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1).differentiable.comp
      (compactSeedProfile_entire a b (kernelSeedHeightBound a S hS) ha))

lemma kernelLocalSeedL2_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalSeedL2 S hS a b ha s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelQuotientSeed a b s) := by
  let B := kernelSeedHeightBound a S hS
  have hB := kernelSeedHeightBound_spec a S hS
  filter_upwards [kernelMassRestriction_coe S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)),
    compactProfileL2_ae_eq a B hB.1 (compactSeedProfile a b B ha s)] with q hr hp
  change kernelMassRestriction S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)) q=S.indicator (kernelQuotientSeed a b s) q
  rw [hr]
  by_cases hq : q∈S
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,hp]
    exact kernelCompactProfile_seed a b B ha hab hB.1 hB.2.1 s q (hB.2.2 q hq)
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelCorrectedSeed (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotient→ℂ :=
  fun q => kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q

def kernelLocalCorrectedSeed (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  kernelLocalSeedL2 S hS a b ha s +
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)

lemma kernelLocalCorrectedSeed_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS a b ha hab) (4/3:ℂ) := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt (4/3)).meromorphicAt.add
    (meromorphicAt_clm (kernelMassRestrictionCLM S hS.measurableSet)
      (kernelEisensteinL2Correction_meromorphicAt a b ha hab))

lemma kernelLocalCorrectedSeed_analyticAt_nonreal (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelLocalCorrectedSeed S hS a b ha hab) s := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt s).add
    ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelMassRestrictionCLM S hS.measurableSet) (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq
        (kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s hs hi) rfl)

lemma kernelLocalCorrectedSeed_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalCorrectedSeed S hS a b ha hab s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelCorrectedSeed a b ha hab s) := by
  filter_upwards [Lp.coeFn_add (kernelLocalSeedL2 S hS a b ha s)
      (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)),
    kernelLocalSeedL2_ae_eq S hS a b ha hab s,
    kernelMassRestriction_coe S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)]
    with q hsum hseed hcor
  change (kernelLocalSeedL2 S hS a b ha s+
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)) q=_
  rw [hsum]
  change kernelLocalSeedL2 S hS a b ha s q+
    kernelMassRestriction S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s) q=_
  rw [hseed,hcor]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed]
  · simp only [Set.indicator_of_notMem hq,add_zero]

lemma kernelLocalCorrectedSeed_residue_limit (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelLocalCorrectedSeed S hS a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinResidueVector a b ha hab))) := by
  have hseed : Tendsto (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    have hh : ContinuousAt (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s) (4/3:ℂ) :=
      (continuousAt_id.sub continuousAt_const).smul
        ((kernelLocalSeedL2_entire S hS a b ha).continuous.continuousAt)
    simpa only [sub_self,zero_smul] using hh.tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hcor := (kernelMassRestrictionCLM S hS.measurableSet).continuous.continuousAt.tendsto.comp
    (kernelEisensteinResidueVector_limit a b ha hab)
  have hh := hseed.add hcor
  simpa only [kernelLocalCorrectedSeed,smul_add,map_smul,Function.comp_def,zero_add] using hh

end

section
open Filter
open scoped BigOperators Classical Topology ContDiff

section PartialDerivatives
variable {A E G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma partial_iteratedFDeriv_contDiffAt (F : A→E→G) (a : A) (x : E)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (a,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (a,x) := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G→L[ℝ] E [×0]→L[ℝ]G)
  | succ k ih =>
    have hpair : ContDiffAt ℝ ∞
        (fun p : (A×E)×E => (p.1.1,p.2)) ((a,x),x) :=
      (contDiffAt_fst.fst).prodMk contDiffAt_snd
    have hp := ih.comp ((a,x),x) hpair
    have hd : ContDiffAt ℝ ∞
        (fun p : A×E => fderiv ℝ (fun y => iteratedFDeriv ℝ k (F p.1) y) p.2) (a,x) :=
      hp.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm :
        (E→L[ℝ] E [×k]→L[ℝ]G)→L[ℝ] E [×(k+1)]→L[ℝ]G)

lemma compact_family_derivative_bound (F : A→E→G)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P) (k : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀a∈K,∀x,‖iteratedFDeriv ℝ k (F a) x‖≤C := by
  have hc : ContinuousOn (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (K×ˢP) := by
    intro p hp
    exact (partial_iteratedFDeriv_contDiffAt F p.1 p.2 (hF p.1 hp.1 p.2) k).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod hP).bddAbove_image hc.norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha x
  by_cases hx : x∈P
  · exact (hC ⟨(a,x),⟨ha,hx⟩,rfl⟩).trans (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ k (F a) x=0 := by
      by_contra hn
      exact hx (hsupp a ha (support_iteratedFDeriv_subset k hn))
    rw [hz,norm_zero]
    exact le_max_right _ _

end PartialDerivatives
section

variable {A E ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_smooth_family_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ContDiff ℝ ∞ (fun x => ∑'i,b i*F (a i) x) := by
  choose C hC hbound using compact_family_derivative_bound F K P hK hP hF hsupp
  have hf (i : ι) : ContDiff ℝ ∞ (F (a i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hF (a i) (ha i) x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hprod (i : ι) : ContDiff ℝ ∞ (fun x => b i*F (a i) x) :=
    contDiff_const.mul (hf i)
  apply contDiff_tsum (v := fun k i => ‖b i‖*C k) hprod
  · intro k hk
    exact hb.mul_right (C k)
  · intro k i x hk
    have he : iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x=
        b i • iteratedFDeriv ℝ k (F (a i)) x :=
      by simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := b i) (i := k) (x := x)
          ((hf i).contDiffAt.of_le (by simp)))
    rw [he,norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound k (a i) (ha i) x) (norm_nonneg _)

end

lemma rowEnergy_real_smul (r : ℝ) (u : Fin 2→ℂ) :
    rowEnergy (r • u)=r^2*rowEnergy u := by
  simp only [rowEnergy,Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

def normalizedComplexRow (u : Fin 2→ℂ) : Fin 2→ℂ := (Real.sqrt (rowEnergy u))⁻¹ • u

lemma normalizedComplexRow_energy (u : Fin 2→ℂ) (hu : u≠0) :
    rowEnergy (normalizedComplexRow u)=1 := by
  rw [normalizedComplexRow,rowEnergy_real_smul,inv_pow,
    Real.sq_sqrt (rowEnergy_nonneg u),inv_mul_cancel₀ (rowEnergy_pos u hu).ne']

lemma rowEnergy_continuous : Continuous rowEnergy := by
  unfold rowEnergy
  fun_prop

lemma rowEnergy_unit_isCompact : IsCompact {u : Fin 2→ℂ | rowEnergy u=1} := by
  apply (isCompact_closedBall (0 : Fin 2→ℂ) 1).of_isClosed_subset
    (isClosed_eq rowEnergy_continuous continuous_const)
  intro u hu
  change rowEnergy u=1 at hu
  rw [Metric.mem_closedBall,dist_zero_right]
  simpa only [hu,Real.sqrt_one] using norm_le_sqrt_rowEnergy u

lemma rowEnergy_unit_ne_zero (u : Fin 2→ℂ) (hu : rowEnergy u=1) : u≠0 := by
  intro h
  simp [h,rowEnergy] at hu

def regularSpatialHeight (deltaLoss : ℝ) (p : SpatialCoordinates) : ℝ :=
  deltaLoss*ConcreteCompactWeight.positiveExtension (p 2/deltaLoss)

lemma regularSpatialHeight_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) :
    0< regularSpatialHeight deltaLoss p :=
  mul_pos hδ (ConcreteCompactWeight.positiveExtension_pos _)

lemma regularSpatialHeight_contDiff (deltaLoss : ℝ) : ContDiff ℝ ∞ (regularSpatialHeight deltaLoss) := by
  unfold regularSpatialHeight
  exact contDiff_const.mul (ConcreteCompactWeight.positiveExtension_smooth.comp
    ((contDiff_apply ℝ ℝ 2).div_const deltaLoss))

lemma regularSpatialHeight_eq (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularSpatialHeight deltaLoss p=p 2 := by
  rw [regularSpatialHeight,ConcreteCompactWeight.positiveExtension_eq _ ((le_div_iff₀ hδ).mpr (by simpa using hp))]
  field_simp

def regularRowKernel (s : ℂ) (deltaLoss : ℝ) (u : Fin 2→ℂ) (p : SpatialCoordinates) : ℂ :=
  logRatioPower s (regularSpatialHeight deltaLoss p)
    (heightDenominator (spatialHorizontal p) (regularSpatialHeight deltaLoss p) u)

lemma regularRowDenominator_contDiff (deltaLoss : ℝ) :
    ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates =>
      heightDenominator (spatialHorizontal p.2) (regularSpatialHeight deltaLoss p.2) p.1) := by
  have hc (j : Fin 2) : ContDiff ℝ ∞ (fun p : (Fin 2→ℂ)×SpatialCoordinates => p.1 j) :=
    (contDiff_apply ℝ ℂ j).comp contDiff_fst
  have hz := spatialHorizontal_contDiff.comp (contDiff_snd (E := Fin 2→ℂ))
  have hv := (regularSpatialHeight_contDiff deltaLoss).comp (contDiff_snd (E := Fin 2→ℂ))
  have hw := ((hc 0).mul hz).add (hc 1)
  simp only [heightDenominator,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  exact (((Complex.reCLM.contDiff.comp hw).mul (Complex.reCLM.contDiff.comp hw)).add
    ((Complex.imCLM.contDiff.comp hw).mul (Complex.imCLM.contDiff.comp hw))).add
    ((((Complex.reCLM.contDiff.comp (hc 0)).mul (Complex.reCLM.contDiff.comp (hc 0))).add
      ((Complex.imCLM.contDiff.comp (hc 0)).mul (Complex.imCLM.contDiff.comp (hc 0)))).mul (hv.pow 2))

lemma regularRowKernel_contDiffAt (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (u : Fin 2→ℂ) (hu : u≠0) (p : SpatialCoordinates) :
    ContDiffAt ℝ ∞ (Function.uncurry (regularRowKernel s deltaLoss)) (u,p) := by
  have hv : ContDiff ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => regularSpatialHeight deltaLoss q.2) :=
    (regularSpatialHeight_contDiff deltaLoss).comp contDiff_snd
  have hD := (regularRowDenominator_contDiff deltaLoss).contDiffAt (x := (u,p))
  have hv0 := regularSpatialHeight_pos deltaLoss hδ p
  have hD0 := heightDenominator_pos (spatialHorizontal p) (regularSpatialHeight deltaLoss p) hv0 u hu
  have hl := (hv.contDiffAt.log hv0.ne').sub (hD.log hD0.ne')
  exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (u,p) hl)).cexp

lemma heightDenominator_real_smul (z : ℂ) (v r : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (r•u)=r^2*heightDenominator z v u := by
  unfold heightDenominator
  have he : (r•u) 0*z+(r•u) 1=r•(u 0*z+u 1) := by
    simp only [Pi.smul_apply,smul_add,smul_mul_assoc]
  rw [he]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma heightDenominator_normalized (z : ℂ) (v : ℝ) (u : Fin 2→ℂ) :
    heightDenominator z v (normalizedComplexRow u)=heightDenominator z v u/rowEnergy u := by
  rw [normalizedComplexRow,heightDenominator_real_smul,inv_pow,Real.sq_sqrt (rowEnergy_nonneg u)]
  ring

lemma regularRowKernel_eq (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (u : Fin 2→ℂ)
    (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    regularRowKernel s deltaLoss u p=rowSmoothPower s u p := by
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp]
  unfold rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  rfl

lemma normalized_row_summand (s : ℂ) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (r : CuspCosets) (p : SpatialCoordinates) (hp : deltaLoss≤p 2) :
    summand 1 s r*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p=
      smoothSummand s r p := by
  have hu := embeddedRow_ne_zero r
  have hE := rowEnergy_pos _ hu
  have hv : 0<p 2 := hδ.trans_le hp
  have hD := heightDenominator_pos (spatialHorizontal p) (p 2) hv (embeddedRow r) hu
  rw [regularRowKernel,regularSpatialHeight_eq deltaLoss hδ p hp,heightDenominator_normalized]
  rw [summand,rowOperator_one,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hE.ne'),
    ←Complex.ofReal_log hE.le]
  unfold smoothSummand rowSmoothPower spatialHeightPower
  rw [←heightDenominator_eq_quadratic]
  unfold logRatioPower
  rw [Real.log_div hD.ne' hE.ne',mul_assoc,←Complex.exp_add]
  congr 2
  unfold spatialHorizontal
  push_cast
  ring

theorem regular_eisenstein_compact_smooth (s : ℂ) (hs : 2<s.re)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ψ : SpatialCoordinates→ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ∞ (fun p => ∑'r : CuspCosets,
      summand 1 s r*(ψ p*regularRowKernel s deltaLoss (normalizedComplexRow (embeddedRow r)) p)) := by
  apply compact_smooth_family_tsum (fun u p => ψ p*regularRowKernel s deltaLoss u p)
    {u : Fin 2→ℂ | rowEnergy u=1} (tsupport ψ) rowEnergy_unit_isCompact hcψ
  · intro u hu p
    have hψp : ContDiffAt ℝ ∞ (fun q : (Fin 2→ℂ)×SpatialCoordinates => ψ q.2) (u,p) :=
      hψ.contDiffAt.comp (u,p) contDiffAt_snd
    exact hψp.mul (regularRowKernel_contDiffAt s deltaLoss hδ u (rowEnergy_unit_ne_zero u hu) p)
  · intro u hu
    exact tsupport_mul_subset_left
  · intro r
    exact normalizedComplexRow_energy _ (embeddedRow_ne_zero r)
  · exact summable_norm_summand 1 s hs

theorem smoothEisenstein_contDiffAt (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (smoothEisenstein s) p := by
  let deltaLoss : ℝ:=p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let χ : ContDiffBump p := ⟨1,2,by norm_num,by norm_num⟩
  let ψ : SpatialCoordinates→ℂ:=fun q => (χ q:ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcψ : HasCompactSupport ψ := by
    have he : Function.support ψ=Function.support (fun q => χ q) := by
      ext q
      simp [Function.mem_support,ψ]
    change IsCompact (closure (Function.support ψ))
    rw [he]
    exact χ.hasCompactSupport
  have hsum := regular_eisenstein_compact_smooth s hs deltaLoss hδ ψ hψ hcψ
  apply hsum.contDiffAt.congr_of_eventuallyEq
  have hn : ∀ᶠq in 𝓝 p, deltaLoss<q 2 :=
    (isOpen_lt continuous_const (continuous_apply 2)).mem_nhds (by dsimp [deltaLoss]; linarith)
  filter_upwards [χ.eventuallyEq_one,hn] with q hχ hq
  unfold smoothEisenstein
  apply tsum_congr
  intro r
  have hψq : ψ q=1 := by simp [ψ,hχ]
  rw [hψq,one_mul]
  exact (normalized_row_summand s deltaLoss hδ r q hq.le).symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

lemma kernel_contMDiff_of_spatial (f : KernelQuotient→ℂ) (F : SpatialCoordinates→ℂ)
    (hF : ∀p,0<p 2→ ContDiffAt ℝ ∞ F p)
    (hcoord : ∀q : KernelQuotient,∀p∈hyperbolicSpatialChart.target,
      f ((kernelQuotientChart q).symm p)=F p) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hc : ContinuousAt (kernelQuotientChart q) q :=
    (kernelQuotientChart q).continuousOn.continuousAt ((kernelQuotientChart q).open_source.mem_nhds hq)
  have heq : f=ᶠ[𝓝 q] (fun t => F (kernelQuotientChart q t)) := by
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with t ht
    rw [←hcoord q _ ((kernelQuotientChart q).map_source ht).1,
      (kernelQuotientChart q).left_inv ht]
  rw [contMDiffAt_iff]
  refine ⟨((hF _ (hyperbolicSpatialChart_target_positive hp)).continuousAt.comp hc).congr heq.symm,?_⟩
  have he : (fun p => f ((kernelQuotientChart q).symm p))=ᶠ[𝓝 (kernelQuotientChart q q)] F := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hp
    exact hcoord q p hp
  have hh := (hF _ (hyperbolicSpatialChart_target_positive hp)).congr_of_eventuallyEq he
  have hh' := hh.contDiffWithinAt (s := Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    chartAt_self_eq,kernelSpatial_chartAt,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh'

lemma kernelQuotientEisenstein_coordinate (s : ℂ) (hs : 2<s.re) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientEisenstein s hs ((kernelQuotientChart q).symm p)=smoothEisenstein s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp,
    kernelQuotientEisenstein_mk,hyperbolicEisenstein_upperPoint,
    smoothEisenstein_eq_actual s p (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientEisenstein_contMDiff (s : ℂ) (hs : 2<s.re) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientEisenstein s hs) :=
  kernel_contMDiff_of_spatial _ _ (smoothEisenstein_contDiffAt s hs)
    (kernelQuotientEisenstein_coordinate s hs)

lemma kernelQuotientSeed_coordinate (a b : ℝ) (s : ℂ) (q : KernelQuotient)
    (p : SpatialCoordinates) (hp : p∈hyperbolicSpatialChart.target) :
    kernelQuotientSeed a b s ((kernelQuotientChart q).symm p)=smoothCuspSeedField a b s p := by
  rw [kernelQuotientChart_symm,hyperbolicSpatialChart_symm_eq hp]
  change smoothCuspSeed a b s _=smoothCuspSeedField a b s p
  rw [smoothCuspSeedField,dite_eq_left (hyperbolicSpatialChart_target_positive hp)]
  rfl

lemma kernelQuotientSeed_contMDiff (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelQuotientSeed a b s) :=
  kernel_contMDiff_of_spatial _ _ (actual_smoothCuspSeed_contDiffAt a b s ha hab)
    (kernelQuotientSeed_coordinate a b s)

def kernelCutoffRemainderTest (n : ℕ) (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) : kernelSmoothTests := by
  let f : KernelQuotient→ℂ:=fun q => (kernelExhaustionCutoff n q:ℂ)*
    (kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q)
  refine ⟨f,?_,?_⟩
  · have hm : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1*z.2) := contDiff_fst.mul contDiff_snd
    exact hm.contMDiff.comp
      ((Complex.ofRealCLM.contDiff.contMDiff.comp (kernelExhaustionCutoff_smooth n)).prodMk_space
        ((kernelQuotientEisenstein_contMDiff s hs).sub (kernelQuotientSeed_contMDiff a b s ha hab)))
  · apply HasCompactSupport.of_support_subset_isCompact (kernelExhaustionCutoff_hasCompactSupport n)
    intro q hq
    by_contra hn
    have hz : kernelExhaustionCutoff n q=0 := by
      by_contra hne
      exact hn (subset_closure hne)
    exact hq (by simp [f,hz])

lemma kernelCutoffRemainderTest_apply (n : ℕ) (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (q : KernelQuotient) :
    (kernelCutoffRemainderTest n a b ha hab s hs).1 q=(kernelExhaustionCutoff n q:ℂ)*
      (kernelQuotientEisenstein s hs q-kernelQuotientSeed a b s q) := rfl

end CubicEisenstein

open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)

def HasInitialCanonicalDensityAtRadius {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∀ A : ℝ,0≤A → ∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    (∀s,V₁ s≠0→|s|≤A) → (∀s,V₂ s≠0→|s|≤A) →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      (∀z∈T,IsCoprime z.1 (∏P∈S,P)) →
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2

end InitialMeanSquare

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CuspResidues -/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

lemma levelThree_integral_eq_translation (M : CubicKubota.levelThree)
    (hc : (M : SL(2,ActualEisensteinCubic.O)) 1 0=0) :
    integralComplexMatrix M.1=complexTranslation (ConcreteTraceCRT.eisEmbedding ((M : SL(2,ActualEisensteinCubic.O)) 0 1)) := by
  have hr := row_eq_one_of_lower_left_zero M hc
  have hd : (M : SL(2,ActualEisensteinCubic.O)) 1 1=1 := by
    simpa [row,Matrix.one_apply] using congrFun hr 1
  have ha : (M : SL(2,ActualEisensteinCubic.O)) 0 0=1 := by
    have hh : (M : SL(2,ActualEisensteinCubic.O)) 0 0 * (M : SL(2,ActualEisensteinCubic.O)) 1 1-
      (M : SL(2,ActualEisensteinCubic.O)) 0 1 * (M : SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,ActualEisensteinCubic.O)).property
    simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,ha,hc,hd]

lemma periodDomain_unique_translate (z w t : ℂ) (hz : z∈periodDomain) (hw : w∈periodDomain)
    (ht : t∈periodLattice) (he : z=w+t) : z=w := by
  have hf := ZSpan.fract_add_ZSpan periodBasis w ht
  rw [←he,(ZSpan.fract_eq_self (b := periodBasis)).mpr hz,
    (ZSpan.fract_eq_self (b := periodBasis)).mpr hw] at hf
  exact hf

def cuspPeriodRegion : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ 1<hyperbolicHeight w}

lemma cuspPeriodRegion_measurable : MeasurableSet cuspPeriodRegion :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Ioi.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodRegion_injective :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) cuspPeriodRegion := by
  intro u hu v hv he
  obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff globalKubotaKernel u v).mp he
  have hMu : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • v=u := hM
  have hc : (M:SL(2,ActualEisensteinCubic.O)) 1 0=0 := by
    by_contra hn
    have hb := integral_hyperbolicHeight_mul_le_one (M:SL(2,ActualEisensteinCubic.O)) hn v
    rw [hMu] at hb
    have huh : 1<hyperbolicHeight u := hu.2
    have hvh : 1<hyperbolicHeight v := hv.2
    nlinarith [mul_pos (sub_pos.mpr huh) (sub_pos.mpr hvh)]
  let N : CubicKubota.levelThree := ⟨M,globalKubotaKernel_le_levelThree M.2⟩
  have ht := levelThree_integral_eq_translation N hc
  obtain ⟨z,t,htpos,hvrep⟩ := upperPoint_surjective v
  have hua : u=upperPoint (z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)) t htpos := by
    rw [←hMu,←hvrep,ht,complexTranslation_action]
  have hvl : hyperbolicHorizontal v=z := by rw [←hvrep,hyperbolicHorizontal_upperPoint]
  have hul : hyperbolicHorizontal u=z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1) := by
    rw [hua,hyperbolicHorizontal_upperPoint]
  obtain ⟨k,hk⟩ := CubicKubota.levelThree_upper N
  have hper : ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)∈periodLattice := by
    change ConcreteTraceCRT.eisEmbedding ((N:CubicKubota.levelThree).1 0 1)∈periodLattice
    rw [hk,map_mul,map_ofNat]
    exact three_embedding_mem k
  have hehor : hyperbolicHorizontal u=hyperbolicHorizontal v :=
    periodDomain_unique_translate _ _ _ hu.1 hv.1 hper (by rw [hul,hvl])
  have hez : z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)=z := by
    simpa only [hul,hvl] using hehor
  rw [hua,hez,←hvrep]

def cuspPeriodStrip (a b : ℝ) : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ hyperbolicHeight w∈Set.Icc a b}

lemma cuspPeriodStrip_measurable (a b : ℝ) : MeasurableSet (cuspPeriodStrip a b) :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Icc.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodStrip_injective (a b : ℝ) (ha : 1<a) :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) (cuspPeriodStrip a b) := by
  apply kernelProjection_cuspPeriodRegion_injective.mono
  intro w hw
  exact ⟨hw.1,ha.trans_le hw.2.1⟩

lemma kernelProjection_cuspPeriodStrip_measurePreserving (a b : ℝ) (ha : 1<a) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      ((integralQuotientVolume globalKubotaKernel).restrict
        (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b)) :=
  kernelProjection_measurePreserving_on _ (cuspPeriodStrip_measurable a b)
    (kernelProjection_cuspPeriodStrip_injective a b ha)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

def kernelCuspStripSet : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6

lemma kernelCuspStripSet_measurable : MeasurableSet kernelCuspStripSet :=
  (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn
    (kernelProjection_cuspPeriodStrip_injective 5 6 (by norm_num))

def kernelCuspStripAverage : KernelQuotientL2→L[ℂ]ℂ :=
  innerSL ℂ (indicatorConstLp 2 kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) (1:ℂ))

lemma kernelCuspStripAverage_apply (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫q in kernelCuspStripSet,F q∂integralQuotientVolume globalKubotaKernel :=
  L2.inner_indicatorConstLp_one kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) F

lemma kernelCuspStripAverage_hyperbolic (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspStripAverage_apply]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := (Lp.aestronglyMeasurable F).mono_measure (Measure.restrict_le_self (s := kernelCuspStripSet))
  change AEStronglyMeasurable F ((integralQuotientVolume globalKubotaKernel).restrict
    (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6)) at hh
  change (∫q in integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6,
    F q∂integralQuotientVolume globalKubotaKernel)=_
  rw [←hm.map_eq] at hh ⊢
  exact integral_map hm.measurable.aemeasurable hh

def kernelCuspAverageCompact : Set KernelQuotient :=
  {q | kernelQuotientBarrier 2 3 q≤6}

lemma kernelCuspAverageCompact_isCompact : IsCompact kernelCuspAverageCompact :=
  kernelBarrier_sublevel_isCompact 6

lemma kernelCuspStripSet_subset_compact : kernelCuspStripSet⊆kernelCuspAverageCompact := by
  rintro q ⟨w,hw,rfl⟩
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  have hfive : 5≤v := by simpa only [hyperbolicHeight_upperPoint] using hw.2.1
  have hsix : v≤6 := by simpa only [hyperbolicHeight_upperPoint] using hw.2.2
  change cuspBarrier 2 3 (upperPoint z v hv)≤6
  have hh := cuspBarrier_high 2 3 (by norm_num) (by norm_num) 1 z v hv (by linarith)
  simpa only [map_one,one_smul] using hh.le.trans hsix

lemma kernelCuspStripAverage_restrict (F : KernelQuotientL2) :
    kernelCuspStripAverage (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspStripAverage F := by
  rw [kernelCuspStripAverage_apply,kernelCuspStripAverage_apply]
  apply setIntegral_congr_ae kernelCuspStripSet_measurable
  filter_upwards [kernelMassRestriction_coe kernelCuspAverageCompact
    kernelCuspAverageCompact_isCompact.measurableSet F] with q hq
  intro hmem
  exact hq.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact hmem) F)

def kernelCuspAverageFamily (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspStripAverage
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspAverageFamily_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspAverageFamily a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm kernelCuspStripAverage
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspAverageFamily_residue_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspAverageFamily a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := kernelCuspStripAverage.continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspStripAverage_restrict,kernelCuspAverageFamily] using hh

lemma kernelCuspAverageFamily_actual_integral (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspAverageFamily a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspAverageFamily,kernelCuspStripAverage_hyperbolic]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hlocal := kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s
  have hrestr := ae_restrict_of_ae hlocal (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  apply integral_congr_ae
  filter_upwards [hp,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

def spatialComplexSplit : EuclideanSpatial ≃ᵐ ℝ × ℂ :=
  spatialHeightSplit.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)

lemma spatialComplexSplit_fst (p : EuclideanSpatial) : (spatialComplexSplit p).1=p 2 := rfl
lemma spatialComplexSplit_snd (p : EuclideanSpatial) :
    (spatialComplexSplit p).2=(p 0:ℂ)+(p 1:ℂ)*Complex.I := rfl

lemma spatialComplexSplit_preserves_volume : MeasurePreserving spatialComplexSplit volume volume :=
  ((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi.symm).comp
    spatialHeightSplit_preserves_volume

lemma spatialComplexSplit_coordinates (w : HyperbolicSpace) :
    spatialComplexSplit (hyperbolicEuclideanCoordinates w)=
      (hyperbolicHeight w,hyperbolicHorizontal w) := by
  apply Prod.ext
  · rfl
  · change (hyperbolicHorizontal w).re+(hyperbolicHorizontal w).im*Complex.I=hyperbolicHorizontal w
    exact Complex.re_add_im _

def cuspCoordinateLift (q : ℝ × ℂ) : HyperbolicSpace :=
  euclideanToHyperbolic (spatialComplexSplit.symm q)

lemma cuspCoordinateLift_positive (v : ℝ) (z : ℂ) (hv : 0<v) :
    cuspCoordinateLift (v,z)=upperPoint z v hv := by
  have he : spatialComplexSplit (hyperbolicEuclideanCoordinates (upperPoint z v hv))=(v,z) := by
    simp only [spatialComplexSplit_coordinates,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  have he' := congrArg spatialComplexSplit.symm he
  rw [spatialComplexSplit.symm_apply_apply] at he'
  rw [cuspCoordinateLift,←he',euclideanToHyperbolic_coordinates]

def cuspEuclideanStrip : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc (5:ℝ) 6 ×ˢ periodDomain)

lemma cuspEuclideanStrip_measurable : MeasurableSet cuspEuclideanStrip :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma cuspEuclideanStrip_positive : cuspEuclideanStrip⊆euclideanUpperHalf := by
  intro p hp
  have hh : 5≤p 2 := hp.1.1
  change 0<p 2
  linarith

lemma cuspEuclideanStrip_preimage :
    hyperbolicEuclideanCoordinates ⁻¹' cuspEuclideanStrip=cuspPeriodStrip 5 6 := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc (5:ℝ) 6 ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates (g : HyperbolicSpace→ℂ)
    (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive
  rw [cuspEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip 5 6))
  have he : (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [cuspEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma hyperbolicEisenstein_continuous (s : ℂ) (hs : 2<s.re) :
    Continuous (hyperbolicEisenstein s) := by
  have hcoord : Continuous (fun p : UpperCoordinates =>
      upperEisenstein p.1.1 p.1.2 p.2 s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hin : ContinuousAt (fun q : UpperCoordinates => (q,s)) p :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun q : UpperCoordinates => (q,s))
      (upperEisenstein_joint_continuousAt (p,s) hs) hin
  convert hcoord.comp hyperbolicCoordinates_continuous using 1
  ext w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  simp only [Function.comp_def,hyperbolicEisenstein_upperPoint,hyperbolicCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma spatialComplexSplit_symm_eq (q : ℝ × ℂ) :
    spatialComplexSplit.symm q=WithLp.toLp 2 ![q.2.re,q.2.im,q.1] := by
  apply spatialComplexSplit.injective
  rw [spatialComplexSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (Complex.re_add_im q.2).symm

lemma spatialComplexSplit_symm_continuous : Continuous spatialComplexSplit.symm := by
  change Continuous (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  fun_prop

lemma cuspCoordinateLift_continuousAt (q : ℝ × ℂ) (hq : 0<q.1) :
    ContinuousAt cuspCoordinateLift q := by
  have hp : 0<(spatialComplexSplit.symm q) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hq
  exact (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt.comp
    spatialComplexSplit_symm_continuous.continuousAt

lemma cuspCoordinateLift_weighted_integrable (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2

lemma hyperbolicEisenstein_cusp_average (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  rw [cuspPeriodStrip_integral_coordinates _
    (hyperbolicEisenstein_continuous s hs).aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable _ (hyperbolicEisenstein_continuous s hs))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,hyperbolicEisenstein s (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint]
    rw [eisensteinFourierCoefficient]
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,mul_one]
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (by positivity))).symm
  dsimp only
  rw [hh,eisensteinConstantCoefficient_formula v hpos s hs]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def cuspMainHeightFactor (s : ℂ) : ℂ :=
  ((6:ℂ)^(s-2)-(5:ℂ)^(s-2))/(s-2)

def cuspScatterHeightFactor (s : ℂ) : ℂ :=
  ((5:ℂ)^(-s)-(6:ℂ)^(-s))/s

lemma cuspHeightPower_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^s) (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (by linarith [hv.1]))).continuousWithinAt

lemma cuspMainHeightFactor_integral (s : ℂ) (hs : s≠2) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(s-3))=cuspMainHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : s-3≠(-1:ℂ) := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(s-3+1)-(5:ℂ)^(s-3+1))/(s-3+1)=_
  have he : s-3+1=s-2 := by ring
  rw [he]
  rfl

lemma cuspScatterHeightFactor_integral (s : ℂ) (hs : s≠0) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1))=cuspScatterHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : -s-1≠(-1:ℂ) := by intro h; apply hs; linear_combination -h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(-s-1+1)-(5:ℂ)^(-s-1+1))/(-s-1+1)=_
  have he : -s-1+1=-s := by ring
  rw [he,cuspScatterHeightFactor]
  ring

lemma cuspMainHeightFactor_differentiableAt (s : ℂ) (hs : s≠2) :
    DifferentiableAt ℂ cuspMainHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z-2) s := differentiableAt_id.sub_const 2
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div hd (sub_ne_zero.mpr hs)

lemma cuspScatterHeightFactor_differentiableAt (s : ℂ) (hs : s≠0) :
    DifferentiableAt ℂ cuspScatterHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div differentiableAt_id hs

def cuspConstantAverage (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(cuspMainHeightFactor s+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*cuspScatterHeightFactor s)

lemma hyperbolicEisenstein_cusp_average_eq (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      cuspConstantAverage s := by
  have hs2 : s≠2 := by intro he; subst s; norm_num at hs
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  rw [hyperbolicEisenstein_cusp_average s hs]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
        ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*(v:ℂ)^(-s-1)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have h1 : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have h2 : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [h1,h2]
    ring
  rw [heq,integral_const_mul,integral_add (cuspHeightPower_integrable _)
    ((cuspHeightPower_integrable _).const_mul _),integral_const_mul,
    cuspMainHeightFactor_integral s hs2,cuspScatterHeightFactor_integral s hs0]
  rfl

lemma cuspConstantAverage_differentiableAt (s : ℂ) (hs : 4/3<s.re) (hs2 : s≠2) :
    DifferentiableAt ℂ cuspConstantAverage s := by
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hsc : DifferentiableAt ℂ (fun z : ℂ => scatteringCoefficient z 0) s :=
    (arithmeticDirichletSeries_zero_differentiableAt s hs).div_const _
  exact ((cuspMainHeightFactor_differentiableAt s hs2).add
    ((((differentiableAt_const (Real.pi:ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).mul hsc).mul
      (cuspScatterHeightFactor_differentiableAt s hs0))).const_mul _

lemma cuspScatterHeightFactor_center_re_pos :
    0<(cuspScatterHeightFactor (4/3:ℂ)).re := by
  have h5 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤5) (-(4/3:ℝ))
  have h6 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤6) (-(4/3:ℝ))
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at h5 h6
  have he : cuspScatterHeightFactor (4/3:ℂ)=
      (((5:ℝ)^(-(4/3:ℝ))-(6:ℝ)^(-(4/3:ℝ)))/(4/3:ℝ):ℝ) := by
    rw [cuspScatterHeightFactor,←h5,←h6]
    push_cast
    rfl
  rw [he,Complex.ofReal_re]
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
  · norm_num

def cuspConstantAverageResidue : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    cuspScatterHeightFactor (4/3:ℂ)

lemma cuspConstantAverageResidue_ne_zero : cuspConstantAverageResidue≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero
  · intro he
    have hh := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh

lemma cuspConstantAverage_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*cuspConstantAverage (x:ℂ))
      (𝓝[>] (4/3:ℝ)) (𝓝 cuspConstantAverageResidue) := by
  have harg : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝 (4/3:ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hlinear := harg.sub_const (4/3:ℂ)
  norm_num only [sub_self] at hlinear
  have hm := (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hh := (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hpi : Tendsto (fun x : ℝ => (Real.pi:ℂ)/((x:ℂ)-1))
      (𝓝[>] (4/3:ℝ)) (𝓝 (3*(Real.pi:ℂ))) := by
    convert tendsto_const_nhds.div (harg.sub_const 1) (by norm_num : (4/3:ℂ)-1≠0) using 1 ; ring_nf
  have hall := ((hlinear.mul hm).add
    ((hpi.mul scatteringCoefficient_zero_oneSidedResidue).mul hh)).const_mul
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  convert hall using 1
  · ext x
    dsimp only [cuspConstantAverage,Function.comp_def]
    ring
  · simp only [zero_mul,zero_add,cuspConstantAverageResidue]
    ring_nf

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma kernelSpectralResolvent_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_of_isUnit z hz) rfl

lemma kernelEisensteinResolvent_analyticAt_of_isUnit (s : ℂ)
    (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_of_isUnit _ hs).comp_of_eq
    (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelCuspAverageFamily_analyticAt_of_isUnit (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s := by
  have hcor : AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s :=
    ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_of_isUnit s hs)
  have hlocal : AnalyticAt ℂ
      (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab) s :=
    ((kernelLocalSeedL2_entire kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha).analyticAt s).add
      ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
        (kernelMassRestrictionCLM kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet)
        (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq hcor rfl)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    kernelCuspStripAverage _).comp_of_eq hlocal rfl

lemma kernelCuspAverageFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s :=
  kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

def cuspUpperParameterRegion : Set ℂ := {s | (4/3:ℝ)<s.re ∧ 0<s.im}

lemma cuspUpperParameterRegion_isOpen : IsOpen cuspUpperParameterRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma cuspUpperParameterRegion_convex : Convex ℝ cuspUpperParameterRegion :=
  ((convex_Ioi (4/3:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)

lemma cuspConstantAverage_analyticOn_upper : AnalyticOnNhd ℂ cuspConstantAverage cuspUpperParameterRegion := by
  apply (Complex.analyticOnNhd_iff_differentiableOn cuspUpperParameterRegion_isOpen).mpr
  intro s hs
  apply (cuspConstantAverage_differentiableAt s hs.1 ?_).differentiableWithinAt
  intro he
  subst s
  norm_num [cuspUpperParameterRegion] at hs

lemma kernelCuspAverageFamily_eq_upper_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion := by
  have hleft : AnalyticOnNhd ℂ (kernelCuspAverageFamily a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelCuspAverageFamily_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈cuspUpperParameterRegion := by
    norm_num [cuspUpperParameterRegion]
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : kernelCuspAverageFamily a b ha hab =ᶠ[𝓝 (5+Complex.I:ℂ)] cuspConstantAverage := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact (hoverlap s hs.1 hs.2).trans (hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1]))
  exact hleft.eqOn_of_preconnected_of_eventuallyEq cuspConstantAverage_analyticOn_upper
    cuspUpperParameterRegion_convex.isPreconnected hstart hevent

lemma kernelCuspAverageFamily_eq_real_of_upper (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hupper : Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion)
    (x : ℝ) (hx : (4/3:ℝ)<x) (hx2 : x≠2)
    (hunit : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter (x:ℂ)))) :
    kernelCuspAverageFamily a b ha hab (x:ℂ)=cuspConstantAverage (x:ℂ) := by
  have hpath : Tendsto (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hcont : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) :=
      (Complex.continuous_ofReal.mul_const Complex.I).const_add (x:ℂ)
    have hh := (hcont.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hh
  have hleft := (kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab (x:ℂ) hunit).continuousAt.tendsto.comp hpath
  have hx2' : (x:ℂ)≠2 := by exact_mod_cast hx2
  have hright := (cuspConstantAverage_differentiableAt (x:ℂ) hx hx2').continuousAt.tendsto.comp hpath
  have hevent : (fun t : ℝ => kernelCuspAverageFamily a b ha hab ((x:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => cuspConstantAverage ((x:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    apply hupper
    simpa only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.mul_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add,mul_one] using And.intro hx ht
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright hevent

lemma realAbove_tendsto_complex_punctured :
    Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (4/3:ℝ)<x at hx
    change (x:ℂ)≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith [hx]

lemma kernelEisensteinResidueVector_average_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab)=cuspConstantAverageResidue := by
  have hupper := kernelCuspAverageFamily_eq_upper_of_overlap a b ha hab hoverlap
  have hleft := (kernelCuspAverageFamily_residue_limit a b ha hab).comp realAbove_tendsto_complex_punctured
  have hunit := realAbove_tendsto_complex_punctured.eventually kernelEisensteinPencil_eventually_isUnit
  have hlt : ∀ᶠx : ℝ in 𝓝[>] (4/3:ℝ),x<2 := by
    have hh : ∀ᶠx : ℝ in 𝓝 (4/3:ℝ),x<2 := Iio_mem_nhds (by norm_num)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hevent : (fun x : ℝ => ((x:ℂ)-4/3)*kernelCuspAverageFamily a b ha hab (x:ℂ))
      =ᶠ[𝓝[>] (4/3:ℝ)] (fun x : ℝ => ((x:ℂ)-4/3)*cuspConstantAverage (x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,hunit,hlt] with x hx hux hxx
    rw [kernelCuspAverageFamily_eq_real_of_upper a b ha hab hupper x hx hxx.ne hux]
  exact tendsto_nhds_unique_of_eventuallyEq hleft cuspConstantAverage_oneSidedResidue hevent

lemma kernelEisensteinResidueVector_ne_zero_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelEisensteinResidueVector a b ha hab≠0 := by
  intro he
  have hh := kernelEisensteinResidueVector_average_of_overlap a b ha hab hoverlap
  rw [he,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.DensityTransfer -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalShortState_from_certificate
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (A : ℝ) (hA : 0≤A) (ε κ : ℝ) (hε : 0<ε) (hκ : 0<κ) :
    ∃d : ℕ,∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
      ∃C : ℝ,0≤C ∧ ∀(θ Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
        W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      C*(X*F)^2*Z^(κ+7*ε-(1:ℝ)/40)*(1+|θ|)^d := by
  obtain ⟨d,hshort⟩:=canonicalShortState_uniform_twist
    (Real.exp (-A)) (Real.exp A) (Real.exp_pos _) ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨Cs,hCs,hsbound⟩:=hshort W hs hW
  obtain ⟨Cm,hCm,hm⟩:=hmodels A hA W hs hW κ hκ
  refine ⟨Cs*Cm,mul_nonneg hCs hCm,?_⟩
  intro θ Z η Ψ m labels X F K hstate hZ hZbig hη hbudget hfixed
  by_cases hF : F<Z^((1:ℝ)/1000)
  · have hgeometry:=canonicalShortState_geometry S hSp hbad base Z η Ψ m labels X F K
      hstate hZ hZbig hη hbudget hfixed
    obtain ⟨rays,lengthScale,hsize,hformula⟩:=hm Z K X F θ hZ hstate.row_ge_one hstate.column_pos
      hstate.label_ge_one hF.le Ψ hstate.coefficient m hstate.mask_ne_zero hgeometry.2.2.2.2
    have hb:=hsbound θ rays S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig
      hη hbudget hfixed lengthScale (fun _=>hformula)
    calc
      _ ≤ (Cs*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=hb
      _ = Cs*(1+|θ|)^d*((rays:ℝ)^2*‖lengthScale‖^2)*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=by
        rw [Real.norm_eq_abs]
        ring
      _ ≤ Cs*(1+|θ|)^d*(Cm*Z^κ)*(X*F)^2*Z^(7*ε-(1:ℝ)/40):=by gcongr
      _ = _ := by
        rw [show κ+7*ε-(1:ℝ)/40=κ+(7*ε-(1:ℝ)/40) by ring,
          Real.rpow_add (zero_lt_one.trans_le hZ)]
        ring
  · have hb:=hsbound θ 0 S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig
      hη hbudget hfixed 0 (fun hf=>False.elim (hF hf))
    have hz : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
        W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤0 := by
      simpa only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_mul] using hb
    exact hz.trans (by positivity)

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalLog_actual_step
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (A : ℝ) (hA : 0≤A) (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) :
    ∃d : ℕ,∀J : ℕ,d≤2*J →
    ∃child : Bool→Bool→ℝ→ℂ,
      (∀side neg,ContDiff ℝ ∞ (child side neg)) ∧
      (∀side neg s,child side neg s≠0→|s|≤2*A+11) ∧
      ∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
      ∃C : ℝ,0≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K E t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      1≤X → Real.exp A*X≤D → 1≤E →
      (∀side neg (Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏P∈S,P) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        outsideLogEnergy S D hbad (normHeightTwist Ψ' s) m' labels' (child side neg) X' K'≤
          E*(X'*F')^2*(1+‖s‖)^(2*J)) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
  obtain ⟨d,hshort⟩:=canonicalShortState_from_certificate S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels A hA η η hη hη
  refine ⟨d,?_⟩
  intro J hJ
  obtain ⟨g,v,hgc,hvc,hgone,hgb,hwin,hvb⟩:=fixed_reopening_profiles A hA
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  obtain ⟨w₁,w₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hlarge⟩:=
    progressingCanonicalFamily_closed_step g v A (2*A+4) (2*A+5) (by linarith) (by linarith)
      hgb hvb hwin hgone η η η hη hη hη hηsmall hbudget' J
  let child : Bool→Bool→ℝ→ℂ:=fun side neg=>
    orientedLogProfile neg ((if side then w₁ else w₂) (if neg then 5 else 6))
  have hcs : ∀side neg,ContDiff ℝ ∞ (child side neg) := by
    intro side neg
    cases side <;> cases neg
    · exact hws₂ 6
    · exact Complex.conjCLE.contDiff.comp (hws₂ 5)
    · exact hws₁ 6
    · exact Complex.conjCLE.contDiff.comp (hws₁ 5)
  have hcb : ∀side neg s,child side neg s≠0→|s|≤2*A+11 := by
    intro side neg s hn
    have hnorm (w : Fin 7→ℝ→ℂ) (hw : ∀i t,w i t≠0→|t|≤(2*A+4)+7)
        (i : Fin 7) (hi : w i s≠0) : |s|≤2*A+11 := by
      have hh:=hw i s hi
      linarith
    cases side <;> cases neg
    · exact hnorm w₂ hwb₂ 6 hn
    · apply hnorm w₂ hwb₂ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
    · exact hnorm w₁ hwb₁ 6 hn
    · apply hnorm w₁ hwb₁ 5
      intro hz
      exact hn (by simp [child,orientedLogProfile,hz])
  refine ⟨child,hcs,hcb,?_⟩
  intro V hVs hV
  let W : ℝ→ℂ:=radialFromLog V hVs A hV
  have hW : ContDiff ℝ ∞ W:=(radialFromLog V hVs A hV).smooth ⊤
  have hs : Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A):=
    fun s hs=>radialFromLog_support V hVs A hV s hs
  obtain ⟨Cs,hCs,hsmall⟩:=hshort W hs hW
  obtain ⟨Cl,hCl,hlong⟩:=hlarge W hs hW (radialFromLog_hasCompactSupport V hVs A hV)
  refine ⟨Cs+Cl,add_nonneg hCs hCl,?_⟩
  intro D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hD hE ih
  obtain ⟨hXZ,hFZ⟩:=canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
    hZbig hX hstate.label_ge_one hstate.mass_le
  have hsbound:=hsmall t Z η Ψ m labels X F K hstate hZ.le hZbig hη.le hbudget hfixed
  have hb:=hlong S D hbad hSp base Z Ψ m labels X F K E t hstate hbase hZ hZbig
    hX hXZ hFZ hE hD
  dsimp only at hb
  have hlbound:=hb (by
    intro side Ψ' m' labels' X' F' K' hs' hr s
    exact ⟨ih side true Ψ' m' labels' X' F' K' hs' hr s,
      ih side false Ψ' m' labels' X' F' K' hs' hr s⟩)
  have he : η+17*η+39*η=57*η:=by ring
  rw [he] at hlbound
  have hp : Z^(η+7*η-(1:ℝ)/40)≤Z^(57*η):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have ht : (1+|t|)^d≤(1+|t|)^(2*J):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hs' : 2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ t) (m*excludedGenerator S) (idealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
      Cs*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J) := by
    calc
      _ ≤ Cs*(X*F)^2*Z^(η+7*η-(1:ℝ)/40)*(1+|t|)^d:=hsbound
      _ ≤ Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=by gcongr
      _ ≤ (Cs*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J))*E:=
        le_mul_of_one_le_right (by positivity) hE
      _ = _:=by ring
  rw [outsideLogEnergy_eq_completed S D hbad (normHeightTwist Ψ t) m labels V hVs A hV X K hstate.column_pos]
  exact hlbound.trans ((add_le_add hs' le_rfl).trans_eq (by ring))

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation
open ConcreteTraceCRT (eisEmbedding)

theorem outsideLogEnergy_finite_rank
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (r : ℕ) :
    ∀(A : ℝ),0≤A → ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V →
    (∀s,V s≠0→|s|≤A) → ∃C : ℝ,1≤C ∧
    ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      fixedDepthRank Z K≤ r → Real.exp (radiusIter A r)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^(57*η*(r:ℝ))*(X*F)^2*(1+|t|)^d := by
  have hbudget' : 3000*η≤(1:ℝ)/40:=by linarith
  induction r with
  | zero =>
    intro A hA
    refine ⟨0,?_⟩
    intro V hVs hV
    obtain ⟨C,hC,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    refine ⟨max 1 C,le_max_left _ _,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget'
      (Or.inl (Nat.eq_zero_of_le_zero hr))
    simpa only [Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,pow_zero] using
      hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) (sq_nonneg (X*F)))
  | succ r ih =>
    intro A hA
    obtain ⟨dc,hchild⟩:=ih (2*A+11) (by linarith)
    obtain ⟨ds,hstep⟩:=canonicalLog_actual_step S hSp hbad base hbase ρ q levelBound
      hρ hq hlevel hmodels A hA η hη hηsmall hbudget
    let J : ℕ:=dc+ds
    have hdchild : dc≤2*J:=by dsimp [J];omega
    have hdstep : ds≤2*J:=by dsimp [J];omega
    obtain ⟨child,hcs,hcb,hparent⟩:=hstep J hdstep
    choose childC hchildC using (fun side neg=>hchild (child side neg) (hcs side neg) (hcb side neg))
    have hcnonneg (side neg : Bool) : 0≤ childC side neg:=zero_le_one.trans (hchildC side neg).1
    let E0 : ℝ:=1+∑side : Bool,∑neg : Bool,childC side neg
    have hE0 : 1≤E0:=by
      have hs : 0≤∑side : Bool,∑neg : Bool,childC side neg:=
        Finset.sum_nonneg (fun side _=>Finset.sum_nonneg (fun neg _=>hcnonneg side neg))
      exact le_add_of_nonneg_right hs
    have hcE (side neg : Bool) : childC side neg≤E0:=by
      have h1 : childC side neg≤∑j : Bool,childC side j:=
        Finset.single_le_sum (fun j _=>hcnonneg side j) (Finset.mem_univ neg)
      have h2 : (∑j : Bool,childC side j)≤∑i : Bool,∑j : Bool,childC i j:=
        Finset.single_le_sum (fun i _=>Finset.sum_nonneg (fun j _=>hcnonneg i j)) (Finset.mem_univ side)
      exact h1.trans (h2.trans (le_add_of_nonneg_left zero_le_one))
    refine ⟨2*J,?_⟩
    intro V hVs hV
    obtain ⟨Ct,hCt,hterm⟩:=outsideLogEnergy_terminal_constant V hVs A hV
    obtain ⟨Cp,hCp,hp⟩:=hparent V hVs hV
    let C : ℝ:=1+Ct+Cp*E0
    have hC : 1≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have htC : Ct≤C:=by dsimp [C];nlinarith [mul_nonneg hCp (zero_le_one.trans hE0)]
    have hpC : Cp*E0≤C:=by dsimp [C];linarith
    refine ⟨C,hC,?_⟩
    intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
    have hZ0 : 0<Z:=zero_lt_one.trans hZ
    have hpow : 1≤Z^(57*η*((r+1:ℕ):ℝ)):=
      Real.one_le_rpow hZ.le (by positivity)
    have hheight : 1≤(1+|t|)^(2*J):=one_le_pow₀ (by linarith [abs_nonneg t])
    by_cases hstop : fixedDepthRank Z K=0 ∨ X≤1
    · have hb:=hterm S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη.le hbudget' hstop
      apply hb.trans
      calc
        Ct*(X*F)^2≤C*(X*F)^2:=mul_le_mul_of_nonneg_right htC (sq_nonneg _)
        _ ≤ C*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by
          calc
            _ ≤ (C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)):=
              le_mul_of_one_le_right (by positivity) hpow
            _ ≤ ((C*(X*F)^2)*Z^(57*η*((r+1:ℕ):ℝ)))*(1+|t|)^(2*J):=
              le_mul_of_one_le_right (by positivity) hheight
            _ = _:=by ring
    · have hX : 1≤X:=(lt_of_not_ge (fun hh=>hstop (Or.inr hh))).le
      have hXZ : X≤Z^3:=(canonical_live_scale_bounds Z X F (fixedDepthRank Z K)
        hZbig hX hstate.label_ge_one hstate.mass_le).1
      have hDparent : Real.exp A*X≤D:=
        common_pool_parent A Z X D (r+1) hA hZ0.le hstate.column_pos.le hXZ hD
      let E : ℝ:=E0*Z^(57*η*(r:ℝ))
      have hEr : 1≤Z^(57*η*(r:ℝ)):=Real.one_le_rpow hZ.le (by positivity)
      have hE : 1≤E:=by
        change 1≤E0*Z^(57*η*(r:ℝ))
        simpa only [one_mul] using mul_le_mul hE0 hEr zero_le_one (zero_le_one.trans hE0)
      have hb:=hp D Z Ψ m labels X F K E t hstate hZ hZbig hfixed hX hDparent hE
      have hbound : outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
          Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J):=hb (by
        intro side neg Ψ' m' labels' X' F' K' hs hr' s
        have hrchild : fixedDepthRank Z K'≤ r:=by omega
        have hDchild : Real.exp (radiusIter (2*A+11) r)*Z^3≤D:=by
          simpa only [radiusIter_succ] using hD
        have hh:=(hchildC side neg).2 D Z Ψ' m' labels' X' F' K' s hs hZ hZbig hfixed hrchild hDchild
        apply hh.trans
        rw [Real.norm_eq_abs]
        change childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2*(1+|s|)^dc≤_
        have hcscale : childC side neg*Z^(57*η*(r:ℝ))*(X'*F')^2≤
            (E0*Z^(57*η*(r:ℝ)))*(X'*F')^2:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hcE side neg) (Real.rpow_nonneg hZ0.le _)) (sq_nonneg _)
        have hheight' : (1+|s|)^dc≤(1+|s|)^(2*J):=
          pow_le_pow_right₀ (by linarith [abs_nonneg s]) hdchild
        exact mul_le_mul hcscale hheight' (by positivity) (by positivity))
      apply hbound.trans
      have hexp : Z^(57*η*(r:ℝ))*Z^(57*η)=Z^(57*η*((r+1:ℕ):ℝ)):=by
        rw [←Real.rpow_add hZ0]
        congr 1
        push_cast
        ring
      calc
        Cp*E*(X*F)^2*Z^(57*η)*(1+|t|)^(2*J)=
            (Cp*E0)*(Z^(57*η*(r:ℝ))*Z^(57*η))*(X*F)^2*(1+|t|)^(2*J):=by dsimp [E];ring
        _ = (Cp*E0)*Z^(57*η*((r+1:ℕ):ℝ))*(X*F)^2*(1+|t|)^(2*J):=by rw [hexp]
        _ ≤ _:=by gcongr

def canonicalDescentPadding (ε : ℝ) : ℝ:=canonicalPadding ε 57/2

theorem canonicalDescentPadding_budget (ε : ℝ) (hε : 0<ε) :
    0<canonicalDescentPadding ε ∧ canonicalDescentPadding ε≤(1:ℝ)/1000 ∧
    3000*canonicalDescentPadding ε≤(1:ℝ)/80 ∧
    171000*canonicalDescentPadding ε≤ε := by
  have h:=canonicalPadding_budget ε 57 hε (by norm_num)
  dsimp [canonicalDescentPadding]
  refine ⟨by linarith [h.1],by linarith [h.2.1],by linarith [h.2.2.1],?_⟩
  have ht:=h.2.2.2.2.1
  nlinarith [h.1]

theorem outsideLogEnergy_state_small_power
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε η : ℝ) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/80) (hloss : 171000*η≤ε)
    (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  obtain ⟨d,hd⟩:=outsideLogEnergy_finite_rank S hSp hbad base hbase ρ q levelBound
    hρ hq hlevel hmodels η hη hηsmall hbudget 3000 A hA
  refine ⟨d,?_⟩
  intro V hVs hV
  obtain ⟨C,hC,hbound⟩:=hd V hVs hV
  refine ⟨C,hC,?_⟩
  intro D Z Ψ m labels X F K t hstate hZ hZbig hfixed hD
  have hr:=fixedDepthRank_initial Z K hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global
  have hb:=hbound D Z Ψ m labels X F K t hstate hZ hZbig hfixed hr hD
  have he : 57*η*(3000:ℝ)≤ε:=by linarith
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le he) (zero_le_one.trans hC)

theorem outsideLogEnergy_small_power
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (hbase : ∀u,‖base u‖≤1)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S base ρ q levelBound)
    (ε : ℝ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) :
    ∃d : ℕ,∀(V : ℝ→ℂ),ContDiff ℝ ∞ V → (∀s,V s≠0→|s|≤A) →
    ∃C : ℝ,1≤C ∧ ∀(D : ℕ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z (canonicalDescentPadding ε) Ψ m labels X F K →
      1<Z → Real.exp 9000≤Z →
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) →
      Real.exp (radiusIter A 3000)*Z^3≤D →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤
        C*Z^ε*(X*F)^2*(1+|t|)^d := by
  have h:=canonicalDescentPadding_budget ε hε
  exact outsideLogEnergy_state_small_power S hSp hbad base hbase ρ q levelBound hρ hq hlevel hmodels
    ε (canonicalDescentPadding ε) h.1 h.2.1 h.2.2.1 h.2.2.2 A hA

end CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels (primeProductNorm)
open InitialMeanSquare hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)
open ConcreteTraceCRT (eisEmbedding)

theorem initialCanonicalState
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (base Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : IsBaseRayTwist base Ψ) (Z η X lengthScale K : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hX : 1≤X) (hL : 1≤lengthScale) (hK : 1≤K)
    (R : Finset (OutsidePrimeIndex S D)) (T : Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O))
    (hmass : X*lengthScale≤Z^2)
    (hinv : K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R)≤
      X*lengthScale*Z^(-(1:ℝ)/20))
    (hlabels : ∀z∈T,Admissible z.1 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale)
    (houtside : ∀z∈T,IsCoprime z.1 (∏P∈S,P)) :
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ
      (primeSubsetGenerator (fun i=>Ideal.span {outsidePrime S D i}) R)
      (T.image Prod.fst) X lengthScale K := by
  let p:=outsidePrime S D
  have hp:=outsidePrime_ne_zero S hbad D
  let:=outsidePrime_maximal S hbad D
  have hN : 1≤primeProductNorm p R:=primeProductNorm_ge_one p hp R
  have hN0 : 0≤primeProductNorm p R:=zero_le_one.trans hN
  have hmod : 1 ≤ initialExcludedNorm S*primeProductNorm p R:=
    one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hN
  have hdecay : Z^(-(1:ℝ)/20)≤1:=by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -(1:ℝ)/20≤0)
  have hKmass : K≤X*lengthScale := by
    calc
      K ≤ K*(initialExcludedNorm S*primeProductNorm p R):=
        le_mul_of_one_le_right (zero_le_one.trans hK) hmod
      _ ≤ X*lengthScale*Z^(-(1:ℝ)/20):=hinv
      _ ≤ X*lengthScale:=mul_le_of_le_one_right (by positivity) hdecay
  have hKg : K≤Z^3 :=
    (hKmass.trans hmass).trans (pow_le_pow_right₀ hZ (by decide : (2:ℕ)≤3))
  refine ⟨hΨ,primeSubsetGenerator_ne_zero _ _,by linarith,hL,hK,hKg,
    hmass.trans (canonicalRankMass_initial Z _),?_,?_⟩
  · rw [primeSubsetGenerator_norm_eq_productNorm]
    calc
      K*primeProductNorm p R ≤ K*(initialExcludedNorm S*primeProductNorm p R) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
        exact le_mul_of_one_le_left hN0 (initialExcludedNorm_ge_one S)
      _ ≤ X*lengthScale*Z^(-(1:ℝ)/20):=hinv
      _ ≤ X*lengthScale*Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le hZ
        unfold canonicalRankMargin
        have hn : 0≤η*((3000-fixedDepthRank Z K:ℕ):ℝ):=mul_nonneg hη (Nat.cast_nonneg _)
        linarith
  · intro I hI
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hI
    exact ⟨(hlabels z hz).1.1,(hlabels z hz).1.2.1,houtside z hz,(hlabels z hz).2⟩

theorem canonicalInitialThreshold (S : Finset (Ideal ActualEisensteinCubic.O)) :
    ∃Z₀ : ℝ,1≤Z₀ ∧ ∀Z : ℝ,Z₀≤Z →
      1<Z ∧ Real.exp 9000≤Z ∧
      2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) := by
  let c:=2*‖eisEmbedding (excludedGenerator S)‖^2
  let Z₀:=2+Real.exp 9000+c^80
  have hc : 0≤ c:=by dsimp only [c];positivity
  have hp : 0≤ c^80:=pow_nonneg hc _
  have he:=Real.exp_pos (9000:ℝ)
  refine ⟨Z₀,by dsimp only [Z₀];linarith,?_⟩
  intro Z hZ
  have hZ1 : 1<Z:=by dsimp only [Z₀] at hZ;linarith
  refine ⟨hZ1,by dsimp only [Z₀] at hZ;linarith,?_⟩
  have hpow : c^80≤Z:=by dsimp only [Z₀] at hZ;linarith
  have hh := (Real.le_rpow_inv_iff_of_pos hc (by linarith : 0≤Z) (by norm_num : (0:ℝ)<80)).mpr
    (show c^(80:ℝ)≤Z by simpa only [Real.rpow_ofNat] using hpow)
  simpa only [one_div] using hh

end CanonicalRowCompletion

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

theorem densityChildEnergy_from_canonical_heights {ι : Type*} [DecidableEq ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O×ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V₁ V₂ : ℝ→ℂ)
    (X F K E : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels) (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K)
    (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)≤
      6*E*(X*F)^2*(∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have hl (a : ℝ) : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0≤
      (6*E*(X*F)^2)*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ₁ m
      T labels V₁ X K a 0 hX hK true false hlabels hrows hzero
    simp only [secondSignedHeight,ite_true,zero_sub] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ (-a)) (by norm_num : (0:ℝ)≤6)).trans_eq
      (by rw [norm_neg];ring))
  have hr (a : ℝ) : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0≤
      (6*E*(X*F)^2)*(1+‖a‖)^(2*J) := by
    have hh:=childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ₂ m
      T labels V₂ X K a 0 hX hK false true hlabels hrows hzero
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ a) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hb : 0≤6*E*(X*F)^2:=by positivity
  have hd:=densityChildEnergy_polynomial_bound p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X J
    (6*E*(X*F)^2) (6*E*(X*F)^2) hb hb hl hr
  rwa [Real.mul_self_sqrt hb] at hd

end SecondPassIntegration
end

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O
open FiniteGaussPhase hiding O

theorem quadratic_ray_cross (a b : ActualEisensteinCubic.O) (ha : a≠0) (hb : b≠0)
    [(Ideal.span {a}).IsMaximal] [(Ideal.span {b}).IsMaximal]
    (hab : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (hca : ringChar (ActualEisensteinCubic.O⧸Ideal.span {a})≠2)
    (hcb : ringChar (ActualEisensteinCubic.O⧸Ideal.span {b})≠2) :
    quadraticRayValue (residue (a*b))=
      character (Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)*
      character (Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a)*
      quadraticRayValue (residue a)*quadraticRayValue (residue b) := by
  let p : Bool→ActualEisensteinCubic.O:=fun i=>if i then a else b
  have hp : ∀i,p i≠0:=by
    intro i
    cases i
    · exact hb
    · exact ha
  let (i : Bool) : (Ideal.span {p i}).IsMaximal := by
    cases i <;> dsimp [p] <;> infer_instance
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})) := by
    intro i j hij
    cases i <;> cases j <;> simp_all [p,Function.onFun,isCoprime_comm]
  have hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2 := by
    intro i
    cases i
    · exact hcb
    · exact hca
  have h:=quadraticGamma_product p hp hcop hc
  simp only [quadraticGammaO_eq_rayValue] at h
  have ht : cofactor p true=b:=by
    apply mul_left_cancel₀ ha
    simpa [p] using prime_mul_cofactor p true
  have hf : cofactor p false=a:=by
    apply mul_left_cancel₀ hb
    simpa [p,mul_comm] using prime_mul_cofactor p false
  simp only [Fintype.prod_bool,ht,hf] at h
  simpa [p,mul_comm,mul_left_comm,mul_assoc] using h

theorem quadraticRayValue_ne_zero_of_odd (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : quadraticRayValue r≠0 := by
  rcases r with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      zpow_neg,Complex.I_sq,Complex.I_pow_three,Complex.inv_I,ZMod.val] at * <;>
      intro h <;> solve | (have hh:=congrArg Complex.re h; norm_num at hh) | (have hh:=congrArg Complex.im h; norm_num at hh)

end QuadraticAllOddCRT

end

end OAI

end

