module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part017

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part018

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.ResidualOrthogonality -/

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

section
open Filter MeasureTheory
open scoped Classical MatrixGroups BigOperators

namespace CubicEisenstein
open CubicKubota
local notation "O" => ActualEisensteinCubic.O

lemma cubicSourceResidualFunction_kernel_invariant (M : globalKubotaKernel)
    (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • w)=
      cubicSourceResidualFunction w := by
  obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
  have h := cubicSourceResidualFunction_automorphy
    ⟨(M:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo hM⟩ w
  rw [levelTwoComplexCharacter_restrict ⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩,hchar,one_mul] at h
  exact h

def cubicSourceQuotientFunction : KernelQuotient→ℂ :=
  Quotient.lift cubicSourceResidualFunction (by
    rintro w u ⟨h,rfl⟩
    exact (cubicSourceResidualFunction_kernel_invariant h w).symm)

lemma cubicSourceQuotientFunction_projection (w : HyperbolicSpace) :
    cubicSourceQuotientFunction (integralOrbitProjection globalKubotaKernel w)=
      cubicSourceResidualFunction w := rfl

lemma cubicSourceQuotientFunction_measurable : Measurable cubicSourceQuotientFunction := by
  apply measurable_from_quotient.mpr
  exact cubicSourceResidualFunction_continuous.measurable

lemma cubicSourceQuotientFunction_represents :
    kernelSourceProjection cubicEisensteinResidue=ᵐ[integralQuotientVolume globalKubotaKernel]
      cubicSourceQuotientFunction := by
  unfold integralQuotientVolume
  apply (ae_map_iff (measurable_integralOrbitProjection _).aemeasurable
    (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      cubicSourceQuotientFunction_measurable)).mpr
  exact ae_restrict_of_ae cubicSourceResidualFunction_represents_projection

end CubicEisenstein

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeLegIndex (p : ActualEisensteinCubic.O) := Option (CubeResidues p)

def cubeLegTarget (p : ActualEisensteinCubic.O) (hp : p≠0) : CubeLegIndex p→Subgroup (SL(2,ActualEisensteinCubic.O))
  | none => cubeCommonCover p hp
  | some r => cubeCommonTarget p hp r

lemma cubeLegTarget_le (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    cubeLegTarget p hp i≤globalKubotaKernel := by
  cases i with
  | none => exact cubeCommonCover_le p hp
  | some r => exact cubeCommonTarget_le p hp r

lemma cubeLegTarget_finiteIndex (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    (cubeLegTarget p hp i).FiniteIndex := by
  cases i with
  | none => exact cubeCommonCover_finiteIndex p hp
  | some r => exact cubeCommonTarget_finiteIndex p hp r

def cubeLegEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) : (i : CubeLegIndex p)→
    cubeCommonCover p hp≃*cubeLegTarget p hp i
  | none => MulEquiv.refl _
  | some r => cubeCommonEquiv p hp r

def cubeLegMatrix (p : ActualEisensteinCubic.O) (hp : p≠0) : CubeLegIndex p→SL(2,ℂ)
  | none => 1
  | some r => cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)

lemma cubeLeg_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    IntegralCoverIntertwines (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) := by
  cases i with
  | none =>
    intro h
    change 1*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))*1
    simp only [one_mul,mul_one]
  | some r => exact cubeCommon_intertwines p hp r

def cubeLeg (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    KernelQuotientL2→L[ℂ]IntegralQuotientL2 (cubeCommonCover p hp) := by
  letI := cubeLegTarget_finiteIndex p hp i
  letI : (cubeLegTarget p hp i).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p hp) (cubeLegTarget_le p hp i)
    (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i)

def cubeLegCoefficient (p : ActualEisensteinCubic.O) : CubeLegIndex p→ℂ
  | none => -(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
  | some _ => (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3

def cubeLegQuotientFunction (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ :=
  fun q=>cubicSourceQuotientFunction
    (integralCoverMap (cubeLegTarget_le p hp i)
      (integralConjugateMap (cubeLegEquiv p hp i) (cubeLegMatrix p hp i)
        (cubeLeg_intertwines p hp i) q))

lemma cubeLegQuotientFunction_projection (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p)
    (w : HyperbolicSpace) :
    cubeLegQuotientFunction p hp i (integralOrbitProjection (cubeCommonCover p hp) w)=
      cubicSourceResidualFunction (cubeLegMatrix p hp i • w) := rfl

lemma cubeLegQuotientFunction_measurable (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    Measurable (cubeLegQuotientFunction p hp i) :=
  cubicSourceQuotientFunction_measurable.comp
    ((integralCoverMap_measurable (cubeLegTarget_le p hp i)).comp
      (integralConjugateMap_measurable _ _ _))

lemma cubeLeg_representative (p : ActualEisensteinCubic.O) (hp : p≠0) (i : CubeLegIndex p) :
    cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp)]cubeLegQuotientFunction p hp i := by
  let := cubeLegTarget_finiteIndex p hp i
  let : (cubeLegTarget p hp i).IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg_representative (cubeCommonCover_le p hp) (cubeLegTarget_le p hp i)
    (cubeLegEquiv p hp i) (cubeLegMatrix p hp i) (cubeLeg_intertwines p hp i)
    _ _ cubicSourceQuotientFunction_represents

def cubeDifferenceL2 (p : ActualEisensteinCubic.O) (hp : p≠0) : IntegralQuotientL2 (cubeCommonCover p hp) :=
  ∑' i:CubeLegIndex p,cubeLegCoefficient p i •
    cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)

def cubeDifferenceQuotientFunction (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ :=
  fun q=>∑' i:CubeLegIndex p,cubeLegCoefficient p i*cubeLegQuotientFunction p hp i q

lemma cubeDifferenceQuotientFunction_projection (p : ActualEisensteinCubic.O) (hp : p≠0)
    (w : HyperbolicSpace) :
    cubeDifferenceQuotientFunction p hp (integralOrbitProjection (cubeCommonCover p hp) w)=
      cubeSourceDifference p hp w := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  simp only [cubeDifferenceQuotientFunction,tsum_fintype,Fintype.sum_option,
    cubeLegCoefficient,cubeLegQuotientFunction_projection,cubeLegMatrix,one_smul,
    cubeSourceDifference,cubeAverage,Finset.mul_sum]
  ring

lemma cubeDifferenceQuotientFunction_measurable (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Measurable (cubeDifferenceQuotientFunction p hp) := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeDifferenceQuotientFunction
  simp only [tsum_fintype]
  exact Finset.measurable_sum _ (fun i _=>measurable_const.mul (cubeLegQuotientFunction_measurable p hp i))

lemma cubeDifferenceL2_representative (p : ActualEisensteinCubic.O) (hp : p≠0) :
    cubeDifferenceL2 p hp=ᵐ[integralQuotientVolume (cubeCommonCover p hp)]
      cubeDifferenceQuotientFunction p hp := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  unfold cubeDifferenceL2 cubeDifferenceQuotientFunction
  simp only [tsum_fintype]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hh (i : CubeLegIndex p) :
      ((cubeLegCoefficient p i • cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue) :
        IntegralQuotientL2 (cubeCommonCover p hp)) : IntegralOrbitQuotient (cubeCommonCover p hp)→ℂ)
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp)]
      (fun q=>cubeLegCoefficient p i*cubeLegQuotientFunction p hp i q) :=
    by
      filter_upwards [Lp.coeFn_smul (cubeLegCoefficient p i)
        (cubeLeg p hp i (kernelSourceProjection cubicEisensteinResidue)),
        cubeLeg_representative p hp i] with q hq hr
      simpa only [Pi.smul_apply,smul_eq_mul,hr] using hq
  filter_upwards [eventuallyEq_sum (fun i (_ : i∈Finset.univ)=>hh i)] with q hq
  simpa only [Finset.sum_apply] using hq

end CubicKubota
end

namespace CubicEisenstein

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspLeadingCoefficient_ramified (j:Fin 3) (hj:j≠0) :
    sourceCuspLeadingCoefficient (cuspRepresentative j)=0 := by
  unfold sourceCuspLeadingCoefficient sourceCuspConstant
  rw [sourceCuspRepresentative_average]
  simp only [ite_eq_right hj,zero_mul,zero_div]

theorem sourceCuspRemainder_representatives_decay (a:ℝ) (ha:0<a) :
    ∃K:ℝ,0≤K∧∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,a≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3 := by
  obtain ⟨K0,hK0,h0⟩:=sourceCuspRemainder_principal_cubic_decay a ha
  obtain ⟨K1,hK1,h1⟩:=ramifiedSource_cubic_decay false a ha
  obtain ⟨K2,hK2,h2⟩:=ramifiedSource_cubic_decay true a ha
  refine ⟨K0+K1+K2,by positivity,?_⟩
  intro j z v hv hav
  have hD:0≤v^3:=pow_nonneg hv.le 3
  fin_cases j
  · have hb:‖sourceCuspRemainder (cuspRepresentative 0) z v hv‖≤K0/v^3:=by
      simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using h0 z v hv hav
    exact hb.trans (div_le_div_of_nonneg_right (by linarith) hD)
  · have he:sourceCuspRemainder (cuspRepresentative 1) z v hv=
        ramifiedSourceFunction (ramifiedCuspRoot false:Eis) (upperPoint z v hv):=by
      rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_ramified 1 (by decide),zero_mul,sub_zero]
      simp [cuspRepresentative,cuspParameter,ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val]
    change ‖sourceCuspRemainder (cuspRepresentative 1) z v hv‖≤_
    rw [he]
    exact (h1 v hv z hav).trans (div_le_div_of_nonneg_right (by linarith) hD)
  · have he:sourceCuspRemainder (cuspRepresentative 2) z v hv=
        ramifiedSourceFunction (ramifiedCuspRoot true:Eis) (upperPoint z v hv):=by
      rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_ramified 2 (by decide),zero_mul,sub_zero]
      simp [cuspRepresentative,cuspParameter,ramifiedSourceFunction,ramifiedCuspRoot,
        Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    change ‖sourceCuspRemainder (cuspRepresentative 2) z v hv‖≤_
    rw [he]
    exact (h2 v hv z hav).trans (div_le_div_of_nonneg_right (by linarith) hD)

theorem cubeSourceDifference_cubic_decay (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    ∃C:ℝ,0≤C∧∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,1≤v→
      ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  obtain ⟨K,hK,hrep⟩:=sourceCuspRemainder_representatives_decay (‖eisEmbedding p‖^3)⁻¹ (by positivity)
  refine ⟨K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹),by positivity,?_⟩
  intro M z v hv hv1
  exact cubeSourceDifference_decay p hp hprimary K hK hrep M z v hv hv1

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_norm_sq_le {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) :
    ‖cubeCuspTriangular d hp 1 1‖^2≤‖eisEmbedding p‖^3 := by
  rw [cubeCuspTriangular_norm_sq d hp,←Real.rpow_natCast ‖eisEmbedding p‖ 3]
  apply Real.rpow_le_rpow_of_exponent_le (cubePrime_norm_ge_one p hp)
  norm_num only [Nat.cast_ofNat]
  have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
  linarith

lemma cubeReducedRemainder_bound_from_height {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (a K:ℝ) (ha:0<a) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,a/‖eisEmbedding p‖^3≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hav:a≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hd:D≤‖eisEmbedding p‖^3:=cubeCuspTriangular_norm_sq_le d hp
  have hlow:a/‖eisEmbedding p‖^3≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(a/‖eisEmbedding p‖^3)*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _=a:=div_mul_cancel₀ a (pow_ne_zero 3 hr.ne')
      _≤v:=hav
  have hb:=sourceCuspRemainder_bound_all K (a/‖eisEmbedding p‖^3) hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) hlow
  change ‖cubeReducedRemainder d hp z v hv‖≤K/(v/D)^3 at hb
  refine hb.trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hd 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

theorem cubeSourceDifference_cubic_decay_from_height (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C∧∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,a≤v→
      ‖cubeSourceDifference p hp.ne_zero (integralComplexMatrix M • upperPoint z v hv)‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  obtain ⟨K,hK,hrep⟩:=sourceCuspRemainder_representatives_decay
    (a/‖eisEmbedding p‖^3) (by positivity)
  refine ⟨K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹),by positivity,?_⟩
  intro M z v hv hav
  have hlow:a/‖eisEmbedding p‖^3≤v:=by
    calc
      _≤a:=div_le_self ha.le (one_le_pow₀ hr1)
      _≤v:=hav
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv hlow
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound_from_height (d r) hp.ne_zero a K ha hK hrep z v hv hav)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold cubeSourceDifference
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

def cubeInverseLeftMatrix (q:Eis) : SL(2,Eis) :=
  ⟨!![3*q,1;-1,0],by simp⟩

lemma cubeAverageMatrix_inverse_factor (p:Eis) (hp:p≠0) (q:Eis) :
    (cubeAverageMatrix p hp q)⁻¹=
      integralComplexMatrix (cubeInverseLeftMatrix q)*cubeAverageMatrix p hp 0*
        integralComplexMatrix (rationalEmbedding ModularGroup.S) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    integralComplexMatrix_apply, rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [cubeInverseLeftMatrix, ModularGroup.S, map_ofNat]
  ring

lemma cubeAverageMatrix_inverse_cusp_factor (M:SL(2,Eis)) (p q:Eis)
    (hp:Prime p) (hprimary:lambda^2∣p-1) :
    let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
    (cubeAverageMatrix p hp.ne_zero q)⁻¹*integralComplexMatrix M=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*cubeCuspTriangular d hp.ne_zero := by
  dsimp only
  let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
  calc
    _=integralComplexMatrix (cubeInverseLeftMatrix q)*
        (cubeAverageMatrix p hp.ne_zero 0*integralComplexMatrix (rationalEmbedding ModularGroup.S*M)):=by
      rw [cubeAverageMatrix_inverse_factor,map_mul]
      group
    _=integralComplexMatrix (cubeInverseLeftMatrix q)*
        (integralComplexMatrix d.matrix*cubeCuspTriangular d hp.ne_zero):=by
      rw [cubeCuspTriangular_factor d hp.ne_zero]
    _=integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*cubeCuspTriangular d hp.ne_zero:=by
      rw [map_mul,mul_assoc]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSourceDifference_inverse_cubic_decay (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) :
    ∃C:ℝ,0≤C∧∀q:Eis,∀M:SL(2,Eis),∀z:ℂ,∀v:ℝ,∀hv:0<v,1≤v→
      ‖cubeSourceDifference p hp.ne_zero ((cubeAverageMatrix p hp.ne_zero q)⁻¹ •
        (integralComplexMatrix M • upperPoint z v hv))‖≤C/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  obtain ⟨K,hK,hdecay⟩:=cubeSourceDifference_cubic_decay_from_height p hp hprimary
    (‖eisEmbedding p‖^3)⁻¹ (by positivity)
  refine ⟨K*‖eisEmbedding p‖^9,by positivity,?_⟩
  intro q M z v hv hv1
  let d:=actualCubeCuspData (rationalEmbedding ModularGroup.S*M) p 0 hp hprimary
  let T:=cubeCuspTriangular d hp.ne_zero
  let D:=‖T 1 1‖^2
  have hT:T 1 0=0:=(cubeCuspTriangular_entries d hp.ne_zero).2.1
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp.ne_zero
  have hDle:D≤‖eisEmbedding p‖^3:=cubeCuspTriangular_norm_sq_le d hp.ne_zero
  have hlow:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hDle (by positivity)
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hfactor: (cubeAverageMatrix p hp.ne_zero q)⁻¹*integralComplexMatrix M=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix)*T :=
    cubeAverageMatrix_inverse_cusp_factor M p q hp hprimary
  have hact: (cubeAverageMatrix p hp.ne_zero q)⁻¹ •
      (integralComplexMatrix M • upperPoint z v hv)=
      integralComplexMatrix (cubeInverseLeftMatrix q*d.matrix) •
        upperPoint ((T 0 0*z+T 0 1)/T 1 1) (v/D) (div_pos hv hD) := by
    rw [←mul_smul,hfactor,mul_smul,complex_upper_triangular_action T hT z v hv]
  rw [hact]
  refine (hdecay (cubeInverseLeftMatrix q*d.matrix) _ _ _ hlow).trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hDle 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma kernelSourcePullback_pairing_inverse (M : CubicKubota.levelTwo) (F G : KernelQuotientL2) :
    inner ℂ F (kernelSourcePullback M G)=inner ℂ (kernelSourcePullback M⁻¹ F) G := by
  calc
    _ = inner ℂ (kernelSourcePullback M (kernelSourcePullback M⁻¹ F)) (kernelSourcePullback M G) := by
      rw [kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]
    _ = _ := LinearIsometry.inner_map_map _ _ _

lemma kernelSourcePullback_integral_cusp_decay (M : CubicKubota.levelTwo)
    (f : KernelQuotient→ℂ) (C : ℝ)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3)
    (N : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖f (kernelSourceAction M (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix N•upperPoint z v hv)))‖≤C/v^3 := by
  rw [kernelSourceAction_mk]
  change ‖f (integralOrbitProjection globalKubotaKernel
    (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O))•(integralComplexMatrix N•upperPoint z v hv)))‖≤C/v^3
  have hh := hdec ((M:SL(2,ActualEisensteinCubic.O))*N) z v hv hlarge
  simpa only [map_mul,mul_smul] using hh

lemma cubicEisensteinResidue_source_translate_orthogonal
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ)•F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f)
    (C : ℝ) (hC : 0≤C)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3)
    (M : CubicKubota.levelTwo) :
    inner ℂ F (kernelSourcePullback M cubicEisensteinResidue)=0 := by
  rw [kernelSourcePullback_pairing_inverse]
  have hrepM : kernelSourcePullback M⁻¹ F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q=>f (kernelSourceAction M⁻¹ q) :=
    (kernelSourcePullback_ae_eq M⁻¹ F).trans
      ((kernelSourceAction_measurePreserving M⁻¹).quasiMeasurePreserving.ae_eq_comp hrep)
  apply cubicEisensteinResidue_orthogonal_of_cusp_chart_decay _
    (kernelSource_eigenvector M⁻¹ F (8/9:ℂ) hF) _ hrepM C hC
  intro N z v hv hlarge
  exact kernelSourcePullback_integral_cusp_decay M⁻¹ f C hdec (N:SL(2,ActualEisensteinCubic.O)) z v hv hlarge

theorem cubicSourceResidue_orthogonal_of_integral_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ)•F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f)
    (C : ℝ) (hC : 0≤C)
    (hdec : ∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C/v^3) :
    inner ℂ F (kernelSourceProjection cubicEisensteinResidue)=0 := by
  rw [kernelSourceProjection_apply,inner_smul_right,inner_sum]
  simp only [cubicEisensteinResidue_source_translate_orthogonal F hF f hrep C hC hdec,
    Finset.sum_const_zero,mul_zero]

theorem commonCover_source_span_vanish {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (leg : ι→KernelQuotientL2→L[ℂ]IntegralQuotientL2 H) (c : ι→ℂ)
    (D : IntegralQuotientL2 H)
    (hD : D=∑i,c i • leg i (kernelSourceProjection cubicEisensteinResidue))
    (hEig : ∀i,(ContinuousLinearMap.adjoint (leg i) D,
      (8/9:ℂ)•ContinuousLinearMap.adjoint (leg i) D)∈kernelEnergyLaplacian.graph)
    (f : ι→KernelQuotient→ℂ)
    (hrep : ∀i,ContinuousLinearMap.adjoint (leg i) D=ᵐ[integralQuotientVolume globalKubotaKernel]f i)
    (C : ι→ℝ) (hC : ∀i,0≤C i)
    (hdec : ∀i,∀N : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f i (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix N•upperPoint z v hv))‖≤C i/v^3) : D=0 := by
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  calc
    inner ℂ D D=inner ℂ D (∑i,c i • leg i (kernelSourceProjection cubicEisensteinResidue)) :=
      congrArg (inner ℂ D) hD
    _ = ∑i,c i * inner ℂ D (leg i (kernelSourceProjection cubicEisensteinResidue)) := by
      simp only [inner_sum,inner_smul_right]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [←ContinuousLinearMap.adjoint_inner_left]
      rw [cubicSourceResidue_orthogonal_of_integral_cusp_decay _ (hEig i) (f i) (hrep i) (C i) (hC i) (hdec i),mul_zero]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem kernelCoverLeg_adjoint_sum_eigenvector
    {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (J : ι→Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hHK : H≤globalKubotaKernel) (hJK : ∀i,J i≤globalKubotaKernel)
    [∀i,(J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀i,H≃*J i) (g : ι→SL(2,ℂ)) (he : ∀i,IntegralCoverIntertwines (e i) (g i))
    (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph)
    (c : ι→ℂ) (j : ι) :
    let D := ∑i,c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D,
      eigenvalue • ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D)
      ∈kernelEnergyLaplacian.graph := by
  let traced (i : ι) :=
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F)
  have hi (i : ι) : (traced i,eigenvalue • traced i)∈kernelEnergyLaplacian.graph := by
    change (((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F,
      eigenvalue • ((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F)∈kernelEnergyLaplacian.graph
    rw [kernelCoverLeg_adjoint_comp]
    exact kernelCorrespondence_eigenvector _ _ _ _ _ F eigenvalue hF
  have hsum : (∑i,c i • (traced i,eigenvalue • traced i))∈kernelEnergyLaplacian.graph :=
    kernelEnergyLaplacian.graph.sum_mem (fun i _=>kernelEnergyLaplacian.graph.smul_mem (c i) (hi i))
  have hEq : (∑i,c i • (traced i,eigenvalue • traced i))=
      (∑i,c i • traced i,eigenvalue • ∑i,c i • traced i) := by
    apply Prod.ext <;> simp [Prod.fst_sum,Prod.snd_sum,Finset.smul_sum,smul_smul,mul_comm]
  rw [hEq] at hsum
  simpa only [map_sum,map_smul] using hsum

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.PrimeRecurrence -/

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
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

theorem integralCoverTraceFunction_integral_cusp_decay (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (integralComplexMatrix M•upperPoint z v hv))‖≤C/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖integralCoverTraceFunction H K f
      (integralOrbitProjection K (integralComplexMatrix M•upperPoint z v hv))‖≤
        (H.relIndex K:ℝ)*C/v^3 := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  change ‖∑q : IntegralCoverCosets H K,
    f (integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv))‖≤_
  calc
    _ ≤ ∑q : IntegralCoverCosets H K,
        ‖f (integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv))‖ :=
      norm_sum_le _ _
    _ ≤ ∑_q : IntegralCoverCosets H K,C/v^3 := by
      apply Finset.sum_le_sum
      intro q _
      let r := integralCoverRep H K q
      have he : integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv)=
          integralOrbitProjection H (integralComplexMatrix ((r:SL(2,ActualEisensteinCubic.O))⁻¹*M)•upperPoint z v hv) := by
        rw [integralCoverFiberPoint_rep,integralSubgroup_smul,map_mul,mul_smul]
        rfl
      rw [he]
      exact hdec _ z v hv hlarge
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc : Fintype.card (IntegralCoverCosets H K)=H.relIndex K := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hc]
      ring

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCoverLegAdjointFunction (f : IntegralOrbitQuotient H→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction J globalKubotaKernel
    (fun q=>f (integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) q))

lemma kernelCoverLegAdjointFunction_measurable (f : IntegralOrbitQuotient H→ℂ)
    (hf : Measurable f) : Measurable (kernelCoverLegAdjointFunction e g he f) :=
  integralCoverTraceFunction_measurable J globalKubotaKernel _
    (hf.comp (integralConjugateMap_measurable _ _ _))

theorem kernelCoverLegAdjointFunction_represents (D : IntegralQuotientL2 H)
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f)
    (hrep : D=ᵐ[integralQuotientVolume H]f) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) D
      =ᵐ[integralQuotientVolume globalKubotaKernel]kernelCoverLegAdjointFunction e g he f := by
  rw [kernelCoverLeg_adjoint_apply]
  have hconj := (integralConjugatePullback_ae e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he)
    (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) D).trans
    ((integralConjugateMap_measurePreserving e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)
      (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hrep)
  exact integralCoverTrace_representative hJK globalKubotaKernel_le_levelThree _ _
    (hf.comp (integralConjugateMap_measurable _ _ _)) hconj

theorem kernelCoverLegAdjointFunction_cusp_decay (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (g⁻¹•(integralComplexMatrix M•upperPoint z v hv)))‖≤C/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖kernelCoverLegAdjointFunction e g he f
      (integralOrbitProjection globalKubotaKernel (integralComplexMatrix M•upperPoint z v hv))‖≤
        (J.relIndex globalKubotaKernel:ℝ)*C/v^3 := by
  apply integralCoverTraceFunction_integral_cusp_decay J globalKubotaKernel _ C _ M z v hv hlarge
  intro N zz vv hvv hl
  exact hdec N zz vv hvv hl

end

local notation "O" => ActualEisensteinCubic.O

theorem commonCover_source_sum_eq_zero_of_inverse_cusp_decay
    {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (J : ι→Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hHK : H≤globalKubotaKernel) (hJK : ∀i,J i≤globalKubotaKernel)
    [∀i,(J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀i,H≃*J i) (g : ι→SL(2,ℂ)) (he : ∀i,IntegralCoverIntertwines (e i) (g i))
    (c : ι→ℂ) (D : IntegralQuotientL2 H)
    (hD : D=∑i,c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
      (kernelSourceProjection cubicEisensteinResidue))
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f)
    (hrep : D=ᵐ[integralQuotientVolume H]f)
    (C : ι→ℝ) (hC : ∀i,0≤C i)
    (hdec : ∀i,∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H ((g i)⁻¹•(integralComplexMatrix M•upperPoint z v hv)))‖≤C i/v^3) :
    D=0 := by
  let leg (i : ι) := kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
  apply commonCover_source_span_vanish leg c D hD
    (f:=fun i=>kernelCoverLegAdjointFunction (e i) (g i) (he i) f)
    (C:=fun i=>(J i).relIndex globalKubotaKernel*C i)
  · intro i
    rw [hD]
    exact kernelCoverLeg_adjoint_sum_eigenvector J hHK hJK e g he
      (kernelSourceProjection cubicEisensteinResidue) (8/9:ℂ)
      kernelSourceProjection_cubicEisensteinResidue_eigenvector c i
  · intro i
    exact kernelCoverLegAdjointFunction_represents hHK (hJK i) (e i) (g i) (he i) D f hf hrep
  · intro i
    exact mul_nonneg (Nat.cast_nonneg _) (hC i)
  · intro i M z v hv hlarge
    exact kernelCoverLegAdjointFunction_cusp_decay (e i) (g i) (he i) f (C i) (hdec i) M z v hv hlarge

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

local notation "Eis" => ActualEisensteinCubic.O

lemma integralProjection_quasiMeasurePreserving (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection H)
      hyperbolicVolume (integralQuotientVolume H) := by
  let proj:=integralOrbitProjection H
  have hp:Measurable proj:=measurable_integralOrbitProjection H
  refine ⟨hp,Measure.AbsolutelyContinuous.mk fun S hS hzero=>?_⟩
  rw [Measure.map_apply hp hS]
  have hd:hyperbolicVolume ((proj ⁻¹' S)∩hyperbolicFundamentalSet H)=0:=by
    simpa only [integralQuotientVolume,proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv:∀M:H,M • (proj ⁻¹' S)=proj ⁻¹' S:=by
    intro M
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      change proj (M • u)∈S
      change proj u∈S at hu
      rwa [show proj (M • u)=proj u from integralOrbitProjection_eq H M u]
    · intro hw
      refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
      change proj (M⁻¹ • w)∈S
      rwa [show proj (M⁻¹ • w)=proj w from integralOrbitProjection_eq H M⁻¹ w]
  exact (hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_zero_of_invariant
    (proj ⁻¹' S) hinv hd

theorem integralQuotient_continuous_lifts_eq (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) (F G:IntegralOrbitQuotient H→ℂ)
    (f g:HyperbolicSpace→ℂ) (hf:Continuous f) (hg:Continuous g)
    (hF:∀w,F (integralOrbitProjection H w)=f w)
    (hG:∀w,G (integralOrbitProjection H w)=g w)
    (he:F=ᵐ[integralQuotientVolume H]G) : f=g := by
  have hl: f=ᵐ[hyperbolicVolume]g:=by
    have hh:=(integralProjection_quasiMeasurePreserving H hH).ae_eq_comp he
    simpa only [Function.comp_def,hF,hG] using hh
  exact Measure.eq_of_ae_eq hl hf hg

theorem integralQuotient_zero_continuous_lift (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) (F:IntegralOrbitQuotient H→ℂ)
    (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (hF:∀w,F (integralOrbitProjection H w)=f w)
    (hzero:F=ᵐ[integralQuotientVolume H]0) : ∀w,f w=0 := by
  have he:f=0:=integralQuotient_continuous_lifts_eq H hH F 0 f 0 hf
    continuous_const hF (fun _=>rfl) hzero
  intro w
  exact congrFun he w

end

section
open Filter MeasureTheory
open scoped Classical MatrixGroups BigOperators

open CubicKubota ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem cubeDifferenceL2_eq_zero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) :
    cubeDifferenceL2 p hp.ne_zero=0 := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  let : ∀i : CubeLegIndex p,(cubeLegTarget p hp.ne_zero i).FiniteIndex :=
    cubeLegTarget_finiteIndex p hp.ne_zero
  let : ∀i : CubeLegIndex p,(cubeLegTarget p hp.ne_zero i).IsFiniteRelIndex globalKubotaKernel :=
    fun i=>Subgroup.isFiniteRelIndex_of_finiteIndex
  obtain ⟨C0,hC0,h0⟩ := cubeSourceDifference_cubic_decay p hp hprimary
  obtain ⟨C1,hC1,h1⟩ := cubeSourceDifference_inverse_cubic_decay p hp hprimary
  let C : CubeLegIndex p→ℝ := fun i=>i.elim C0 (fun _=>C1)
  apply commonCover_source_sum_eq_zero_of_inverse_cusp_decay
    (cubeLegTarget p hp.ne_zero) (cubeCommonCover_le p hp.ne_zero)
    (cubeLegTarget_le p hp.ne_zero) (cubeLegEquiv p hp.ne_zero)
    (cubeLegMatrix p hp.ne_zero) (cubeLeg_intertwines p hp.ne_zero)
    (cubeLegCoefficient p) (cubeDifferenceL2 p hp.ne_zero) ?_
    (cubeDifferenceQuotientFunction p hp.ne_zero)
    (cubeDifferenceQuotientFunction_measurable p hp.ne_zero)
    (cubeDifferenceL2_representative p hp.ne_zero) C ?_ ?_
  · simp only [cubeDifferenceL2,tsum_fintype,cubeLeg]
  · intro i
    cases i with
    | none => exact hC0
    | some r => exact hC1
  · intro i M z v hv hlarge
    rw [cubeDifferenceQuotientFunction_projection]
    cases i with
    | none =>
      simpa only [cubeLegMatrix,inv_one,one_smul,C,Option.elim] using h0 M z v hv hlarge.le
    | some r =>
      exact h1 (GaussianShiftedPartition.representative (p^3) r) M z v hv hlarge.le

theorem cubeSourceDifference_eq_zero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (w : HyperbolicSpace) :
    cubeSourceDifference p hp.ne_zero w=0 := by
  have hz : cubeDifferenceQuotientFunction p hp.ne_zero
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp.ne_zero)]0 := by
    apply (cubeDifferenceL2_representative p hp.ne_zero).symm.trans
    rw [cubeDifferenceL2_eq_zero p hp hprimary]
    exact Lp.coeFn_zero ℂ 2 _
  exact integralQuotient_zero_continuous_lift (cubeCommonCover p hp.ne_zero)
    ((cubeCommonCover_le p hp.ne_zero).trans globalKubotaKernel_le_levelThree)
    (cubeDifferenceQuotientFunction p hp.ne_zero) (cubeSourceDifference p hp.ne_zero)
    (cubeSourceDifference_continuous p hp.ne_zero)
    (cubeDifferenceQuotientFunction_projection p hp.ne_zero) hz w

theorem cubicSource_cubeAverage (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (w : HyperbolicSpace) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w :=
  sub_eq_zero.mp (cubeSourceDifference_eq_zero p hp hprimary w)

theorem sourceArithmeticResidue_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h :=
  sourceArithmeticResidue_cube_of_eigenrelation p hp.ne_zero
    (cubicSource_cubeAverage p hp hprimary) h hh

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_inversion_complex :
    integralComplexMatrix (rationalEmbedding ModularGroup.S)=complexWeyl := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [integralComplexMatrix_apply, rationalEmbedding,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, complexWeyl]

theorem exists_nonzero_sourceResidualFourierCoefficient :
    ∃h:Eis,h≠0 ∧ sourceResidualFourierCoefficient h≠0 := by
  by_contra hn
  have hz:∀h:Eis,h≠0→sourceResidualFourierCoefficient h=0:=by
    intro h hh
    by_contra hne
    exact hn ⟨h,hh,hne⟩
  let C:ℂ:=(3*(Real.pi:ℂ))*constantArithmeticResidue
  have hC:C≠0:=mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    constantArithmeticResidue_ne_zero
  have hprofile (z:ℂ) (v:ℝ) (hv:0<v) :
      cubicSourceResidualFunction (upperPoint z v hv)=C*(v:ℂ)^(2/3:ℂ):=by
    rw [cubicSourceResidualFunction_bessel]
    have hsum:(∑'h:Eis,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z))=0:=by
      calc
        _=∑' (_:Eis),(0:ℂ):=by
          apply tsum_congr
          intro h
          by_cases hh:h=0
          · simp [hh]
          · simp [hh,hz h hh]
        _=0:=tsum_zero
    rw [hsum,add_zero]
  have hpoint: integralComplexMatrix (rationalEmbedding ModularGroup.S) •
      upperPoint 0 2 (by norm_num)=upperPoint 0 (1/2) (by norm_num):=by
    rw [rational_inversion_complex,complexWeyl_action]
    apply upperPoint_congr <;> norm_num
  have hi:=cubicSourceResidualFunction_rational_invariant ModularGroup.S
    (upperPoint 0 2 (by norm_num))
  rw [hpoint,hprofile,hprofile] at hi
  have hc:(1/2:ℂ)^(2/3:ℂ)=(2:ℂ)^(2/3:ℂ):=by
    exact mul_left_cancel₀ hC (by simpa only [Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_ofNat] using hi)
  have hr:(1/2:ℝ)^(2/3:ℝ)=(2:ℝ)^(2/3:ℝ):=by
    apply Complex.ofReal_injective
    have h1:=Complex.ofReal_cpow (show (0:ℝ)≤1/2 by norm_num) (2/3:ℝ)
    have h2:=Complex.ofReal_cpow (show (0:ℝ)≤2 by norm_num) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at h1 h2
    exact h1.trans (hc.trans h2.symm)
  have hlt:(1/2:ℝ)^(2/3:ℝ)<(2:ℝ)^(2/3:ℝ):=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  exact hlt.ne hr

theorem exists_nonzero_sourceArithmeticResidue :
    ∃h:Eis,h≠0 ∧ sourceArithmeticResidue h≠0 := by
  obtain ⟨h,hh,hn⟩:=exists_nonzero_sourceResidualFourierCoefficient
  refine ⟨h,hh,?_⟩
  intro hz
  apply hn
  simp only [sourceResidualFourierCoefficient,hz,mul_zero]

end

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

abbrev PrincipalRamifiedIndex (h:Eis) := Eisˣ × Fin (ramifiedFrequencyBound h+1)

def principalRamifiedIndex (h:Eis) (i:PrincipalRamifiedIndex h) : Eis :=
  h*(9*(i.1.val*lambda^(i.2.val+2)))

def principalRamifiedWeight (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) : ℂ :=
  ((3^(i.2.val+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h i.1 (i.2.val+2)

lemma principalRamifiedWeight_analytic (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) :
    AnalyticAt ℂ (principalRamifiedWeight h i) s := by
  apply AnalyticAt.mul _ analyticAt_const
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow
    (Or.inl (by exact_mod_cast (pow_ne_zero (i.2.val+2) (by norm_num : (3:ℕ)≠0))))

lemma scatteringCoefficient_eq_principalRamified (s:ℂ) (hs:2<s.re)
    (h:Eis) (hh:h≠0) :
    scatteringCoefficient s h=
      (∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i s*
        unramifiedCubicGaussSeries s (principalRamifiedIndex h i))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient_explicit_ramified s hs h hh,tsum_fintype]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  rw [←Fin.sum_univ_eq_sum_range]
  rfl

theorem principalArithmeticResidue_eq_ramified_table (h:Eis) (hh:h≠0) :
    principalArithmeticResidue h=
      (∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
        unramifiedGaussResidue (principalRamifiedIndex h i))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  let coeff (i:PrincipalRamifiedIndex h) (s:ℂ) :=
    principalRamifiedWeight h i s*cuspWhittakerHeightFactor s h
  have he:=finite_unramified_residue (principalRamifiedIndex h) coeff
    (fun i s hs=>(principalRamifiedWeight_analytic h i s).mul
      (cuspWhittakerHeightFactor_analyticAt h s hs))
    (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
    (kernelCuspFourier h cubicEisensteinResidue)
    (fun s hs hi=>kernelCuspFourierFamily_analyticAt_nonreal h 2 3
      (by norm_num) (by norm_num) s hs.ne' hi.ne')
    (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num))
    (fun s hs hi=>by
      rw [kernelCuspFourierFamily_eq_upper h hh ⟨by linarith,hi⟩]
      dsimp only
      rw [scatteringCoefficient_eq_principalRamified s (by linarith) h hh]
      simp only [coeff]
      rw [mul_div_cancel₀ _ cusp_volume_ne_zero,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      ring)
  rw [kernelCuspFourier_principal_residue] at he
  have hH:=cuspWhittakerHeightFactor_center_ne_zero h
  apply (eq_div_iff cusp_volume_ne_zero).mpr
  apply mul_right_cancel₀ hH
  calc
    principalArithmeticResidue h*((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3) h
        = kernelCuspFourier h cubicEisensteinResidue := by
          rw [kernelCuspFourier_principal_residue]
          ring
    _ = _ := by
      rw [kernelCuspFourier_principal_residue,he]
      simp only [coeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sourceArithmeticResidue_eq_ramified_table (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue h=
      if ShortDraftTrace.breveE (cuspFrequency h)=1 then
        ((∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
            unramifiedGaussResidue (principalRamifiedIndex h i))+
          3*unramifiedGaussResidue (9*h))/(4*((9*Real.sqrt 3/2:ℝ):ℂ))
      else 0 := by
  rw [sourceArithmeticResidue,principalArithmeticResidue_eq_ramified_table h hh]
  split_ifs
  · ring
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma arithmeticResidueSum_frequency_cube (h c p:Eis) (hc:c≠0)
    (hlevel:(3:Eis)∣c) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum (h*p^3) c=arithmeticResidueSum h c := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hb:(eisEmbedding (symbol c p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
  have h1:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have h2:=arithmeticResidueSum_frequency_twist (h*p) c p hc hlevel ht
  have h3:=arithmeticResidueSum_frequency_twist (h*p*p) c p hc hlevel ht
  rw [show h*p^3=h*p*p*p by ring]
  calc
    _=eisEmbedding (symbol c p)^3*arithmeticResidueSum (h*p*p*p) c:=by rw [hb,one_mul]
    _=eisEmbedding (symbol c p)^2*arithmeticResidueSum (h*p*p) c:=by rw [pow_succ,mul_assoc,h3]
    _=eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c:=by rw [pow_two,mul_assoc,h2]
    _=arithmeticResidueSum h c:=h1

lemma ramified_prime_Gauss_cancel (h c p:Eis) (hc:c≠0) (hlevel:(3:Eis)∣c)
    (hp:Prime p) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (h*(9*c))=
      arithmeticResidueSum (h*p) c*primeCubicGauss p hp hprimary 1 (9*h) := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hA:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have hG:=cubicUnitGaussSum_frequency_twist (9*h) p c hp.ne_zero hprimary hcp.symm
  rw [←primeCubicGauss_one_eq p hp hprimary,←primeCubicGauss_one_eq p hp hprimary] at hG
  rw [show (9*h)*c=h*(9*c) by ring] at hG
  have hb:eisEmbedding (symbol c p)≠0:=by
    have hcube:(eisEmbedding (symbol c p))^3=1:=by
      rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
    intro hz
    simp only [hz,zero_pow (by decide : (3:ℕ)≠0)] at hcube
    exact zero_ne_one hcube
  apply mul_left_cancel₀ hb
  calc
    _=arithmeticResidueSum h c*(eisEmbedding (symbol c p)*
      primeCubicGauss p hp hprimary 1 (h*(9*c))):=by ring
    _=arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (9*h):=by rw [hG]
    _=(eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c)*
      primeCubicGauss p hp hprimary 1 (9*h):=by rw [hA]
    _=_:=by ring

lemma ramified_prime_frequency_not_dvd (h p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    ¬p∣h*(9*(u.val*lambda^n)) := by
  intro hd
  rcases hp.dvd_mul.mp hd with hh|hc
  · exact hph hh
  have hcp: IsCoprime (9*(u.val*lambda^n)) p := by
    have h3: IsCoprime (3:Eis) p:=(primary_coprime_three p hprimary).symm
    have hram: IsCoprime (u.val*lambda^n) p:=
      (ramified_primary_coprime u n p hprimary).of_mul_left_right
    convert h3.pow_left (m:=2) |>.mul_left hram using 1 ; norm_num
  exact hp.not_isUnit (hcp.symm.isUnit_of_dvd hc)

lemma sourceRayPhase_mul_primary (h p:Eis) (hprimary:lambda^2∣p-1) :
    ShortDraftTrace.breveE (cuspFrequency (h*p))=
      ShortDraftTrace.breveE (cuspFrequency h) := by
  obtain ⟨d,hd⟩:=three_dvd_lambda_sq.trans hprimary
  have hp:p=1+3*d:=by linear_combination hd
  have he:cuspFrequency (h*p)=cuspFrequency h+cuspFrequency h*(3*eisEmbedding d):=by
    rw [hp,cuspFrequency,cuspFrequency,map_mul,map_add,map_mul,map_one,map_ofNat]
    ring
  rw [he,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def principalResidueTerm (h:Eis) (u:Eisˣ) (n:ℕ) : ℂ :=
  ((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(n+2))*
    unramifiedGaussResidue (h*(9*(u.val*lambda^(n+2))))

lemma principalResidueTerm_vanish (h:Eis) (hh:h≠0) (u:Eisˣ) (n:ℕ)
    (hn:ramifiedFrequencyBound h<n+2) : principalResidueTerm h u n=0 := by
  have hA:arithmeticResidueSum h (u.val*lambda^(n+2))=0:=by
    by_contra hne
    have hb:=Nat.le_log_of_pow_le (by decide : 1<3)
      (ramified_arithmetic_norm_bound h hh u (n+2) (by omega) hne)
    exact (not_le_of_gt hn) hb
  simp only [principalResidueTerm,hA,mul_zero,zero_mul]

lemma principalArithmeticResidue_eq_sum (h:Eis) (hh:h≠0) (N:ℕ)
    (hN:ramifiedFrequencyBound h+1≤N) :
    principalArithmeticResidue h=
      (∑u:Eisˣ,∑n∈Finset.range N,principalResidueTerm h u n)/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [principalArithmeticResidue_eq_ramified_table h hh,Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  change (∑n:Fin (ramifiedFrequencyBound h+1),
    principalRamifiedWeight h (u,n) (4/3)*unramifiedGaussResidue (principalRamifiedIndex h (u,n)))=_
  have hcoeff (n:ℕ) : explicitRamifiedCoefficient h u (n+2)=
      arithmeticResidueSum h (u.val*lambda^(n+2)):=
    (arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (n+2) (by omega)).symm
  simp only [principalRamifiedWeight,principalRamifiedIndex,hcoeff]
  change (∑n:Fin (ramifiedFrequencyBound h+1),principalResidueTerm h u n.val)=_
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono hN)
  intro n hn hn'
  exact principalResidueTerm_vanish h hh u n (by simp only [Finset.mem_range] at hn';omega)

lemma principalResidueTerm_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^3) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm h u n-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        principalResidueTerm (h*p) u n := by
  let c:=u.val*lambda^(n+2)
  have hc:c≠0:=ramifiedElement_ne_zero u (n+2)
  have hlevel:(3:Eis)∣c:=ramifiedElement_level u (n+2) (by omega)
  have hcp:IsCoprime c p:=(ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  have hA:=arithmeticResidueSum_frequency_cube h c p hc hlevel hprimary hcp
  have hG:=ramified_prime_Gauss_cancel h c p hc hlevel hp hprimary hcp
  change _*arithmeticResidueSum (h*p^3) c*unramifiedGaussResidue ((h*p^3)*(9*c))=_
  rw [hA,show (h*p^3)*(9*c)=(h*(9*c))*p^3 by ring,
    unramifiedGaussResidue_prime_recurrence p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h c*unramifiedGaussResidue (h*(9*c)))-
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p) c*unramifiedGaussResidue ((h*p)*(9*c)))
  rw [show (h*p)*(9*c)=(h*(9*c))*p by ring]
  linear_combination -(((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ)))*
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*unramifiedGaussResidue ((h*(9*c))*p)*hG

theorem principalArithmeticResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        principalArithmeticResidue (h*p) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^3)+1)
    (max (ramifiedFrequencyBound h+1) (ramifiedFrequencyBound (h*p)+1))
  rw [principalArithmeticResidue_eq_sum (h*p^3) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_trans (le_max_left _ _) (le_max_right _ _)),
    principalArithmeticResidue_eq_sum (h*p) (mul_ne_zero hh hp.ne_zero) N
      (le_trans (le_max_right _ _) (le_max_right _ _))]
  simp_rw [principalResidueTerm_prime_recurrence p hp hprimary h hph,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        sourceArithmeticResidue (h*p) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^3))=
      ShortDraftTrace.breveE (cuspFrequency h):=by
    rw [show h*p^3=((h*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm,sourceRayPhase_mul_primary h p hprimary]
  split_ifs with hh
  · rw [principalArithmeticResidue_prime_recurrence p hp hprimary h hph,
      show 9*(h*p^3)=(9*h)*p^3 by ring,
      unramifiedGaussResidue_prime_recurrence p hp hprimary (9*h) hp9,
      show 9*(h*p)=(9*h)*p by ring]
    ring
  · ring

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.PrimeGaussFactors -/

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
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma unramifiedCubicGaussSeries_prime_two_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^2)=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1:cubicUnitGaussSum (h*p^2) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans (dvd_mul_left (p^2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^2) (p^2)=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ (p^2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p^2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^2) (p^3)= -(Ideal.absNorm (Ideal.span {p}):ℂ)^2:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p^2) h,mul_neg_one] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,mul_zero,zero_mul,add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph 2
  rw [←unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph] at he
  simpa only [show 2+3=5 from rfl,add_mul,one_mul] using he

theorem unramifiedGaussResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^2) := by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^5) (h*p^2) 0 A (fun _=>0)
    (fun s _=>hA s) (fun _ _=>analyticAt_const) (hA _).continuousAt continuousAt_const
    (fun s hs _=>by simpa only [A,zero_mul,add_zero] using
      unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul,add_zero] using he

lemma principalResidueTerm_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^5) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm (h*p^2) u n := by
  let c:=u.val*lambda^(n+2)
  have hA:=arithmeticResidueSum_frequency_cube (h*p^2) c p
    (ramifiedElement_ne_zero u (n+2)) (ramifiedElement_level u (n+2) (by omega)) hprimary
    (ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  rw [show (h*p^2)*p^3=h*p^5 by ring] at hA
  change _*arithmeticResidueSum (h*p^5) c*unramifiedGaussResidue ((h*p^5)*(9*c))=_
  rw [hA,show (h*p^5)*(9*c)=(h*(9*c))*p^5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p^2) c*
      unramifiedGaussResidue ((h*p^2)*(9*c)))
  rw [show (h*p^2)*(9*c)=(h*(9*c))*p^2 by ring]
  ring

lemma principalArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue (h*p^2) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^5)+1) (ramifiedFrequencyBound (h*p^2)+1)
  rw [principalArithmeticResidue_eq_sum (h*p^5) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum (h*p^2) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  simp_rw [principalResidueTerm_square_cube p hp hprimary h hph,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue (h*p^2) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^5))=
      ShortDraftTrace.breveE (cuspFrequency (h*p^2)):=by
    rw [show h*p^5=(((h*p^2)*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm]
  split_ifs
  · rw [principalArithmeticResidue_square_cube p hp hprimary h hph,
      show 9*(h*p^5)=(9*h)*p^5 by ring,
      unramifiedGaussResidue_square_cube p hp hprimary (9*h) hp9,
      show 9*(h*p^2)=(9*h)*p^2 by ring]
    ring
  · ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceArithmeticResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hh:h≠0) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=sourceArithmeticResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem sourceArithmeticResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=sourceArithmeticResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero))] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem sourceArithmeticResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=sourceArithmeticResidue_prime_recurrence p hp hprimary h hph
  rw [sourceArithmeticResidue_prime_cube p hp hprimary h hh] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue h:=by
    linear_combination hrec
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  have hG:=primeCubicGauss_one_mul_two p hp hprimary (9*h) hp9
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    sourceArithmeticResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*sourceArithmeticResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 (9*h)*primeCubicGauss p hp hprimary 2 (9*h))*
          sourceArithmeticResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      field_simp [hq]

theorem sourceArithmeticResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=
      if n%3=0 then sourceArithmeticResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [sourceArithmeticResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact sourceArithmeticResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,sourceArithmeticResidue_prime_square p hp hprimary h hph]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_inverse (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (primeCubicMulChar p hp hprimary)⁻¹=primeCubicMulChar p hp hprimary^2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [←pow_succ'] using primeCubicMulChar_cube p hp hprimary

lemma primeCubicGauss_two_eq_star (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis) :
    primeCubicGauss p hp hprimary 2 h=star (primeCubicGauss p hp hprimary 1 h) := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  rw [primeCubicGauss_eq_gaussSum,primeCubicGauss_eq_gaussSum,pow_one,star_gaussSum_eq,
    primeCubicMulChar_inverse]
  have he:=mul_gaussSum_inv_eq_gaussSum
    (primeCubicMulChar p hp hprimary^2) ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h))
  have hm:(primeCubicMulChar p hp hprimary^2) (-1 : Eis⧸Ideal.span {p})=1:=by
    rw [MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),←map_pow]
    norm_num
  rw [hm,one_mul] at he
  exact he.symm

lemma primeCubicGauss_one_normalized (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    [(Ideal.span {p}:Ideal Eis).IsMaximal] (hg:lambda∉(Ideal.span {p}:Ideal Eis)) :
    primeCubicGauss p hp hprimary 1 1/(‖eisEmbedding p‖:ℂ)=
      breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero := by
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  unfold breveGamma2
  rw [primeCubicGauss_eq_gaussSum,pow_one,canonicalSextic_pow_two]
  simp only [map_one,AddChar.mulShift_one]
  congr 2
  apply DFunLike.ext
  intro x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [primeCubicMulChar_mk,MulChar.ringHomComp_apply,
    symbol_prime p hp hprimary,primeValue_eq _ hg]

lemma primeCubicGauss_two_twist (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) :
    primeCubicGauss p hp hprimary 2 h=eisEmbedding (symbol h p)*primeCubicGauss p hp hprimary 2 1 := by
  have hcop:IsCoprime p h:=hp.coprime_iff_not_dvd.mpr hph
  have he:=cubicUnitGaussSum_frequency_twist (1:Eis) p h hp.ne_zero hprimary hcop
  simp only [one_mul,←primeCubicGauss_one_eq p hp hprimary] at he
  have hs:(eisEmbedding (symbol h p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime h p hprimary hcop.symm,map_one]
  have hstar:star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p)=1:=by
    have hn:‖eisEmbedding (symbol h p)‖=1:=by
      have hn:=congrArg norm hs
      simp only [norm_pow,norm_one] at hn
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp (by simpa using hn)
    rw [mul_comm]
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using Complex.mul_conj (eisEmbedding (symbol h p))
  have hconj:=congrArg star he
  simp only [star_mul,←primeCubicGauss_two_eq_star] at hconj
  calc
    _=(star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h:=by rw [hstar,one_mul]
    _=eisEmbedding (symbol h p)*(star (eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h):=by ring
    _=_:=by rw [mul_comm (star (eisEmbedding (symbol h p))),hconj]

lemma cubicBesselNormalizer_mul (h p:Eis) :
    cubicBesselNormalizer (h*p)=(‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*cubicBesselNormalizer h := by
  have hfreq:‖cuspFrequency (h*p)‖=‖cuspFrequency h‖*‖eisEmbedding p‖:=by
    rw [cuspFrequency_mul_right,norm_mul]
  have he:(2*Real.pi*‖cuspFrequency (h*p)‖:ℂ)=
      (‖eisEmbedding p‖:ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by rw [hfreq];push_cast;ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (by positivity)]
  push_cast
  ring

lemma prime_normalizer_powers (p:Eis) (hp:p≠0) :
    (‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))=
      (‖eisEmbedding p‖:ℂ)⁻¹ := by
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  rw [←Complex.ofReal_natCast,←eisEmbedding_norm_sq_eq_absNorm_span,pow_two,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ←mul_assoc,←Complex.cpow_add _ _ hr,←Complex.cpow_add _ _ hr]
  convert Complex.cpow_neg_one (‖eisEmbedding p‖:ℂ) using 1 ; congr 1 ; norm_num

theorem sourceResidualFourierCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      (primeCubicGauss p hp hprimary 2 (9*h)/(‖eisEmbedding p‖:ℂ))*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul,
    sourceArithmeticResidue_prime_factor p hp hprimary h hph,sourceResidualFourierCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hprimary 2 (9*h)*(cubicBesselNormalizer h*sourceArithmeticResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero];ring

theorem sourceResidualFourierCoefficient_prime_gamma (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) [(Ideal.span {p}:Ideal Eis).IsMaximal]
    (hg:lambda∉(Ideal.span {p}:Ideal Eis)) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero)*
        sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    ←primeCubicGauss_one_normalized p hp hprimary hg,star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def normalizedCubicUnitGauss (n:Eis) : ℂ :=
  cubicUnitGaussSum 1 n/(‖eisEmbedding n‖:ℂ)

@[simp] lemma normalizedCubicUnitGauss_one : normalizedCubicUnitGauss 1=1 := by
  simp [normalizedCubicUnitGauss]

lemma cubicSymbol_star_mul (a b:Eis) (hb:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b)=1 := by
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hb hab,map_one]
  have hn:‖eisEmbedding (symbol a b)‖=1:=by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
    simpa only [norm_pow,norm_one,one_pow] using congrArg norm hc
  rw [mul_comm]
  simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
    Complex.mul_conj (eisEmbedding (symbol a b))

lemma normalizedCubicUnitGauss_coprime_product (a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (normalizedCubicUnitGauss (a*b))=
      eisEmbedding (symbol a b)*star (normalizedCubicUnitGauss a)*star (normalizedCubicUnitGauss b) := by
  have hG:=cubicUnitGaussSum_coprime_product 1 a b ha hb hap hbp hab
  simp only [one_mul] at hG
  have ht:=cubicUnitGaussSum_frequency_twist 1 b a hb hbp hab.symm
  simp only [one_mul] at ht
  have hN:eisEmbedding (symbol a b)*normalizedCubicUnitGauss (a*b)=
      normalizedCubicUnitGauss a*normalizedCubicUnitGauss b:=by
    unfold normalizedCubicUnitGauss
    rw [hG,map_mul,norm_mul,Complex.ofReal_mul]
    calc
      _=cubicUnitGaussSum 1 a*(eisEmbedding (symbol a b)*cubicUnitGaussSum a b)/
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)):=by ring
      _=_:=by rw [ht];ring
  have hs:=congrArg star hN
  simp only [star_mul] at hs
  have hc:=cubicSymbol_star_mul a b hbp hab
  calc
    _=(star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b))*
        star (normalizedCubicUnitGauss (a*b)):=by rw [hc,one_mul]
    _=eisEmbedding (symbol a b)*(star (normalizedCubicUnitGauss (a*b))*
        star (eisEmbedding (symbol a b))):=by ring
    _=_:=by rw [hs];ring

lemma sourceResidualFourierCoefficient_prime_normalized (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (normalizedCubicUnitGauss p)*sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    normalizedCubicUnitGauss,←primeCubicGauss_one_eq p hp hprimary,
    star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

lemma primary_finset_product {ι:Type*} (s:Finset ι) (p:ι→Eis)
    (hp:∀i∈s,lambda^2∣p i-1) : lambda^2∣(∏i∈s,p i)-1 := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi]
    exact primary_mul _ _ (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))

theorem sourceResidualFourierCoefficient_prime_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    sourceResidualFourierCoefficient (h*(∏i∈s,p i))=
      eisEmbedding (symbol (9*h) (∏i∈s,p i))*
        star (normalizedCubicUnitGauss (∏i∈s,p i))*sourceResidualFourierCoefficient h := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hbs:(∏j∈s,p j)≠0:=Finset.prod_ne_zero_iff.mpr (fun j hj=>(hps j hj).ne_zero)
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    have hih:=ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_normalized (p i) hpi hpri _ hpb,hih]
    rw [mul_comm (p i) (∏j∈s,p j),
      normalizedCubicUnitGauss_coprime_product _ _ hbs hpi.ne_zero
        (primary_finset_product s p hprs) hpri hcpi.symm,
      symbol_mul_denominator,map_mul]
    rw [show (9:Eis)*(h*(∏j∈s,p j))=(9*h)*(∏j∈s,p j) by ring,
      symbol_mul_numerator _ _ (p i) hpri,map_mul]
    ring

lemma symbol_nine_eq_paperLambda (n:Eis) (hn:lambda^2∣n-1) :
    symbol 9 n=symbol ramifiedTraceLambda n := by
  have he:(9:Eis)=ramifiedTraceLambda^4:=by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,ramifiedTraceLambda_square]
    norm_num
  have hcop:IsCoprime ramifiedTraceLambda n:=
    ramified_character_coprime 0 1 _ n (Or.inl (by simp)) hn
  rw [he,symbol_pow_numerator _ _ hn,show (4:ℕ)=3+1 from rfl,pow_add,
    symbol_cube_of_isCoprime _ _ hn hcop,pow_one,one_mul]

theorem sourceResidualFourierCoefficient_primary_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j)) :
    star (sourceResidualFourierCoefficient (∏i∈s,p i))=
      star (sourceResidualFourierCoefficient 1)*
        star (eisEmbedding (symbol ramifiedTraceLambda (∏i∈s,p i)))*
        normalizedCubicUnitGauss (∏i∈s,p i) := by
  have he:=sourceResidualFourierCoefficient_prime_product s p hp hprimary hpair 1
    (fun i hi=>fun hd=>(hp i hi).not_isUnit (isUnit_of_dvd_one hd))
  simp only [one_mul,mul_one] at he
  rw [symbol_nine_eq_paperLambda _ (primary_finset_product s p hprimary)] at he
  rw [he,star_mul,star_mul,star_star]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue (h*b^3)=sourceArithmeticResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbprimary
  rw [←hs]
  clear hs hb hbprimary b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    have hs0:s.prod≠0:=by
      intro hz
      exact (hs 0 (Multiset.prod_eq_zero_iff.mp hz)).1.ne_zero rfl
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      sourceArithmeticResidue_prime_cube p hp.1 hp.2 _ (mul_ne_zero hh (pow_ne_zero _ hs0))]
    exact ih h hh hs

theorem sourceResidualFourierCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    sourceArithmeticResidue_primary_cube b hb hbprimary h hh,sourceResidualFourierCoefficient]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_prime_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (x:Eis) (hpx:p∣x) : symbol x p=0 := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpx),MulChar.map_zero]

lemma cubicSymbol_zero_of_not_coprime (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1)
    (x:Eis) (hnot:¬IsCoprime n x) : symbol x n=0 := by
  obtain ⟨s,hs,hp⟩:=exists_primary_prime_factorization n hn hprimary
  rw [←hs] at hnot ⊢
  clear hs hn hprimary n
  induction s using Multiset.induction_on with
  | empty=>exact False.elim (hnot (by simpa using (isCoprime_one_left : IsCoprime (1:Eis) x)))
  | @cons p s ih=>
    have hprime:=hp p (Multiset.mem_cons_self _ _)
    have hrest:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hp q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,symbol_mul_denominator]
    by_cases hc:IsCoprime p x
    · have hnc:¬IsCoprime s.prod x:=fun h=>hnot (by simpa using hc.mul_left h)
      rw [ih hnc hrest,mul_zero]
    · rw [cubicSymbol_prime_zero p hprime.1 hprime.2 x
        (hprime.1.irreducible.dvd_iff_not_isCoprime.mpr hc),zero_mul]

lemma cubicRow_eq_idealSymbol (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) (a:Eis) :
    cubicRow I hI (Ideal.Quotient.mk I a)=eisEmbedding (idealSymbol I a) := by
  rw [cubicRow_mk]
  simp_rw [canonicalSextic_pow_two,MulChar.ringHomComp_apply,←primeValue_eq]
  change (∏P:primeSupport I,eisEmbedding (primeValue P.val a))=eisEmbedding (idealSymbol I a)
  rw [←Finset.prod_subtype (primeSupport I) (fun _=>Iff.rfl)
    (fun P=>eisEmbedding (primeValue P a)),←map_prod]
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hnodup: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  congr 1
  rw [idealSymbol,ite_eq_right hI0]
  change (((primeSupport I).val.map (fun P=>primeValue P a)).prod)=_
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hnodup.dedup
  rw [hv]

lemma cubicUnitGaussSum_full (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1) (h:Eis) :
    cubicUnitGaussSum h n=
      ∑'x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
        quotientTrace n hn (Ideal.Quotient.mk _ h*x) := by
  let f:(Eis⧸Ideal.span {n})→ℂ:=fun x=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
      quotientTrace n hn (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hnot
    change ¬IsUnit x at hnot
    have hcop:¬IsCoprime n (GaussianShiftedPartition.representative n x):=by
      intro hc
      apply hnot
      have hh:=(isUnit_quotient_span_iff n (GaussianShiftedPartition.representative n x)).mpr hc
      simpa only [GaussianShiftedPartition.representative_spec] using hh
    exact hx (by simp only [f,cubicSymbol_zero_of_not_coprime n hn hprimary _ hcop,map_zero,zero_mul])
  change cubicUnitGaussSum h n=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  dsimp only [f]
  rw [←GaussianShiftedPartition.representative_spec n x.val,quotientTrace_mk_product]
  simp only [GaussianShiftedPartition.representative_spec]

theorem normalizedCubicUnitGauss_eq_gaussTwo (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hsq:Squarefree I) :
    normalizedCubicUnitGauss (primaryGenerator I)=gaussTwo I hI := by
  let n:=primaryGenerator I
  let:Finite (Eis⧸Ideal.span {n}):=finite_quotient_span hI
  let:Fintype (Eis⧸Ideal.span {n}):=Fintype.ofFinite _
  let e:=Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  rw [normalizedCubicUnitGauss,cubicUnitGaussSum_full _ hI (primaryGenerator_spec I hI).2 1,
    tsum_fintype]
  change (∑x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
    quotientTrace n hI (Ideal.Quotient.mk _ 1*x))/(‖eisEmbedding n‖:ℂ)=
    (∑x:Eis⧸Ideal.span {n},cubicRow I hI (e x)*quotientTrace n hI x)/(‖eisEmbedding n‖:ℂ)
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk,cubicRow_eq_idealSymbol I hI hsq]
  have hc:n∣GaussianShiftedPartition.representative n (Ideal.Quotient.mk (Ideal.span {n}) a)-a:=
    gaussRep_mk_congr n a
  have hs:symbol a n=idealSymbol I a:=by
    unfold symbol
    rw [(primaryGenerator_spec I hI).1]
  rw [symbol_congr hc,hs,map_one,one_mul]

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients -/

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
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primaryGenerator_squarefree_support (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) : primaryGenerator I=∏P∈primeSupport I,primaryPrime P := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hn: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  unfold primaryGenerator
  rw [ite_eq_right hI0]
  change _=((primeSupport I).val.map primaryPrime).prod
  rw [hv]

lemma primaryPrime_isPrime_of_mem (I P:Ideal Eis) (hI:primaryGenerator I≠0)
    (hP:P∈primeSupport I) : Prime (primaryPrime P) := by
  have hp0:=primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP)
  have hs:=primaryPrime_spec P hp0
  let:P.IsMaximal:=hs.1
  apply (Ideal.span_singleton_prime hp0).mp
  rw [hs.2.2.1]
  infer_instance

lemma primaryPrime_support_coprime (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (P:Ideal Eis) (hP:P∈primeSupport I) (Q:Ideal Eis) (hQ:Q∈primeSupport I) (hne:P≠Q) :
    IsCoprime (primaryPrime P) (primaryPrime Q) := by
  have hp:=primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))
  have hq:=primaryPrime_spec Q (primaryPrime_factor_ne_zero I Q hI (Multiset.mem_toFinset.mp hQ))
  let:P.IsMaximal:=hp.1
  let:Q.IsMaximal:=hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1,hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal hne

def infinityCoefficientScalar : ℂ := star (sourceResidualFourierCoefficient 1)

theorem infinityCoefficient_squarefree (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I))=
      infinityCoefficientScalar*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  have hpr:∀P∈primeSupport I,lambda^2∣primaryPrime P-1:=by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  have he:=sourceResidualFourierCoefficient_primary_product (primeSupport I) primaryPrime
    (fun P hP=>primaryPrime_isPrime_of_mem I P hI hP) hpr
    (primaryPrime_support_coprime I hI)
  rw [←primaryGenerator_squarefree_support I hI hsq,normalizedCubicUnitGauss_eq_gaussTwo I hI hsq] at he
  exact he

theorem infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      infinityCoefficientScalar*(‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _ hI,
    star_mul,infinityCoefficient_squarefree I hI hsq]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_valuation_ne_two (I P:Ideal Eis)
    (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hS
  rw [hgen,mul_comm,sourceArithmeticResidue_prime_power_table p hp hps.2.2.2 _ hpd,
    hm]
  norm_num

def thetaSquarefreePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈(primeSupport I).filter (fun P=>(normalizedFactors I).count P%3=1),P

def thetaCubePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈primeSupport I,P^((normalizedFactors I).count P/3)

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I ^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [ite_eq_right (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [ite_eq_left hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI

theorem sourceArithmeticResidue_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    Squarefree (thetaSquarefreePart I) ∧
    primaryGenerator (thetaSquarefreePart I)≠0 ∧
    primaryGenerator (thetaCubePart I)≠0 ∧
    thetaSquarefreePart I*thetaCubePart I ^3=I := by
  have he:=thetaParts_mul_cube I (primaryGenerator_ne_zero_ideal I hI)
    (fun P hP=>sourceArithmeticResidue_valuation_ne_two I P hI hP hS)
  have hgen:primaryGenerator I=
      primaryGenerator (thetaSquarefreePart I)*(primaryGenerator (thetaCubePart I))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart I*thetaCubePart I ^3):=congrArg primaryGenerator he.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_mul])
  have hB:primaryGenerator (thetaCubePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  exact ⟨thetaSquarefreePart_squarefree I,hA,hB,he⟩

theorem sourceFourier_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceResidualFourierCoefficient (primaryGenerator I)≠0) :
    ∃A B:Ideal Eis,Squarefree A ∧ primaryGenerator A≠0 ∧ primaryGenerator B≠0 ∧ A*B^3=I := by
  have hs:sourceArithmeticResidue (primaryGenerator I)≠0:=by
    intro hz
    exact hS (by rw [sourceResidualFourierCoefficient,hz,mul_zero])
  exact ⟨thetaSquarefreePart I,thetaCubePart I,
    sourceArithmeticResidue_squarefree_cube_support I hI hs⟩

theorem sourceFourier_primary_zero_of_base_zero (hC:infinityCoefficientScalar=0)
    (n:Eis) (hprimary:lambda^2∣n-1) : sourceResidualFourierCoefficient n=0 := by
  have hn:n≠0:=primary_ne_zero n hprimary
  let I:Ideal Eis:=Ideal.span {n}
  have hgen:primaryGenerator I=n:=primaryGenerator_span n hn hprimary
  have hI:primaryGenerator I≠0:=by rwa [hgen]
  by_contra hT
  have hTI:sourceResidualFourierCoefficient (primaryGenerator I)≠0:=by rwa [hgen]
  obtain ⟨A,B,hA,hAg,hBg,hAB⟩:=sourceFourier_squarefree_cube_support I hI hTI
  have harg:primaryGenerator A*(primaryGenerator B)^3=n:=by
    have he:=congrArg primaryGenerator hAB
    simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he
  have he:=infinityCoefficient_squarefree_cube A B hAg hBg hA
  rw [harg,hC,zero_mul,zero_mul,zero_mul] at he
  exact hT (star_eq_zero.mp he)

end

section
open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_eq_of_initial_eq (h k:Eis)
    (he:∀s:ℂ,4<s.re→0<s.im→
      unramifiedCubicGaussSeries s h=unramifiedCubicGaussSeries s k) :
    unramifiedGaussResidue h=unramifiedGaussResidue k := by
  have hh:=unramifiedGaussResidue_of_initial_relation h k 0 (fun _=>1) (fun _=>0)
    (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
    continuousAt_const continuousAt_const (fun s hs hi=>by simpa using he s hs hi)
  simpa only [one_mul,zero_mul,add_zero] using hh

theorem unramifiedGaussResidue_neg (h:Eis) :
    unramifiedGaussResidue (-h)=unramifiedGaussResidue h :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_neg s h)

theorem unramifiedGaussResidue_lambda_pow (h:Eis) (n:ℕ) :
    unramifiedGaussResidue (h*lambda^n)=
      unramifiedGaussResidue (h*lambda^(n%3)) :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_lambda_pow s h n)

theorem unramifiedGaussResidue_lambda_cube (h:Eis) :
    unramifiedGaussResidue (h*lambda^3)=unramifiedGaussResidue h := by
  simpa using unramifiedGaussResidue_lambda_pow h 3

theorem unramifiedGaussResidue_nine_family (h:Eis) (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))=
      unramifiedGaussResidue (h*omega^j.val*lambda^k.val) := by
  obtain ⟨j,k,hjk⟩:=unramifiedCubicGaussSeries_nine_family h u n
  exact ⟨j,k,unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>hjk s)⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedResidueFamilyMass (h:Eis) : ℝ :=
  ∑a:Fin 3×Fin 3,‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖

lemma ramifiedResidueFamilyMass_nonneg (h:Eis) : 0≤ ramifiedResidueFamilyMass h :=
  Finset.sum_nonneg (fun _ _=>norm_nonneg _)

lemma unramifiedGaussResidue_family_norm_le (h:Eis) (j k:Fin 3) :
    ‖unramifiedGaussResidue (h*omega^j.val*lambda^k.val)‖≤ ramifiedResidueFamilyMass h := by
  unfold ramifiedResidueFamilyMass
  exact Finset.single_le_sum (a:=(j,k)) (s:=Finset.univ)
    (f:=fun a:Fin 3×Fin 3=>‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ (j,k))

lemma unramifiedGaussResidue_nine_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))‖≤ ramifiedResidueFamilyMass h := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_nine_family h u n
  rw [hjk]
  exact unramifiedGaussResidue_family_norm_le h j k

theorem unramifiedGaussResidue_unit_lambda_family (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue ((u:Eis)*lambda^n)=
      unramifiedGaussResidue (omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj⟩:=unit_eq_sign_omega u
  refine ⟨j,⟨n%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  rcases hj with hj|hj
  · rw [hj,unramifiedGaussResidue_lambda_pow]
  · rw [hj,neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_lambda_pow]

lemma unramifiedGaussResidue_unit_lambda_norm_le (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue ((u:Eis)*lambda^n)‖≤ ramifiedResidueFamilyMass 1 := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_unit_lambda_family u n
  rw [hjk]
  simpa only [one_mul] using unramifiedGaussResidue_family_norm_le 1 j k

lemma ramifiedResidueFamilyMass_unit_lambda_le (u:Eisˣ) (n:ℕ) :
    ramifiedResidueFamilyMass ((u:Eis)*lambda^n)≤9*ramifiedResidueFamilyMass 1 := by
  calc
    _≤∑a:Fin 3×Fin 3,ramifiedResidueFamilyMass 1:=by
      apply Finset.sum_le_sum
      intro a ha
      let v:Eisˣ:=u*ramifiedOmegaUnit^a.1.val
      have he:((u:Eis)*lambda^n)*omega^a.1.val*lambda^a.2.val=
          (v:Eis)*lambda^(n+a.2.val):=by
        simp only [v,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,pow_add]
        ring
      rw [he]
      exact unramifiedGaussResidue_unit_lambda_norm_le v _
    _=_:=by simp

theorem sourceArithmeticResidue_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤
      ((∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)) := by
  have hM:=ramifiedResidueFamilyMass_nonneg h
  have hden:0<4*(9*Real.sqrt 3/2):=by positivity
  rw [sourceArithmeticResidue_eq_ramified_table h hh]
  split_ifs with hphase
  · rw [norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<(9*Real.sqrt 3/2:ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _≤‖∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
          unramifiedGaussResidue (principalRamifiedIndex h i)‖+
          ‖(3:ℂ)*unramifiedGaussResidue (9*h)‖:=norm_add_le _ _
      _≤(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)*
          ramifiedResidueFamilyMass h+3*ramifiedResidueFamilyMass h:=by
        apply add_le_add
        · calc
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)*
                unramifiedGaussResidue (principalRamifiedIndex h i)‖:=norm_sum_le _ _
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖*
                ramifiedResidueFamilyMass h:=by
              apply Finset.sum_le_sum
              intro i hi
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (unramifiedGaussResidue_nine_norm_le h i.1 (i.2.val+2)) (norm_nonneg _)
            _=_:=by rw [Finset.sum_mul]
        · rw [norm_mul,Complex.norm_ofNat]
          have hb:=unramifiedGaussResidue_nine_norm_le h (1:Eisˣ) 0
          simp only [Units.val_one,pow_zero,mul_one] at hb
          simpa only [mul_comm 9 h] using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3)
      _=_:=by ring
  · rw [norm_zero]
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedDecayRatio : ℝ := (3:ℝ)^(-(1/3:ℝ))

lemma ramifiedDecayRatio_pos : 0< ramifiedDecayRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma ramifiedDecayRatio_lt_one : ramifiedDecayRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma explicitRamifiedCoefficient_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖explicitRamifiedCoefficient h u n‖≤(3^n:ℕ) := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · dsimp only
    split_ifs <;> simp [residueAdditive,breveE_norm]
  · simp

lemma ramifiedWeight_norm_scalar (n:ℕ) :
    ‖((3^n:ℕ):ℂ)^(-(4/3:ℂ))‖*(3^n:ℕ)=ramifiedDecayRatio^n := by
  have ha:0<(3:ℝ)^n:=pow_pos (by norm_num) _
  have hn:‖((3:ℂ)^n)^(-(4/3:ℂ))‖=((3:ℝ)^n)^(-(4/3:ℝ)):=by
    have he:=Complex.norm_cpow_eq_rpow_re_of_pos ha (-(4/3:ℂ))
    have hre:(-(4/3:ℂ)).re=-(4/3:ℝ):=by norm_num
    rw [hre] at he
    simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using he
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hn]
  calc
    ((3:ℝ)^n)^(-(4/3:ℝ))*(3:ℝ)^n=
        ((3:ℝ)^n)^(-(4/3:ℝ))*((3:ℝ)^n)^(1:ℝ):=by rw [Real.rpow_one]
    _=((3:ℝ)^n)^(-(1/3:ℝ)):=by
      rw [←Real.rpow_add ha]
      congr 1
      norm_num
    _=(3:ℝ)^((n:ℝ)*(-(1/3:ℝ))):=(Real.rpow_natCast_mul (by norm_num) n _).symm
    _=(3:ℝ)^((-(1/3:ℝ))*(n:ℝ)):=by rw [mul_comm]
    _=ramifiedDecayRatio^n:=by
      rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
      rfl

lemma principalRamifiedWeight_norm_le (h:Eis) (i:PrincipalRamifiedIndex h) :
    ‖principalRamifiedWeight h i (4/3)‖≤ ramifiedDecayRatio^(i.2.val+2) := by
  unfold principalRamifiedWeight
  rw [norm_mul]
  calc
    _≤‖((3^(i.2.val+2):ℕ):ℂ)^(-(4/3:ℂ))‖*(3^(i.2.val+2):ℕ):=
      mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h i.1 _) (norm_nonneg _)
    _=_:=ramifiedWeight_norm_scalar _

theorem principalRamifiedWeight_sum_norm_le (h:Eis) :
    (∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio) := by
  have ht0:=ramifiedDecayRatio_pos.le
  have ht1:=ramifiedDecayRatio_lt_one
  have hfin:(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2))≤
      ramifiedDecayRatio^2/(1-ramifiedDecayRatio):=by
    rw [Fin.sum_univ_eq_sum_range (fun n:ℕ=>ramifiedDecayRatio^(n+2))]
    simp_rw [pow_add,mul_comm _ (ramifiedDecayRatio^2)]
    rw [←Finset.mul_sum]
    have hs: (∑n∈Finset.range (ramifiedFrequencyBound h+1),ramifiedDecayRatio^n)≤
        (1-ramifiedDecayRatio)⁻¹:=by
      rw [←tsum_geometric_of_lt_one ht0 ht1]
      exact (summable_geometric_of_lt_one ht0 ht1).sum_le_tsum _ (fun n _=>pow_nonneg ht0 n)
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs (sq_nonneg ramifiedDecayRatio)
  calc
    _≤∑i:PrincipalRamifiedIndex h,ramifiedDecayRatio^(i.2.val+2):=
      Finset.sum_le_sum (fun i _=>principalRamifiedWeight_norm_le h i)
    _=(6:ℝ)*(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2)):=by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc:Fintype.card Eisˣ=6:=by
        simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
      rw [hc]
      norm_num
    _≤6*(ramifiedDecayRatio^2/(1-ramifiedDecayRatio)):=mul_le_mul_of_nonneg_left hfin (by norm_num)
    _=_:=by ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedSourceFamilyConstant : ℝ :=
  (6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)/(4*(9*Real.sqrt 3/2))

lemma ramifiedSourceFamilyConstant_nonneg : 0≤ ramifiedSourceFamilyConstant := by
  have ht:0<1-ramifiedDecayRatio:=sub_pos.mpr ramifiedDecayRatio_lt_one
  unfold ramifiedSourceFamilyConstant
  positivity

theorem sourceArithmeticResidue_nine_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤ ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h := by
  have hm:=ramifiedResidueFamilyMass_nonneg h
  refine (sourceArithmeticResidue_family_bound h hh).trans ?_
  have hw:(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3:=by
    linarith [principalRamifiedWeight_sum_norm_le h]
  calc
    _≤(6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw hm) (by positivity)
    _=ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h:=by
      unfold ramifiedSourceFamilyConstant
      ring

theorem sourceArithmeticResidue_unit_lambda_bound (u:Eisˣ) (n:ℕ) :
    ‖sourceArithmeticResidue ((u:Eis)*lambda^n)‖≤
      9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1 := by
  refine (sourceArithmeticResidue_nine_family_bound _ (ramifiedElement_ne_zero u n)).trans ?_
  have he:=mul_le_mul_of_nonneg_left (ramifiedResidueFamilyMass_unit_lambda_le u n)
    ramifiedSourceFamilyConstant_nonneg
  convert he using 1 ; ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def extraPeriodWitness : levelThree := by
  let M:SL(2,Eis):=⟨!![1+3*omega,3*omega^2;-3,1-3*omega],by
    rw [Matrix.det_fin_two_of]
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨omega,by change 1+3*omega-1=3*omega;ring⟩
  · exact ⟨omega^2,by change 3*omega^2-0=3*omega^2;ring⟩
  · exact ⟨-1,by change -3-(0:Eis)=3*(-1);ring⟩
  · exact ⟨-omega,by change 1-3*omega-1=3*(-omega);ring⟩

def rationalLowerMinusThree : SL(2,ℤ):=⟨!![1,0;-3,1],by simp [Matrix.det_fin_two]⟩

lemma extraPeriodWitness_factor :
    integralComplexMatrix (extraPeriodWitness:SL(2,Eis))=
      complexTranslation (-eisEmbedding omega)*
        integralComplexMatrix (rationalEmbedding rationalLowerMinusThree)*
        complexTranslation (eisEmbedding omega) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix_apply,
    rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [extraPeriodWitness, rationalLowerMinusThree, complexTranslation, map_ofNat] <;> ring

lemma extraPeriodWitness_character : complexCharacter extraPeriodWitness=eisEmbedding omega := by
  change eisEmbedding (symbol (-3) (1+3*omega))=eisEmbedding omega
  apply congrArg eisEmbedding
  have hp:lambda^2∣(1+3*omega)-1:=lambda_sq_dvd_three.trans ⟨omega,by ring⟩
  rw [symbol_neg_numerator _ _ hp]
  have he:=ramified_symbol_at_omega (-(ramifiedOmegaUnit^2)) 2 2
    (Or.inr (by simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]))
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination ramified_omega_relation
  have hnum:((-(ramifiedOmegaUnit^2):Eisˣ):Eis)*lambda^2=3:=by
    simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    rw [hl]
    calc
      _=3*omega^3:=by ring
      _=3:=by rw [omega_primitive.pow_eq_one];ring
  rw [hnum] at he
  have hw:omega^(2*2)=omega:=by
    norm_num only [Nat.reduceMul]
    calc
      omega^4=omega^3*omega:=by ring
      _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]
  exact he.trans hw

lemma extraPeriodWitness_character_ne_one : complexCharacter extraPeriodWitness≠1 := by
  rw [extraPeriodWitness_character]
  intro he
  exact omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa only [map_one] using he))

theorem cubicSource_not_eisenstein_periodic :
    ¬(∀a:Eis,∀w:HyperbolicSpace,
      cubicSourceResidualFunction (complexTranslation (eisEmbedding a) • w)=
        cubicSourceResidualFunction w) := by
  intro hperiod
  apply cubicSourceResidualFunction_ne_zero
  funext w
  have hneg (u:HyperbolicSpace):
      cubicSourceResidualFunction (complexTranslation (-eisEmbedding omega) • u)=
        cubicSourceResidualFunction u:=by
    simpa only [map_neg] using hperiod (-omega) u
  have hinv:cubicSourceResidualFunction
      (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=cubicSourceResidualFunction w:=by
    rw [extraPeriodWitness_factor,mul_smul,mul_smul,hneg,
      cubicSourceResidualFunction_rational_invariant,hperiod]
  have hchar:=cubicSourceResidualFunction_automorphy (sourceLevelInclusion extraPeriodWitness) w
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    levelTwoComplexCharacter ⟨(extraPeriodWitness:SL(2,Eis)),levelThree_le_levelTwo extraPeriodWitness.property⟩*
      cubicSourceResidualFunction w at hchar
  rw [levelTwoComplexCharacter_restrict] at hchar
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    complexCharacter extraPeriodWitness*cubicSourceResidualFunction w at hchar
  rw [hinv] at hchar
  have hz:(complexCharacter extraPeriodWitness-1)*cubicSourceResidualFunction w=0:=by
    linear_combination -hchar
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr extraPeriodWitness_character_ne_one)

end CubicEisenstein

end

end OAI

end

