module

public import Green64.Library.Analysis.NumberTheory.DirichletL.GaussSum.Part005

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / QuadraticSieve / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents -/

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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator

theorem poissonComparisonMajorant_small_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ (η : ℝ) (hη : 0<η), η≤1 ∧ 259*η≤ρ ∧
    ∃ (l A : ℕ), 4≤η*l ∧ 4≤η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0≤CD → 0≤CS → 0≤CT → 0≤CP →
      ∀ (B C1 : ℝ), 1≤B → 1≤C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0<Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
          1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1≤ selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤
          Cfinal*(M*X)^ρ*poissonShape M X α := by
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : 259*η≤ρ := by
    have hh : η≤ρ/600 := min_le_right _ _
    linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith
  refine ⟨η,hη,hη1,hηρ,l,l,horder,horder,?_⟩
  intro sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  obtain ⟨Cfinal,hCf,hbound⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l l horder horder sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  refine ⟨Cfinal,hCf,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  apply (hbound C M X q G hC hBC hCC hM hX hq hqX hG hGN hK).trans
  have hP : 1≤M*X := by nlinarith
  have hshape : 0≤poissonShape M X α := by unfold poissonShape; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hηρ) hCf.le) hshape

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

namespace CubicEisenstein

lemma hyperbolicHeight_continuous : Continuous hyperbolicHeight := by
  apply Continuous.quotient_lift
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  apply Continuous.inv₀
  · exact ((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2)
  · intro g
    exact (rowEnergy_pos _ (complexBottomRow_ne_zero g)).ne'

lemma matrixCross_eq_gram (g : SL(2,ℂ)) : matrixCross g=matrixGram g 0 1 := by
  simp only [matrixCross,matrixGram,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]

lemma hyperbolicGram_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicGram (upperPoint z v hv) 0 1=z/(v:ℂ) := by
  change matrixGram (upperSection z v hv) 0 1=_
  rw [←matrixCross_eq_gram]
  have hh := matrixCross_upperSection (1:SL(2,ℂ)) z v hv
  simpa [Matrix.one_apply] using hh

def hyperbolicHorizontal (w : HyperbolicSpace) : ℂ :=
  hyperbolicGram w 0 1*(hyperbolicHeight w:ℂ)

lemma hyperbolicHorizontal_continuous : Continuous hyperbolicHorizontal := by
  unfold hyperbolicHorizontal
  exact ((continuous_apply 1).comp ((continuous_apply 0).comp hyperbolicGram_continuous)).mul
    (Complex.continuous_ofReal.comp hyperbolicHeight_continuous)

@[simp] lemma hyperbolicHorizontal_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHorizontal (upperPoint z v hv)=z := by
  simp only [hyperbolicHorizontal,hyperbolicGram_upperPoint,hyperbolicHeight_upperPoint]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hv.ne')

def hyperbolicCoordinates (w : HyperbolicSpace) : UpperCoordinates :=
  ⟨(hyperbolicHorizontal w,hyperbolicHeight w),hyperbolicHeight_pos w⟩

lemma hyperbolicCoordinates_continuous : Continuous hyperbolicCoordinates :=
  (hyperbolicHorizontal_continuous.prodMk hyperbolicHeight_continuous).subtype_mk _

lemma upperCoordinates_left_inverse : Function.LeftInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro p
  apply Subtype.ext
  exact Prod.ext (hyperbolicHorizontal_upperPoint _ _ _) (hyperbolicHeight_upperPoint _ _ _)

lemma upperCoordinates_right_inverse : Function.RightInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  exact congrArg (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2)
    (upperCoordinates_left_inverse ⟨(z,v),hv⟩)

def upperCoordinatesHomeomorph : UpperCoordinates ≃ₜ HyperbolicSpace where
  toFun p := upperPoint p.1.1 p.1.2 p.2
  invFun := hyperbolicCoordinates
  left_inv := upperCoordinates_left_inverse
  right_inv := upperCoordinates_right_inverse
  continuous_toFun := continuous_upperCoordinates
  continuous_invFun := hyperbolicCoordinates_continuous

lemma fundamentalSet_measure_le_cover (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hH : H≤CubicKubota.levelThree) (B : Set HyperbolicSpace)
    (hB : ∀w,∃M:H,M • w∈B) :
    hyperbolicVolume (hyperbolicFundamentalSet H)≤hyperbolicVolume B := by
  rw [(hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_eq_tsum B]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro w hw
  obtain ⟨M,hM⟩ := hB w
  apply Set.mem_iUnion.mpr
  refine ⟨M⁻¹,?_,hw⟩
  exact ⟨M • w,hM,inv_smul_smul M w⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

def spatialHeightSplit : EuclideanSpatial ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)

lemma spatialHeightSplit_fst (p : EuclideanSpatial) : (spatialHeightSplit p).1=p 2 := rfl
lemma spatialHeightSplit_snd_zero (p : EuclideanSpatial) : (spatialHeightSplit p).2 0=p 0 := rfl
lemma spatialHeightSplit_snd_one (p : EuclideanSpatial) : (spatialHeightSplit p).2 1=p 1 := rfl

lemma spatialHeightSplit_preserves_volume : MeasurePreserving spatialHeightSplit volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))

def horizontalUnitBox : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1) 1)
lemma horizontalUnitBox_measurable : MeasurableSet horizontalUnitBox :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
lemma horizontalUnitBox_volume : volume horizontalUnitBox=4 := by
  rw [horizontalUnitBox,volume_pi_pi]
  norm_num

def euclideanCuspBox (a : ℝ) : Set EuclideanSpatial :=
  spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox)
lemma euclideanCuspBox_measurable (a : ℝ) : MeasurableSet (euclideanCuspBox a) :=
  spatialHeightSplit.measurable (measurableSet_Ioi.prod horizontalUnitBox_measurable)
lemma euclideanCuspBox_positive (a : ℝ) (ha : 0≤a) : euclideanCuspBox a ⊆ euclideanUpperHalf := by
  intro p hp
  exact ha.trans_lt hp.1

theorem euclideanCuspBox_volume (a : ℝ) (ha : 0<a) :
    hyperbolicEuclideanVolume (euclideanCuspBox a)=4*ENNReal.ofReal (1/(2*a^2)) := by
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (euclideanCuspBox_measurable a),
    Measure.restrict_restrict (euclideanCuspBox_measurable a),
    Set.inter_eq_left.mpr (euclideanCuspBox_positive a ha.le)]
  change (∫⁻p in spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox),
    ENNReal.ofReal (((spatialHeightSplit p).1^3)⁻¹))=_
  rw [spatialHeightSplit_preserves_volume.setLIntegral_comp_preimage
    (f := fun q : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal ((q.1^3)⁻¹))
    (measurableSet_Ioi.prod horizontalUnitBox_measurable) (by fun_prop)]
  change (∫⁻q : ℝ × (Fin 2 → ℝ) in Set.Ioi a ×ˢ horizontalUnitBox,
    ENNReal.ofReal ((q.1^3)⁻¹) ∂((volume : Measure ℝ).prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    horizontalUnitBox_volume]
  rw [lintegral_mul_const _ (by fun_prop),cusp_height_volume a ha]
  exact mul_comm _ _

local notation "O" => ActualEisensteinCubic.O

instance fullSLMeasurableAction : MeasurableConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨fun g => (continuous_hyperbolic_action g).measurable⟩
instance fullSLVolumeInvariant : SMulInvariantMeasure (SL(2,ℂ)) HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul g s hs := by
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s) (hyperbolicVolume_invariant g)
    simpa only [Measure.map_apply (continuous_hyperbolic_action g).measurable hs] using he

def hyperbolicCuspBox (a : ℝ) : Set HyperbolicSpace :=
  {w | ‖hyperbolicHorizontal w‖≤1 ∧ a<hyperbolicHeight w}

lemma hyperbolicCuspBox_measurable (a : ℝ) : MeasurableSet (hyperbolicCuspBox a) :=
  (isClosed_le hyperbolicHorizontal_continuous.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const hyperbolicHeight_continuous).measurableSet

lemma hyperbolicCuspBox_volume_le (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)≤4*ENNReal.ofReal (1/(2*a^2)) := by
  rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable
    (hyperbolicCuspBox_measurable a),←euclideanCuspBox_volume a ha]
  apply measure_mono_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp hB
  rw [Set.mem_preimage,euclideanToHyperbolic_positive p hp] at hB
  change ‖hyperbolicHorizontal (upperPoint _ _ hp)‖≤1 ∧ a<hyperbolicHeight (upperPoint _ _ hp) at hB
  rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint] at hB
  refine ⟨hB.2,?_⟩
  intro j hj
  fin_cases j
  · change -1≤p 0 ∧ p 0≤1
    have hh := (Complex.abs_re_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
  · change -1≤p 1 ∧ p 1≤1
    have hh := (Complex.abs_im_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh

lemma hyperbolicCuspBox_volume_lt_top (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)<⊤ :=
  (hyperbolicCuspBox_volume_le a ha).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)

theorem hyperbolicFundamentalSet_volume_lt_top (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] :
    hyperbolicVolume (hyperbolicFundamentalSet H)<⊤ := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  let a : ℝ := Real.sqrt (2/3)/2
  have ha : 0<a := by dsimp [a]; positivity
  let B : Set HyperbolicSpace := ⋃r∈S,integralComplexMatrix r⁻¹ • hyperbolicCuspBox a
  have hcover : ∀w,∃M:H,M • w∈B := by
    intro w
    obtain ⟨M,r,hr,z,v,hv,hM,hz,hfloor⟩ := hS w
    refine ⟨M,?_⟩
    rw [integralSubgroup_smul,hM]
    apply Set.mem_iUnion.mpr
    refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
    apply Set.mem_smul_set.mpr
    refine ⟨upperPoint z v hv,?_,rfl⟩
    change ‖hyperbolicHorizontal (upperPoint z v hv)‖≤1 ∧ a<hyperbolicHeight (upperPoint z v hv)
    rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
    refine ⟨?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    · dsimp [a] at *
      linarith
  apply (fundamentalSet_measure_le_cover H hH B hcover).trans_lt
  apply (measure_biUnion_finset_le S (fun r => integralComplexMatrix r⁻¹ • hyperbolicCuspBox a)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro r hr
  rw [measure_smul]
  exact hyperbolicCuspBox_volume_lt_top a ha

lemma integralQuotientVolume_univ (H : Subgroup (SL(2,O))) :
    integralQuotientVolume H Set.univ=hyperbolicVolume (hyperbolicFundamentalSet H) := by
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection H) MeasurableSet.univ]
  simp

theorem integralQuotientVolume_finite (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] : IsFiniteMeasure (integralQuotientVolume H) :=
  ⟨by rw [integralQuotientVolume_univ]; exact hyperbolicFundamentalSet_volume_lt_top H hH⟩

instance kernelQuotientVolume_finite : IsFiniteMeasure (integralQuotientVolume globalKubotaKernel) := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact integralQuotientVolume_finite globalKubotaKernel globalKubotaKernel_le_levelThree

end CubicEisenstein

namespace CanonicalQuadraticSieve

section

theorem improved_threshold_ge_column (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N≤M := by
  have hp : 1≤2-1/α := by
    have hh : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα
    linarith
  calc
    N = N^(1:ℝ) := (Real.rpow_one N).symm
    _ ≤ N^(2-1/α) := Real.rpow_le_rpow_of_exponent_le hN hp
    _ ≤ M := hM

theorem improved_threshold_power (α N M : ℝ) (hα : 0<α) (hN : 0<N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)≤M^α := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hM hα.le
  rw [←Real.rpow_mul hN.le] at hh
  have he : (2-1/α)*α=2*α-1 := by field_simp
  rwa [he] at hh

theorem improved_threshold_main (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)*M^(1-α)≤M := by
  have hNM := improved_threshold_ge_column α N M hα hN hM
  have hM0 : 0<M := by linarith
  have hh := improved_threshold_power α N M (by linarith) (by linarith) hM
  calc
    _ ≤ M^α*M^(1-α) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hM0.le _)
    _ = M := by rw [←Real.rpow_add hM0]; simp

theorem improved_threshold_shape (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : M+N+N^(2*α-1)*M^(1-α)≤3*M := by
  linarith [improved_threshold_main α N M hα hN hM,
    improved_threshold_ge_column α N M hα hN hM]

theorem improved_threshold_reciprocal (α N M : ℝ) (_hα : 0<α) (hN : 0<N) (hM0 : 0<M)
    (hM : N^(2-1/α)≤M) : N^2/M≤N^(1/α) := by
  apply (div_le_iff₀ hM0).mpr
  have he : N^2=N^(2-1/α)*N^(1/α) := by
    rw [←Real.rpow_add hN]
    convert (Real.rpow_two N).symm using 1 ; ring_nf
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hN.le (1/α))

theorem improved_threshold_low (α C η N M : ℝ) (hα : 0<α) (hC : 0<C)
    (hN : 0<N) (hM0 : 0<M) (hM : N^(2-1/α)≤M) :
    (selectedPoissonK C M N η)^α≤C^α*(M*N)^(η*α)*N := by
  have hk : selectedPoissonK C M N η≤C*(M*N)^η*N^(1/α) := by
    unfold selectedPoissonK selectedPoissonT
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (improved_threshold_reciprocal α N M hα hN hM0 hM) (by positivity)
  have hk0 : 0≤ selectedPoissonK C M N η := by
    unfold selectedPoissonK selectedPoissonT
    positivity
  calc
    _ ≤ (C*(M*N)^η*N^(1/α))^α := Real.rpow_le_rpow hk0 hk hα.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤C*(M*N)^η) (by positivity),
        Real.mul_rpow hC.le (by positivity),←Real.rpow_mul (by positivity : 0≤M*N),
        ←Real.rpow_mul hN.le]
      have he : (1/α)*α=1 := by field_simp
      rw [he,Real.rpow_one]

theorem sieveNorm_large_rows (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hlarge : N^2≤M) :
    sieveNorm M N≤5*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤2*N := by
    have h := Nat.ceil_lt_add_one (by linarith : 0≤N)
    linarith
  have hsq : (⌈N⌉₊:ℝ)^2≤4*M := by
    calc
      _ ≤ (2*N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 2
      _ = 4*N^2 := by ring
      _ ≤ 4*M := by linarith
  have hh := sieveNorm_initial M N hM hN
  have hC := QuadraticInitialBound.initialSieveConstant_pos
  nlinarith

theorem hasSieveExponent_of_threshold_band (β : ℝ) (_hβ1 : 1≤β) (hβ2 : β≤2)
    (hband : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^β≤M → M≤N^2 → sieveNorm M N≤C*(M*N)^ρ*M) :
    HasSieveExponent β := by
  intro ε hε
  have hρ : 0<ε/3 := by positivity
  obtain ⟨C,hC,hbound⟩ := hband (ε/3) hρ
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨C+5*I,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hpow : 1≤(M*N)^ε := Real.one_le_rpow hMN hε.le
  have hNb : 0≤N^β := Real.rpow_nonneg hN0.le _
  by_cases hlarge : N^2≤M
  · calc
      _ ≤ 5*I*M := sieveNorm_large_rows M N hM hN hlarge
      _ = (5*I)*1*M := by ring
      _ ≤ (C+5*I)*(M*N)^ε*(M+N^β) := by gcongr <;> linarith
  · let R := max M (N^β)
    have hNβsq : N^β≤N^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN hβ2
    have hR : 1≤R := hM.trans (le_max_left _ _)
    have hRM : M≤R := le_max_left _ _
    have hRN : N^β≤R := le_max_right _ _
    have hRsq : R≤N^2 := max_le (le_of_not_ge hlarge) hNβsq
    have hb := hbound R N hR hN hRN hRsq
    have hmono := sieveNorm_mono hRM (le_refl N)
    have hN2 : 1≤N^2 := one_le_pow₀ hN
    have hM3 : M≤M^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show (1:ℕ)≤3 by decide)
    have hRN2 : R≤M*N^2 := by
      apply max_le
      · nlinarith
      · exact hNβsq.trans (by nlinarith)
    have hprod : R*N≤(M*N)^3 := by
      calc
        _ ≤ (M*N^2)*N := mul_le_mul_of_nonneg_right hRN2 hN0.le
        _ = M*N^3 := by ring
        _ ≤ M^3*N^3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = _ := by ring
    have hRprod : (R*N)^(ε/3)≤(M*N)^ε := by
      calc
        _ ≤ ((M*N)^3)^(ε/3) := Real.rpow_le_rpow (by positivity) hprod hρ.le
        _ = _ := by
          rw [←Real.rpow_natCast (M*N) 3,←Real.rpow_mul (by positivity : 0≤M*N)]
          congr 1
          ring
    have hRadd : R≤M+N^β := max_le (by linarith) (by linarith)
    exact hmono.trans (hb.trans (by gcongr ; linarith))

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_of_shell_threshold (β : ℝ) (hβ1 : 1≤β) (hβ2 : β≤2)
    (hshell : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M X : ℝ,
      1≤M → 1≤X → X^β≤M → ∀a : idealRange X → ℂ, CoefficientOnShell X X a →
      ballQuadraticEnergy M X a≤C*(M*X)^ρ*M*∑J,‖a J‖^2) :
    HasSieveExponent β := by
  apply hasSieveExponent_of_threshold_band β hβ1 hβ2
  intro ε hε
  have hρ : 0<ε/2 := by positivity
  obtain ⟨C,hC,hbound⟩ := hshell (ε/2) hρ
  let lengthScale := 2+1/((ε/2)*Real.log 2)
  have hL : 0<lengthScale := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [lengthScale]
    positivity
  refine ⟨4*C*8^(ε/2)*lengthScale,by positivity,?_⟩
  intro M N hM hN hMN hMsq
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hprod : 0<M*N := by positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N) _ (by positivity)
  intro a
  let a' := fun j : Fin (columnDyadicLength N+1) =>
    coefficientAtScale N ((2:ℝ)^j.val)
      (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)
  have hpart := ballQuadraticEnergy_column_shells_at_scale M N (columnDyadicLength N)
    (columnDyadicLength_cover N) a
  have hj (j : Fin (columnDyadicLength N+1)) :
      ballQuadraticEnergy M ((2:ℝ)^j.val) (a' j) ≤
        (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
    let X := (2:ℝ)^j.val
    have hx := columnDyadicScale_bounds N hN j
    have hβ0 : 0≤β := by linarith
    have hXpow : X^β≤4*M := by
      calc
        _ ≤ (2*N)^β := Real.rpow_le_rpow (by positivity) hx.2 hβ0
        _ = 2^β*N^β := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 4*N^β := by
          have ht : (2:ℝ)^β≤4 := by
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ)≤2) hβ2
            norm_num at ht
            exact ht
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hN0.le _)
        _ ≤ 4*M := by linarith
    have hshell' : CoefficientOnShell X X (a' j) :=
      coefficientAtScale_shell N X _ (dyadicColumnCoefficient_shell N _ _ j a)
    have hb := hbound (4*M) X (by linarith) hx.1 hXpow (a' j) hshell'
    have hp : ((4*M)*X)^(ε/2)≤8^(ε/2)*(M*N)^(ε/2) := by
      calc
        _ ≤ (8*(M*N))^(ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [hx.2]) hρ.le
        _ = _ := Real.mul_rpow (by norm_num) hprod.le
    apply (ballQuadraticEnergy_mono (by linarith : M≤4*M) (a' j)).trans
    apply hb.trans
    calc
      _ ≤ C*(8^(ε/2)*(M*N)^(ε/2))*(4*M)*∑J,‖a' j J‖^2 := by gcongr
      _ = _ := by ring
  have he : (∑j : Fin (columnDyadicLength N+1), ∑J,‖a' j J‖^2)=∑J,‖a J‖^2 :=
    dyadicColumnCoefficient_at_scale_energy N _ _ a
  have hlen : (columnDyadicLength N+1:ℝ)≤lengthScale*(M*N)^(ε/2) := by
    apply (columnDyadicLength_small_power (ε/2) hρ N hN).trans
    change lengthScale*N^(ε/2)≤lengthScale*(M*N)^(ε/2)
    gcongr
    nlinarith
  change ballQuadraticEnergy M N a≤_
  apply hpart.trans
  calc
    _ ≤ (columnDyadicLength N+1:ℝ)*
        ∑j : Fin (columnDyadicLength N+1),
          (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
      gcongr with j
      exact hj j
    _ = (columnDyadicLength N+1:ℝ)*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by
      rw [←Finset.mul_sum,he]
      ring
    _ ≤ (lengthScale*(M*N)^(ε/2))*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by gcongr
    _ = _ := by
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2)=(M*N)^ε := by
        rw [←Real.rpow_add hprod]
        congr 1
        ring
      calc
        _ = (4*C*8^(ε/2)*lengthScale)*((M*N)^(ε/2)*(M*N)^(ε/2))*M*(∑J,‖a J‖^2) := by ring
        _ = _ := by rw [hp]

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

def fixedBadNorm : ℝ := Ideal.absNorm (∏P∈fixedBadPrimes,P)
def fixedCutoffBase : ℝ := max 4 fixedBadNorm

theorem fixedBadNorm_one_le : 1≤fixedBadNorm := by
  have h1 : Admissible (1 : Ideal O) := by
    refine ⟨one_ne_zero, isUnit_one.squarefree, ?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.notMem_zero] at hP
  have he := commonMaskIdeal_eq_fixed_mul (1 : Ideal O) h1
  rw [mul_one] at he
  have hn : (∏P∈fixedBadPrimes,P)≠0 := by
    rw [←he]
    exact (commonMaskIdeal_squarefree 1).ne_zero
  unfold fixedBadNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hn (Ideal.absNorm_eq_zero_iff.mp h))

theorem fixedCutoffBase_bounds : 4≤fixedCutoffBase ∧ fixedBadNorm≤fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem HasSieveExponent.annular_selected_bound {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) (C1 : ℝ) (hC1 : 1≤C1) :
    ∃ C : ℝ, 0<C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase≤ c → c≤C1 → 1≤M → 4≤N → N^(2-1/α)≤M →
      1≤ selectedPoissonK c M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hα : 1/2≤α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 QuadraticInitialBound.annularSieveCutoff
  have hdiv : 0<divisorConstant η hη := divisorConstant_pos η hη
  let SD := supportConstant η hη*divisorConstant η hη
  have hSD : 0<SD := mul_pos (supportConstant_pos η hη) (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2^η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hN1 : 1≤N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hc4 : 4≤ c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm≤ c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4≤ selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N^2/M≤ selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0≤N^2/M := by positivity
    nlinarith
  have hH := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈gcdPool (fun J : idealRange N => J.val),
      (Ideal.absNorm D:ℝ)≤largeGcdThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (commonMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        QuadraticInitialBound.annularSieveCutoff ≤ 3*CF*(M*N)^(259*η)*M := by
    intro D hD hd
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hD
    have hd1 : 1≤(Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hadm.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (commonMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [commonMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (commonMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (commonMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α≤3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N)^(259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeGcdThreshold α N) (3*CF*(M*N)^(259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_gcd_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N^η≤(M*N)^η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N)^(259*η)*(M*N)^η=(M*N)^(260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N)^η*((M*N)^η)^2=(M*N)^(3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N)^(3*η)≤(M*N)^(260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hfirst : (3*CF*(M*N)^(259*η)*M/6)*(divisorConstant η hη*N^η) ≤
      (3*CF*divisorConstant η hη)*(M*N)^(260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N)^(259*η)*M)*(divisorConstant η hη*(M*N)^η) := by
        gcongr
        nlinarith [show 0≤3*CF*(M*N)^(259*η)*M by positivity]
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeGcdThreshold α N))^η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeGcdThreshold α N)^α))*
      SD*(N^η)^2 ≤ (4*CH*2^η*SD)*(M*N)^(260*η)*M := by
    calc
      _ ≤ ((4*CH*2^η)*(M*N)^η*M)*SD*((M*N)^η)^2 := by gcongr
      _ = (4*CH*2^η*SD)*(M*N)^(3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  change 16*(_+_*SD*(N^η)^2)*_≤_
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N)^(260*η)*M+
      (4*CH*2^η*SD)*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring

end CanonicalQuadraticSieve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CompactProfiles -/

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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

lemma cosetHeight_continuous (r : CuspCosets) : Continuous (cosetHeight r) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    have heq : cosetHeight (cosetOf M)=(fun w => hyperbolicHeight (complexMatrix M • w)) :=
      funext (cosetHeight_cosetOf M)
    change Continuous (cosetHeight (cosetOf M))
    rw [heq]
    exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action _)

lemma cuspCutoffCorrection_measurable (Y : ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cuspCutoffCorrection Y F) := by
  unfold cuspCutoffCorrection
  apply Measurable.tsum
  intro r
  apply Measurable.ite
  · exact (isOpen_lt continuous_const (cosetHeight_continuous r)).measurableSet
  · exact measurable_const.mul (hF.comp (cosetHeight_continuous r).measurable)
  · exact measurable_const

lemma cuspCutoffCorrection_norm_le (F : ℝ → ℂ) (C : ℝ) (hC : 0≤C)
    (hF : ∀v,‖F v‖≤C) (w : HyperbolicSpace) : ‖cuspCutoffCorrection 1 F w‖≤C := by
  by_cases hh : ∃r : CuspCosets,1<cosetHeight r w
  · obtain ⟨r,hr⟩ := hh
    rw [cuspCutoffCorrection_eq 1 le_rfl F w r hr,norm_mul,norm_inv,
      norm_cosetCharacter,inv_one,one_mul]
    exact hF _
  · have hz : cuspCutoffCorrection 1 F w=0 := by
      unfold cuspCutoffCorrection
      have hz : (fun r => cuspCutoffTerm 1 F r w)=(fun _ : CuspCosets => (0:ℂ)) := by
        funext r
        simp [cuspCutoffTerm,show ¬1<cosetHeight r w from fun h => hh ⟨r,h⟩]
      rw [hz,tsum_zero]
    rw [hz,norm_zero]
    exact hC

lemma smoothCuspSeedDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (smoothCuspSeedDefect a b s) :=
  cuspCutoffCorrection_measurable 1 _ (cuspSeedDefectProfile_continuous a b s ha hab).measurable

lemma smoothCuspSeedDefect_bounded (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    ∃C : ℝ, 0≤C ∧ ∀w,‖smoothCuspSeedDefect a b s w‖≤C := by
  obtain ⟨C,hC⟩ := (cuspSeedDefectProfile_hasCompactSupport a b s hab).exists_bound_of_continuous
    (cuspSeedDefectProfile_continuous a b s ha hab)
  refine ⟨max C 0,le_max_right _ _,fun w => ?_⟩
  exact cuspCutoffCorrection_norm_le _ _ (le_max_right _ _) (fun v => (hC v).trans (le_max_left _ _)) w

lemma kernelQuotientDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (kernelQuotientDefect a b s) :=
  measurable_from_quotient.mpr (smoothCuspSeedDefect_measurable a b s ha hab)

theorem kernelQuotientDefect_memLp (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    MemLp (kernelQuotientDefect a b s) 2 (integralQuotientVolume globalKubotaKernel) := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_bounded a b s ha hab
  apply MemLp.of_bound (kernelQuotientDefect_measurable a b s ha hab).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact hbound w

def kernelL2Defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  (kernelQuotientDefect_memLp a b s ha hab).toLp (kernelQuotientDefect a b s)

lemma kernelL2Defect_ae_eq (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelL2Defect a b ha hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientDefect a b s :=
  MemLp.coeFn_toLp _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

lemma cuspCutoffCorrection_add (F G : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (F+G) w=cuspCutoffCorrection 1 F w+cuspCutoffCorrection 1 G w := by
  unfold cuspCutoffCorrection
  rw [←(cuspCutoffTerm_summable 1 le_rfl F w).tsum_add (cuspCutoffTerm_summable 1 le_rfl G w)]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.add_apply]
  split_ifs <;> simp [mul_add]

lemma cuspCutoffCorrection_smul (c : ℂ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (c • F) w=c • cuspCutoffCorrection 1 F w := by
  unfold cuspCutoffCorrection
  rw [smul_eq_mul,←tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

def compactHeightProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) : ℝ → ℂ :=
  (Set.Icc a b).indicator (fun v => F (Set.projIcc a b hab v))

lemma compactHeightProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (compactHeightProfile a b hab F) :=
  (F.continuous.comp continuous_projIcc).measurable.indicator measurableSet_Icc

lemma compactHeightProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) (v : ℝ) :
    ‖compactHeightProfile a b hab F v‖≤‖F‖ := by
  unfold compactHeightProfile
  by_cases hv : v∈Set.Icc a b
  · rw [Set.indicator_of_mem hv]
    exact F.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hv,norm_zero]
    exact norm_nonneg _

lemma compactHeightProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (F+G)=compactHeightProfile a b hab F+compactHeightProfile a b hab G := by
  funext v
  simp [compactHeightProfile,Set.indicator_add]

lemma compactHeightProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (c • F)=c • compactHeightProfile a b hab F := by
  funext v
  by_cases hv : v∈Set.Icc a b <;> simp [compactHeightProfile,hv]

def kernelCompactProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (cuspCutoffCorrection 1 (compactHeightProfile a b hab F)) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
    have he := cuspCutoffCorrection_automorphy 1 le_rfl (compactHeightProfile a b hab F)
      (⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩ : CubicKubota.levelThree) w
    rw [hchar,one_mul] at he
    exact he.symm)

lemma kernelCompactProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (kernelCompactProfile a b hab F) :=
  measurable_from_quotient.mpr (cuspCutoffCorrection_measurable 1 _
    (compactHeightProfile_measurable a b hab F))

lemma kernelCompactProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ))
    (q : IntegralOrbitQuotient globalKubotaKernel) : ‖kernelCompactProfile a b hab F q‖≤‖F‖ := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact cuspCutoffCorrection_norm_le _ _ (norm_nonneg F)
      (compactHeightProfile_norm_le a b hab F) w

lemma kernelCompactProfile_memLp (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    MemLp (kernelCompactProfile a b hab F) 2 (integralQuotientVolume globalKubotaKernel) :=
  MemLp.of_bound (kernelCompactProfile_measurable a b hab F).aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall (kernelCompactProfile_norm_le a b hab F))

lemma kernelCompactProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (F+G)=kernelCompactProfile a b hab F+kernelCompactProfile a b hab G := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_add,cuspCutoffCorrection_add]
    rfl

lemma kernelCompactProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (c • F)=c • kernelCompactProfile a b hab F := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_smul,cuspCutoffCorrection_smul]
    rfl

def compactProfileL2Linear (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →ₗ[ℂ] KernelQuotientL2 where
  toFun F := (kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)
  map_add' F G := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_add,MemLp.coeFn_toLp,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_add]
  map_smul' c F := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_smul,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_smul]
    exact Filter.Eventually.of_forall (fun _ => rfl)

lemma compactProfileL2Linear_bound (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    ‖compactProfileL2Linear a b hab F‖≤
      (measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹)*‖F‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg F)
  filter_upwards [MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)] with q hq
  change ‖((kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)) q‖≤‖F‖
  rw [hq]
  exact kernelCompactProfile_norm_le a b hab F q

def compactProfileL2 (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →L[ℂ] KernelQuotientL2 :=
  (compactProfileL2Linear a b hab).mkContinuous
    ((measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹))
    (compactProfileL2Linear_bound a b hab)

lemma compactProfileL2_ae_eq (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    compactProfileL2 a b hab F =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCompactProfile a b hab F :=
  MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)

def compactLogProfile (a b : ℝ) (ha : 0<a) : C(Set.Icc a b,ℂ) :=
  ⟨fun v => (Real.log (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => (ha.trans_le v.2.1).ne'))⟩

def compactDefectSecond (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)^2*((deriv (deriv (cuspTransition a b)) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).pow 2 |>.mul
      (Complex.continuous_ofReal.comp (hdd.continuous.comp continuous_subtype_val))

def compactDefectFirst (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)*((deriv (cuspTransition a b) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp (hd.continuous.comp continuous_subtype_val))

def compactDefectProfile (a b : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a b,ℂ) :=
  NormedSpace.exp (s • compactLogProfile a b ha)*
    (compactDefectSecond a b+(2*s-1) • compactDefectFirst a b)

lemma compactDefectProfile_apply (a b : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a b) :
    compactDefectProfile a b ha s v=cuspSeedDefectProfile a b s v := by
  have hexp := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a b ha)
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v*
    (compactDefectSecond a b v+(2*s-1)*compactDefectFirst a b v)=_
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v=
    NormedSpace.exp ((s • compactLogProfile a b ha) v) at hexp
  rw [hexp,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,
    compactDefectSecond,compactDefectFirst,cuspSeedDefectProfile,positiveHeightPower,
    logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]
  ring

lemma compactDefectProfile_entire (a b : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactDefectProfile a b ha) := by
  have he := differentiable_exp_smul_const ℂ (compactLogProfile a b ha)
  exact he.mul ((differentiable_const _).add
    (((differentiable_const (2:ℂ)).mul differentiable_id |>.sub (differentiable_const 1)).smul
      (differentiable_const (compactDefectFirst a b))))

lemma compactHeightProfile_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactHeightProfile a b hab.le (compactDefectProfile a b ha s)=cuspSeedDefectProfile a b s := by
  funext v
  by_cases hv : v∈Set.Icc a b
  · rw [compactHeightProfile,Set.indicator_of_mem hv,Set.projIcc_of_mem hab.le hv,
      compactDefectProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem hv]
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    exact (cuspSeedDefectProfile_zero a b s v hab hout).symm

lemma compactProfileL2_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactProfileL2 a b hab.le (compactDefectProfile a b ha s)=kernelL2Defect a b ha hab s := by
  apply Lp.ext
  grw [compactProfileL2_ae_eq,kernelL2Defect_ae_eq]
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a b hab.le (compactDefectProfile a b ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s) w
    rw [compactHeightProfile_actual_defect a b ha hab s]

theorem kernelL2Defect_entire (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Differentiable ℂ (kernelL2Defect a b ha hab) := by
  have heq : kernelL2Defect a b ha hab=
      fun s => compactProfileL2 a b hab.le (compactDefectProfile a b ha s) :=
    funext (fun s => (compactProfileL2_actual_defect a b ha hab s).symm)
  rw [heq]
  exact (compactProfileL2 a b hab.le).differentiable.comp (compactDefectProfile_entire a b ha)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem full_uniform_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W g₁ g₂ X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro ι _ p hp _ hcop hg
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  apply secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

theorem full_uniform_twisted_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (θ₁ θ₂ D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro ι _ p hp _ hcop hg
    θ₁ θ₂ D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  have htw₁ : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have htw₂ : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₁ : ∀ s, frequencyTwist A₁ (-θ₁) s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₂ : ∀ s, frequencyTwist A₂ θ₂ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hh := secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs
    (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂ windows
  dsimp only at hh
  rw [normalized_conjugate_frequencyTwist U hUc hUs,
    halfNormalization_twist U hUc hUs] at hh
  exact hh (hwo _ _ _ _ _ hz hud hue huv hkap)
    (fun a ha => hwt (frequencyTwist A₁ (-θ₁)) _ hsupp₁ hz 5 a ha)
    (fun a ha => hwt (frequencyTwist A₂ θ₂) _ hsupp₂ hz 6 a ha)

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassFiber (newRow)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLiteralTerm (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    secondExpansionSource p hp hcop hg (globalSecondRawPool F x) Ψ m' c d ray {x.source}
      (fun A => normalizedColumn p (fun S => g₁ (columnLog p X S)) A)
      (fun A => normalizedColumn p (fun S => g₂ (columnLog p X S)) A) W Y

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] hp in
theorem globalResidualScale_eq (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    secondExpansionScale p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
      (expansionSupportData x.common x.firstDivisor x.source) = globalActualResidualScale p ell side x := by
  simp only [secondExpansionScale,expansionSupportData,primeSubsetGenerator_norm_eq_productNorm,globalActualResidualScale]
  ring

end

theorem globalSecondLiteralTerm_fixed_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray g₁ g₂ W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            A₁ A₂ W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray g₁ g₂ W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM frequencyTwist frequencyTwist_apply halfNormalization_twist)
open SecondPassFiber (newRow)

theorem globalSecondLiteralTerm_twisted_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (θ₁ θ₂ ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_twisted_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray θ₁ θ₂ ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have htw₁ : ∀ t, frequencyTwist g₁ θ₁ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₁ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have htw₂ : ∀ t, frequencyTwist g₂ θ₂ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₂ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale,halfNormalization_twist U hUc hUs,halfNormalization_twist U hUc hUs] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg θ₁ θ₂ (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
open ActualEisensteinCubic
open JointLogSeparation (frequencyTwist)
open SecondPassIntegration (densityChildEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLiteralBinSource (γ : GlobalSecondData ι → ℂ)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) : ℂ :=
  ∑ ray : SecondRayIndex,∑ x∈globalLogSector p s side j,
    γ x * globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g₁ g₂ W ell Y side x

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sum_globalArithmeticBin {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (f : GlobalSecondData ι → M) :
    ∑ x∈globalLogSector p s side j,f x =
    ∑ q∈globalBinTriples p s side j,∑ x∈globalArithmeticBin p s side q j,f x := by
  have h := sum_globalSecondFixedTriple p (globalLogSector p s side j) f
  simpa only [globalBinTriples,globalLogSector,globalArithmeticBin,Finset.filter_filter,and_comm] using h
end

theorem globalSecondLiteralBinSource_transfer
    (ε : ℝ) (hε : 0 < ε) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (M : ℝ) (hM : 0 ≤ M)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ M) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ M)
    (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0 ≤ C ∧
      (∀ i,HasCompactSupport (windows i)) ∧
      (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
        (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨U,hUc,hUs,hUone,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := globalSecondLiteralTerm_twisted_profiles U hUc hUs
    g₁ g₂ W M hM (fun t ht => hUone t (hg₁ t ht)) (fun t ht => hUone t (hg₂ t ht)) hg₁ hg₂
  obtain ⟨C,hC,htrans⟩ := weightedGlobalPositiveBin_transfer ε hε A₁ A₂ W windows
    (fun _ => M+6+1) (fun _ => by linarith) hwb hwc (fun i => (hws i).continuous) A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have heq : globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
      (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j) =
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows ell (globalPooledRowScale K ell B F j) := by
    unfold globalSecondLiteralBinSource
    apply Finset.sum_congr rfl
    intro ray hray
    rw [sum_globalArithmeticBin p s side j]
    apply Finset.sum_congr rfl
    intro q hq
    unfold weightedGlobalArithmeticBinSource globalSecondRawSource
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxs,hxq,hxj⟩ := Finset.mem_filter.mp hx
    have h := hid p hp hcop hg hinj hpr pool Ψ m ray θ₁ θ₂ ell
      (globalPooledRowScale K ell B F j) side x hell (hs x hxs).2.1 (hk x hxs)
    dsimp only at h
    rw [hxj] at h
    rw [h,mul_assoc]
  rw [heq]
  simpa only [globalDescentWeight,norm_neg] using
    htrans p hp hcop hg hinj hc (-θ₁) θ₂ K ell B F s side j pool Ψ m γ Γ
      hK hell hB hF hΓ hγ hΨ hs hk

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

local notation "O" => ActualEisensteinCubic.O

lemma complex_norm_mul_add_sq (a b c d : ℂ) :
    ‖a*c+b*d‖^2≤(‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have ht : ‖a*c+b*d‖≤‖a‖*‖c‖+‖b‖*‖d‖ := by simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  have hs := pow_le_pow_left₀ (norm_nonneg (a*c+b*d)) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]

lemma matrixFrobenius_nonneg (g : SL(2,ℂ)) : 0≤ matrixFrobenius g := by
  unfold matrixFrobenius rowEnergy
  positivity

lemma matrixFrobenius_mul_le (g h : SL(2,ℂ)) :
    matrixFrobenius (g*h)≤ matrixFrobenius g*matrixFrobenius h := by
  have hb (i j : Fin 2) := complex_norm_mul_add_sq (g i 0) (g i 1) (h 0 j) (h 1 j)
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  nlinarith only [hb 0 0,hb 0 1,hb 1 0,hb 1 1]

lemma matrixFrobenius_inv (g : SL(2,ℂ)) : matrixFrobenius g⁻¹=matrixFrobenius g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow]
  change ‖g 1 1‖^2+‖-g 0 1‖^2+(‖-g 1 0‖^2+‖g 0 0‖^2)=_
  simp only [norm_neg]
  ring

lemma hyperbolicFrobenius_nonneg (w : HyperbolicSpace) : 0≤hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ g => exact matrixFrobenius_nonneg g

lemma matrixFrobenius_le_displacement (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    matrixFrobenius g≤hyperbolicFrobenius (g • w)*hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change matrixFrobenius g≤ matrixFrobenius (g*h)*matrixFrobenius h
    have hb := matrixFrobenius_mul_le (g*h) h⁻¹
    simpa only [mul_inv_cancel_right,matrixFrobenius_inv] using hb

instance integralSubgroupContinuousAction (H : Subgroup (SL(2,O))) :
    ContinuousConstSMul H HyperbolicSpace :=
  ⟨fun M => continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))⟩

instance integralSubgroupProperlyDiscontinuous (H : Subgroup (SL(2,O))) :
    ProperlyDiscontinuousSMul H HyperbolicSpace where
  finite_disjoint_inter_image := by
    intro source target hsource htarget
    obtain ⟨C,hC⟩ := hsource.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    obtain ⟨D,hD⟩ := htarget.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    have hfin : Set.Finite {M : H | matrixFrobenius (integralComplexMatrix (M:SL(2,O)))≤
        max D 0*max C 0} := by
      have hf := Set.Finite.preimage (f := fun M : H => (M:SL(2,O))) Subtype.val_injective.injOn
        (integral_frobenius_sublevel_finite 1 (max D 0*max C 0))
      simpa only [mul_one,Set.preimage_ofPred_eq] using hf
    apply hfin.subset
    rintro M ⟨u,⟨w,hw,rfl⟩,hu⟩
    have hb := matrixFrobenius_le_displacement (integralComplexMatrix (M:SL(2,O))) w
    apply hb.trans
    apply mul_le_mul
    · exact ((le_abs_self _).trans (hD _ hu)).trans (le_max_left _ _)
    · exact ((le_abs_self _).trans (hC _ hw)).trans (le_max_left _ _)
    · exact hyperbolicFrobenius_nonneg _
    · exact le_max_right _ _

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

namespace CubicEisenstein

section
local notation "O" => ActualEisensteinCubic.O

instance upperCoordinatesLocallyCompact : LocallyCompactSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).locallyCompactSpace
instance hyperbolicLocallyCompact : LocallyCompactSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
instance hyperbolicSecondCountable : SecondCountableTopology HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.secondCountableTopology

instance upperCoordinatesPolish : PolishSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).polishSpace
instance hyperbolicPolish : PolishSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isClosedEmbedding.polishSpace

lemma integralOrbitRel_eq (H : Subgroup (SL(2,O))) :
    integralOrbitRel H=MulAction.orbitRel H HyperbolicSpace := by
  ext u v
  change (∃M:H,M • u=v) ↔ ∃M:H,M • v=u
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩

instance integralOrbitQuotientT2 (H : Subgroup (SL(2,O))) : T2Space (IntegralOrbitQuotient H) := by
  change T2Space (Quotient (integralOrbitRel H))
  rw [integralOrbitRel_eq]
  infer_instance

lemma integralSubgroupFree (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCancelSMul H HyperbolicSpace :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (subgroup_action_free H hH)

lemma integralOrbitProjection_eq_iff (H : Subgroup (SL(2,O))) (u v : HyperbolicSpace) :
    integralOrbitProjection H u=integralOrbitProjection H v ↔ u∈MulAction.orbit H v := by
  constructor
  · intro he
    obtain ⟨M,hM⟩ := Quotient.exact he.symm
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨M,hM⟩

theorem integralOrbitProjection_quotientCovering (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) : IsQuotientCoveringMap (integralOrbitProjection H) H := by
  let : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  have hq : Topology.IsQuotientMap (integralOrbitProjection H) := isQuotientMap_quotient_mk'
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (integralOrbitProjection_eq_iff H _ _)

lemma integralOrbitProjection_covering (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCoveringMap (integralOrbitProjection H) :=
  (integralOrbitProjection_quotientCovering H hH).isCoveringMap

lemma integralOrbitProjection_openQuotient (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsOpenQuotientMap (integralOrbitProjection H) :=
  ⟨Quotient.mk_surjective,continuous_integralOrbitProjection H,
    (integralOrbitProjection_covering H hH).isOpenMap⟩

instance kernelQuotientLocallyCompact : LocallyCompactSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).locallyCompactSpace
instance kernelQuotientSecondCountable : SecondCountableTopology (IntegralOrbitQuotient globalKubotaKernel) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree)

instance kernelQuotientBorel : BorelSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  Quotient.borelSpace

lemma kernelQuotient_localHomeomorph : IsLocalHomeomorph (integralOrbitProjection globalKubotaKernel) :=
  (integralOrbitProjection_covering globalKubotaKernel globalKubotaKernel_le_levelThree).isLocalHomeomorph

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

lemma integralOrbitProjection_preimage_image (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (S : Set HyperbolicSpace) :
    integralOrbitProjection H ⁻¹' (integralOrbitProjection H '' S)=⋃M:H,M • S := by
  ext w
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff H w u).mp he.symm
    exact Set.mem_iUnion.mpr ⟨M,⟨u,hu,hM⟩⟩
  · intro hw
    obtain ⟨M,u,hu,rfl⟩ := Set.mem_iUnion.mp hw
    exact ⟨u,hu,(integralOrbitProjection_eq H M u).symm⟩

lemma kernelProjection_translates_disjoint (S : Set HyperbolicSpace)
    (hS : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    Pairwise (fun M N : globalKubotaKernel => Disjoint (M • S) (N • S)) := by
  let : IsCancelSMul globalKubotaKernel HyperbolicSpace :=
    integralSubgroupFree globalKubotaKernel globalKubotaKernel_le_levelThree
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w,hw,rfl⟩ ⟨u,hu,he⟩
  have hwu : w=u := hS hw hu (by
    calc
      integralOrbitProjection globalKubotaKernel w=
          integralOrbitProjection globalKubotaKernel (M • w) := (integralOrbitProjection_eq _ M w).symm
      _=integralOrbitProjection globalKubotaKernel (N • u) := congrArg _ he.symm
      _=integralOrbitProjection globalKubotaKernel u := integralOrbitProjection_eq _ N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)

theorem kernelProjection_measure_image (S : Set HyperbolicSpace) (hS : MeasurableSet S)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    integralQuotientVolume globalKubotaKernel (integralOrbitProjection globalKubotaKernel '' S)=
      hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn hinj
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image,Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (globalKubotaKernel_isFundamentalDomain.measure_eq_tsum S).symm
  · intro M N hMN
    exact (kernelProjection_translates_disjoint S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)

theorem kernelProjection_measurePreserving_on (U : Set HyperbolicSpace) (hU : MeasurableSet U)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) U) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict U)
      ((integralQuotientVolume globalKubotaKernel).restrict (integralOrbitProjection globalKubotaKernel '' U)) := by
  refine ⟨measurable_integralOrbitProjection _,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.restrict_apply hB]
  have hset : B∩(integralOrbitProjection globalKubotaKernel '' U)=
      integralOrbitProjection globalKubotaKernel '' (integralOrbitProjection globalKubotaKernel ⁻¹' B∩U) := by
    ext q
    constructor
    · rintro ⟨hq,w,hw,rfl⟩
      exact ⟨w,⟨hq,hw⟩,rfl⟩
    · rintro ⟨w,⟨hw,hu⟩,rfl⟩
      exact ⟨hw,⟨w,hu,rfl⟩⟩
  rw [hset,kernelProjection_measure_image _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]

theorem kernelL2_continuous_compact_approx (f : KernelQuotientL2) (ε : ℝ≥0∞) (hε : ε≠0) :
    ∃g : IntegralOrbitQuotient globalKubotaKernel → ℂ,
      HasCompactSupport g ∧ eLpNorm ((f : _ → ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)≤ε ∧
      Continuous g ∧ MemLp g 2 (integralQuotientVolume globalKubotaKernel) := by
  exact (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)

@[ext] structure GlobalFirstData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι

namespace GlobalFirstData
variable {ι : Type*}
def append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : GlobalSecondData ι :=
  ⟨b.cube,b.firstCommon,b.common,b.firstDivisor,x⟩
end GlobalFirstData

namespace GlobalSecondData
variable {ι : Type*}
def first (x : GlobalSecondData ι) : GlobalFirstData ι :=
  ⟨x.cube,x.firstCommon,x.common,x.firstDivisor⟩
@[simp] theorem append_first (x : GlobalSecondData ι) : x.first.append x.source=x := by cases x; rfl
@[simp] theorem first_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).first=b := rfl
@[simp] theorem source_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).source=x := rfl
end GlobalSecondData

section
variable {ι : Type*} [DecidableEq ι]

def globalFirstRawPool (pool : Finset ι) (b : GlobalFirstData ι) : Finset ι :=
  (pool\(b.cube.support∪b.common))\b.firstCommon

def globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : Finset (GlobalSecondData ι) :=
  s.biUnion (fun b => (secondExpansionPool (globalFirstRawPool pool b) (cutoff b)).image b.append)

theorem mem_globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (x : GlobalSecondData ι) :
    x∈globalFirstExpansionPool pool s cutoff ↔
      x.first∈s ∧ x.source∈secondExpansionPool (globalFirstRawPool pool x.first) (cutoff x.first) := by
  simp only [globalFirstExpansionPool,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,z,hz,rfl⟩
    exact ⟨hb,hz⟩
  · rintro ⟨hb,hx⟩
    exact ⟨x.first,hb,x.source,hx,x.append_first⟩

theorem sum_globalFirstExpansionPool {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (f : GlobalSecondData ι → M) :
    ∑ x∈globalFirstExpansionPool pool s cutoff,f x =
    ∑ b∈s,∑ x∈secondExpansionPool (globalFirstRawPool pool b) (cutoff b),f (b.append x) := by
  unfold globalFirstExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro x hx y hy heq
    exact congrArg GlobalSecondData.source heq
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalSecondData.first heq).symm

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstBlockColumnScale (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  ell/(primeProductNorm p (b.cube.sideDivisor side)*primeProductNorm p b.common)

def globalFirstBlockLabel (b : GlobalFirstData ι) : O :=
  secondBaseLabel p b.cube.support b.common b.cube.leftExponent b.cube.rightExponent b.cube.leftBit b.cube.rightBit

def globalFirstBlockBadLabel (b : GlobalFirstData ι) : O :=
  b0Label p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit

def globalFirstBlockTest (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : Finset ι → ℂ :=
  normalizedColumn p (fun A => g (columnLog p
    (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) A))

def globalFirstTruncatedSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondSource p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

theorem globalFirstTruncatedSource_eq_literal
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstExpansionPool pool s cutoff,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  unfold globalFirstTruncatedSource
  simp_rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  rw [Finset.sum_comm]
  simp_rw [sum_globalFirstExpansionPool]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold secondExpansionSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [globalSecondLiteralTerm,GlobalFirstData.append,GlobalSecondData.first,
    globalSecondRawPool,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    globalFirstBlockTest,globalFirstBlockColumnScale,globalFirstColumnScale,
    secondExpansionSource,Finset.sum_singleton,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstCoreRow (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayCharacter)
    (r : FirstCoreIndex) (t : ℝ) (b : GlobalFirstData ι) (z : O) : ℂ :=
  firstCoreInputRow p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t z

def globalFirstCoreCorrection (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) : ℝ :=
  ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b)) side t b.firstCommon ∅‖^2

def globalFirstSourceTail (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    secondSourceTail p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

def globalFirstSourceZero
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondZero p hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

theorem globalFirstTruncatedSource_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      globalFirstTruncatedSource p hp hg hinj pool s w (fun b G E => (cutoff b G E).erase 0) Ψ m g W ell side Y +
      globalFirstSourceZero p hg pool s w cutoff Ψ m g W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceZero
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncatedSecondSource_eq_nonzero_add_zero]
  exact mul_add _ _ _

theorem globalFirstCoreRows_smoothed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b) :
    (∑ b∈s,w b*∑' z : O,W (‖eisEmbedding z‖^2/Y b)*
      (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)) =
      globalFirstTruncatedSource p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y +
      globalFirstSourceTail p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hX : 0 < globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc
    (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m g V W (globalFirstBlockColumnScale p ell side b) hX (Y b) (hY b hb)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (cutoff b)
  dsimp only at he
  have he' := congrArg (fun z : ℂ => w b*z) he
  simpa only [globalFirstCoreRow,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    secondBaseLabel,globalFirstBlockTest,mul_add,mul_assoc,Complex.ofReal_inv] using he'

theorem globalFirstCoreRows_finite_le_sources
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b∈s,0 ≤ w b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b)
    (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (hT0 : ∀ b∈s,∀ z∈T b,z ≠ 0) :
    (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      ‖globalFirstTruncatedSource p hp hg hinj pool s (fun b => w b)
        (fun b G E => (cutoff b G E).erase 0) (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceZero p hg pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ := by
  have henergy : (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      (∑ b∈s,(w b : ℂ)*∑' z : O,rowMajorant (‖eisEmbedding z‖^2/Y b)*
        (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hh := firstCoreInputRow_finite_le_corrected_source p hg
      (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
      V (columnLog p (globalFirstBlockColumnScale p ell side b))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (T b) (Y b) (hY b hb) (hT b hb) (hT0 b hb)
    have hh' := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hh) (hw b hb)
    simpa only [globalFirstCoreRow,globalFirstCoreCorrection,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh'
  rw [globalFirstCoreRows_smoothed p hp hg hinj hc pool s (fun b => w b) cutoff Ψ m g V rowMajorant ell hell side χ r t Y hY,
    globalFirstTruncatedSource_split] at henergy
  exact henergy.trans ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)))

end SecondPassArithmetic

end

end OAI

end

