module

public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.CubeCuspAverage

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Eisenstein / Part016

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.InverseCorrespondence -/

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
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverFiber_memLp {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    MemLp (fun w=>f (integralCoverFiberPoint H K q w)) 2
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) := by
  have hD := hf.comp_measurePreserving (integralCoverDomain_projection_measurePreserving hHK hK)
  have hS := MemLp.mono_measure
    (Measure.restrict_mono_set hyperbolicVolume (Set.subset_iUnion (integralCoverSheet H K) q)) hD
  have hm := integralCoverSheet_measurePreserving H K q
  have hi := memLp_map_measure_iff (p:=2)
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  simpa only [Function.comp_def,integralCoverFiberPoint_rep_smul] using hS

theorem integralCoverTraceFunction_memLp {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) :
    MemLp (integralCoverTraceFunction H K f) 2 (integralQuotientVolume K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hm := quotient_projection_measurePreserving K
  have hi := memLp_map_measure_iff (p:=2)
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  change MemLp (fun w=>∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)) 2 _
  exact memLp_finsetSum Finset.univ (fun q _=>integralCoverFiber_memLp hHK hK f hmeas hf q)

lemma integralCoverMap_fiberPoint {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralCoverFiberPoint H K q w)=integralOrbitProjection K w := by
  rw [integralCoverFiberPoint_rep,integralCoverMap_projection,integralSubgroup_smul,
    integralOrbitProjection_eq]

lemma integralCoverTraceFunction_pairing {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (F : IntegralOrbitQuotient K→ℂ)
    (f : IntegralOrbitQuotient H→ℂ) (q : IntegralOrbitQuotient K) :
    integralCoverTraceFunction H K (fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)) q=
      inner ℂ (F q) (integralCoverTraceFunction H K f q) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,inner ℂ
      (F (integralCoverMap hHK (integralCoverFiberPoint H K r w)))
      (f (integralCoverFiberPoint H K r w)))=
      inner ℂ (F (integralOrbitProjection K w)) (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))
    simp only [integralCoverMap_fiberPoint,inner_sum]

theorem integralCoverTrace_toLp_ae {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) :
    integralCoverTrace hHK hK (hf.toLp f)=ᵐ[integralQuotientVolume K]
      integralCoverTraceFunction H K f := by
  let htr := integralCoverTraceFunction_memLp hHK hK f hmeas hf
  let Tf : IntegralQuotientL2 K := htr.toLp (integralCoverTraceFunction H K f)
  have he : Tf=integralCoverTrace hHK hK (hf.toLp f) := by
    apply ext_inner_left ℂ
    intro F
    let pair : IntegralOrbitQuotient H→ℂ := fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)
    have hpm : Measurable pair := by
      have hFm : Measurable (fun r=>F (integralCoverMap hHK r)) :=
        (Lp.stronglyMeasurable F).measurable.comp (integralCoverMap_measurable hHK)
      have hstar : Measurable (fun r=>star (F (integralCoverMap hHK r))) :=
        continuous_star.measurable.comp hFm
      have hm := hmeas.mul hstar
      change Measurable (fun r=>f r*star (F (integralCoverMap hHK r))) at hm
      simpa only [pair,RCLike.inner_apply,starRingEnd_apply] using hm
    have hae : (fun r=>inner ℂ (integralCoverPullback hHK hK F r) (hf.toLp f r))
        =ᵐ[integralQuotientVolume H]pair := by
      filter_upwards [integralCoverPullback_ae hHK hK F,hf.coeFn_toLp] with r hr hfR
      dsimp [pair]
      rw [hr,hfR]
    have hpi : Integrable pair (integralQuotientVolume H) :=
      (L2.integrable_inner (integralCoverPullback hHK hK F) (hf.toLp f)).congr hae
    calc
      inner ℂ F Tf = ∫q,inner ℂ (F q) (integralCoverTraceFunction H K f q)∂integralQuotientVolume K := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [htr.coeFn_toLp] with q hq
        change inner ℂ (F q) (htr.toLp (integralCoverTraceFunction H K f) q)=_
        rw [hq]
      _ = ∫q,integralCoverTraceFunction H K pair q∂integralQuotientVolume K := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun q=>(integralCoverTraceFunction_pairing hHK F f q).symm)
      _ = ∫r,pair r∂integralQuotientVolume H :=
        integralCoverTraceFunction_integral hHK hK pair hpm hpi
      _ = inner ℂ (integralCoverPullback hHK hK F) (hf.toLp f) :=
        (integral_congr_ae hae).symm
      _ = inner ℂ F (integralCoverTrace hHK hK (hf.toLp f)) :=
        (integralCoverTrace_pairing hHK hK F (hf.toLp f)).symm
  rw [←he]
  exact htr.coeFn_toLp

theorem integralCoverTrace_representative {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (G : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hrep : G=ᵐ[integralQuotientVolume H]f) :
    integralCoverTrace hHK hK G=ᵐ[integralQuotientVolume K]integralCoverTraceFunction H K f := by
  have hf : MemLp f 2 (integralQuotientVolume H) := (memLp_congr_ae hrep).mp (Lp.memLp G)
  have he : G=hf.toLp f := Lp.ext (hrep.trans hf.coeFn_toLp.symm)
  rw [he]
  exact integralCoverTrace_toLp_ae hHK hK f hmeas hf

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

theorem integralCoverTrace_cusp_representative {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (G : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hrep : G=ᵐ[integralQuotientVolume H]f) (C : ℝ)
    (hdec : ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (complexMatrix M•upperPoint z v hv))‖≤C/v^3) :
    ∃g : IntegralOrbitQuotient K→ℂ,Measurable g ∧
      integralCoverTrace hHK hK G=ᵐ[integralQuotientVolume K]g ∧
      ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
        ‖g (integralOrbitProjection K (complexMatrix M•upperPoint z v hv))‖≤
          (H.relIndex K:ℝ)*C/v^3 := by
  refine ⟨integralCoverTraceFunction H K f,
    integralCoverTraceFunction_measurable H K f hmeas,
    integralCoverTrace_representative hHK hK G f hmeas hrep,?_⟩
  exact integralCoverTraceFunction_cusp_decay H K hK f C hdec

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def primaryDenominatorShift (a:PrimaryLower) (m:Eis) : PrimaryCoprimeDenominator a≃PrimaryCoprimeDenominator a where
  toFun d:=⟨⟨d.val.val+3*a.val*m,by
    convert dvd_add d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val+3*a.val*m) d.val.val ⟨3*m,by ring⟩).mpr d.2⟩
  invFun d:=⟨⟨d.val.val-3*a.val*m,by
    convert dvd_sub d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val-3*a.val*m) d.val.val ⟨-(3*m),by ring⟩).mpr d.2⟩
  left_inv d:=by apply Subtype.ext;apply Subtype.ext;dsimp;ring
  right_inv d:=by apply Subtype.ext;apply Subtype.ext;dsimp;ring

def unitLowerDataShift (m:Eis) : UnitLowerData≃UnitLowerData :=
  Equiv.sigmaCongrRight (fun a=>primaryDenominatorShift a m)

lemma affineCusp_term_weighted_period (h q r:Eis) (j n:ℕ) (a d:PrimaryLower) (m:Eis)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a.val (d.val+3*a.val*(q*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m) v s a.val d.val*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m)) := by
  have hd:(3:Eis)∣d.val-a.val:=by simpa only [sub_sub_sub_cancel_right] using dvd_sub d.2 a.2
  obtain ⟨x,hx⟩:=hd
  have hdx:d.val=a.val+3*x:=by linear_combination hx
  have hb:(3:Eis)∣h+ramifiedAffineParameter j n*q*a.val:=by
    convert dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q)) using 1 ;ring
  obtain ⟨ell,hell⟩:=hb
  have he:=affineCusp_general_weighted_translate h q r a.val ell x (q*m) j n
    (primaryLower_primary a) hq hr hell.symm z v s
  have hqm:Ideal.Quotient.mk (Ideal.span {q}) (q*m)=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right q m))
  rw [hqm,AddChar.map_zero_eq_one,one_mul] at he
  have hshift:3*eisEmbedding (q*m)/eisEmbedding q=3*eisEmbedding m:=by
    rw [map_mul]
    field_simp [eisEmbedding_ne_zero hq]
  rw [hshift] at he
  rw [hdx,show a.val+3*x+3*a.val*(q*m)=a.val+3*(x+a.val*(q*m)) by ring]
  exact he

def affineCuspBlock (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) : ℂ :=
  ∑'p:UnitLowerData,affineLowerTerm q r z v s p.1.val p.2.val.val

lemma affineCuspBlock_weighted_periodic (h q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (v:ℝ) (s:ℂ) (m:Eis) (z:ℂ) :
    affineCuspBlock q r (z+3*eisEmbedding m) v s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
      affineCuspBlock q r z v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [affineCuspBlock,affineCuspBlock,←tsum_mul_right,←tsum_mul_right]
  calc
    _ = ∑'p:UnitLowerData,affineLowerTerm q r z v s
      ((unitLowerDataShift (q*m) p).1.val) ((unitLowerDataShift (q*m) p).2.val.val)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
      apply tsum_congr
      intro p
      exact (affineCusp_term_weighted_period h q r j n p.1 p.2.val m hq hr hbase z v s).symm
    _ = _ := (unitLowerDataShift (q*m)).tsum_eq
      (fun p:UnitLowerData=>affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))

lemma period_integral_twisted_translation (f:ℂ→ℂ) (freq:ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)*ShortDraftTrace.breveE (-freq*(z+3*eisEmbedding n))=
      f z*ShortDraftTrace.breveE (-freq*z)) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-freq*z))=
      ShortDraftTrace.breveE (freq*b)*∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-freq*z)
  have he (z:ℂ):f (z+b)*ShortDraftTrace.breveE (-freq*z)=ShortDraftTrace.breveE (freq*b)*g (b+z):=by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1;ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hp b]

lemma affineCuspBlock_integral_translation (h q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (v:ℝ) (s b:ℂ) :
    (∫z in periodDomain,affineCuspBlock q r (z+b) v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,affineCuspBlock q r z v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation (fun z=>affineCuspBlock q r z v s) (ninthCuspFrequency h)
    (affineCuspBlock_weighted_periodic h q r j n hq hr hbase v s) b

end
section

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma diagonal_unit_weighted_periodic (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  simpa only [diagonal_unit_eisenstein_rows,affineCuspBlock] using
    affineCuspBlock_weighted_periodic h (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
      (by simpa using hr) hbase v s m z

lemma diagonal_once_block_expansion (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s=
    ∑l:Fin 3,affineCuspBlock (onceCuspScale t*omega^l.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s := by
  have hsum:=(diagonalOnceCuspIndex u t).summable_iff.mpr
    (summable_summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s hs)
  have ht:Summable (fun p:OnceRamifiedData=>affineLowerTerm (onceCuspScale t*omega^p.1.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val):=
    hsum.congr (fun p=>diagonal_once_summand u t z v hv s p)
  rw [mul_assoc,diagonal_once_eisenstein_rows,ht.tsum_prod,tsum_fintype]
  rfl

lemma diagonal_once_weighted_periodic (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [diagonal_once_block_expansion u t _ v hv s hs,diagonal_once_block_expansion u t _ v hv s hs,
    Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  exact affineCuspBlock_weighted_periodic h (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (onceCuspRayIndex u t l).val 1
      (mul_ne_zero (onceCusp_scale_ne_zero t) (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero))
      (by simpa only [pow_one] using onceCuspRayIndex_spec u t l)
      (onceCusp_period_congruence t l h _ hfreq) v s m z

lemma diagonal_unit_fourier_shift (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s b:ℂ) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_unit_weighted_periodic u t j h hr hbase v hv s) b

lemma diagonal_once_fourier_shift (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s b:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_once_weighted_periodic u t h hfreq v hv s hs) b

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspRoot (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else ramifiedOmegaUnit

def ramifiedCuspScaleUnit (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else -ramifiedOmegaUnit

def ramifiedCuspDirectIndex (b:Bool) : ℕ := if b then 2 else 1

def ramifiedCuspOppositeIndex (b:Bool) : ℕ := if b then 1 else 2

lemma ramified_omega_four : omega^4=omega := by
  rw [show (4:ℕ)=3+1 from rfl,pow_add,omega_primitive.pow_eq_one,pow_one,one_mul]

lemma ramifiedCuspRoot_val (b:Bool) : (ramifiedCuspRoot b:Eis)=omega^(ramifiedCuspDirectIndex b) := by
  cases b <;>simp [ramifiedCuspRoot,ramifiedCuspDirectIndex,ramifiedOmegaUnit_val]

lemma ramifiedCuspRoot_cube (b:Bool) : (ramifiedCuspRoot b:Eis)^3=1 := by
  rw [ramifiedCuspRoot_val,←pow_mul,Nat.mul_comm,pow_mul,omega_primitive.pow_eq_one,one_pow]

lemma ramifiedCuspRoot_primitive (b:Bool) :
    (ramifiedCuspRoot b:Eis)^2+(ramifiedCuspRoot b:Eis)+1=0 := by
  cases b
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramified_omega_relation
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,←pow_mul]
    rw [show 2*2=4 from rfl,ramified_omega_four]
    linear_combination ramified_omega_relation

lemma ramifiedCuspScaleUnit_spec (b:Bool) :
    -(ramifiedCuspRoot b:Eis)*(1+2*(ramifiedCuspRoot b:Eis))=onceCuspScale (ramifiedCuspScaleUnit b) := by
  cases b
  · simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedTraceLambda,ramifiedOmegaUnit_val]
  · simp only [ramifiedCuspRoot,ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedTraceLambda]
    linear_combination -(2*omega^2)*ramified_omega_relation

lemma ramifiedCusp_neg_inv_square (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2=(ramifiedCuspRoot b:Eis) := by
  have hi:(↑(-(ramifiedCuspRoot b))⁻¹:Eis)=-(ramifiedCuspRoot b:Eis)^2:=by
    apply (-(ramifiedCuspRoot b)).inv_eq_of_mul_eq_one_right
    change -(ramifiedCuspRoot b:Eis)*(-(ramifiedCuspRoot b:Eis)^2)=1
    convert ramifiedCuspRoot_cube b using 1 ;ring
  rw [hi]
  linear_combination (ramifiedCuspRoot b:Eis)*ramifiedCuspRoot_cube b

lemma ramifiedCusp_opposite_character (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2*(-(ramifiedCuspRoot b:Eis))=
      -(omega^(ramifiedCuspOppositeIndex b)) := by
  rw [ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  cases b
  · simp [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,pow_two]
  · simp only [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,ite_true,pow_one]
    rw [mul_neg,←pow_add,show 2+2=4 from rfl,ramified_omega_four]

lemma ramifiedCusp_direct_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  cases b
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨ramifiedTraceLambda*omega^2,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_opposite_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  cases b
  · refine ⟨-(omega*ramifiedTraceLambda),?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_unit_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  cases b
  · refine ⟨-omega^2,?_⟩
    simp [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,onceCuspScale,Units.val_neg,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_one,one_mul,sub_zero,
      ramifiedTraceLambda]
    linear_combination ramified_omega_relation
  · refine ⟨-omega^2,?_⟩
    simp only [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_ofNat,Nat.cast_zero,sub_zero,
      ramifiedTraceLambda]
    linear_combination (2*omega+2)*ramified_omega_relation

lemma ramifiedCusp_support_standard (b:Bool) (h:Eis) :
    (3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b) ↔
      (3:Eis)∣h-(if b then -(omega-1) else omega-1) := by
  have hc:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)-(if b then -(omega-1) else omega-1):=by
    cases b
    · refine ⟨1,?_⟩
      simp [ramifiedCuspScaleUnit,onceCuspScale,Units.val_neg,ramifiedOmegaUnit_val,
        ramifiedTraceLambda]
      linear_combination -2*ramified_omega_relation
    · refine ⟨0,?_⟩
      simp only [ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
        ramifiedTraceLambda]
      linear_combination (2*omega-1)*ramified_omega_relation
  constructor
  · intro hh
    convert dvd_add hh hc using 1 ;ring
  · intro hh
    convert dvd_sub hh hc using 1 ;ring

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspGaussSeries (u t:Eisˣ) (h:Eis) (s:ℂ) : ℂ :=
  ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
    unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h))

lemma unitCusp_eisenstein_fourier_base (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspGaussSeries u t h s := by
  have hh:h=(t:Eis)*((↑t⁻¹:Eis)*h):=by simp [←mul_assoc]
  have hf:(3:Eis)∣(↑t⁻¹:Eis)*h+ramifiedAffineParameter j 0:=by
    have he:(↑t⁻¹:Eis)*(h+ramifiedAffineParameter j 0*(t:Eis))=
        (↑t⁻¹:Eis)*h+ramifiedAffineParameter j 0:=by
      rw [mul_add]
      congr 1
      calc
        _ = ((↑t⁻¹:Eis)*(t:Eis))*ramifiedAffineParameter j 0 := by ring
        _ = _ := by simp
    rw [←he]
    exact hbase.mul_left _
  rw [diagonal_unit_eisenstein_fourier u t j h ((↑t⁻¹:Eis)*h) hr hh hf v hv s hs,
    unitCuspGaussSeries]
  ring

lemma unitCuspDiagonal_one : unitCuspDiagonal (1:Eisˣ)=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;>fin_cases j <;>simp [unitCuspDiagonal]

lemma ramifiedCusp_direct_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  convert dvd_add hf (ramifiedCusp_direct_period_constant b) using 1 ;ring

lemma ramifiedCusp_opposite_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  convert dvd_add hf (ramifiedCusp_opposite_period_constant b) using 1 ;ring

lemma ramifiedCusp_unit_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  convert dvd_add hf (ramifiedCusp_unit_period_constant b) using 1 ;ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicKubota
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma cubeKernelLeftGlobal_injective (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Function.Injective (cubeKernelLeftGlobal p) := by
  intro x y hxy
  apply (cubeKernel_finite_covers p hp).1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

lemma cubeKernelRightGlobal_injective (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Function.Injective (cubeKernelRightGlobal p hp) := by
  intro x y hxy
  apply (cubeKernel_finite_covers p hp).2.1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

def cubeKernelRangeEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) :
    (cubeKernelLeftGlobal p).range≃*(cubeKernelRightGlobal p hp).range :=
  (MonoidHom.ofInjective (cubeKernelLeftGlobal_injective p hp)).symm.trans
    (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp))

def cubeCoverMatrix (p : ActualEisensteinCubic.O) (hp : p≠0) : SL(2,ℂ) :=
  (cubeArchimedean_correspondence p hp).choose

lemma cubeCoverMatrix_spec (p : ActualEisensteinCubic.O) (hp : p≠0) :
    cubeCoverMatrix p hp 0 1=0 ∧ cubeCoverMatrix p hp 1 0=0 ∧
    cubeCoverMatrix p hp 0 0/cubeCoverMatrix p hp 1 1=ConcreteTraceCRT.eisEmbedding p^3 ∧
    ∀x : cubeKernelCorrespondence p,
      cubeCoverMatrix p hp*integralComplexMatrix (cubeKernelLeftGlobal p x)=
        integralComplexMatrix (cubeKernelRightGlobal p hp x)*cubeCoverMatrix p hp :=
  (cubeArchimedean_correspondence p hp).choose_spec

lemma cubeCoverMatrix_intertwines (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralCoverIntertwines (cubeKernelRangeEquiv p hp) (cubeCoverMatrix p hp) := by
  intro h
  let x := (MonoidHom.ofInjective (cubeKernelLeftGlobal_injective p hp)).symm h
  have hl : cubeKernelLeftGlobal p x=(h : SL(2,ActualEisensteinCubic.O)) :=
    MonoidHom.apply_ofInjective_symm (cubeKernelLeftGlobal_injective p hp) h
  change cubeCoverMatrix p hp*integralComplexMatrix (h : SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (cubeKernelRightGlobal p hp x)*cubeCoverMatrix p hp
  rw [←hl]
  exact (cubeCoverMatrix_spec p hp).2.2.2 x

lemma cubeLeft_le_levelThree (p : ActualEisensteinCubic.O) :
    (cubeKernelLeftGlobal p).range≤levelThree :=
  (cubeKernelLeftGlobal_le p).trans globalKubotaKernel_le_levelThree

lemma cubeRight_le_levelThree (p : ActualEisensteinCubic.O) (hp : p≠0) :
    (cubeKernelRightGlobal p hp).range≤levelThree :=
  (cubeKernelRightGlobal_le p hp).trans globalKubotaKernel_le_levelThree

def cubeForwardL2Pullback (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralQuotientL2 (cubeKernelRightGlobal p hp).range→ₗᵢ[ℂ]
      IntegralQuotientL2 (cubeKernelLeftGlobal p).range :=
  integralConjugatePullback (cubeKernelRangeEquiv p hp) (cubeCoverMatrix p hp)
    (cubeCoverMatrix_intertwines p hp) (cubeLeft_le_levelThree p) (cubeRight_le_levelThree p hp)

def cubeInverseL2Pullback (p : ActualEisensteinCubic.O) (hp : p≠0) :
    IntegralQuotientL2 (cubeKernelLeftGlobal p).range→ₗᵢ[ℂ]
      IntegralQuotientL2 (cubeKernelRightGlobal p hp).range :=
  integralConjugatePullback (cubeKernelRangeEquiv p hp).symm (cubeCoverMatrix p hp)⁻¹
    (integralCoverIntertwines_inverse _ _ (cubeCoverMatrix_intertwines p hp))
    (cubeRight_le_levelThree p hp) (cubeLeft_le_levelThree p)

theorem cubeInverseL2Pullback_ae (p : ActualEisensteinCubic.O) (hp : p≠0)
    (F : IntegralQuotientL2 (cubeKernelLeftGlobal p).range) :
    cubeInverseL2Pullback p hp F=ᵐ[integralQuotientVolume (cubeKernelRightGlobal p hp).range]
      fun q=>F (integralConjugateMap (cubeKernelRangeEquiv p hp).symm (cubeCoverMatrix p hp)⁻¹
        (integralCoverIntertwines_inverse _ _ (cubeCoverMatrix_intertwines p hp)) q) :=
  integralConjugatePullback_ae _ _ _ _ _ F

def cubeInverseL2Correspondence (p : ActualEisensteinCubic.O) (hp : p≠0) : KernelQuotientL2→L[ℂ]KernelQuotientL2 := by
  letI := (cubeKernelGlobal_finite_covers p hp).1
  letI := (cubeKernelGlobal_finite_covers p hp).2
  letI : (cubeKernelLeftGlobal p).range.IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  letI : (cubeKernelRightGlobal p hp).range.IsFiniteRelIndex globalKubotaKernel :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  exact (integralCoverTrace (cubeKernelRightGlobal_le p hp) globalKubotaKernel_le_levelThree).comp
    ((cubeInverseL2Pullback p hp).toContinuousLinearMap.comp
      (integralCoverPullback (cubeKernelLeftGlobal_le p) globalKubotaKernel_le_levelThree))

end CubicKubota

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceTests -/

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

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeAverageMatrix_translate_lattice (p:Eis) (hp:p≠0) (q n:Eis) :
    cubeAverageMatrix p hp q*complexTranslation (3*eisEmbedding n)=cubeAverageMatrix p hp (q+n) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries, cubeAverageMatrix_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, map_add]
  ring

lemma cubeAverage_period_three (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (n:Eis) (w:HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation (3*eisEmbedding n) • w)=cubeAverage p hp F w := by
  let a:(Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}):=
    { toFun:=fun r=>r+Ideal.Quotient.mk _ n
      invFun:=fun r=>r-Ideal.Quotient.mk _ n
      left_inv:=fun r=>add_sub_cancel_right r _
      right_inv:=fun r=>sub_add_cancel r _ }
  let f (r:Eis⧸Ideal.span {p^3}):=
    F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
        (complexTranslation (3*eisEmbedding n) • w))=f (a r) := by
    rw [←mul_smul,cubeAverageMatrix_translate_lattice]
    apply cubeAverage_summand_congr p hp F hF
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_add,GaussianShiftedPartition.representative_spec,
      GaussianShiftedPartition.representative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r,f (a r):=tsum_congr hpoint
    _ = ∑' r,f r:=a.tsum_eq f

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSource_period_three (n:Eis) (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation (3*eisEmbedding n) • w)=
      cubicSourceResidualFunction w := by
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  simp only [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_period v hv z n

lemma cubicSource_period_one (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation 1 • w)=cubicSourceResidualFunction w := by
  have h:=cubicSourceResidualFunction_rational_invariant ModularGroup.T w
  change cubicSourceResidualFunction (rationalComplex ModularGroup.T • w)=_ at h
  rwa [rationalComplex_T_eq] at h

lemma cubicSource_period_finTwo (t:Fin 2) (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation (t.val:ℂ) • w)=cubicSourceResidualFunction w := by
  fin_cases t
  · have hz:complexTranslation 0=1:=by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [complexTranslation]
    simp only [Nat.cast_zero,hz,one_smul]
  · simpa using cubicSource_period_one w

lemma cubicSource_cube_period_finTwo (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1)
    (t:Fin 2) (w:HyperbolicSpace) :
    cubeAverage p hp cubicSourceResidualFunction (complexTranslation (t.val:ℂ) • w)=
      cubeAverage p hp cubicSourceResidualFunction w := by
  fin_cases t
  · have hz:complexTranslation 0=1:=by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [complexTranslation]
    simp only [Nat.cast_zero,hz,one_smul]
  · simpa using cubeAverage_period_one p hp hprimary cubicSourceResidualFunction
      cubicSource_period_three cubicSource_period_one w

theorem cubeSource_summand_average {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (cubeAverageMatrix p hp q •
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨d.matrix*M⁻¹,d.congruent⟩*sourceCuspConstant M*
        (v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  have hpoint (z:ℂ):cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)=
        integralComplexMatrix d.matrix •
          (cubeCuspTriangular d hp • upperPoint (3*(eisEmbedding (p^3)*z)) v hv):=by
    rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul]
  simp_rw [hpoint]
  rw [sourceCusp_average_complex_upper d.matrix (cubeCuspTriangular d hp)
    (cubeCuspTriangular_entries d hp).2.1 (p^3) (p^(2*d.exponent.val))
    (pow_ne_zero _ hp) (cubeCuspTriangular_integral_scale d hp) v hv,
    cubeCuspTriangular_height d hp v hv,sourceCuspConstant_congruent M d.matrix d.congruent]
  ring

theorem cubeSource_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hM:sourceCuspConstant M=0) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=0 := by
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous M (p^3) v hv]
  have hz (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=0:=by
    rw [cubeSource_summand_average
      (actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary)
      hp.ne_zero v hv,hM]
    ring
  simp_rw [hz]
  simp

theorem cubeSource_primary_upper_average (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous ((A:SL(2,Eis))*T) (p^3) v hv]
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average ((d r).right_upper T hT) hp.ne_zero v hv,
      CubeCuspData.right_upper_character,CubeCuspData.right_upper_exponent]
  simp_rw [hpoint]
  have hsum:(∑' r:Eis⧸Ideal.span {p^3},
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent)=
      (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
        actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p):=by
    unfold actualCubeCuspPhaseSum
    rw [←tsum_mul_left]
    apply tsum_congr
    intro r
    change _=(sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
      (cubeCuspHeightWeight p (d r).exponent*complexCharacter
        ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩)
    ring
  rw [hsum]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p))*
        (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)):=by ring
    _=_:=by rw [actualCubeCuspPhaseSum_normalized A p hp hprimary hA];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSource_levelTwo_upper_average (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨B,hB,t,ht⟩:=exists_primary_cusp_shift A
  have hm (w:HyperbolicSpace):integralComplexMatrix ((B:SL(2,Eis))*T) • w=
      complexTranslation (t.val:ℂ) • (integralComplexMatrix ((A:SL(2,Eis))*T) • w):=by
    simp only [map_mul,mul_smul]
    exact ht (integralComplexMatrix T • w)
  have hc:sourceCuspConstant ((B:SL(2,Eis))*T)=sourceCuspConstant ((A:SL(2,Eis))*T):=by
    unfold sourceCuspConstant
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hm,cubicSource_period_finTwo]
  calc
    _=∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
        (integralComplexMatrix ((B:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv):=by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hm,cubicSource_cube_period_finTwo p hp.ne_zero hprimary]
    _=_:=by rw [cubeSource_primary_upper_average B T hT p hp hprimary hB v hv,hc]

theorem cubeSource_average_all_cusps (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  by_cases hz:sourceCuspConstant M=0
  · rw [cubeSource_average_zero M p hp hprimary hz v hv,hz]
    ring
  · obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
    have hj:j=0:=by
      by_contra h
      exact hz ((sourceCuspConstant_zero_iff M G j T hT hM).mpr h)
    have he:M=(G:SL(2,Eis))*T:=by
      simpa [hj,cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using hM
    rw [he]
    exact cubeSource_levelTwo_upper_average G T hT p hp hprimary v hv

theorem cubeSource_difference_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,
      (cubeAverage p hp.ne_zero cubicSourceResidualFunction
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=0 := by
  let c:ℂ→UpperCoordinates:=fun z=>⟨(3*(eisEmbedding (p^3)*z),v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.mul continuous_id)).prodMk continuous_const
  have hcoord:= (continuous_translatedUpperCoordinates (integralComplexMatrix M)).comp hc
  have h0:Continuous (fun z=>cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)):=by
    simpa only [Function.comp_def,c] using cubicSourceResidualFunction_continuous.comp hcoord
  have h1:Continuous (fun z=>cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)):=by
    simpa only [Function.comp_def,c] using
      (cubeAverage_continuous p hp.ne_zero cubicSourceResidualFunction cubicSourceResidualFunction_continuous).comp hcoord
  have h2:Continuous (fun z:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)):=
    continuous_const.mul h0
  rw [integral_sub (periodDomain_integrable_of_continuous _ h1)
    (periodDomain_integrable_of_continuous _ h2),integral_const_mul,
    cubeSource_average_all_cusps M p hp hprimary v hv,
    sourceCusp_average_enlarged M (p^3) (pow_ne_zero 3 hp.ne_zero) v hv]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverFiberPoint_continuous (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) : Continuous (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (continuous_integralOrbitProjection H).comp
    (continuous_hyperbolic_action (integralComplexMatrix ((integralCoverRep H K q)⁻¹:SL(2,ActualEisensteinCubic.O))))

lemma integralCoverMap_fiber {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (w : HyperbolicSpace) :
    (integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w}=
      Set.range (fun q : IntegralCoverCosets H K=>integralCoverFiberPoint H K q w) := by
  ext u
  constructor
  · intro hu
    induction u using Quotient.inductionOn with
    | _ z =>
      have he : integralOrbitProjection K z=integralOrbitProjection K w := hu
      obtain ⟨k,hk⟩ := Quotient.exact he
      refine ⟨(k : IntegralCoverCosets H K),?_⟩
      change integralCoverFiberPoint H K (k : IntegralCoverCosets H K) w=integralOrbitProjection H z
      rw [integralCoverFiberPoint_mk]
      congr 1
      rw [←hk]
      exact inv_smul_smul k z
  · rintro ⟨q,rfl⟩
    exact integralCoverMap_fiberPoint hHK q w

lemma integralCoverMap_preimage_image {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (S : Set (IntegralOrbitQuotient H)) :
    (integralOrbitProjection K) ⁻¹' (integralCoverMap hHK '' S)=
      ⋃q : IntegralCoverCosets H K,(integralCoverFiberPoint H K q) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨u,hu,huw⟩
    have hh : u∈(integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w} := huw
    rw [integralCoverMap_fiber hHK w] at hh
    obtain ⟨q,rfl⟩ := hh
    exact Set.mem_iUnion.mpr ⟨q,hu⟩
  · intro hw
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hw
    exact ⟨integralCoverFiberPoint H K q w,hq,integralCoverMap_fiberPoint hHK q w⟩

theorem integralCoverMap_isClosedMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsClosedMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  intro S hS
  have hq : Topology.IsQuotientMap (integralOrbitProjection K) := isQuotientMap_quotient_mk'
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [integralCoverMap_preimage_image]
  exact isClosed_iUnion_of_finite (fun q=>hS.preimage (integralCoverFiberPoint_continuous H K q))

theorem integralCoverMap_isProperMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsProperMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨integralCoverMap_continuous hHK,integralCoverMap_isClosedMap hHK,?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change IsCompact ((integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w})
    rw [integralCoverMap_fiber hHK w]
    exact (Set.finite_range _).isCompact

theorem integralCoverMap_compact_preimage {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K]
    (S : Set (IntegralOrbitQuotient K)) (hS : IsCompact S) :
    IsCompact ((integralCoverMap hHK) ⁻¹' S) :=
  (integralCoverMap_isProperMap hHK).isCompact_preimage hS

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_norm_sq_pos {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) : 0<‖cubeCuspTriangular d hp 1 1‖^2 := by
  rw [cubeCuspTriangular_norm_sq]
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) _

def cubeReducedRemainder {M:SL(2,Eis)} {p q:Eis} (d:CubeCuspData M p q) (hp:p≠0)
    (z:ℂ) (v:ℝ) (hv:0<v) : ℂ :=
  sourceCuspRemainder d.matrix
    ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/‖cubeCuspTriangular d hp 1 1‖^2) (div_pos hv (cubeCuspTriangular_norm_sq_pos d hp))

lemma cubeSource_remainder_summand {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder d hp z v hv+
        sourceCuspLeadingCoefficient d.matrix*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
    complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  unfold cubeReducedRemainder sourceCuspRemainder
  rw [cubeCuspTriangular_height d hp v hv]
  ring

lemma cubeSource_leading_sum (M:SL(2,Eis)) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        sourceCuspLeadingCoefficient d.matrix*cubeCuspHeightWeight p d.exponent)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have h:=cubeSource_average_all_cusps M p hp hprimary 1 (by norm_num)
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous M (p^3) 1 (by norm_num)] at h
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) 1 (by norm_num))))=
      sourceCuspConstant (d r).matrix*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average (d r) hp.ne_zero 1 (by norm_num),
      ←sourceCuspConstant_congruent M (d r).matrix (d r).congruent]
    simp only [Complex.ofReal_one,Complex.one_cpow,mul_one]
  rw [tsum_congr hpoint] at h
  simp only [Complex.ofReal_one,Complex.one_cpow,mul_one] at h
  change (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3}, sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)=_
  unfold sourceCuspLeadingCoefficient
  simp_rw [div_mul_eq_mul_div]
  rw [tsum_div_const]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},sourceCuspConstant (d r).matrix*cubeCuspHeightWeight p (d r).exponent)) /
        ((9*Real.sqrt 3/2:ℝ):ℂ):=by ring
    _=_:=by rw [h];ring

theorem cubeSource_difference_eq_remainders (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        cubeReducedRemainder d hp.ne_zero z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      cubicSourceResidualFunction (cubeAverageMatrix p hp.ne_zero
        (GaussianShiftedPartition.representative (p^3) r) • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder (d r) hp.ne_zero z v hv+(v:ℂ)^(2/3:ℂ)*
        (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent):=by
    rw [cubeSource_remainder_summand (d r) hp.ne_zero z v hv]
    ring
  have hu:cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
        (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M*(v:ℂ)^(2/3:ℂ):=by
    unfold cubeAverage
    have hs1:Summable (fun r:Eis⧸Ideal.span {p^3}=>cubeReducedRemainder (d r) hp.ne_zero z v hv):=Summable.of_finite
    have hs2:Summable (fun r:Eis⧸Ideal.span {p^3}=>(v:ℂ)^(2/3:ℂ)*
      (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=Summable.of_finite
    rw [tsum_congr hpoint,hs1.tsum_add hs2,tsum_mul_left]
    calc
      _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
        (v:ℂ)^(2/3:ℂ)*((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=by ring
      _=_:=by rw [cubeSource_leading_sum M p hp hprimary];ring
  rw [hu]
  unfold sourceCuspRemainder
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubePrime_norm_ge_one (p:Eis) (hp:p≠0) : 1≤‖eisEmbedding p‖ := by
  have hn:1≤‖eisEmbedding p‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    have hq:Ideal.absNorm (Ideal.span {p})≠0:=
      (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  nlinarith [norm_nonneg (eisEmbedding p)]

lemma cubeReducedRemainder_bound {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp
  have hd:D≤‖eisEmbedding p‖^3:=by
    rw [show D=‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)) from cubeCuspTriangular_norm_sq d hp]
    rw [←Real.rpow_natCast ‖eisEmbedding p‖ 3]
    apply Real.rpow_le_rpow_of_exponent_le hr1
    norm_num only [Nat.cast_ofNat]
    have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
    linarith
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_nonneg hr.le 3))
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hb:=sourceCuspRemainder_bound_all K (‖eisEmbedding p‖^3)⁻¹ hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) ha
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

lemma cube_normalized_sum_bound (p:Eis) (hp:p≠0)
    (f:(Eis⧸Ideal.span {p^3})→ℂ) (B:ℝ) (_hB:0≤B) (hf:∀r,‖f r‖≤B) :
    ‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r,f r)‖≤B := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℝ)≠0:=by exact_mod_cast hqN
  have hs:‖∑' r,f r‖≤(Ideal.absNorm (Ideal.span {p}):ℝ)^3*B:=by
    calc
      _≤∑' r,‖f r‖:=norm_tsum_le_tsum_norm (Summable.of_finite)
      _≤∑' (_:Eis⧸Ideal.span {p^3}),B:=(Summable.of_finite).tsum_le_tsum hf Summable.of_finite
      _=_:=by
        rw [tsum_const,nsmul_eq_mul]
        change (Ideal.absNorm (Ideal.span {p^3}):ℝ)*B=_
        rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rw [norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
  calc
    _≤(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹^3*((Ideal.absNorm (Ideal.span {p}):ℝ)^3*B):=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3)
    _=B:=by field_simp

theorem cubeSource_difference_decay_from_representatives (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)‖≤
    (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v:=by
    calc
      _≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
      _≤v:=hv1
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv ha
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound (d r) hp.ne_zero K hK hrep z v hv hv1)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverMap_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient K→ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun q=>f (integralCoverMap hHK q)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (integralCoverMap_compact_preimage hHK (tsupport f) hf.isCompact)
  intro q hq
  exact subset_tsupport f hq

lemma integralCoverTraceFunction_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply HasCompactSupport.of_support_subset_isCompact
    (hf.isCompact.image (integralCoverMap_continuous hHK))
  intro q hq
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))≠0 at hq
    obtain ⟨r,_,hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact ⟨integralCoverFiberPoint H K r w,subset_tsupport f hr,
      integralCoverMap_fiberPoint hHK r w⟩

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceFunction (f : KernelQuotient→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction H globalKubotaKernel
    (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)))

omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_lift (f : KernelQuotient→ℂ) (w : HyperbolicSpace) :
    kernelCorrespondenceFunction hJK e g he f (integralOrbitProjection globalKubotaKernel w)=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        f (integralOrbitProjection globalKubotaKernel
          ((g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:
              globalKubotaKernel):SL(2,ActualEisensteinCubic.O)))•w)) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change (∑q : IntegralCoverCosets H globalKubotaKernel,
    f (integralCoverMap hJK (integralConjugateMap e g he
      (integralCoverFiberPoint H globalKubotaKernel q w))))=_
  apply Finset.sum_congr rfl
  intro q _
  rw [integralCoverFiberPoint_rep,integralSubgroup_smul,
    integralConjugateMap_projection,integralCoverMap_projection,mul_smul]

include hHK in
lemma kernelCorrespondenceFunction_hasCompactSupport (f : KernelQuotient→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (kernelCorrespondenceFunction hJK e g he f) := by
  apply integralCoverTraceFunction_hasCompactSupport hHK
  exact (integralCoverMap_hasCompactSupport hJK f hf).comp_homeomorph
    (integralConjugateHomeomorph e g he)

omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_contMDiff (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelCorrespondenceFunction hJK e g he f) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  apply kernel_contMDiff_of_lift
  simp_rw [kernelCorrespondenceFunction_lift]
  apply ContMDiff.sum
  intro q _
  exact (hf.comp kernelProjection_contMDiff).comp
    (hyperbolicAction_contMDiff (g*integralComplexMatrix
      (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))))

def kernelCorrespondenceTest (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨kernelCorrespondenceFunction hJK e g he f.1,
    kernelCorrespondenceFunction_contMDiff hJK e g he f.1 f.2.1,
    kernelCorrespondenceFunction_hasCompactSupport hHK hJK e g he f.1 f.2.2⟩

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CorrespondencePullback -/

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
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma integralCoverMap_quasiMeasurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Measure.QuasiMeasurePreserving (integralCoverMap hHK)
      (integralQuotientVolume H) (integralQuotientVolume K) := by
  refine ⟨integralCoverMap_measurable hHK,?_⟩
  rw [integralCoverMap_measure hHK hK]
  exact Measure.smul_absolutelyContinuous

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceL2 : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (integralCoverTrace hHK globalKubotaKernel_le_levelThree).comp
    ((integralConjugatePullback e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree))

lemma kernelCorrespondenceL2_representative (F : KernelQuotientL2)
    (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCorrespondenceL2 hHK hJK e g he F=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCorrespondenceFunction hJK e g he f := by
  have hcover := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK
      globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  have hconj := (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hcover)
  exact integralCoverTrace_representative hHK globalKubotaKernel_le_levelThree _ _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

lemma kernelCorrespondenceTest_mass (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelCorrespondenceTest hHK hJK e g he f)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  exact (kernelSmoothTests_memLp (kernelCorrespondenceTest hHK hJK e g he f)).coeFn_toLp.trans
    (kernelCorrespondenceL2_representative hHK hJK e g he _ f.1
      f.2.1.continuous.measurable (kernelSmoothTests_memLp f).coeFn_toLp).symm

include hHK in
lemma kernelCorrespondenceFunction_integrable (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    Integrable (kernelCorrespondenceFunction hJK e g he f)
      (integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK
    globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  exact integralCoverTraceFunction_integrable hHK globalKubotaKernel_le_levelThree _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

include hHK in
lemma kernelCorrespondenceFunction_integral (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    (∫q,kernelCorrespondenceFunction hJK e g he f q∂integralQuotientVolume globalKubotaKernel)=
      (J.relIndex globalKubotaKernel:ℂ)*(∫q,f q∂integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK
    globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)
  change Integrable (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q))) _ at hconj
  calc
    _ = ∫q,f (integralCoverMap hJK (integralConjugateMap e g he q))∂integralQuotientVolume H :=
      integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
        ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj
    _ = ∫q,f (integralCoverMap hJK q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (hf.comp (integralCoverMap_measurable hJK)).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = ∫q,f q∂Measure.map (integralCoverMap hJK) (integralQuotientVolume J) :=
      (integral_map (integralCoverMap_measurable hJK).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [integralCoverMap_measure hJK globalKubotaKernel_le_levelThree,
        integral_smul_measure]
      simp only [ENNReal.toReal_natCast,Complex.real_smul,Complex.ofReal_natCast]

end

def coverEnergyDensity (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℝ :=
  euclideanScalarDirichletDensity (fun x=>(F x).re) p+
    euclideanScalarDirichletDensity (fun x=>(F x).im) p

def coverGradientAt (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j=>(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))

lemma coverEnergyDensity_nonneg (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    0≤ coverEnergyDensity F p := by
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  positivity

lemma coverGradientAt_norm_sq (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    ‖coverGradientAt F p‖^2=coverEnergyDensity F p := by
  have hr := (Complex.reCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun x=>(F x).re) p=_ at hr
  change fderiv ℝ (fun x=>(F x).im) p=_ at hi
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑j:Fin 3,‖(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ‖fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2=
    (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).re^2+
      (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).im^2
  simpa only [Complex.normSq_apply,pow_two] using
    (Complex.normSq_eq_norm_sq (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))).symm

lemma coverEnergyDensity_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    coverEnergyDensity (F ∘ euclideanAction g) p=coverEnergyDensity F (euclideanAction g p) := by
  have hr := hyperbolic_cotangent_energy_comp g (fun p=>(F p).re) p hp
    (Complex.reCLM.differentiableAt.comp _ hF)
  have hi := hyperbolic_cotangent_energy_comp g (fun p=>(F p).im) p hp
    (Complex.imCLM.differentiableAt.comp _ hF)
  exact congrArg₂ (fun x y : ℝ=>x+y) hr hi

lemma coverGradientAt_sum {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverGradientAt (fun x=>∑i∈s,F i x) p=∑i∈s,coverGradientAt (F i) p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_fun_sum hF,_root_.sum_apply,
    WithLp.equiv_apply,Finset.mul_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma norm_sum_sq_le_card {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι→E) :
    ‖∑i∈s,f i‖^2≤(s.card:ℝ)*∑i∈s,‖f i‖^2 := by
  calc
    _ ≤ (∑i∈s,‖f i‖)^2 := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
      (norm_sum_le _ _)
    _ ≤ _ := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq s (fun _=> (1:ℝ)) (fun i=>‖f i‖))

lemma coverEnergyDensity_sum_le {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverEnergyDensity (fun x=>∑i∈s,F i x) p≤(s.card:ℝ)*∑i∈s,coverEnergyDensity (F i) p := by
  rw [←coverGradientAt_norm_sq _ _ (DifferentiableAt.fun_sum hF),coverGradientAt_sum s F p hF]
  have hh := norm_sum_sq_le_card s (fun i=>coverGradientAt (F i) p)
  calc
    _ ≤ _ := hh
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact coverGradientAt_norm_sq (F i) p (hF i hi)

lemma kernelTestEnergyDensity_eq_cover (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=coverEnergyDensity (kernelTestField f) (hyperbolicEuclideanCoordinates w) := rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_unipotent_upper (n:ℕ) :
    rationalEmbedding (ModularGroup.T^n)=unitCuspUpper (n:Eis) := by
  rw [←rationalUnipotent_nat]
  apply Subtype.ext
  change ( !![(1 : ℤ), (n : ℤ); 0, 1]).map (Int.castRingHom Eis) =
    !![1, (n : Eis); 0, 1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

lemma rational_cusp_lower_section (u:Eisˣ) (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
      integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv=
      integralComplexMatrix (unitCuspDiagonal (-u))*
        integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis))))*
          upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv := by
  have hm:=congrArg integralComplexMatrix (rational_cusp_lower_factor u (n:ℤ))
  simp only [map_mul,Int.cast_natCast] at hm
  have hu:integralComplexMatrix (unitCuspUpper (n:Eis))=rationalComplex (ModularGroup.T^n):=by
    rw [←rational_unipotent_upper]
    rfl
  rw [hu] at hm
  change rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
    integralComplexMatrix (lowerCuspMatrix (u:Eis))=_ at hm
  rw [hm,mul_assoc,unitCuspUpper_section]

lemma hyperbolicEisenstein_fixed_upper (g:SL(2,ℂ)) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    hyperbolicEisenstein s (g • upperPoint z v hv)=eisenstein (g*upperSection z v hv) s:=rfl

theorem sourceEisenstein_unit_lower (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        ∑n:Fin 3,eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n.val:Eis)*(u:Eis))))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_four_cusps]
  simp only [←mul_smul,hyperbolicEisenstein_fixed_upper]
  apply congrArg (fun c:ℂ=>(4:ℂ)⁻¹*(eisenstein
    (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+c))
  apply Finset.sum_congr rfl
  intro n hn
  rw [←mul_assoc,rational_cusp_lower_section]

theorem sourceEisenstein_primitive_lower_four (u t:Eisˣ)
    (hu:(u:Eis)^2+(u:Eis)+1=0)
    (ht:-(u:Eis)*(1+2*(u:Eis))=onceCuspScale t)
    (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)))*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_unit_lower,Fin.sum_univ_three]
  have h1:-(u:Eis)*(1+1*(u:Eis))=1:=by linear_combination -hu
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
    zero_mul,add_zero,mul_one,h1,ht]
  ring

lemma continuous_fixed_left_Eisenstein (g:SL(2,ℂ)) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (b:ℂ) :
    Continuous (fun z:ℂ=>eisenstein (g*upperSection (z+b) v hv) s) := by
  have hc:Continuous (fun z:ℂ=>(⟨(z+b,v),hv⟩:UpperCoordinates)):=by fun_prop
  have he : Continuous (fun z:ℂ=>hyperbolicEisenstein s (g • upperPoint (z+b) v hv)) := by
    simpa only [Function.comp_def] using
      ((hyperbolicEisenstein_continuous s hs).comp (continuous_translatedUpperCoordinates g)).comp hc
  simpa only [hyperbolicEisenstein_fixed_upper] using he

lemma integrable_fixed_left_Eisenstein_fourier (g:SL(2,ℂ)) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (b freq:ℂ) :
    IntegrableOn (fun z:ℂ=>eisenstein (g*upperSection (z+b) v hv) s*ShortDraftTrace.breveE (-freq*z)) periodDomain := by
  apply periodDomain_integrable_of_continuous
  apply (continuous_fixed_left_Eisenstein g v hv s hs b).mul
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
  fun_prop

end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspGaussSeries (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (s:ℂ) : ℂ :=
  (4:ℂ)⁻¹*(unitCuspGaussSeries 1 (ramifiedCuspRoot b) h s+
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑(ramifiedCuspRoot b)⁻¹:Eis))*
      (unitCuspGaussSeries (-(ramifiedCuspRoot b)) (-(ramifiedCuspRoot b)) h s+
        unitCuspGaussSeries (-(ramifiedCuspRoot b)) 1 h s+
          onceCuspGaussSeries (-(ramifiedCuspRoot b)) (ramifiedCuspScaleUnit b) h hf s))

theorem ramifiedSourceEisenstein_fourier (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot b:Eis)) • upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*ramifiedCuspGaussSeries b h hf s := by
  let t:=ramifiedCuspRoot b
  let shift:=eisEmbedding (↑t⁻¹:Eis)
  let arch:=(v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v)
  let f0:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
    ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f1:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (-(t:Eis)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f2:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f3:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (onceCuspScale (ramifiedCuspScaleUnit b)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  have hi0:IntegrableOn f0 periodDomain:=by
    simpa only [f0,add_zero] using integrable_fixed_left_Eisenstein_fourier
      (integralComplexMatrix (lowerCuspMatrix (t:Eis))) v hv s hs 0 (ninthCuspFrequency h)
  have hi1:IntegrableOn f1 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi2:IntegrableOn f2 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi3:IntegrableOn f3 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have heq:(∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)) • upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (4:ℂ)⁻¹*((∫z in periodDomain,f0 z)+(∫z in periodDomain,f1 z)+
        (∫z in periodDomain,f2 z)+(∫z in periodDomain,f3 z)):=by
    calc
      _ = ∫z in periodDomain,(4:ℂ)⁻¹*(f0 z+f1 z+f2 z+f3 z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z=>by
          dsimp only
          rw [sourceEisenstein_primitive_lower_four t (ramifiedCuspScaleUnit b)
            (ramifiedCuspRoot_primitive b) (ramifiedCuspScaleUnit_spec b)]
          dsimp only [f0,f1,f2,f3,shift]
          ring)
      _ = _ := by
        rw [integral_const_mul]
        rw [integral_add (f:=fun z=>f0 z+f1 z+f2 z) (g:=f3) ((hi0.add hi1).add hi2) hi3,
          integral_add (f:=fun z=>f0 z+f1 z) (g:=f2) (hi0.add hi1) hi2,
          integral_add (f:=f0) (g:=f1) hi0 hi1]
  have hr0:(↑(1:Eisˣ)⁻¹:Eis)^2*(t:Eis)=omega^(ramifiedCuspDirectIndex b):=by
    simpa [t] using ramifiedCuspRoot_val b
  have hr1:(↑(-t)⁻¹:Eis)^2*((-t:Eisˣ):Eis)=-(omega^(ramifiedCuspOppositeIndex b)):=
    ramifiedCusp_opposite_character b
  have hr2:(↑(-t)⁻¹:Eis)^2*((1:Eisˣ):Eis)=omega^(ramifiedCuspDirectIndex b):=by
    rw [Units.val_one,mul_one,ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  have hb2:(3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*((1:Eisˣ):Eis):=by
    simpa using ramifiedCusp_unit_base b h hf
  have h0:(∫z in periodDomain,f0 z)=arch*unitCuspGaussSeries 1 t h s:=by
    simpa only [unitCuspDiagonal_one,map_one,one_mul,f0,arch] using
      unitCusp_eisenstein_fourier_base 1 t (ramifiedCuspDirectIndex b) h (Or.inl hr0)
        (ramifiedCusp_direct_base b h hf) v hv s hs
  have h1:(∫z in periodDomain,f1 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) (-t) h s):=by
    have he:=diagonal_unit_fourier_shift (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
      (ramifiedCusp_opposite_base b h hf) v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
        (ramifiedCusp_opposite_base b h hf) v hv s hs] at he
    simpa only [f1,Units.val_neg,arch] using he
  have h2:(∫z in periodDomain,f2 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) 1 h s):=by
    have he:=diagonal_unit_fourier_shift (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
      hb2 v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
        hb2 v hv s hs] at he
    simpa only [f2,Units.val_one,arch] using he
  have h3:(∫z in periodDomain,f3 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*onceCuspGaussSeries (-t) (ramifiedCuspScaleUnit b) h hf s):=by
    dsimp only [f3]
    rw [diagonal_once_fourier_shift (-t) (ramifiedCuspScaleUnit b) h hf v hv s shift hs,
      onceCusp_eisenstein_fourier (-t) (ramifiedCuspScaleUnit b) h hf v hv s hs]
  rw [heq,h0,h1,h2,h3]
  dsimp only [ramifiedCuspGaussSeries,arch,shift,t]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "Eis" => ActualEisensteinCubic.O

theorem finite_unramified_residue {ι:Type*} [Fintype ι] [DecidableEq ι]
    (index:ι→Eis) (coefficient:ι→ℂ→ℂ)
    (hc:∀i s,1<s.re→AnalyticAt ℂ (coefficient i) s)
    (f:ℂ→ℂ) (R:ℂ)
    (hf:∀s,1<s.re→0<s.im→AnalyticAt ℂ f s)
    (hlim:Tendsto (fun s:ℂ=>(s-4/3)*f s) (𝓝[≠] (4/3:ℂ)) (𝓝 R))
    (hinit:∀s:ℂ,4<s.re→0<s.im→
      f s=∑i,coefficient i s*unramifiedCubicGaussSeries s (index i)) :
    R=∑i,coefficient i (4/3)*unramifiedGaussResidue (index i) := by
  let H:ι→ℂ→ℂ:=fun i s=>cuspWhittakerHeightFactor s (3*index i)
  let G:ι→ℂ→ℂ:=fun i s=>translatedCuspFamily (3*index i) oppositeSource 2 3
    (by norm_num) (by norm_num) s
  let D:ℂ→ℂ:=fun s=>∏i,H i s
  let E:ι→ℂ→ℂ:=fun i s=>∏j∈Finset.univ.erase i,H j s
  have hH:∀i s,1<s.re→AnalyticAt ℂ (H i) s:=fun i s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*index i) s hs
  have hD:∀s,1<s.re→AnalyticAt ℂ D s:=fun s hs=>
    Finset.analyticAt_fun_prod _ (fun i hi=>hH i s hs)
  have hE:∀i s,1<s.re→AnalyticAt ℂ (E i) s:=fun i s hs=>
    Finset.analyticAt_fun_prod _ (fun j hj=>hH j s hs)
  have hprod (i:ι) (s:ℂ):H i s*E i s=D s:=by
    exact Finset.mul_prod_erase Finset.univ (fun j=>H j s) (Finset.mem_univ i)
  let domain:Set ℂ:={s|1<s.re∧0<s.im}
  have hconvex:Convex ℝ domain:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have ha:AnalyticOnNhd ℂ (fun s=>f s*D s) domain:=fun s hs=>(hf s hs.1 hs.2).mul (hD s hs.1)
  have hb:AnalyticOnNhd ℂ (fun s=>∑i,coefficient i s*G i s*E i s) domain:=by
    intro s hs
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact ((hc i s hs.1).mul (translatedCuspFamily_analyticAt_nonreal (3*index i)
      oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')).mul (hE i s hs.1)
  have hopen:IsOpen {s:ℂ|4<s.re∧0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:(fun s=>f s*D s)=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>∑i,coefficient i s*G i s*E i s):=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [hinit s hs.1 hs.2,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    rw [translatedCuspFamily_opposite_initial (index i) s hs.1 hs.2]
    change coefficient i s*unramifiedCubicGaussSeries s (index i)*D s=
      coefficient i s*(unramifiedCubicGaussSeries s (index i)*H i s)*E i s
    rw [←hprod i s]
    ring
  have heq:=ha.eqOn_of_preconnected_of_eventuallyEq hb hconvex.isPreconnected
    (show (5+Complex.I:ℂ)∈domain by norm_num [domain]) hev
  have hDc:Tendsto D (𝓝[≠] (4/3:ℂ)) (𝓝 (D (4/3))):=
    (hD (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl:=(hlim.mul hDc).comp upperVertical_tendsto_cubic_punctured
  have hg:∀i,Tendsto (fun s:ℂ=>coefficient i s*((s-4/3)*G i s)*E i s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
        cubicEisensteinResidue*E i (4/3))):=by
    intro i
    exact (((hc i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (translatedCuspFamily_residue_limit (3*index i) oppositeSource 2 3
        (by norm_num) (by norm_num))).mul
          ((hE i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hr:=(tendsto_finsetSum Finset.univ (fun i hi=>hg i)).comp upperVertical_tendsto_cubic_punctured
  have hel:(fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*f ((4/3:ℂ)+(t:ℂ)*Complex.I))*
      D ((4/3:ℂ)+(t:ℂ)*Complex.I))=ᶠ[𝓝[>] (0:ℝ)]
      (fun t:ℝ=>∑i,coefficient i ((4/3:ℂ)+(t:ℂ)*Complex.I)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*G i ((4/3:ℂ)+(t:ℂ)*Complex.I))*
          E i ((4/3:ℂ)+(t:ℂ)*Complex.I)):=by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0:0<t:=ht
    have he:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
      constructor
      · norm_num
      · simpa using ht0)
    dsimp only at he
    rw [mul_assoc,he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hres:=tendsto_nhds_unique_of_eventuallyEq hl hr hel
  have hDn:D (4/3)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>
    cuspWhittakerHeightFactor_center_ne_zero (3*index i))
  apply mul_right_cancel₀ hDn
  rw [Finset.sum_mul]
  refine hres.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  change coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
    cubicEisensteinResidue*E i (4/3)=coefficient i (4/3)*
      (translatedCuspFourier (3*index i) oppositeSource cubicEisensteinResidue/H i (4/3))*D (4/3)
  rw [←hprod i (4/3)]
  field_simp [show H i (4/3)≠0 from cuspWhittakerHeightFactor_center_ne_zero (3*index i)]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota

lemma cuspStrip_integrable_continuous (a b:ℝ) (ha:0<a)
    (f:HyperbolicSpace→ℂ) (hf:Continuous f) :
    IntegrableOn f (cuspPeriodStrip a b) hyperbolicVolume :=
  (hf.continuousOn.integrableOn_compact (cuspHeightCompact_isCompact a b ha)).mono_set
    (cuspPeriodStrip_subset_heightCompact a b ha)

def sourceArbitraryHeightFamily (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ :=
  (24:ℂ)⁻¹*∑i:RationalBruhatIndex,arbitraryCuspHeightFamily
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq s

def sourceArbitraryHeightFourier (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (24:ℂ)⁻¹ • ∑i:RationalBruhatIndex,arbitraryCuspHeightFourier
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq

lemma sourceArbitraryHeightFamily_analyticAt (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:1<s.re) (hi:0<s.im) :
    AnalyticAt ℂ (sourceArbitraryHeightFamily M a b ha ρ freq) s := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro i hi'
  exact arbitraryCuspHeightFamily_analyticAt _ a b ha ρ freq s hs.ne' hi.ne'

lemma sourceArbitraryHeightFamily_residue_limit (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    Tendsto (fun s:ℂ=>(s-4/3)*sourceArbitraryHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (sourceArbitraryHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have he:=(tendsto_finsetSum Finset.univ (fun i hi=>
    arbitraryCuspHeightFamily_residue_limit (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq)).const_mul ((24:ℂ)⁻¹)
  convert he using 1
  · funext s
    rw [sourceArbitraryHeightFamily,←Finset.mul_sum]
    ring
  · simp only [sourceArbitraryHeightFourier,_root_.smul_apply,
      _root_.sum_apply,smul_eq_mul]

lemma sourceProjection_integral (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    (∫w in cuspPeriodStrip a b,sourceProjection f (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      (24:ℂ)⁻¹*∑i:RationalBruhatIndex,∫w in cuspPeriodStrip a b,
        f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  have hi (i:RationalBruhatIndex) : IntegrableOn
      (fun w=>f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w)
      (cuspPeriodStrip a b) hyperbolicVolume :=
    cuspStrip_integrable_continuous a b ha _ ((hf.comp (continuous_hyperbolic_action _)).mul
      (arbitraryCuspWeightedPhase_continuous ρ freq))
  calc
    _ = ∫w in cuspPeriodStrip a b,(24:ℂ)⁻¹*∑i:RationalBruhatIndex,
        f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun w=>by
        dsimp only
        rw [sourceProjection_eq_twentyFour]
        simp only [rationalComplex,MonoidHom.comp_apply,mul_smul]
        rw [←Finset.sum_mul]
        ring)
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun i hi'=>hi i)]

lemma sourceArbitraryHeightFamily_initial (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    sourceArbitraryHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,sourceEisenstein s (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [sourceEisenstein,sourceProjection_integral _ (hyperbolicEisenstein_continuous s (by linarith)) M a b ha ρ freq]
  unfold sourceArbitraryHeightFamily
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  exact arbitraryCuspHeightFamily_initial _ a b ha ρ freq s hs hi

lemma arbitraryCuspHeightFourier_residue_integral (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicResidualFunction (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFourier_integral]
  have he:=(measurePreserving_smul M hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp
    cubicEisensteinResidue_continuous_representative
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae he] with w hw
  exact congrArg (fun c:ℂ=>c*arbitraryCuspWeightedPhase ρ freq w) hw

lemma sourceArbitraryHeightFourier_residue_integral (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    sourceArbitraryHeightFourier M a b ha ρ freq cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicSourceResidualFunction (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [cubicSourceResidualFunction,sourceProjection_integral _ cubicResidualFunction_continuous M a b ha ρ freq]
  simp only [sourceArbitraryHeightFourier,_root_.smul_apply,
    _root_.sum_apply,smul_eq_mul,arbitraryCuspHeightFourier_residue_integral]

end CubicEisenstein

end

end OAI

end

