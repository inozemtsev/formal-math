module

public import Green64.Library.OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Reciprocity / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Reciprocity.RamifiedCuspPhases -/

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

namespace CubicKubota

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def actualCubeCuspPhaseSum (A:levelTwo) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (w:Fin 4→ℂ) : ℂ :=
  ∑' r:Eis⧸Ideal.span {p^3},
    let d:=actualCubeCuspData (A:SL(2,Eis)) p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
    w d.exponent * complexCharacter ⟨d.matrix*(A:SL(2,Eis))⁻¹,d.congruent⟩

theorem actualCubeCuspPhaseSum_coprime (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  let e:=cubeResidueStrataEquiv p hp hprimary
  let a:=cubeCuspAffineEquiv p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0) hprimary hC
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let phi (s:CubeResidueStrata p):=w s.1*cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) s.1 s.2
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=
        phi (e.symm (a r)) := by
    rw [(d r).comparison_phase A hp hprimary hA hC]
    change phi ((d r).stratum hp.ne_zero)=phi (e.symm (a r))
    apply congrArg phi
    apply e.injective
    rw [e.apply_symm_apply]
    change cubeResidueStratumMap p ((d r).stratum hp.ne_zero)=a r
    rw [(d r).stratum_map hp.ne_zero]
    rw [←cubeCuspAffineEquiv_mk p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0)
      (GaussianShiftedPartition.representative (p^3) r) hprimary hC,
      GaussianShiftedPartition.representative_spec]
  let (j:Fin 4):Finite (Eis⧸Ideal.span {p^(3-j.val)}) :=
    finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let (j:Fin 4):Finite (CubicUnitResidue (p^(3-j.val))) := inferInstance
  have hphi:Summable phi:=Summable.of_finite
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r,phi (e.symm (a r)) := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = ∑' r,phi (e.symm r) := a.tsum_eq (fun r => phi (e.symm r))
    _ = ∑' s,phi s := e.symm.tsum_eq phi
    _ = ∑j:Fin 4,w j*∑' b:CubicUnitResidue (p^(3-j.val)),cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b := by
      rw [hphi.tsum_sigma,tsum_fintype]
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_mul_left (f := fun b:CubicUnitResidue (p^(3-j.val)) =>
        cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b) (a := w j)
    _ = _ := cubeStrata_weighted_sum p ((A:SL(2,Eis)) 1 0) hp hprimary hC w

theorem actualCubeCuspPhaseSum_dvd (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:p∣((A:SL(2,Eis)) 1 0)) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^3 := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0 := by
    have hj:((d r).exponent:ℕ)=0:=cube_exponent_zero_of_lower_divisible
      (A:SL(2,Eis)) (d r).matrix p _ _ hp hC (d r).first
    have hj':(d r).exponent=0:=Fin.ext hj
    let N:levelTwo:=⟨(d r).matrix,comparison_levelTwo A (d r).matrix (d r).congruent⟩
    have hphase:=levelTwo_cube_zero_phase A N p
      (GaussianShiftedPartition.representative (p^3) r) hprimary hA
      (comparison_primary _ _ (d r).congruent hA)
      (by simpa only [hj,pow_zero,one_mul] using (d r).first)
      (by simpa only [hj,Nat.sub_zero] using (d r).lower_eq hp.ne_zero)
      (d r).congruent
    change w (d r).exponent*complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0
    rw [hphase,hj',mul_one]
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r:Eis⧸Ideal.span {p^3},w 0 := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = (Nat.card (Eis⧸Ideal.span {p^3}):ℂ)*w 0 := by
      rw [tsum_const,nsmul_eq_mul]
    _ = _ := by
      change (Ideal.absNorm (Ideal.span {p^3}):ℂ)*w 0 = _
      rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
      ring

end CubicKubota

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma onceCusp_trace_lambda : ramifiedTraceLambda*ramLambda=3*omega^2 := by
  unfold ramifiedTraceLambda
  linear_combination -ramified_omega_relation

lemma onceCusp_lambda_dvd_trace : ramLambda∣ramifiedTraceLambda := by
  refine ⟨-omega,?_⟩
  unfold ramifiedTraceLambda
  linear_combination ramified_omega_relation

def onceCuspScale (u:Eisˣ) : Eis := (u:Eis)*ramifiedTraceLambda

def onceCuspComplement (u:Eisˣ) : Eis := -(↑u⁻¹:Eis)*ramifiedTraceLambda

lemma onceCusp_scale_complement (u:Eisˣ) : onceCuspScale u*onceCuspComplement u=3 := by
  calc
    _ = -((u:Eis)*(↑u⁻¹:Eis))*ramifiedTraceLambda^2 := by
      unfold onceCuspScale onceCuspComplement; ring
    _ = 3 := by simp [ramifiedTraceLambda_square]

lemma onceCusp_scale_ne_zero (u:Eisˣ) : onceCuspScale u≠0 := by
  intro h
  have hh:=onceCusp_scale_complement u
  rw [h,zero_mul] at hh
  exact (by norm_num : (0:Eis)≠3) hh

lemma onceCusp_scale_lambda (u:Eisˣ) : (3:Eis)∣onceCuspScale u*ramLambda := by
  refine ⟨(u:Eis)*omega^2,?_⟩
  simp only [onceCuspScale,mul_assoc,onceCusp_trace_lambda]
  ring

lemma onceCusp_complement_lambda (u:Eisˣ) : ramLambda∣onceCuspComplement u :=
  onceCusp_lambda_dvd_trace.mul_left _

lemma onceCusp_scale_coprime (u:Eisˣ) (d:PrimaryLower) : IsCoprime (onceCuspScale u) d.val := by
  apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
  apply (primary_coprime_three d.val (primaryLower_primary d)).symm.of_isCoprime_of_dvd_left
  exact ⟨-ramifiedTraceLambda,by linear_combination ramifiedTraceLambda_square⟩

abbrev OnceRamifiedData := Fin 3×UnitLowerData

def onceRamifiedToPrimitive (u:Eisˣ) (p:OnceRamifiedData) : PrimitiveRow := by
  let b:=omega^p.1.val*p.2.1.val
  let d:=p.2.2.val.val
  refine ⟨![onceCuspScale u*(b-d),d],?_,?_,p.2.2.val.2⟩
  · change IsCoprime (onceCuspScale u*(b-d)) d
    apply (onceCusp_scale_coprime u p.2.2.val).mul_left
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd d (b-d) b ⟨-1,by ring⟩).mpr
    exact ((isCoprime_mul_unit_left_left ((omega_primitive.isUnit (by decide)).pow _) _ _).mpr
      p.2.2.2).symm
  · change (3:Eis)∣onceCuspScale u*(b-d)
    have hb:ramLambda∣b-1:=(halfPrimaryFromAssociate (p.1,p.2.1)).2
    have hd:ramLambda∣d-1:=halfPrimary_lambda_dvd_three.trans p.2.2.val.2
    have hbd:ramLambda∣b-d:=by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub hb hd
    obtain ⟨k,hk⟩:=hbd
    rw [hk,←mul_assoc]
    exact (onceCusp_scale_lambda u).mul_right k

lemma onceRamifiedToPrimitive_bijective (u:Eisˣ) :
    Function.Bijective (onceRamifiedToPrimitive u) := by
  constructor
  · rintro ⟨j,a,d,had⟩ ⟨k,b,e,hbe⟩ h
    have hrow:=congrArg Subtype.val h
    have hde:d=e:=Subtype.ext (congrFun hrow 1)
    subst e
    have he:=congrFun hrow 0
    change onceCuspScale u*(omega^j.val*a.val-d.val)=
      onceCuspScale u*(omega^k.val*b.val-d.val) at he
    have hsub:=mul_left_cancel₀ (onceCusp_scale_ne_zero u) he
    have hassoc:halfPrimaryFromAssociate (j,a)=halfPrimaryFromAssociate (k,b):=by
      apply Subtype.ext
      change omega^j.val*a.val=omega^k.val*b.val
      linear_combination hsub
    have hp:=halfPrimaryFromAssociate_injective hassoc
    have hj:j=k:=congrArg Prod.fst hp
    have hab:a=b:=congrArg Prod.snd hp
    subst k
    subst b
    rfl
  · intro r
    obtain ⟨k,hk⟩:=r.2.2.1
    let d:PrimaryLower:=⟨r.val 1,r.2.2.2⟩
    let b:HalfPrimary:=⟨onceCuspComplement u*k+d.val,by
      have hh:=dvd_add ((onceCusp_complement_lambda u).mul_right k)
        (halfPrimary_lambda_dvd_three.trans d.2)
      convert hh using 1 ;ring⟩
    let p:=halfPrimaryAssociateEquiv.symm b
    have hp:omega^p.1.val*p.2.val=b.val:=
      congrArg Subtype.val (halfPrimaryAssociateEquiv.apply_symm_apply b)
    have hr:onceCuspScale u*(b.val-d.val)=r.val 0:=by
      change onceCuspScale u*(onceCuspComplement u*k+d.val-d.val)=_
      rw [add_sub_cancel_right,←mul_assoc,onceCusp_scale_complement,hk]
    have hcop:IsCoprime p.2.val d.val:=by
      have h0:IsCoprime (b.val-d.val) d.val:=
        (hr ▸ r.2.1).of_isCoprime_of_dvd_left (dvd_mul_left _ _)
      have hb:IsCoprime b.val d.val:=by
        apply IsCoprime.symm
        exact (isCoprime_right_congr_of_dvd d.val (b.val-d.val) b.val ⟨-1,by ring⟩).mp h0.symm
      rw [←hp] at hb
      exact hb.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
    refine ⟨(p.1,⟨p.2,d,hcop⟩),Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change onceCuspScale u*(omega^p.1.val*p.2.val-d.val)=r.val 0
      rw [hp,hr]
    · rfl

def onceRamifiedEquiv (u:Eisˣ) : OnceRamifiedData≃PrimitiveRow :=
  Equiv.ofBijective _ (onceRamifiedToPrimitive_bijective u)

lemma onceRamified_row_phase (u:Eisˣ) (p:OnceRamifiedData) :
    (cosetCharacter (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))⁻¹=
      eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
        eisEmbedding (symbol p.2.2.val.val p.2.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val))
    p.2.2.val.val)=_
  have hh : symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val)) p.2.2.val.val=
      symbol ((onceCuspScale u*omega^p.1.val)*p.2.1.val) p.2.2.val.val :=
    symbol_congr ⟨-onceCuspScale u,by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.2.val),
    symbol_reciprocity p.2.1.val p.2.2.val.val (primaryLower_ne_zero p.2.1)
      (primaryLower_ne_zero p.2.2.val) (primaryLower_primary p.2.1)
        (primaryLower_primary p.2.2.val),map_mul]

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def diagonalPrimitiveMap (u:Eisˣ) (v:PrimitiveRow) : PrimitiveRow :=
  ⟨![(u:Eis)^2*v.val 0,v.val 1],by
    refine ⟨?_,?_,v.2.2.2⟩
    · exact (isCoprime_mul_unit_left_left (u.isUnit.pow 2) _ _).mpr v.2.1
    · exact v.2.2.1.mul_left _⟩

def diagonalPrimitiveEquiv (u:Eisˣ) : PrimitiveRow≃PrimitiveRow where
  toFun:=diagonalPrimitiveMap u
  invFun:=diagonalPrimitiveMap u⁻¹
  left_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (↑u⁻¹:Eis)^2*((u:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl
  right_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (u:Eis)^2*((↑u⁻¹:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl

lemma rowOperator_unitCuspDiagonal (u:Eisˣ) (v:PrimitiveRow) :
    rowOperator (integralComplexMatrix (unitCuspDiagonal u))
      (embeddedRow (primitiveRowEquiv.symm v))=
      eisEmbedding (↑u⁻¹:Eis) •
        embeddedRow (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  simp only [embeddedRow, Function.comp_def, primitiveRowEquiv_symm_row]
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    integralComplexMatrix_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · change eisEmbedding (v.val 0) * eisEmbedding (u : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (0 : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding ((u : Eis) ^ 2 * v.val 0)
    simp only [map_zero, mul_zero, add_zero, map_mul, pow_two]
    have hu : eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis) = 1 := by
      rw [← map_mul]
      simp
    calc
      _ = (eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis)) *
          (eisEmbedding (v.val 0) * eisEmbedding (u : Eis)) := by rw [hu, one_mul]
      _ = _ := by ring
  · change eisEmbedding (v.val 0) * eisEmbedding (0 : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (↑u⁻¹ : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (v.val 1)
    simp [mul_comm]

lemma rowEnergy_unit_smul (u:Eisˣ) (v:Fin 2→ℂ) :
    rowEnergy (eisEmbedding (u:Eis) • v)=rowEnergy v := by
  simp only [rowEnergy,Pi.smul_apply,smul_eq_mul,norm_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

lemma diagonal_ray_summand (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) (v:PrimitiveRow) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*g) s (primitiveRowEquiv.symm v)=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        summand g s (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  have hphase : (cosetCharacter (primitiveRowEquiv.symm v))⁻¹=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        (cosetCharacter (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)))⁻¹ := by
    simp only [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (v.val 0) (v.val 1))=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        eisEmbedding (symbol ((u:Eis)^2*v.val 0) (v.val 1))
    rw [←map_mul,←symbol_mul_numerator _ _ _ (lambda_sq_dvd_three.trans v.2.2.2)]
    congr 2
    rw [←mul_assoc,←mul_pow]
    simp
  rw [summand,←rowOperator_mul,rowOperator_unitCuspDiagonal,map_smul,rowEnergy_unit_smul,hphase,
    summand]
  ring

def rayEisenstein (r:Eis) (g:SL(2,ℂ)) (s:ℂ) : ℂ :=
  ∑'v:PrimitiveRow,eisEmbedding (symbol r (v.val 1))*summand g s (primitiveRowEquiv.symm v)

theorem eisenstein_unit_diagonal (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*g) s=
      rayEisenstein ((↑u⁻¹:Eis)^2) g s := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq]
  simp_rw [diagonal_ray_summand]
  exact (diagonalPrimitiveEquiv u).tsum_eq
    (fun v:PrimitiveRow=>eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
      summand g s (primitiveRowEquiv.symm v))

end

section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def affineLowerTerm (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:Eis) : ℂ :=
  (eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding (q*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s

lemma affineLowerTerm_mul_ray (q r t:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:PrimaryLower) :
    eisEmbedding (symbol t d.val)*affineLowerTerm q r z v s a.val d.val=
      affineLowerTerm q (t*r) z v s a.val d.val := by
  rw [affineLowerTerm,affineLowerTerm,symbol_mul_numerator _ _ _ (primaryLower_primary d),
    map_mul eisEmbedding (symbol t d.val) (symbol r d.val)]
  ring

lemma onceRamified_summand (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u))*upperSection z v hv) s
      (primitiveRowEquiv.symm (onceRamifiedEquiv u p))=
      affineLowerTerm (onceCuspScale u*omega^p.1.val) (onceCuspScale u*omega^p.1.val)
        z v s p.2.1.val p.2.2.val.val := by
  let r:Fin 2→ℂ:=![eisEmbedding ((onceCuspScale u*omega^p.1.val)*p.2.1.val),
    eisEmbedding p.2.2.val.val]
  have hr:rowOperator (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u)))
      (embeddedRow (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [onceRamifiedEquiv, Equiv.ofBijective_apply, onceRamifiedToPrimitive,
        r, map_mul, map_sub, mul_sub, mul_assoc]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.2.val) he
  have hp:=heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,onceRamified_row_phase]
  change _= (eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
    eisEmbedding (symbol p.2.2.val.val p.2.1.val))*((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=(((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

def diagonalOnceCuspIndex (u t:Eisˣ) : OnceRamifiedData≃CuspCosets :=
  (onceRamifiedEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

def diagonalUnitCuspIndex (u t:Eisˣ) : UnitLowerData≃CuspCosets :=
  (unitLowerEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

lemma diagonal_once_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s
      (diagonalOnceCuspIndex u t p)=
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (onceRamifiedEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,onceRamified_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.2.1 p.2.2.val

lemma diagonal_unit_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:UnitLowerData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s
      (diagonalUnitCuspIndex u t p)=
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val := by
  rw [mul_assoc]
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (unitLowerEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,unitLower_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.1 p.2.val

theorem diagonal_once_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s=
      ∑'p:OnceRamifiedData,affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  rw [eisenstein,←(diagonalOnceCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_once_summand u t z v hv s)

theorem diagonal_unit_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s=
      ∑'p:UnitLowerData,affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis))
        z v s p.1.val p.2.val.val := by
  rw [eisenstein,←(diagonalUnitCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_unit_summand u t z v hv s)

theorem hasSum_diagonal_once_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:OnceRamifiedData=>∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val*
          ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalOnceCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [mul_assoc,diagonal_once_summand])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def eisensteinCoordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) : Fin 2→ℝ :=
  ![(ActualEisensteinCoordinates.coords b).1 • x 0-(ActualEisensteinCoordinates.coords b).2 • x 1,
    (ActualEisensteinCoordinates.coords b).2 • x 0+
      ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • x 1]

def eisensteinTorusMul (b : ActualEisensteinCubic.O) : UnitAddTorus (Fin 2)→+UnitAddTorus (Fin 2) where
  toFun t :=
    ![(ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1,
      (ActualEisensteinCoordinates.coords b).2 • t 0+
        ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' t s := by ext i;fin_cases i <;> simp [smul_add] <;> abel

lemma eisensteinTorusMul_continuous (b : ActualEisensteinCubic.O) : Continuous (eisensteinTorusMul b) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1)
    fun_prop
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).2 • t 0+((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1)
    fun_prop

lemma periodVector_coordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) :
    periodVector (eisensteinCoordinateMul b x)=eisEmbedding b*periodVector x := by
  have hb : eisEmbedding b=((ActualEisensteinCoordinates.coords b).1:ℂ)+
      ((ActualEisensteinCoordinates.coords b).2:ℂ)*omega3 := by
    simpa only [ActualEisensteinCubic.eisEmbedding_eval] using (congrArg eisEmbedding (ActualEisensteinCoordinates.eval_coords b)).symm
  rw [periodVector_apply,periodVector_apply,hb]
  simp only [eisensteinCoordinateMul,Matrix.cons_val_zero,Matrix.cons_val_one,
    zsmul_eq_mul]
  push_cast
  linear_combination -(3*((ActualEisensteinCoordinates.coords b).2:ℂ)*(x 1:ℂ))*EisensteinEmbedding.omega3_sq

lemma eisensteinTorusMul_periodTorus (b : ActualEisensteinCubic.O) (z : ℂ) :
    eisensteinTorusMul b (periodTorus z)=periodTorus (eisEmbedding b*z) := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  rw [←periodVector_coordinateMul,periodTorus_periodVector,periodTorus_periodVector]
  ext i
  fin_cases i <;> rfl

lemma eisensteinTorusMul_surjective (b : ActualEisensteinCubic.O) (hb : b≠0) : Function.Surjective (eisensteinTorusMul b) := by
  intro t
  refine ⟨periodTorus ((eisEmbedding b)⁻¹*periodSection t),?_⟩
  rw [eisensteinTorusMul_periodTorus,←mul_assoc,mul_inv_cancel₀ (eisEmbedding_ne_zero hb),one_mul,
    periodTorus_section]

theorem eisensteinTorusMul_measurePreserving (b : ActualEisensteinCubic.O) (hb : b≠0) :
    MeasurePreserving (eisensteinTorusMul b) volume volume :=
  AddMonoidHom.measurePreserving (eisensteinTorusMul_continuous b) (eisensteinTorusMul_surjective b hb) rfl

lemma periodTorus_eq_implies_lattice_difference (z w : ℂ) (h : periodTorus z=periodTorus w) :
    ∃n : ActualEisensteinCubic.O,z=w+3*eisEmbedding n := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  obtain ⟨y,rfl⟩ := periodVector.surjective w
  rw [periodTorus_periodVector,periodTorus_periodVector] at h
  have hz (i : Fin 2) : ((x i-y i:ℝ):UnitAddCircle)=0 := by
    rw [AddCircle.coe_sub,congrFun h i,sub_self]
  obtain ⟨n0,hn0⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 0)
  obtain ⟨n1,hn1⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 1)
  simp only [zsmul_eq_mul,mul_one] at hn0 hn1
  have hx0 : x 0=y 0+n0 := by linarith
  have hx1 : x 1=y 1+n1 := by linarith
  refine ⟨ActualEisensteinCoordinates.eval n0 n1,?_⟩
  rw [periodVector_apply,periodVector_apply,ActualEisensteinCubic.eisEmbedding_eval,hx0,hx1]
  push_cast
  ring

lemma periodic_function_periodSection (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (z : ℂ) :
    f (periodSection (periodTorus z))=f z := by
  obtain ⟨n,hn⟩ := periodTorus_eq_implies_lattice_difference (periodSection (periodTorus z)) z
    (periodTorus_section (periodTorus z))
  rw [hn,hp]

theorem period_integral_eisenstein_mul (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (b : ActualEisensteinCubic.O) (hb : b≠0) :
    (∫z in periodDomain,f (eisEmbedding b*z))=∫z in periodDomain,f z := by
  let F : UnitAddTorus (Fin 2)→ℂ := fun t=>f (periodSection t)
  have hF : Measurable F := hf.comp periodSection_measurableEmbedding.measurable
  have hm := eisensteinTorusMul_measurePreserving b hb
  have hi : (∫t,F (eisensteinTorusMul b t))=∫t,F t := by
    have hh := integral_map («μ» := (volume : Measure (UnitAddTorus (Fin 2)))) hm.measurable.aemeasurable hF.stronglyMeasurable.aestronglyMeasurable
    rw [hm.map_eq] at hh
    exact hh.symm
  rw [periodTorus_integral,periodTorus_integral] at hi
  simp only [eisensteinTorusMul_periodTorus,F,periodic_function_periodSection f hp] at hi
  simp only [Complex.real_smul] at hi
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (show (2/(9*Real.sqrt 3):ℝ)≠0 by positivity)) hi

end CubicEisenstein

open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_index_period_unfold_of_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f)
    (hsum:Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫z:ℂ,f z := by
    rw [GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  have hsplit:=(hsum.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q}))).tsum_eq.symm
  change (∑'n:Eis,I n)=_ at hsplit ⊢
  rw [hsplit]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=_
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_lintegral (q:Eis) (hq:q≠0) (f:ℂ→ℝ≥0∞) :
    (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℝ≥0∞)*(∫⁻z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℝ≥0∞:=fun n=>∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫⁻z:ℂ,f z := by
    rw [←(GaussianFiberEquiv.fiberEquiv q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)).tsum_eq]
    change (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    simp_rw [he]
    rw [←lintegral_eq_period_lintegrals (fun z=>f (z+b))]
    exact lintegral_add_right_eq_self f b
  change (∑'n:Eis,I n)=_
  rw [←ENNReal.tsum_fiberwise I (Ideal.Quotient.mk (Ideal.span {q}))]
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℝ≥0∞)=(Nat.card (Eis⧸Ideal.span {q}):ℝ≥0∞)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_integrals_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)) := by
  apply Summable.of_enorm
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n=>enorm_integral_le_lintegral_enorm _))
  rw [finite_index_period_lintegral q hq (fun z=>‖f z‖ₑ)]
  exact ENNReal.mul_lt_top (by simp) hf.hasFiniteIntegral

theorem finite_index_period_unfold (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) :=
  finite_index_period_unfold_of_summable q hq f hf
    (finite_index_period_integrals_summable q hq f hf)

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.AffineCuspFourier -/

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
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineLowerTerm_eq_shifted (q r:Eis) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    affineLowerTerm q r z v s a d=
      (eisEmbedding (symbol r d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding (q*a)‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding (q*a)) z := by
  rw [affineLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s (q*a) d (mul_ne_zero hq ha)]
  ring

lemma affineLowerTerm_integrable (q r:Eis) (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    Integrable (fun z=>affineLowerTerm q r z v s a d) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma affineLowerTerm_fourier_integral (q r:Eis) (v:ℝ) (hv:0<v) (s freq:ℂ)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    (∫z:ℂ,affineLowerTerm q r z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding (q*a)‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding (q*a))) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding (q*a)) freq]
  ring_nf

lemma affineCuspGaussTerm_factor (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol x a)*residueAdditive (3*k) a x) := by
  have hs:symbol (a+3*x) a=symbol (3*x) a:=symbol_congr ⟨1,by ring⟩
  rw [ramified_symbol_primary_shift_signed j n r a x hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary,map_mul eisEmbedding (symbol 3 a) (symbol x a)]
  have hp:=affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) x ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

lemma affineCuspTwistedCoefficient_add (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*(x+a*m)))*eisEmbedding (symbol (a+3*(x+a*m)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a))=
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a)) := by
  rw [affineCuspGaussTerm_factor h h1 q r a k (x+a*m) j n ha hprimary hq hr hh hk,
    affineCuspGaussTerm_factor h h1 q r a k x j n ha hprimary hq hr hh hk]
  rw [symbol_congr (show a∣x+a*m-x from ⟨m,by ring⟩),
    residueAdditive_three_congr k a (x+a*m) x ha ⟨m,by ring⟩]

lemma affineLowerTerm_weighted_translate (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)) := by
  let c1:=eisEmbedding (symbol r (a+3*(x+a*m)))*eisEmbedding (symbol (a+3*(x+a*m)) a)
  let c0:=eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a)
  let B:=ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a)
  let Q:=ninthCuspFrequency h*(3*eisEmbedding m/eisEmbedding q)
  have harg:ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a)=B+Q:=by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef:=affineCuspTwistedCoefficient_add h h1 q r a k x m j n ha hprimary hq hr hh hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a))=
    c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB:ShortDraftTrace.breveE B≠0:=Complex.exp_ne_zero _
  have heQ:ShortDraftTrace.breveE Q≠0:=Complex.exp_ne_zero _
  have hmult:c1*ShortDraftTrace.breveE Q=c0:=by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve:c1=c0*ShortDraftTrace.breveE (-Q):=by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow:eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))=
      eisEmbedding (q*a)*(z+3*eisEmbedding m/eisEmbedding q)+eisEmbedding (a+3*x):=by
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq]
    ;ring
  change c1*((v/(‖eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))‖^2+
    ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold affineLowerTerm
  have hphase:-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)=(-Q)+(-ninthCuspFrequency h*z):=by
    dsimp [Q];ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma affineLowerIntegral_sum_translate (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  rw [←finite_index_period_unfold q hq _ hint]
  apply tsum_congr
  intro m
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>affineLowerTerm_weighted_translate
    h h1 q r a k x m j n ha hprimary hq hr hh hk z v s)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineDenominator_integral_formula (h h1 q r k:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a.val)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*ramifiedAffineGauss h q r a.val := by
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
  rw [←e.tsum_eq]
  change (∑'p:CubicUnitResidue a.val×Eis,∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=_
  rw [hpair.tsum_prod]
  have hinner (x:CubicUnitResidue a.val) :
      (∑'m:Eis,∫z in periodDomain,
        affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val x.val+a.val*m))*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*
            ((eisEmbedding (symbol r (a.val+3*GaussianShiftedPartition.representative a.val x.val))*
              eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val x.val) a.val))*
                ShortDraftTrace.breveE (ninthCuspFrequency h*
                  eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val x.val)/eisEmbedding (q*a.val)))) := by
    rw [affineLowerIntegral_sum_translate h h1 q r a.val k _ j n (primaryLower_ne_zero a)
      (primaryLower_primary a) hq hr hh hk v hv s hs,
      affineLowerTerm_fourier_integral q r v hv s _ a.val _ (primaryLower_ne_zero a) hq]
  simp_rw [hinner]
  unfold ramifiedAffineGauss
  simp_rw [mul_assoc]
  rw [tsum_mul_left,tsum_mul_left,tsum_mul_left,tsum_mul_left]

lemma affineCuspFrequency_lift (h1:Eis) (j n:ℕ) (a:PrimaryLower)
    (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n) :
    ∃k:Eis,3*k=h1+ramifiedAffineParameter j n*a.val := by
  have hh:=dvd_add hfreq (a.2.mul_left (ramifiedAffineParameter j n))
  have hd:(3:Eis)∣h1+ramifiedAffineParameter j n*a.val:=by
    convert hh using 1 ;ring
  obtain ⟨k,hk⟩:=hd
  exact ⟨k,hk.symm⟩

lemma affineCusp_norm_factor (q:Eis) (s:ℂ) (a:PrimaryLower) :
    ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)=
      ((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s) := by
  rw [map_mul,norm_mul,mul_pow,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _)]

theorem affineCusp_branch_fourier (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
            unramifiedCubicGaussSeries s (3*r^2*h1) := by
  rw [hsum.tsum_sigma]
  have ha (a:PrimaryLower):
      (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
        affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q))*
        (((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*cubicUnitGaussSum (3*r^2*h1) a.val) := by
    obtain ⟨k,hk⟩:=affineCuspFrequency_lift h1 j n a hfreq
    rw [affineDenominator_integral_formula h h1 q r k j n a hq hr hh hk v hv s hs
      (hsum.sigma_factor a),ramifiedAffineGauss_eq_unramified h h1 q r a.val k j n
        (primaryLower_ne_zero a) (primaryLower_primary a) hq hr hh hk,
      affineCusp_norm_factor]
    ring
  simp_rw [ha]
  rw [tsum_mul_left]
  congr 1
  rw [←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  change ((‖eisEmbedding (CompletedGauss.primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (3*r^2*h1) (CompletedGauss.primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(CompletedGauss.primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]

end

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma hasSum_diagonal_unit_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val*
        ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalUnitCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [diagonal_unit_summand])

theorem diagonal_unit_eisenstein_fourier (u t:Eisˣ) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hh:h=(t:Eis)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 0)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
          unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*h1) := by
  have hsum:=hasSum_diagonal_unit_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq]
  have h:=affineCusp_branch_fourier h h1 (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
    (by simpa using hr) hh hfreq v hv s (by linarith) hsum.summable
  simpa only [GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,Complex.ofReal_one,
    Complex.one_cpow,Ideal.span_singleton_eq_top.mpr t.isUnit,Ideal.absNorm_top,map_one,Nat.cast_one,one_mul] using h

lemma onceCusp_q_norm (t:Eisˣ) (j:Fin 3) :
    ‖eisEmbedding (onceCuspScale t*omega^j.val)‖^2=3 := by
  have hw:‖eisEmbedding omega‖=1:=by
    let w:Eisˣ:=(omega_primitive.isUnit (by decide)).unit
    have hw:(w:Eis)=omega:=(omega_primitive.isUnit (by decide)).unit_spec
    rw [←hw]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit w
  simp only [onceCuspScale,map_mul,norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_mul,map_pow,norm_pow,hw,one_pow,mul_one,ramifiedEmbedding_traceLambda]
  rw [←ramifiedEmbedding_traceLambda,←norm_pow,←map_pow,ramifiedTraceLambda_square]
  norm_num [map_ofNat]

lemma onceCusp_q_absNorm (t:Eisˣ) (j:Fin 3) :
    Ideal.absNorm (Ideal.span {onceCuspScale t*omega^j.val})=3 := by
  have h:=onceCusp_q_norm t j
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at h
  exact_mod_cast h

theorem diagonal_once_branch_fourier (u t:Eisˣ) (l:Fin 3) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^j*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^j*ramifiedTraceLambda))
    (hh:h=(onceCuspScale t*omega^l.val)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 1)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^l.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s p.1.val p.2.val.val*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (3:ℂ)*(3:ℂ)^(-s)*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
          unramifiedCubicGaussSeries s
            (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*h1) := by
  have hsum:=(hasSum_diagonal_once_integrals u t v hv s (ninthCuspFrequency h) hs).summable.prod_factor l
  have hq:onceCuspScale t*omega^l.val≠0:=mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)
  have h:=affineCusp_branch_fourier h h1 (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) j 1 hq (by simpa only [pow_one] using hr)
      hh hfreq v hv s (by linarith) hsum
  simpa only [onceCusp_q_norm,onceCusp_q_absNorm,Nat.cast_ofNat,Complex.ofReal_ofNat] using h

end

section
open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem quotient_weighted_period_unfold (q:Eis) (hq:q≠0)
    (ψ:(Eis⧸Ideal.span {q})→ℂ) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*
      ∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (∑'r:Eis⧸Ideal.span {q},ψ r)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hs:Summable (fun n:Eis=>ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*I n):=by
    apply (((finite_index_period_integrals_summable q hq f hf).norm).mul_left ‖ψ‖).of_norm_bounded
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ψ _) (norm_nonneg _)
  have hinner (r:Eis⧸Ideal.span {q}):
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
        ψ (Ideal.Quotient.mk (Ideal.span {q}) n.val)*I n.val)=ψ r*(∫z:ℂ,f z) := by
    have heval (n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r})):
        Ideal.Quotient.mk (Ideal.span {q}) n.val=r:=n.2
    simp_rw [heval]
    rw [tsum_mul_left,GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    congr 1
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ):
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b:=by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  rw [←(hs.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q})) ).tsum_eq]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
    ψ (Ideal.Quotient.mk (Ideal.span {q}) n.val)*I n.val)=_
  simp_rw [hinner]
  exact tsum_mul_right

theorem character_weighted_period_unfold (q:Eis) (hq:q≠0)
    (ψ:AddChar (Eis⧸Ideal.span {q}) ℂ) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*
      ∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      if ψ=1 then (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) else 0 := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  rw [quotient_weighted_period_unfold q hq ψ f hf,tsum_fintype]
  split_ifs with hψ
  · rw [AddChar.sum_eq_card_of_eq_one hψ]
    congr 1
    change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
    rw [Nat.card_eq_fintype_card]
  · rw [AddChar.sum_eq_zero_of_ne_one hψ,zero_mul]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def affinePeriodChar (q:Eis) (hq:q≠0) (ell:Eis) : AddChar (Eis⧸Ideal.span {q}) ℂ :=
  (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates q hq).mulShift
    (Ideal.Quotient.mk (Ideal.span {q}) ell)

lemma affinePeriodChar_mk (q:Eis) (hq:q≠0) (ell x:Eis) :
    affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) x)=
      ShortDraftTrace.breveE (eisEmbedding (ell*x)/(eisEmbedding q*eisLam)) := by
  simp only [affinePeriodChar,AddChar.mulShift_apply,←map_mul,eisTraceModChar,
    IdealGaussCRT.traceModChar_mk]

lemma affinePeriodChar_eq_one (q:Eis) (hq:q≠0) (ell:Eis) :
    affinePeriodChar q hq ell=1 ↔ q∣ell := by
  constructor
  · intro h
    by_contra hd
    have hz:Ideal.Quotient.mk (Ideal.span {q}) ell≠0:=by
      intro he
      exact hd (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
    exact GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive q hq hz h
  · intro hd
    have hz:Ideal.Quotient.mk (Ideal.span {q}) ell=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    simp [affinePeriodChar,hz]

lemma affineCusp_general_weighted_translate (h q r a ell x m:Eis) (j n:ℕ)
    (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hell:3*ell=h+ramifiedAffineParameter j n*q*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
        (affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q))) := by
  let A:=eisEmbedding (ramifiedAffineParameter j n*(a*m))/eisLam/3
  let delta:=3*eisEmbedding m/eisEmbedding q
  have hchar:eisEmbedding (symbol r (a+3*(x+a*m)))=
      eisEmbedding (symbol r (a+3*x))*ShortDraftTrace.breveE A:=by
    have hd:lambda^2∣a+3*x-1:=primary_add_three a x hprimary
    have h:=ramified_symbol_primary_shift_signed j n r (a+3*x) (a*m) hr hd
    convert h using 1 ; congr 2 ;ring
  have hden:symbol (a+3*(x+a*m)) a=symbol (a+3*x) a:=
    symbol_congr ⟨3*m,by ring⟩
  have hrow:eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))=
      eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x):=by
    dsimp [delta]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq]
    ;ring
  have hell':eisEmbedding ell=(eisEmbedding h+eisEmbedding (ramifiedAffineParameter j n)*eisEmbedding q*eisEmbedding a)/3:=by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he:=congrArg eisEmbedding hell
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  have harg:A+ninthCuspFrequency h*delta=eisEmbedding (ell*m)/(eisEmbedding q*eisLam):=by
    dsimp [A,delta,ninthCuspFrequency,cuspFrequency]
    simp only [map_mul]
    rw [hell']
    field_simp [eisEmbedding_ne_zero hq,eisLam_ne_zero]
    ;ring
  have hphase:ShortDraftTrace.breveE A*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+delta)):=by
    rw [affinePeriodChar_mk,←harg,←AddChar.map_add_eq_mul,←AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold affineLowerTerm
  rw [hchar,hden,hrow]
  change _=affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
    ((eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ((v/(‖eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x)‖^2+
        ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+delta)))
  calc
    _ = ((eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ((v/(‖eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x)‖^2+
        ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s)*
        (ShortDraftTrace.breveE A*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by ring
    _ = _ := by rw [hphase];ring

lemma affineCusp_masked_inner (h q r a ell x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hell:3*ell=h+ramifiedAffineParameter j n*q*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      if q∣ell then (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) else 0 := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  simp_rw [affineCusp_general_weighted_translate h q r a ell x _ j n hprimary hq hr hell,
    integral_const_mul]
  rw [character_weighted_period_unfold q hq (affinePeriodChar q hq ell) _ hint]
  simp only [affinePeriodChar_eq_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineDenominator_zero (h h1 q r:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q)
    (hfreq:¬(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=0 := by
  have hdiv:(3:Eis)∣h+ramifiedAffineParameter j n*q*a.val:=by
    have ht:=dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q))
    convert ht using 1 ;ring
  obtain ⟨ell,hell⟩:=hdiv
  have hell':3*ell=h+ramifiedAffineParameter j n*q*a.val:=hell.symm
  have hne:¬q∣ell:=by
    rintro ⟨b,hb⟩
    have he:q*(3*b)=q*(h1+ramifiedAffineParameter j n*a.val):=by
      rw [hb,hh] at hell'
      linear_combination hell'
    have hc:=mul_left_cancel₀ hq he
    have ht:(3:Eis)∣h1+ramifiedAffineParameter j n*a.val:=⟨b,hc.symm⟩
    apply hfreq
    have hh:=dvd_sub ht (a.2.mul_left (ramifiedAffineParameter j n))
    convert hh using 1 ;ring
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
  rw [←e.tsum_eq]
  change (∑'p:CubicUnitResidue a.val×Eis,∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=_
  rw [hpair.tsum_prod]
  have hinner (x:CubicUnitResidue a.val):
      (∑'m:Eis,∫z in periodDomain,
        affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val x.val+a.val*m))*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=0:=by
    rw [affineCusp_masked_inner h q r a.val ell _ j n (primaryLower_ne_zero a)
      (primaryLower_primary a) hq hr hell' v hv s hs,ite_eq_right hne]
  simp only [hinner,tsum_zero]

theorem affineCusp_branch_fourier_masked (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      if (3:Eis)∣h1+ramifiedAffineParameter j n then
        (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
          ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
            ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
              unramifiedCubicGaussSeries s (3*r^2*h1) else 0 := by
  split_ifs with hfreq
  · exact affineCusp_branch_fourier h h1 q r j n hq hr hh hfreq v hv s hs hsum
  · rw [hsum.tsum_sigma]
    simp only [affineDenominator_zero h h1 q r j n _ hq hr hh hbase hfreq v hv s hs
      (hsum.sigma_factor _),tsum_zero]

theorem diagonal_once_eisenstein_fourier (u t:Eisˣ) (j:Fin 3→ℕ) (h:Eis) (h1:Fin 3→Eis)
    (hr:∀l,(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^(j l)*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^(j l)*ramifiedTraceLambda))
    (hh:∀l,h=(onceCuspScale t*omega^l.val)*h1 l)
    (hbase:∀l,(3:Eis)∣h+ramifiedAffineParameter (j l) 1*(onceCuspScale t*omega^l.val))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ∑l:Fin 3,if (3:Eis)∣h1 l+ramifiedAffineParameter (j l) 1 then
        (3:ℂ)*(3:ℂ)^(-s)*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
            unramifiedCubicGaussSeries s
              (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*h1 l) else 0 := by
  have hsum:=hasSum_diagonal_once_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq,hsum.summable.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro l hl
  have hq:onceCuspScale t*omega^l.val≠0:=mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)
  have h:=affineCusp_branch_fourier_masked h (h1 l) (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (j l) 1 hq
      (by simpa only [pow_one] using hr l) (hh l) (hbase l) v hv s (by linarith)
        (hsum.summable.prod_factor l)
  simpa only [onceCusp_q_norm,onceCusp_q_absNorm,Nat.cast_ofNat,Complex.ofReal_ofNat] using h

end CubicEisenstein

end

end OAI

end

