module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part020

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / ChineseRemainder / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions -/

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

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix MatrixGroups

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primary_coprime_nine (a:Eis) (ha:lambda^2∣a-1) : IsCoprime a (9:Eis) := by
  have h3:=primary_coprime_three a ha
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_right h3

lemma nine_coprime_of_not_lambda_dvd (c:Eis) (hc:¬lambda∣c) : IsCoprime (9:Eis) c := by
  have hL:IsCoprime lambda c:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr hc
  have h3:IsCoprime (3:Eis) c:=(hL.mul_left hL).of_isCoprime_of_dvd_left
    (by simpa only [pow_two] using three_dvd_lambda_sq)
  simpa only [show (3:Eis)*3=9 by norm_num] using h3.mul_left h3

lemma primary_numerator_controlled_inverse (c a:Eis)
    (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 :=
  exists_controlled_inverse 9 c a ((primary_coprime_nine a ha).mul_right hac)

lemma completion_primary_lower_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (ha:(3:Eis)∣a-1) (hb:(3:Eis)∣b) : (3:Eis)∣d-1 := by
  have had:(3:Eis)∣a*d-1:=by
    convert dvd_mul_of_dvd_left hb c using 1
    linear_combination hdet
  convert dvd_sub had (dvd_mul_of_dvd_left ha d) using 1 ; ring

lemma completion_negative_upper_right (a b c d:Eis)
    (hdet:a*d-b*c=1) (hc:(3:Eis)∣c-1) (hd:(3:Eis)∣d) : (3:Eis)∣b+1 := by
  have hbc:(3:Eis)∣b*c+1:=by
    convert dvd_mul_of_dvd_right hd a using 1
    linear_combination -hdet
  convert dvd_sub hbc (dvd_mul_of_dvd_right hc b) using 1 ; ring

theorem exists_primary_numerator_completion (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣b ∧
        (3:Eis)∣d-1 ∧ (3:Eis)∣c*r-c := by
  obtain ⟨d0,hd0⟩:=primary_numerator_controlled_inverse c a ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hprimary
  obtain ⟨b,d,hdet,hd,hb⟩:=exists_fixed_completion_upper_right 9 M c r a d0 hc h9M hr har hd0
  refine ⟨b,d,hdet,hd,hb,completion_primary_lower_right a b (c*r) d hdet
    (three_dvd_primary_sub_one a ha) ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb),?_⟩
  convert dvd_mul_of_dvd_right (three_dvd_primary_sub_one r hprimary) c using 1 ; ring

theorem exists_unramified_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:¬lambda∣c) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 := by
  obtain ⟨d0,hzero,hinv⟩:=exists_controlled_zero_inverse 9 c a
    (nine_coprime_of_not_lambda_dvd c hc) hac
  exact ⟨d0,hzero,hinv,fun r hr har=>exists_fixed_completion_lower_right 9 M c r a d0
    h9M hr har hzero hinv⟩

theorem exists_primary_denominator_completion (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃b d:Eis,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ (9:Eis)∣d ∧
        (9:Eis)∣a*d ∧ (9:Eis)∣b*(c*r)+1 ∧ (3:Eis)∣b+1 ∧ (3:Eis)∣c*r-1 := by
  have hcl:¬lambda∣c:=by
    intro hd
    have hcL:IsCoprime lambda c:=
      (primary_coprime_three c hc).symm.of_isCoprime_of_dvd_left
        ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three)
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (hcL.isUnit_of_dvd hd)
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_unramified_denominator_completion M c a h9M hcl hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc⟩:=hcomp r hr har
  have hc3:(3:Eis)∣c*r-1:=three_dvd_primary_sub_one _ (primary_mul c r hc hpr)
  exact ⟨b,d,hdet,hd,hBd,had,hbc,completion_negative_upper_right a b (c*r) d hdet hc3
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hBd),hc3⟩

end

section
variable {R:Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma controlled_inverse_sector (B M c a a0 d0:R)
    (hBM:B∣M) (ha:M*c∣a-a0) (hinv:B*c∣a0*d0-1) : B*c∣a*d0-1 := by
  have hdiff:=dvd_mul_of_dvd_left ((mul_dvd_mul_right hBM c).trans ha) d0
  convert dvd_add hdiff hinv using 1 ; ring

theorem exists_fixed_matrix_completion_controlled
    (B N M c a0 r0 b0 d0 bResidue dResidue:R)
    (hc:c≠0) (hBM:B∣M) (hNM:N∣M)
    (hdet0:a0*d0-b0*(c*r0)=1)
    (hb0:B∣b0-bResidue) (hd0:N∣d0-dResidue) :
    ∀a r:R,M*c∣a-a0→M∣r-r0→IsCoprime r (M*c)→IsCoprime a r→
      ∃b d:R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧ B∣b-bResidue ∧ N∣d-dResidue ∧
        (!![a,b;c*r,d]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M}))=
        (!![a0,b0;c*r0,d0]:Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  obtain ⟨b,d,hdet,hd,hmat⟩:=exists_fixed_matrix_completion M c a0 r0 d0 b0 hc hdet0
    a r ha hrr hr har
  have hbd:B∣b-b0:=hBM.trans (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr)
  have hdd:N∣d-d0:=(hNM.trans (dvd_mul_right M c)).trans hd
  refine ⟨b,d,hdet,hd,?_,?_,hmat⟩
  · convert dvd_add hbd hb0 using 1 ; ring
  · convert dvd_add hdd hd0 using 1 ; ring

end

section
open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal CubicKubota ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O

def controlledCompletionMatrix (a b c d:Eis) (hdet:a*d-b*c=1) : SL(2,Eis) :=
  ⟨!![a,b;c,d],by simpa [Matrix.det_fin_two] using hdet⟩

theorem exists_primary_numerator_matrix (M c a:Eis)
    (hc:c≠0) (h9M:(9:Eis)∣M) (ha:lambda^2∣a-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)*c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃g:SL(2,Eis),g 0 0=a ∧ g 1 0=c*r ∧ M*c∣g 1 1-d0 ∧
        (9:Eis)∣g 0 1 ∧ (3:Eis)∣g 0 0-1 ∧ (3:Eis)∣g 1 1-1 ∧ (3:Eis)∣g 1 0-c := by
  obtain ⟨d0,hd0,hcomp⟩:=exists_primary_numerator_completion M c a hc h9M ha hac
  refine ⟨d0,hd0,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hb,hd3,hc3⟩:=hcomp r hr har hpr
  exact ⟨controlledCompletionMatrix a b (c*r) d hdet,rfl,rfl,hd,hb,
    three_dvd_primary_sub_one a ha,hd3,hc3⟩

theorem exists_primary_denominator_matrix (M c a:Eis)
    (h9M:(9:Eis)∣M) (hc:lambda^2∣c-1) (hac:IsCoprime a c) :
    ∃d0:Eis,(9:Eis)∣d0 ∧ c∣a*d0-1 ∧
      ∀r:Eis,IsCoprime r (M*c)→IsCoprime a r→lambda^2∣r-1→
      ∃g:SL(2,Eis),g 0 0=a ∧ g 1 0=c*r ∧ M*c∣g 1 1-d0 ∧
        (9:Eis)∣g 1 1 ∧ (9:Eis)∣g 0 0*g 1 1 ∧
        (9:Eis)∣g 0 1*g 1 0+1 ∧ (3:Eis)∣g 0 1+1 ∧ (3:Eis)∣g 1 0-1 := by
  obtain ⟨d0,hzero,hinv,hcomp⟩:=exists_primary_denominator_completion M c a h9M hc hac
  refine ⟨d0,hzero,hinv,?_⟩
  intro r hr har hpr
  obtain ⟨b,d,hdet,hd,hBd,had,hbc,hb3,hc3⟩:=hcomp r hr har hpr
  exact ⟨controlledCompletionMatrix a b (c*r) d hdet,rfl,rfl,hd,hBd,had,hbc,hb3,hc3⟩

lemma controlled_primary_principal (g:SL(2,Eis)) (c:Eis)
    (ha:(3:Eis)∣g 0 0-1) (hb:(9:Eis)∣g 0 1)
    (hc:(3:Eis)∣g 1 0-c) (hc0:(3:Eis)∣c) (hd:(3:Eis)∣g 1 1-1) :
    g∈levelThree := by
  apply A3_principal_mem_levelThree g ha
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb) _ hd
  convert dvd_add hc hc0 using 1 ; ring

lemma controlled_primary_ramified (g:SL(2,Eis)) (c u:Eis)
    (ha:(3:Eis)∣g 0 0-1) (hb:(9:Eis)∣g 0 1)
    (hc:(3:Eis)∣g 1 0-c) (hcu:(3:Eis)∣c-u) (hd:(3:Eis)∣g 1 1-1) :
    g*(lowerCuspMatrix u)⁻¹∈levelThree := by
  apply A3_ramified_mem_levelThree g u ha
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hb) _ hd
  convert dvd_add hc hcu using 1 ; ring

lemma controlled_denominator_unramified (g:SL(2,Eis)) (u:Eis)
    (ha:(3:Eis)∣g 0 0-u) (hb:(3:Eis)∣g 0 1+1)
    (hc:(3:Eis)∣g 1 0-1) (hd:(9:Eis)∣g 1 1) :
    g*(A3WeylCusp u)⁻¹∈levelThree :=
  A3_unramified_mem_levelThree g u ha hb hc ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hd)

end

open ActualEisensteinCubic CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_primary_numerator_sector_completions {ι Q:Type*}
    (M c:Eis) (hc:c≠0) (h9M:(9:Eis)∣M)
    (sector:ι→Q) (a r:ι→Eis)
    (haPrimary:∀i,lambda^2∣a i-1) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(9:Eis)∣b i) ∧ (∀i,(3:Eis)∣d i-1) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (9:Eis)∣b ∧ (3:Eis)∣d-1 ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,hcompletion⟩:=exists_primary_numerator_completion M c (a j) hc h9M
        (haPrimary j) (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hb0,hd0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        9 3 M c (a j) (r j) b0 d0 0 1 hc h9M h3M hdet0 (by simpa using hb0) hd0
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

theorem exists_primary_denominator_sector_completions {ι Q:Type*}
    (M c:Eis) (h9M:(9:Eis)∣M) (hcPrimary:lambda^2∣c-1)
    (sector:ι→Q) (a r:ι→Eis) (hrPrimary:∀i,lambda^2∣r i-1)
    (hcop:∀i,IsCoprime (a i) (c*r i)) (hr:∀i,IsCoprime (r i) (M*c))
    (ha:∀i j,sector i=sector j→M*c∣a i-a j)
    (hrr:∀i j,sector i=sector j→M∣r i-r j) :
    ∃(b d:ι→Eis) (C:Q→Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧ (∀i,(3:Eis)∣b i+1) ∧ (∀i,(9:Eis)∣d i) ∧
      ∀i,(!![a i,b i;c*r i,d i]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hc:c≠0:=primary_ne_zero c hcPrimary
  have h3M:(3:Eis)∣M:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9M
  have hlocal (q:Q) :
      ∃C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {M}),
      ∀i,sector i=q→∃b d:Eis,a i*d-b*(c*r i)=1 ∧ (3:Eis)∣b+1 ∧ (9:Eis)∣d ∧
        (!![a i,b;c*r i,d]:Matrix (Fin 2) (Fin 2) Eis).map
          (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq:∃j,sector j=q
    · obtain ⟨j,hj⟩:=hq
      obtain ⟨inverse,_,_,hcompletion⟩:=exists_primary_denominator_completion M c (a j)
        h9M hcPrimary (hcop j).of_mul_right_left
      obtain ⟨b0,d0,hdet0,_,hd0,_,_,hb0,_⟩:=hcompletion (r j) (hr j)
        (hcop j).of_mul_right_right (hrPrimary j)
      refine ⟨(!![a j,b0;c*r j,d0]:Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs:sector i=sector j:=hi.trans hj.symm
      obtain ⟨b,d,hdet,_,hb,hd,hmat⟩:=exists_fixed_matrix_completion_controlled
        3 9 M c (a j) (r j) b0 d0 (-1) 0 hc h3M h9M hdet0
        (by simpa using hb0) (by simpa using hd0)
        (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hdet,by simpa using hb,by simpa using hd,hmat⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i:ι):=hC (sector i) i rfl
  choose b d hdet hb hd hmat using hi
  exact ⟨b,d,C,hdet,hb,hd,hmat⟩

end ShortDraftCRT

namespace CubicEisenstein
open scoped Classical BigOperators ContDiff MatrixGroups

open CompletedGauss CompletedDyadic

theorem sum_smoothedKernel_common_cusp {ι:Type*} [Fintype ι]
    (d:ι→SourceCuspDatum) (w:ι→ℂ) (j:Fin 3) (Q:ℝ)
    (hj:∀i,(d i).index=j) (hQ:∀i,(d i).heightScale=Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑i,w i*(d i).smoothedKernel W X)=fixedRadialCoefficientScalar*
      ∑'p:ThetaFullIndex,
        ((fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
          sourceFrequencyAngle (thetaFullFrequency p))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        CubicReflectionKernel.paperKernel (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2))*
        (∑i,w i*((d i).multiplier*(Q:ℂ))*
          ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency p)*
            ((d i).dualPoint/(sourceCuspScale j:ℂ)))) := by
  let F:ι→ThetaFullIndex→ℂ:=fun i p=>w i*
    ((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
    (sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)))
  have hs (i:ι):Summable (F i):=by
    exact ((d i).smoothedKernel_full_index_norm_summable W a b ha hsupp hW X hX).of_norm.mul_left _
  have he (i:ι):w i*(d i).smoothedKernel W X=∑'p,F i p := by
    rw [(d i).smoothedKernel_full_index]
    simp only [F,tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Summable.tsum_finsetSum (fun i _=>hs i),←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn:=(d i).smoothedFullCoefficient_normalization p
  dsimp only [F]
  calc
    _=w i*(((d i).multiplier*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
      sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)):=by ring
    _=_:=by rw [hn,hj i,hQ i]; ring

end CubicEisenstein

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def coprimalityMask (m:Eis) : Eis→*ℂ where
  toFun n:=if IsCoprime m n then 1 else 0
  map_one' := by simp only [isCoprime_one_right,ite_true]
  map_mul' x y := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hx:IsCoprime m x <;> by_cases hy:IsCoprime m y <;> simp [hx,hy]

lemma coprimalityMask_norm (m n:Eis) : ‖coprimalityMask m n‖≤1 := by
  change ‖if IsCoprime m n then (1:ℂ) else 0‖≤1
  split_ifs <;> norm_num

lemma isCoprime_congr_mod (m x y:Eis) (hxy:m∣x-y) : IsCoprime m x↔IsCoprime m y := by
  obtain ⟨z,hz⟩:=hxy
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨r+s*z,s,?_⟩
    linear_combination hrs-s*hz
  · rintro ⟨r,s,hrs⟩
    refine ⟨r-s*z,s,?_⟩
    linear_combination hrs+s*hz

lemma coprimalityMask_periodic (m:Eis) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {m}) (coprimalityMask m) := by
  intro x y hxy
  change (if IsCoprime m x then (1:ℂ) else 0)=(if IsCoprime m y then 1 else 0)
  rw [isCoprime_congr_mod m x y (Ideal.mem_span_singleton.mp hxy)]

lemma idealRowHom_prime_sixth_mask (m:Eis) (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    idealRowHom (m^6) P=if IsCoprime P (Ideal.span {m}) then 1 else 0 := by
  rw [idealRowHom_prime _ P hg]
  have hm:=canonicalSextic_sixth_power_mask P hg m
  rw [hm]
  rw [SixthPowerAverage.prime_coprime_span_iff]
  by_cases hm:m∈P <;> simp [hm]

theorem idealRowHom_sixth_mask (m:Eis) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (m^6) I=if IsCoprime I (Ideal.span {m}) then 1 else 0 := by
  have hprod (s:Multiset (Ideal Eis))
      (hs:∀P∈s,P.IsMaximal ∧ lambda∉P) :
      idealRowHom (m^6) s.prod=if IsCoprime s.prod (Ideal.span {m}) then 1 else 0 := by
    induction s using Multiset.induction_on with
    | empty =>
      change idealRowHom (m^6) 1=if IsCoprime (1:Ideal Eis) (Ideal.span {m}) then 1 else 0
      simp only [map_one,isCoprime_one_left,ite_true]
    | @cons P s ih =>
      have hp:=hs P (Multiset.mem_cons_self _ _)
      let:P.IsMaximal:=hp.1
      have ht:∀R∈s,R.IsMaximal ∧ lambda∉R:=fun R hR=>hs R (Multiset.mem_cons_of_mem hR)
      rw [Multiset.prod_cons,map_mul,idealRowHom_prime_sixth_mask m P hp.2,ih ht,
        IsCoprime.mul_left_iff]
      by_cases hP:IsCoprime P (Ideal.span {m}) <;>
        by_cases hS:IsCoprime s.prod (Ideal.span {m}) <;> simp [hP,hS]
  have h:=hprod (normalizedFactors I) (fun P hP=>
    ⟨(supported_factors_good I hI P hP).1,(supported_factors_good I hI P hP).2.1⟩)
  rwa [Ideal.prod_normalizedFactors_eq_self hI.1] at h

lemma idealRowHom_sixth_eq_mask (m n:Eis) (hn:Supported (Ideal.span {n})) :
    idealRowHom (m^6) (Ideal.span {n})=coprimalityMask m n := by
  rw [idealRowHom_sixth_mask m _ hn,Ideal.isCoprime_span_singleton_iff]
  change (if IsCoprime n m then (1:ℂ) else 0)=(if IsCoprime m n then 1 else 0)
  rw [isCoprime_comm]

lemma rowTwist_extract_sixth_mask (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hn:Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=Ψ n*coprimalityMask m n*
      idealRowHom (f^4*z) (Ideal.span {n}) := by
  change Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n})=_
  rw [show m^6*f^4*z=m^6*(f^4*z) by ring,idealRowHom_argument_mul,
    idealRowHom_sixth_eq_mask m n hn]
  ring

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicKubota CubicEisenstein ConcreteTraceCRT CubicJacobiGlobal
open CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

theorem embedded_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    eisEmbedding (symbol a (∏i,p i))=
      ∏i,(actualSextic (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk _ a))^2 := by
  change eisEmbedding (idealSymbol (Ideal.span {∏i,p i}) a)=_
  rw [←idealRowHom_square,idealRowHom_product p hg Finset.univ a]
  simp only [ActualEisensteinCubic.finiteSquarefreeRow,actualSextic,Finset.prod_pow]

theorem conjugate_symbol_product {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk _ a) := by
  rw [embedded_symbol_product p hg a,star_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [star_pow,MulChar.star_apply',MulChar.pow_apply' _ (by decide : (2:ℕ)≠0)]

theorem conjugate_symbol_product_frequency {ι : Type*} [Fintype ι]
    (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (a : Eis)
    (σ : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i : Eis⧸Ideal.span {p i})*h i) :
    star (eisEmbedding (symbol a (∏i,p i)))=
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i : Eis⧸Ideal.span {p i})*h i) := by
  rw [conjugate_symbol_product p hg a]
  simp only [ha]

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_field_inverse {F : Type*} [Field F] (a d B : F) (σ ε : Fˣ) (h x : F)
    (had : a*d=1) (ha : a=(σ:F)*h) (hε : B*(σ:F)*(ε:F)=-1) :
    h≠0 ∧ -d*B⁻¹*x=((ε:F)*x)*h⁻¹ := by
  have hh : h≠0 := by
    intro hz
    rw [ha,hz,mul_zero,zero_mul] at had
    exact zero_ne_one had
  have hB : B≠0 := by
    intro hz
    rw [hz,zero_mul,zero_mul] at hε
    exact neg_ne_zero.mpr (one_ne_zero : (1:F)≠0) hε.symm
  have hd : d=((σ:F)*h)⁻¹ := eq_inv_of_mul_eq_one_right (ha ▸ had)
  have he : (ε:F)=-(B*(σ:F))⁻¹ := by
    have heq : (B*(σ:F))*(-(ε:F))=1 := by linear_combination -hε
    exact neg_eq_iff_eq_neg.mp (eq_inv_of_mul_eq_one_right heq)
  refine ⟨hh,?_⟩
  rw [hd,he]
  field_simp

noncomputable local instance A4quotientField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4quotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

lemma A4_active_local {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (a b c0 d : Eis) (hdet : a*d-b*(c0*∏i,p i)=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (x : Eis) (i : ι) :
    h i≠0 ∧
      -(Ideal.Quotient.mk (Ideal.span {p i}) d)*
        (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹*
        Ideal.Quotient.mk (Ideal.span {p i}) x =
      ((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk (Ideal.span {p i}) x)*(h i)⁻¹ := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have had : Ideal.Quotient.mk (Ideal.span {p i}) a*
      Ideal.Quotient.mk (Ideal.span {p i}) d=1 := by
    have he := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hdet
    simpa only [map_sub,map_mul,map_one,hz,mul_zero,sub_zero] using he
  exact A4_field_inverse _ _ _ (σ i) (ε i) (h i) _ had (ha i) (hε i)

lemma A4_complement_inverse {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (c0 U w : Eis) (hbez : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (i : ι) (v t : Eis) (hlocal : t*p i+v*cofactor p i=1) :
    (Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i))⁻¹=
      Ideal.Quotient.mk (Ideal.span {p i}) (w*v) := by
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏k,p k)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr
      (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
  have hp0 : Ideal.Quotient.mk (Ideal.span {p i}) (p i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hw := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hbez
  have hv := congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hlocal
  simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at hw
  simp only [map_add,map_mul,map_one,hp0,mul_zero,zero_add] at hv
  symm
  apply eq_inv_of_mul_eq_one_right
  simp only [map_mul,map_pow]
  calc
    _ = ((Ideal.Quotient.mk _ ramifiedTraceLambda)^3*Ideal.Quotient.mk _ w*
        Ideal.Quotient.mk _ c0)*(Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (cofactor p i)) := by ring
    _ = 1 := by rw [hw,hv,mul_one]

end ShortDraftCusp

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Cusp.ResiduePhases -/

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

namespace ShortDraftCusp
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_bad_modulus_ne_zero (c0:Eis) (hc0:c0≠0) : ramifiedTraceLambda^3*c0≠0 := by
  apply mul_ne_zero _ hc0
  apply pow_ne_zero
  intro hz
  have he:=ramifiedEmbedding_traceLambda
  rw [hz,map_zero] at he
  exact eisLam_ne_zero he.symm

def A4BadPhase (c0:Eis) (hc0:c0≠0) (d U x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (Ideal.Quotient.mk _ (-d*U*x))

lemma A4BadPhase_eq (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    A4BadPhase c0 hc0 d U x =
      ShortDraftTrace.breveE (-(eisEmbedding d*eisEmbedding U*(eisEmbedding x/eisLam^4))/eisEmbedding c0) := by
  change ShortDraftTrace.breveE
    (eisEmbedding (-d*U*x)/(eisEmbedding (ramifiedTraceLambda^3*c0)*eisLam))=_
  simp only [map_mul,map_pow,map_neg,ramifiedEmbedding_traceLambda]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc0]

noncomputable local instance A4phaseField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4phaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem A4_phase_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
      (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹) := by
  let hr : (∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs:=ShortDraftCRT.normalized_crt_pair eisEmbedding ShortDraftTrace.breveE
    ramifiedTraceLambda c0 (∏i,p i) d x U w
    (by simpa only [ramifiedEmbedding_traceLambda] using eisLam_ne_zero)
    (eisEmbedding_ne_zero hc0) (eisEmbedding_ne_zero hr) hbez
  simp only [ramifiedEmbedding_traceLambda] at hs
  rw [hs,←A4BadPhase_eq c0 hc0 d U x]
  congr 1
  have he : ShortDraftTrace.breveE (eisEmbedding (-d*w*x)/(eisLam*eisEmbedding (∏i,p i)))=
      quotientTrace (∏i,p i) hr (Ideal.Quotient.mk _ (-d*w*x)) := by
    simp only [quotientTrace,eisTraceModChar,traceModChar_mk]
    congr 1
    rw [mul_comm eisLam]
  rw [he,addChar_finite_crt_factor (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productElementCRT_mk]
  obtain ⟨t,v,hlocal⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
  have hc:=coordinate_trace_character p hp hcop i t v hlocal
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (quotientTrace (∏i,p i) hr) i (Ideal.Quotient.mk _ (-d*w*x))=_
  change coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
    (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates (∏i,p i) hr) i
    (Ideal.Quotient.mk _ (-d*w*x))=_
  rw [hc]
  change quotientTrace (p i) (hp i)
    (Ideal.Quotient.mk _ v*Ideal.Quotient.mk _ (-d*w*x))=_
  apply congrArg (quotientTrace (p i) (hp i))
  have hinv:=A4_complement_inverse p c0 U w hbez i v t hlocal
  have hphase:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).2
  rw [hinv] at hphase
  convert hphase using 1 ; simp only [map_mul,map_neg] ; ring

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4frequencyField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance A4frequencyFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem A3_A4_frequency_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    star (eisEmbedding (CubicJacobiGlobal.symbol a (∏i,p i)))*
      ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (h i) := by
  rw [conjugate_symbol_product_frequency p hg a σ h ha,
    A4_phase_product p hp hcop a b c0 d U w x hc0 hdet hbez σ ε h ha hε]
  calc
    _ = A4BadPhase c0 hc0 d U x *
      ((∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i:Eis⧸Ideal.span {p i})*h i))*
       ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹)) := by ring
    _ = _ := by
      congr 1
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hn:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).1
      simp only [frequencyMultiplier,ite_eq_right hn]

lemma A4BadPhase_eq_of_residue (c0:Eis) (hc0:c0≠0) (d U d' U' x:Eis)
    (hres:ramifiedTraceLambda^3*c0∣d*U-d'*U') :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d' U' x := by
  unfold A4BadPhase
  congr 1
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd:=dvd_mul_of_dvd_left hres (-x)
  convert hd using 1 ; ring

lemma A4BadPhase_norm (c0:Eis) (hc0:c0≠0) (d U x:Eis) :
    ‖A4BadPhase c0 hc0 d U x‖=1 := by
  rw [A4BadPhase_eq]
  exact breveE_norm _

end ShortDraftCusp

open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

lemma finiteAdditiveFourierCoeff_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (k h : R) :
    finiteAdditiveFourierCoeff (ψ.mulShift k) φ h=
      finiteAdditiveFourierCoeff ψ φ (k*h) := by
  unfold finiteAdditiveFourierCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [AddChar.mulShift_apply]
  congr 2
  ring

theorem finite_fourier_weighted_shift_crt {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e : T≃+*∀i,R i)
    (ψ : AddChar T ℂ) (ψi : ∀i,AddChar (R i) ℂ) (k : ∀i,(R i)ˣ)
    (hψ : ∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ κ : ∀i,R i→ℂ) :
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun x=>∏i,φ i (e x i)) h *
      ∏i,κ i ((k i:R i)*e h i))=
      ∏i,∑h:R i,finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h := by
  rw [finite_fourier_weighted_crt R e ψ φ (fun i h=>κ i ((k i:R i)*h))]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hψ,finiteAdditiveFourierCoeff_mulShift]
  exact Equiv.sum_comp (k i).mulLeft
    (fun h:R i=>finiteAdditiveFourierCoeff (ψi i) (φ i) h*κ i h)

theorem finiteAdditiveFourierCoeff_pair {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T≃+*R×S) (ψ : AddChar T ℂ) (φ : R→ℂ) (f : S→ℂ) (h : T) :
    finiteAdditiveFourierCoeff ψ (fun t=>φ (e t).1*f (e t).2) h=
      finiteAdditiveFourierCoeff (leftAddChar e ψ) φ (e h).1 *
      finiteAdditiveFourierCoeff (rightAddChar e ψ) f (e h).2 := by
  have hs : (∑x:T,(φ (e x).1*f (e x).2)*ψ (-h*x))=
      (∑x:R,φ x*leftAddChar e ψ (-(e h).1*x))*
        (∑y:S,f y*rightAddChar e ψ (-(e h).2*y)) := by
    calc
      _ = ∑x:T,(φ (e x).1*leftAddChar e ψ (-(e h).1*(e x).1))*
          (f (e x).2*rightAddChar e ψ (-(e h).2*(e x).2)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [addChar_crt_factor e ψ (-h*x)]
        simp only [map_mul,map_neg,Prod.fst_mul,Prod.snd_mul,Prod.fst_neg,Prod.snd_neg]
        ring
      _ = ∑x:R×S,(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)) :=
        Equiv.sum_comp e.toEquiv (fun x:R×S=>(φ x.1*leftAddChar e ψ (-(e h).1*x.1))*
          (f x.2*rightAddChar e ψ (-(e h).2*x.2)))
      _ = _ := by rw [Fintype.sum_prod_type,Finset.sum_mul_sum]
  have hc : (Fintype.card T:ℂ)=(Fintype.card R:ℂ)*(Fintype.card S:ℂ) := by
    rw [Fintype.card_congr e.toEquiv,Fintype.card_prod,Nat.cast_mul]
  simp only [finiteAdditiveFourierCoeff,hs,hc]
  ring

end IdealGaussCRT

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance canonicalShiftField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance canonicalShiftFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_finite_reflection_shifted_crt {ι T : Type*} [Fintype ι]
    [CommRing T] [Fintype T]
    (P : ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e : T≃+*∀i,Eis⧸P i) (ψ : AddChar T ℂ)
    (ψi : ∀i,AddChar (Eis⧸P i) ℂ) (hψi : ∀i,(ψi i).IsPrimitive)
    (k : ∀i,(Eis⧸P i)ˣ)
    (hshift : ∀i,coordinateAddChar (fun i=>Eis⧸P i) e ψ i=(ψi i).mulShift (k i:Eis⧸P i))
    (hg : ∀i,lambda∉P i) (hchar : ∀i,ringChar (Eis⧸P i)≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6) (σ ε : ∀i,(Eis⧸P i)ˣ) (x : ∀i,Eis⧸P i) :
    let χ := fun i=>actualSextic (P i) (hg i)
    (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  let χ := fun i=>actualSextic (P i) (hg i)
  let f := fun i=>frequencyRow (χ i) (ψi i) (j i) (σ i) (ε i) (x i)
  have hsum : (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=
      ∑h:∀i,Eis⧸P i,∏i,f i (h i) := by
    rw [finite_fourier_weighted_shift_crt (fun i=>Eis⧸P i) e ψ ψi k hshift
      (fun i t=>(χ i^j i) t) (fun i=>frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i))]
    exact Fintype.prod_sum f
  have hactive (i : ι) : (∑h:(Eis⧸P i)ˣ,f i h)=
      (((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i) := by
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψi i)
      (hψi i) (j i) (hj i) (σ i) (ε i) (x i)
  have hzero (i : ι) : f i 0=if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0 := by
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψi i) (j i) (hj i) (σ i) (ε i) (x i)
  change (∑h:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,(χ i^j i) (e t i)) h*
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i) ((k i:Eis⧸P i)*e h i))=_
  rw [hsum,FixedRayActiveSet.product_sum_by_active_set (fun i=>Eis⧸P i) f]
  simp only [hactive,hzero]
  rfl

end LocalReflectionBrackets

namespace FiniteGaussPhase

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem exists_product_trace_shifts {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∃k : ∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k i:Eis⧸Ideal.span {p i})=1) ∧
      ∀i,coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k i:Eis⧸Ideal.span {p i}) := by
  have hone (i : ι) : ∃k : (Eis⧸Ideal.span {p i})ˣ,
      Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*(k:Eis⧸Ideal.span {p i})=1 ∧
      coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
        (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
          (quotientTrace (p i) (hp i)).mulShift (k:Eis⧸Ideal.span {p i}) := by
    obtain ⟨u,v,hbez⟩:=bezout_of_principal_coprime (cofactor_coprime p hcop i)
    have hv : Ideal.Quotient.mk (Ideal.span {p i}) v*
        Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)=1 := by
      simpa only [mul_comm] using bezout_inverse_left hbez
    refine ⟨Units.mkOfMulEqOne _ _ hv,?_,?_⟩
    · simpa only [Units.val_mkOfMulEqOne,mul_comm] using hv
    · exact coordinate_trace_character p hp hcop i u v hbez
  choose k hki hkψ using hone
  exact ⟨k,hki,hkψ⟩

noncomputable def productTraceShift {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) :
    ∀i,(Eis⧸Ideal.span {p i})ˣ :=
  (exists_product_trace_shifts p hp hcop).choose

lemma productTraceShift_inverse {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)*
      (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})=1 :=
  (exists_product_trace_shifts p hp hcop).choose_spec.1 i

lemma productTraceShift_character {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i}))) (i:ι) :
    coordinateAddChar (fun i=>Eis⧸Ideal.span {p i}) (productElementCRT p hcop)
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))) i=
        (quotientTrace (p i) (hp i)).mulShift
          (productTraceShift p hp hcop i:Eis⧸Ideal.span {p i}) :=
  (exists_product_trace_shifts p hp hcop).choose_spec.2 i

end

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_factor {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) (H:Eis⧸Ideal.span {∏i,p i}) :
    finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H=
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i)
      ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i) := by
  rw [finiteAdditiveFourierCoeff_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [productTraceShift_character,finiteAdditiveFourierCoeff_mulShift]

theorem product_trace_fourier_weighted {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ κ : ∀i,(Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H *
      ∏i,κ i ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∏i,∑h:Eis⧸Ideal.span {p i},finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) h*κ i h := by
  exact finite_fourier_weighted_shift_crt (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ κ

end FiniteGaussPhase

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT CompletedGauss FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance productReflectionField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance productReflectionFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_product_reflection_crt {ι : Type*} [Fintype ι]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hchar : ∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (j : ι→ℕ) (hj : ∀i,j i<6)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (x : ∀i,Eis⧸Ideal.span {p i})
    [Fintype (Eis⧸Ideal.span {∏i,p i})] :
    let χ := fun i=>actualSextic (Ideal.span {p i}) (hg i)
    let ψ := quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let ψi := fun i=>quotientTrace (p i) (hp i)
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff ψ
      (principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
        (span_finset_prod Finset.univ p)) H *
      ∏i,frequencyMultiplier (χ i) (ψi i) (σ i) (ε i) (x i)
        ((productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈A,(((χ i)⁻¹)^2) (σ i)*phase (χ i) (ψi i) (j i) (ε i)*bracket (χ i) (j i) (x i))*
        (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸Ideal.span {p i}):ℂ)⁻¹ else 0) := by
  let e:=productElementCRT p hcop
  have hrow : principalSexticRow (fun i=>Ideal.span {p i}) hcop hg j (∏i,p i)
      (span_finset_prod Finset.univ p)=
      fun t=>∏i,(actualSextic (Ideal.span {p i}) (hg i)^j i) (e t i) := by
    funext t
    rfl
  dsimp only
  rw [hrow]
  exact canonical_finite_reflection_shifted_crt (fun i=>Ideal.span {p i}) e _
    (fun i=>quotientTrace (p i) (hp i))
    (fun i=>GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop)
    hg hchar j hj σ ε x

end LocalReflectionBrackets

open scoped Classical BigOperators

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A4BadPhase_strong_sector (M c0 r r0 d d0 U U0 x:Eis) (hc0:c0≠0)
    (hM:ramifiedTraceLambda^3∣M) (hc:c0∣M)
    (hr:M^2∣r-r0) (hd:M*c0∣d-d0)
    (hcop:IsCoprime (ramifiedTraceLambda^3*c0) r)
    (hU:ramifiedTraceLambda^3*c0∣U*r-1)
    (hU0:ramifiedTraceLambda^3*c0∣U0*r0-1) :
    A4BadPhase c0 hc0 d U x=A4BadPhase c0 hc0 d0 U0 x := by
  obtain ⟨hrr,hdd⟩:=ShortDraftCRT.strong_sector_additive_congruences
    M ramifiedTraceLambda c0 r r0 d d0 hM hc hr hd
  apply A4BadPhase_eq_of_residue
  have he:=ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c0) r r0 U U0 d d0 hcop hrr hU hU0 hdd
  have hn:=dvd_neg.mpr he
  convert hn using 1 ; ring

def A4PhaseFromResidue (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) : ℂ :=
  quotientTrace (ramifiedTraceLambda^3*c0) (A4_bad_modulus_ne_zero c0 hc0)
    (v*Ideal.Quotient.mk _ x)

lemma A4BadPhase_as_fixed_residue (c0:Eis) (hc0:c0≠0) (d U:Eis) :
    A4BadPhase c0 hc0 d U=
      A4PhaseFromResidue c0 hc0 (Ideal.Quotient.mk _ (-d*U)) := by
  funext x
  simp only [A4BadPhase,A4PhaseFromResidue,map_mul]

lemma A4PhaseFromResidue_range (c0:Eis) (hc0:c0≠0) :
    (Set.range (A4PhaseFromResidue c0 hc0)).Finite ∧
      (Set.range (A4PhaseFromResidue c0 hc0)).ncard≤
        Ideal.absNorm (Ideal.span {ramifiedTraceLambda^3*c0}) := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  refine ⟨Set.finite_range _,?_⟩
  have h:=Set.ncard_image_le (s:=Set.univ) (f:=A4PhaseFromResidue c0 hc0)
  simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,Submodule.cardQuot_apply] using h

end ShortDraftCusp

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

variable (Ψ Φ:Eis→*ℂ) (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n)
include h

lemma columnWeight_congr_primary (I:Ideal Eis) : columnWeight Ψ I=columnWeight Φ I := by
  by_cases hi:primaryGenerator I=0
  · simp only [columnWeight,squarefreeGaussCoefficient,hi,ne_eq,not_true_eq_false,and_false,
      dite_false,zero_mul]
  · rw [columnWeight,columnWeight,h _ (primaryGenerator_spec I hi).2]

lemma cubeWeight_congr_primary (I:Ideal Eis) : cubeWeight Ψ I=cubeWeight Φ I := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Ψ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)=star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Φ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)
  by_cases hi:primaryGenerator I=0
  · simp only [hi,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
      div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
  · rw [h _ (primaryGenerator_spec I hi).2]

theorem completedT_congr_primary (W:ℝ→ℂ) (X:ℝ) : completedT Ψ W X=completedT Φ W X := by
  unfold completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

lemma completedMellinCoefficient_congr_primary (p:CompletedMellinIndex) :
    completedMellinCoefficient Ψ p=completedMellinCoefficient Φ p := by
  unfold completedMellinCoefficient
  rw [columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

theorem completedBesselProfile_congr_primary (q:ℝ) :
    completedBesselProfile Ψ q=completedBesselProfile Φ q := by
  have he:completedMellinCoefficient Ψ=completedMellinCoefficient Φ:=
    funext (completedMellinCoefficient_congr_primary Ψ Φ h)
  simp only [completedBesselProfile,he]

end CompletedGauss

namespace CubicEisenstein
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
lemma fixedThetaTwist_congr_primary (Ψ Φ:Eis→*ℂ)
    (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n) : fixedThetaTwist Ψ=fixedThetaTwist Φ := by
  funext n
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary Ψ n hn,fixedThetaTwist_primary Φ n hn,h n hn]
  · rw [fixedThetaTwist_not_primary Ψ n hn,fixedThetaTwist_not_primary Φ n hn]
end CubicEisenstein

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

def finiteCrossNumerator (a c l:Eis) (p h:ι→Eis) : Eis :=
  a*(∏i,p i)+l^2*c*∑i,h i*cofactor p i

lemma prime_dvd_other_cofactor (p:ι→Eis) {i k:ι} (hik:i≠k) : p i∣cofactor p k := by
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨hik,Finset.mem_univ i⟩)

lemma finiteCrossNumerator_local (a c l:Eis) (p h:ι→Eis) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (finiteCrossNumerator a c l p h)=
      Ideal.Quotient.mk (Ideal.span {p i}) (l^2*c*cofactor p i)*
        Ideal.Quotient.mk (Ideal.span {p i}) (h i) := by
  let q:=Ideal.Quotient.mk (Ideal.span {p i})
  have hz:q (∏k,p k)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨cofactor p i, (prime_mul_cofactor p i).symm⟩
  have hs:(∑k,q (h k)*q (cofactor p k))=q (h i)*q (cofactor p i) := by
    apply Finset.sum_eq_single i
    · intro k hk hki
      have hk0:q (cofactor p k)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr (prime_dvd_other_cofactor p hki.symm))
      rw [hk0,mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  change q (finiteCrossNumerator a c l p h)=q (l^2*c*cofactor p i)*q (h i)
  simp only [finiteCrossNumerator,map_add,map_mul,map_sum,map_pow,hz,mul_zero,zero_add,hs]
  ring

lemma finiteCrossNumerator_fixed (N a c l:Eis) (p h:ι→Eis)
    (hh:∀i,N∣h i) : N∣finiteCrossNumerator a c l p h-a*(∏i,p i) := by
  have hs:N∣∑i,h i*cofactor p i:=Finset.dvd_sum (fun i _=>dvd_mul_of_dvd_left (hh i) _)
  convert dvd_mul_of_dvd_right hs (l^2*c) using 1 ; simp [finiteCrossNumerator]

lemma finiteCrossNumerator_fixed_sector {κ:Type*} [Fintype κ]
    (M a c l:Eis) (p h:ι→Eis) (p0 h0:κ→Eis)
    (hc:c∣M) (hh:∀i,M^2∣h i) (hh0:∀i,M^2∣h0 i)
    (hr:M^2∣(∏i,p i)-(∏i,p0 i)) :
    M*c∣finiteCrossNumerator a c l p h-finiteCrossNumerator a c l p0 h0 := by
  have hmc:M*c∣M^2:=by simpa only [pow_two] using mul_dvd_mul_left M hc
  apply hmc.trans
  have h1:=finiteCrossNumerator_fixed (M^2) a c l p h hh
  have h0:=finiteCrossNumerator_fixed (M^2) a c l p0 h0 hh0
  have h2:=dvd_mul_of_dvd_right hr a
  convert dvd_sub (dvd_add h1 h2) h0 using 1 ; ring

lemma finiteCrossNumerator_coprime (a c l:Eis) (p h:ι→Eis)
    (hbase:IsCoprime a c) (hpair:Pairwise (Function.onFun IsCoprime p))
    (hc:∀i,IsCoprime c (p i)) (hl:∀i,IsCoprime l (p i))
    (hh:∀i,IsCoprime (h i) (p i)) :
    IsCoprime (finiteCrossNumerator a c l p h) (c*∏i,p i) := by
  have hmodc:c∣finiteCrossNumerator a c l p h-a*(∏i,p i):=by
    refine ⟨l^2*(∑i,h i*cofactor p i),?_⟩
    unfold finiteCrossNumerator
    ring
  have hcR:IsCoprime c (∏i,p i):=IsCoprime.prod_right (fun i _=>hc i)
  have hca:IsCoprime c (finiteCrossNumerator a c l p h):=
    (CanonicalRowCompletion.isCoprime_congr_mod c _ _ hmodc).mpr (hbase.symm.mul_right hcR)
  apply hca.symm.mul_right
  apply IsCoprime.prod_right
  intro i hi
  have hcof:IsCoprime (p i) (cofactor p i):=
    IsCoprime.prod_right (fun k hk=>hpair (Ne.symm (Finset.mem_erase.mp hk).1))
  have hterm:IsCoprime (p i) (l^2*c*cofactor p i*h i):=
    (((hl i).symm.pow_right : IsCoprime (p i) (l^2)).mul_right (hc i).symm).mul_right hcof |>.mul_right (hh i).symm
  have he:=finiteCrossNumerator_local a c l p h i
  rw [←map_mul] at he
  have hd:p i∣finiteCrossNumerator a c l p h-l^2*c*cofactor p i*h i:=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ((CanonicalRowCompletion.isCoprime_congr_mod (p i) _ _ hd).mpr hterm).symm

end ShortDraftCRT

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts -/

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

open scoped Classical BigOperators

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

omit [Fintype ι] in
theorem exists_strong_unit_frequency_lifts (M:Eis) (p:ι→Eis)
    (hM:∀i,IsCoprime M (p i)) (x:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ∃h:ι→Eis,(∀i,M^2∣h i) ∧
      (∀i,Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i})) ∧
      ∀i,IsCoprime (h i) (p i) := by
  have hx (i:ι) := exists_frequency_lift (M^2) (p i)
    (Quotient.out (x i:Eis⧸Ideal.span {p i})) (hM i).pow_left
  choose h hh hd using hx
  have he (i:ι):Ideal.Quotient.mk (Ideal.span {p i}) (h i)=(x i:Eis⧸Ideal.span {p i}) := by
    calc
      _=Ideal.Quotient.mk (Ideal.span {p i}) (Quotient.out (x i:Eis⧸Ideal.span {p i})) :=
        Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (hd i))
      _=x i:=Ideal.Quotient.mk_out _
  refine ⟨h,hh,he,?_⟩
  intro i
  apply IsCoprime.symm
  apply (isUnit_quotient_span_iff (p i) (h i)).mp
  rw [he]
  exact (x i).isUnit

theorem finiteCrossNumerator_fraction (a c l:Eis) (p h:ι→Eis)
    (hc:c≠0) (hp:∀i,p i≠0) :
    eisEmbedding (finiteCrossNumerator a c l p h)/eisEmbedding (c*∏i,p i)=
      eisEmbedding a/eisEmbedding c+eisEmbedding l^2*
        ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
  have hR:(∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hcC:=eisEmbedding_ne_zero hc
  have hRC:=eisEmbedding_ne_zero hR
  have hs:eisEmbedding (∑i,h i*cofactor p i)/eisEmbedding (∏i,p i)=
      ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
    rw [map_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi:=eisEmbedding_ne_zero (hp i)
    have hr:eisEmbedding (p i)*eisEmbedding (cofactor p i)=eisEmbedding (∏i,p i) := by
      rw [←map_mul,prime_mul_cofactor]
    rw [map_mul]
    apply (div_eq_div_iff hRC hpi).mpr
    linear_combination eisEmbedding (h i)*hr
  simp only [finiteCrossNumerator,map_add,map_mul,map_pow]
  rw [←hs]
  field_simp [hcC,hRC]

end ShortDraftCRT

open scoped BigOperators Classical

namespace IdealGaussCRT
open CubicEisenstein

theorem finite_fourier_sum_reindex {ι T : Type*} [Fintype ι]
    (R : ι→Type*) [CommRing T] [∀i,CommRing (R i)]
    [Fintype T] [∀i,Fintype (R i)] (e:T≃+*∀i,R i)
    (ψ:AddChar T ℂ) (ψi:∀i,AddChar (R i) ℂ) (k:∀i,(R i)ˣ)
    (hψ:∀i,coordinateAddChar R e ψ i=(ψi i).mulShift (k i:R i))
    (φ:∀i,R i→ℂ) (weight:(∀i,R i)→ℂ) :
    (∑H:T,finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H*
      weight (fun i=>(k i:R i)*e H i))=
    ∑h:∀i,R i,(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h := by
  let E:T≃(∀i,R i):=e.toEquiv.trans (Equiv.piCongrRight (fun i=>(k i).mulLeft))
  have hc (H:T) : finiteAdditiveFourierCoeff ψ (fun t=>∏i,φ i (e t i)) H=
      ∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) ((k i:R i)*e H i) := by
    rw [finiteAdditiveFourierCoeff_crt]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hψ,finiteAdditiveFourierCoeff_mulShift]
  simp only [hc]
  exact Equiv.sum_comp E
    (fun h:∀i,R i=>(∏i,finiteAdditiveFourierCoeff (ψi i) (φ i) (h i))*weight h)

end IdealGaussCRT

namespace FiniteGaussPhase
open ActualEisensteinCubic CubicEisenstein IdealGaussCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem product_trace_fourier_sum_reindex {ι : Type*} [Fintype ι]
    (p:ι→Eis) (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    [Fintype (Eis⧸Ideal.span {∏i,p i})] [∀i,Fintype (Eis⧸Ideal.span {p i})]
    (φ:∀i,(Eis⧸Ideal.span {p i})→ℂ)
    (weight:(∀i,Eis⧸Ideal.span {p i})→ℂ) :
    (∑H:Eis⧸Ideal.span {∏i,p i},finiteAdditiveFourierCoeff
      (quotientTrace (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
      (fun t=>∏i,φ i (productElementCRT p hcop t i)) H*
      weight (fun i=>(productTraceShift p hp hcop i:Eis⧸Ideal.span {p i})*productElementCRT p hcop H i))=
    ∑h:∀i,Eis⧸Ideal.span {p i},
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (φ i) (h i))*weight h := by
  exact finite_fourier_sum_reindex (fun i=>Eis⧸Ideal.span {p i})
    (productElementCRT p hcop) _ (fun i=>quotientTrace (p i) (hp i))
    (productTraceShift p hp hcop) (productTraceShift_character p hp hcop) φ weight

end FiniteGaussPhase

namespace FixedRayActiveSet

lemma sum_nonzero_ite {F : Type*} [Field F] [Fintype F] (f:F→ℂ) :
    (∑x:F,if x≠0 then f x else 0)=∑u:Fˣ,f (u:F) := by
  calc
    _ = ∑x∈(Finset.univ:Finset F).filter (fun x=>x≠0),f x := by rw [Finset.sum_filter]
    _ = ∑x:{x:F//x≠0},f x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = _ := (Equiv.sum_comp unitsEquivNeZero (fun x:{x:F//x≠0}=>f x)).symm

def activeStratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)] (A:Finset ι) :
    Finset (∀i,F i) := Finset.univ.filter (fun h=>∀i,h i≠0↔i∈A)

theorem sum_active_stratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (A:Finset ι) (f:∀i,F i→ℂ) :
    (∑h∈activeStratum F A,∏i,f i (h i))=
      (∏i∈A,∑u:(F i)ˣ,f i (u:F i))*
        (∏i∈(Finset.univ:Finset ι)\A,f i 0) := by
  classical
  let g:=fun i (x:F i)=>if (x≠0↔i∈A) then f i x else 0
  have hs : (∑h∈activeStratum F A,∏i,f i (h i))=
      ∏i,∑x:F i,g i x := by
    rw [activeStratum,Finset.sum_filter]
    calc
      _ = ∑h:∀i,F i,∏i,g i (h i) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact (Fintype.prod_ite_zero (p:=fun i=>h i≠0↔i∈A) (f:=fun i=>f i (h i))).symm
      _ = _ := (Fintype.prod_sum g).symm
  have hg (i:ι) : (∑x:F i,g i x)=if i∈A then ∑u:(F i)ˣ,f i (u:F i) else f i 0 := by
    by_cases hi:i∈A
    · simpa only [g,hi,iff_true,ite_true] using sum_nonzero_ite (f i)
    · simp [g,hi]
  rw [hs]
  simp only [hg,Finset.prod_ite]
  have ha : (Finset.univ:Finset ι).filter (fun i=>i∈A)=A := by ext i;simp
  have hn : (Finset.univ:Finset ι).filter (fun i=>i∉A)=(Finset.univ:Finset ι)\A := by ext i;simp
  rw [ha,hn]

theorem sum_by_active_strata {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (weight:(∀i,F i)→ℂ) :
    (∑h:∀i,F i,weight h)=
      ∑A∈(Finset.univ:Finset ι).powerset,∑h∈activeStratum F A,weight h := by
  classical
  symm
  simp only [activeStratum,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  let A:Finset ι:=Finset.univ.filter (fun i=>h i≠0)
  have he : ∀i,h i≠0↔i∈A := by intro i;simp [A]
  rw [Finset.sum_eq_single A]
  · simp only [he,implies_true,ite_true]
  · intro B hB hBA
    have hbad : ¬(∀i,h i≠0↔i∈B) := by
      intro hgood
      apply hBA
      ext i
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using (hgood i).symm
    simp only [hbad,ite_false]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim

end FixedRayActiveSet

namespace LocalReflectionBrackets
open ActualEisensteinCubic CubicEisenstein CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem canonical_active_stratum {ι : Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hchar:∀i,ringChar (Eis⧸P i)≠2)
    (ψ:∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (A:Finset ι) (j:ι→ℕ) (hj:∀i,j i<6)
    (σ ε:∀i,(Eis⧸P i)ˣ) (x:∀i,Eis⧸P i) :
    (∑h∈FixedRayActiveSet.activeStratum (fun i=>Eis⧸P i) A,
      ∏i,frequencyRow (actualSextic (P i) (hg i)) (ψ i) (j i) (σ i) (ε i) (x i) (h i))=
    (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (P i) (hg i)) (ψ i) (j i) (ε i)*
      bracket (actualSextic (P i) (hg i)) (j i) (x i))*
    (∏i∈(Finset.univ:Finset ι)\A,if j i=0 then 1-(Fintype.card (Eis⧸P i):ℂ)⁻¹ else 0) := by
  rw [FixedRayActiveSet.sum_active_stratum]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_units (P i) (hg i) (hchar i) (ψ i) (hψ i) (j i) (hj i) (σ i) (ε i) (x i)
  · apply Finset.prod_congr rfl
    intro i hi
    exact canonical_frequencyRow_zero (P i) (hg i) (hchar i) (ψ i) (j i) (hj i) (σ i) (ε i) (x i)

end LocalReflectionBrackets

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_dvd_of_lambda_dvd (h:Eis) (hh:lambda∣h) :
    ramifiedTraceLambda∣h := by
  obtain ⟨q,hq⟩:=hh
  refine ⟨(paperLambdaUnit⁻¹:Eisˣ)*q,?_⟩
  change h=paperLambda*((paperLambdaUnit⁻¹:Eisˣ)*q)
  rw [paperLambda_eq,hq]
  have hu : (paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)=1 := by
    simpa only [Units.val_mul,Units.val_one] using
      congrArg (fun v:Eisˣ=>(v:Eis)) (mul_inv_cancel paperLambdaUnit)
  calc
    _=(paperLambdaUnit:Eis)*(paperLambdaUnit⁻¹:Eisˣ)*(lambda*q) := by rw [hu,one_mul]
    _=_ := by ring

def paperLambdaQuotient (h:Eis) : Eis :=
  if hh:ramifiedTraceLambda∣h then hh.choose else 0

lemma paperLambdaQuotient_mul (h:Eis) (hh:ramifiedTraceLambda∣h) :
    ramifiedTraceLambda*paperLambdaQuotient h=h := by
  simp only [paperLambdaQuotient,dite_eq_left hh]
  exact hh.choose_spec.symm

lemma sourceCuspCoefficients_ramified_divisibility (j:Fin 3) (hj:j≠0) (h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) : ramifiedTraceLambda∣h := by
  apply ramifiedTraceLambda_dvd_of_lambda_dvd
  fin_cases j
  · exact (hj rfl).elim
  · exact (ramifiedBesselValue_exact_lambda_valuation false h hh).1
  · exact (ramifiedBesselValue_exact_lambda_valuation true h hh).1

def sourceCuspPhaseNumerator (j:Fin 3) (u h:Eis) : Eis :=
  if j=0 then ramifiedTraceLambda*u^2*h else -u^2*paperLambdaQuotient h

lemma sourceCuspPhaseNumerator_embedding (j:Fin 3) (u h:Eis)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    eisEmbedding (sourceCuspPhaseNumerator j u h)=
      -eisLam^4*cuspFrequency h*(eisEmbedding u)^2/(sourceCuspScale j:ℂ) := by
  by_cases hj:j=0
  · subst j
    simp only [sourceCuspPhaseNumerator,ite_true,map_mul,map_pow,
      ramifiedEmbedding_traceLambda,cuspFrequency,sourceCuspScale]
    norm_num only [Matrix.cons_val_zero,Complex.ofReal_one,div_one]
    field_simp [eisLam_ne_zero]
    linear_combination (eisEmbedding h*(eisEmbedding u)^2)*TraceLambdaPhase.eisLam_sq
  · have hdiv:=sourceCuspCoefficients_ramified_divisibility j hj h hh
    have hprod:=congrArg eisEmbedding (paperLambdaQuotient_mul h hdiv)
    have hscale:sourceCuspScale j=3 := by fin_cases j <;> simp_all [sourceCuspScale]
    have hfour:eisLam^4=(9:ℂ) := by
      calc
        eisLam^4=(eisLam^2)^2:=by ring
        _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num
    rw [sourceCuspPhaseNumerator,ite_eq_right hj]
    simp only [map_mul,map_neg,map_pow]
    rw [cuspFrequency,hscale,←hprod,map_mul,ramifiedEmbedding_traceLambda,hfour]
    norm_num only [Complex.ofReal_ofNat]
    field_simp [eisLam_ne_zero]
    ; ring

lemma sourceCuspPhaseNumerator_phase (j:Fin 3) (u h c d:Eis) (hc:c≠0)
    (hh:(sourceCuspCoefficients j).value h≠0) :
    ShortDraftTrace.breveE (cuspFrequency h*(eisEmbedding u)^2*
      (eisEmbedding d/eisEmbedding c)/(sourceCuspScale j:ℂ))=
    ShortDraftTrace.breveE (-(eisEmbedding d*
      (eisEmbedding (sourceCuspPhaseNumerator j u h)/eisLam^4))/eisEmbedding c) := by
  rw [sourceCuspPhaseNumerator_embedding j u h hh]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc,
    Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne']

end CubicEisenstein

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve QuadraticAllOddCRT
open ConcreteTraceCRT UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def cubicTwoSupplement : Eis→*ℂ where
  toFun n:=(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]

def quadraticTwoSupplement : Eis→*ℂ :=
  InitialMeanSquare.normCharacter (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))

def twoSupplement : Eis→*ℂ := cubicTwoSupplement^2*quadraticTwoSupplement

lemma cubicTwoSupplement_norm (n:Eis) : ‖cubicTwoSupplement n‖≤1 := by
  change ‖(actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2)
    (Ideal.Quotient.mk cubicTwoIdeal n)‖≤1
  exact FiniteRayExpansion.norm_char_le_one _ _

lemma twoSupplement_norm (n:Eis) : ‖twoSupplement n‖≤1 := by
  change ‖cubicTwoSupplement n^2*quadraticTwoSupplement n‖≤1
  rw [norm_mul,norm_pow]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    _).trans (InitialMeanSquare.normCharacter_norm_le_one _ n)
  exact pow_le_one₀ (norm_nonneg _) (cubicTwoSupplement_norm n)

lemma cubicTwoSupplement_periodic (x y:Eis) (hxy:x-y∈Ideal.span {(8:Eis)}) :
    cubicTwoSupplement x=cubicTwoSupplement y := by
  have h2:x-y∈cubicTwoIdeal:=by
    obtain ⟨k,hk⟩:=Ideal.mem_span_singleton.mp hxy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨-4*k,?_⟩
    change x-y=(-2:Eis)*(-4*k)
    rw [hk]
    ring
  change (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal x)=
    (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal y)
  rw [Ideal.Quotient.eq.mpr h2]

lemma twoSupplement_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(8:Eis)}) twoSupplement := by
  intro x y hxy
  change cubicTwoSupplement x^2*quadraticTwoSupplement x=
    cubicTwoSupplement y^2*quadraticTwoSupplement y
  rw [cubicTwoSupplement_periodic x y hxy]
  congr 1
  exact CanonicalCoefficientClass.normCharacter_factorsModulo _ x y hxy

lemma idealRowHom_two_prime (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hs:Supported (Ideal.span {p})) :
    idealRowHom (2:Eis) (Ideal.span {p})=twoSupplement p := by
  let:(Ideal.span {p}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  obtain ⟨hg,hc⟩:=supported_prime_data p hp hs
  have h2:idealRowHom (2:Eis) (Ideal.span {p})^2=cubicTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_four_eq_fixed_two (Ideal.span {p}) hg p rfl hprimary
    have hfour:Ideal.Quotient.mk (Ideal.span {p}) (4:Eis)=
      (Ideal.Quotient.mk (Ideal.span {p}) (2:Eis))^2:=by norm_num [map_ofNat]
    rw [hfour,map_pow] at he
    change (actualSextic (Ideal.span {p}) hg) (Ideal.Quotient.mk _ 2)^2=
      (actualSextic cubicTwoIdeal cubicTwoIdeal_good ^ 2) (Ideal.Quotient.mk cubicTwoIdeal p)
    rw [canonicalSextic_pow_two]
    exact he
  have h3:idealRowHom (2:Eis) (Ideal.span {p})^3=quadraticTwoSupplement p:=by
    rw [idealRowHom_prime _ _ hg,←MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),actualSextic_cube_quadratic]
    change ((quadraticChar (Eis⧸Ideal.span {p}) (Ideal.Quotient.mk _ (2:Eis)):ℤ):ℂ)=_
    simp only [map_ofNat]
    rw [quadraticChar_two hc]
    have hn:Ideal.absNorm (Ideal.span {p})=Fintype.card (Eis⧸Ideal.span {p}):=by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    change ((ZMod.χ₈ (Fintype.card (Eis⧸Ideal.span {p})):ℤ):ℂ)=
      ((ZMod.χ₈ (Ideal.absNorm (Ideal.span {p})):ℤ):ℂ)
    rw [hn]
  have hn2:(2:Eis)∉Ideal.span {p}:=by
    intro hz
    have he: (2:Eis⧸Ideal.span {p})=0:=by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hz
    exact Ring.two_ne_zero hc he
  have h6:idealRowHom (2:Eis) (Ideal.span {p})^6=1:=by
    rw [idealRowHom_prime _ _ hg]
    have he:=canonicalSextic_sixth_power_mask (Ideal.span {p}) hg (2:Eis)
    change actualSextic _ hg (Ideal.Quotient.mk _ ((2:Eis)^6))=_ at he
    simpa only [map_pow,ite_eq_right hn2] using he
  calc
    _=idealRowHom (2:Eis) (Ideal.span {p})*idealRowHom (2:Eis) (Ideal.span {p})^6:=by rw [h6,mul_one]
    _=idealRowHom (2:Eis) (Ideal.span {p})^3*(idealRowHom (2:Eis) (Ideal.span {p})^2)^2:=by ring
    _=twoSupplement p:=by
      rw [h2,h3]
      change quadraticTwoSupplement p*cubicTwoSupplement p^2=cubicTwoSupplement p^2*quadraticTwoSupplement p
      ring

theorem idealRowHom_two_formula (n:Eis) (hn:lambda^2∣n-1)
    (hs:Supported (Ideal.span {n})) :
    idealRowHom (2:Eis) (Ideal.span {n})=twoSupplement n := by
  have hn0:n≠0:=by intro hz;apply hs.1;simp [hz]
  obtain ⟨s,hprod,hfactors⟩:=exists_primary_prime_factorization n hn0 hn
  rw [←hprod] at hs ⊢
  clear hprod hn hn0 n
  induction s using Multiset.induction_on with
  | empty=>simp only [Multiset.prod_zero,Ideal.span_singleton_one,←Ideal.one_eq_top,map_one]
  | @cons p s ih=>
    have hp:=hfactors p (Multiset.mem_cons_self _ _)
    have htail:∀q∈s,Prime q ∧ lambda^2∣q-1:=fun q hq=>hfactors q (Multiset.mem_cons_of_mem hq)
    have hsplit:Supported (Ideal.span {p}) ∧ Supported (Ideal.span {s.prod}):=by
      simpa only [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,supported_mul_iff] using hs
    rw [Multiset.prod_cons,←Ideal.span_singleton_mul_span_singleton,map_mul,
      idealRowHom_two_prime p hp.1 hp.2 hsplit.1,ih hsplit.2 htail,map_mul]

end

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def supportedIdealRow (a:Eis) : Eis→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom a (Ideal.span {n}) else 0
  map_one' := by
    have hs:Supported (1:Ideal Eis):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:Eis)}=(1:Ideal Eis) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],
      ite_eq_left hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton,supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

lemma supportedIdealRow_norm (a n:Eis) : ‖supportedIdealRow a n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

lemma exists_supported_primary_unit (x:Eis) (hx:Supported (Ideal.span {x})) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:=supported_primaryGenerator_ne_zero (Ideal.span {x}) hx
  have hp:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hp.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  have he:u.val*x=primaryGenerator (Ideal.span {x}):=by simpa only [mul_comm] using hu
  rw [he]
  exact hp.2

theorem supportedIdealRow_lambda_periodic :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(36:Eis)}) (supportedIdealRow lambda) := by
  intro x y hxy
  have hs:=CanonicalUnitEuler.supported_span_congruent_mod_thirty_six x y hxy
  change (if Supported (Ideal.span {x}) then _ else 0)=
    (if Supported (Ideal.span {y}) then _ else 0)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [ite_eq_left hx,ite_eq_left hy]
    obtain ⟨u,hux⟩:=exists_supported_primary_unit x hx
    have h36:(36:Eis)∣u.val*x-u.val*y:=by
      convert dvd_mul_of_dvd_right (Ideal.mem_span_singleton.mp hxy) u.val using 1 ; ring
    have hl:lambda^2∣u.val*x-u.val*y:=
      lambda_sq_dvd_three.trans ((show (3:Eis)∣36 from ⟨12,by norm_num⟩).trans h36)
    have huy:lambda^2∣u.val*y-1:=by
      convert dvd_sub hux hl using 1 ; ring
    have hsp (z:Eis) : Ideal.span {u.val*z}=Ideal.span {z}:=
      Ideal.span_singleton_mul_left_unit u.isUnit z
    have he:=idealRowHom_lambda_mod_thirty_six (u.val*x) (u.val*y) hux huy
      (by rwa [hsp]) (by rwa [hsp]) h36
    simpa only [hsp] using he
  · rw [ite_eq_right hx,ite_eq_right (fun hy=>hx (hs.mpr hy))]

lemma supportedIdealRow_lambda_primary (n:Eis) (hs:Supported (Ideal.span {n})) :
    supportedIdealRow lambda n=idealRowHom lambda (Ideal.span {n}) := by
  change (if Supported (Ideal.span {n}) then _ else _)=_
  rw [ite_eq_left hs]

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma negative_two_prime : Prime (-2:Eis) :=
  (Ideal.span_singleton_prime (by norm_num : (-2:Eis)≠0)).mp
    (show (Ideal.span {(-2:Eis)}).IsPrime from cubicTwoIdeal_isMaximal.isPrime)

theorem exists_supported_numerator_factorization (x:Eis) (hx:x≠0) :
    ∃u:Eisˣ,∃a b:ℕ,∃r:Eis,Supported (Ideal.span {r}) ∧ lambda^2∣r-1 ∧
      x=u.val*lambda^a*(2:Eis)^b*r := by
  obtain ⟨n,u,a,hn,hxform⟩:=CubicEisenstein.exists_primary_unit_lambda_factor x hx
  have hn0:n≠0:=by
    intro hz
    exact hx (by rw [hxform,hz,zero_mul])
  obtain ⟨r,hr,hrnot⟩:=(FiniteMultiplicity.of_prime_left negative_two_prime hn0).exists_eq_pow_mul_and_not_dvd
  let b:ℕ:=multiplicity (-2:Eis) n
  change n=(-2:Eis)^b*r at hr
  have hp:lambda^2∣(-2:Eis)^b-1:=neg_two_primary.trans (sub_one_dvd_pow_sub_one (-2:Eis) b)
  have hprimary:lambda^2∣r-1:=by
    have hh:=dvd_sub hn (dvd_mul_of_dvd_left hp r)
    have he:n-1-(((-2:Eis)^b-1)*r)=r-1:=by rw [hr];ring
    rwa [he] at hh
  have hnot2:¬(2:Eis)∣r:=by
    intro h2
    exact hrnot (by simpa only [neg_dvd] using h2)
  have hnotlambda:¬lambda∣r:=by
    intro hLam
    have hsub:lambda∣r-1:=(dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hprimary
    have hone:lambda∣(1:Eis):=by
      convert dvd_sub hLam hsub using 1 ; ring
    exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one hone)
  let v:Eisˣ:=u*(-1:Eisˣ)^b
  refine ⟨v,a,b,r,(supported_span_iff r).mpr ⟨hnotlambda,hnot2⟩,hprimary,?_⟩
  have hp2:(-2:Eis)^b=(-1:Eis)^b*(2:Eis)^b:=by
    rw [show (-2:Eis)=(-1)*2 by ring,mul_pow]
  rw [hxform,hr,hp2]
  dsimp only [v]
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_neg_one]
  ring

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma idealRowHom_argument_pow (a:Eis) (k:ℕ) (I:Ideal Eis) (hI:Supported I) :
    idealRowHom (a^k) I=(idealRowHom a I)^k := by
  induction k with
  | zero => simpa only [pow_zero] using idealRowHom_one_supported I hI
  | succ k ih => rw [pow_succ,idealRowHom_argument_mul,ih,pow_succ]

def reciprocityPhaseMonoid (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=sexticReciprocityPhase r n
  map_one' := sexticReciprocityPhase_one_right r hr
  map_mul' := sexticReciprocityPhase_mul_right r

def numeratorBadTwist (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  unitSupplement u * supportedIdealRow lambda^a * twoSupplement^b * reciprocityPhaseMonoid r hr

lemma numeratorBadTwist_norm (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) : ‖numeratorBadTwist u a b r hr n‖≤1 := by
  change ‖((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n‖≤1
  simp only [norm_mul,norm_pow]
  have hu:=unitSupplement_norm u n
  have ha:‖supportedIdealRow lambda n‖^a≤1:=
    pow_le_one₀ (norm_nonneg _) (supportedIdealRow_norm lambda n)
  have hb:‖twoSupplement n‖^b≤1:=
    pow_le_one₀ (norm_nonneg _) (twoSupplement_norm n)
  have hrn:=sexticReciprocityPhase_norm r n
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _)
    ((mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hu).trans ha)).trans hb)).trans hrn

lemma numeratorBadTwist_periodic (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:Eis)}) (numeratorBadTwist u a b r hr) := by
  intro x y hxy
  have h72:(72:Eis)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have h36:x-y∈(Ideal.span {(36:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (36:Eis)∣72 from ⟨2,by norm_num⟩).trans h72)
  have h8:x-y∈(Ideal.span {(8:Eis)}:Ideal Eis):=
    Ideal.mem_span_singleton.mpr ((show (8:Eis)∣72 from ⟨9,by norm_num⟩).trans h72)
  have h4:(4:Eis)∣x-y:=(show (4:Eis)∣72 from ⟨18,by norm_num⟩).trans h72
  change ((unitSupplement u x * (supportedIdealRow lambda x)^a) * (twoSupplement x)^b) *
      sexticReciprocityPhase r x =
    ((unitSupplement u y * (supportedIdealRow lambda y)^a) * (twoSupplement y)^b) *
      sexticReciprocityPhase r y
  rw [unitSupplement_periodic u x y h36,supportedIdealRow_lambda_periodic x y h36,
    twoSupplement_periodic x y h8,sexticReciprocityPhase_congr_right r x y h4]

def movingNumeratorRow (r:Eis) (hr:Supported (Ideal.span {r})) : Eis→*ℂ where
  toFun n:=idealRowHom n (Ideal.span {r})
  map_one' := idealRowHom_one_supported _ hr
  map_mul' a b := idealRowHom_argument_mul a b _

lemma movingNumeratorRow_norm (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖movingNumeratorRow r hr n‖≤1 := idealRowHom_norm n _

lemma movingNumeratorRow_periodic (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {r}) (movingNumeratorRow r hr) :=
  idealRowHom_congr_mod _

theorem idealRowHom_factor_numerator (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hn:Supported (Ideal.span {n})) (hpn:lambda^2∣n-1) :
    idealRowHom (u.val*lambda^a*(2:Eis)^b*r) (Ideal.span {n})=
      numeratorBadTwist u a b r hr n * movingNumeratorRow r hr n := by
  have hu:unitSupplement u n=idealRowHom u.val (Ideal.span {n}):=by
    change (if Supported (Ideal.span {n}) then _ else 0)=_
    rw [ite_eq_left hn]
  have hrec:=reciprocalRow_eq_idealRowHom r n hr hn hpr hpn
  change sexticReciprocityPhase r n*idealRowHom n (Ideal.span {r})=
    idealRowHom r (Ideal.span {n}) at hrec
  change _=(((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n)*idealRowHom n (Ideal.span {r})
  rw [idealRowHom_argument_mul,idealRowHom_argument_mul,idealRowHom_argument_mul,
    idealRowHom_argument_pow _ _ _ hn,idealRowHom_argument_pow _ _ _ hn,
    hu,supportedIdealRow_lambda_primary n hn,←idealRowHom_two_formula n hpn hn,←hrec]
  ring

end CanonicalRowCompletion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.RowCompletion.PeriodicRows -/

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

open scoped BigOperators Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma numeratorBadTwist_zero_of_not_supported (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (n:Eis) (hn:¬Supported (Ideal.span {n})) :
    numeratorBadTwist u a b r hr n=0 := by
  have hu:unitSupplement u n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  change ((unitSupplement u n * (supportedIdealRow lambda n)^a) * (twoSupplement n)^b) *
    sexticReciprocityPhase r n=0
  rw [hu,zero_mul,zero_mul,zero_mul]

lemma rowTwist_zero_of_not_supported (Ψ:Eis→*ℂ) (m f z n:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (hn:¬Supported (Ideal.span {n})) :
    rowTwist Ψ m f z n=0 := by
  have hu:unitSupplement (1:Eisˣ) n=0:=by
    change (if Supported (Ideal.span {n}) then _ else 0)=0
    rw [ite_eq_right hn]
  have h:=congrArg (fun T:Eis→*ℂ=>T n) (rowTwist_unitSupplement Ψ m f z (1:Eisˣ) hmLam hm2)
  change rowTwist Ψ m f ((1:Eisˣ).val*z) n=unitSupplement (1:Eisˣ) n*rowTwist Ψ m f z n at h
  simpa only [Units.val_one,one_mul,hu,zero_mul] using h

def actualPeriodicRow (Ψ:Eis→*ℂ) (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) : Eis→*ℂ :=
  Ψ * coprimalityMask m * numeratorBadTwist u a b r hr * movingNumeratorRow r hr

lemma actualPeriodicRow_norm (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) (n:Eis) :
    ‖actualPeriodicRow Ψ m u a b r hr n‖≤1 := by
  change ‖((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n‖≤1
  simp only [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
    (hΨ n)).trans (coprimalityMask_norm m n))).trans (numeratorBadTwist_norm u a b r hr n))).trans
    (movingNumeratorRow_norm r hr n)

lemma actualPeriodicRow_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (m:Eis) (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
      (actualPeriodicRow Ψ m u a b r hr) := by
  intro x y hxy
  have hQ:x-y∈Q:=Ideal.mul_le_left (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hm:x-y∈Ideal.span {m}:=Ideal.mul_le_right (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have h72:x-y∈Ideal.span {(72:Eis)}:=Ideal.mul_le_right (Ideal.mul_le_left hxy)
  have hrxy:x-y∈Ideal.span {r}:=Ideal.mul_le_right hxy
  change ((Ψ x*coprimalityMask m x)*numeratorBadTwist u a b r hr x)*movingNumeratorRow r hr x=
    ((Ψ y*coprimalityMask m y)*numeratorBadTwist u a b r hr y)*movingNumeratorRow r hr y
  rw [hΨ x y hQ,coprimalityMask_periodic m x y hm,numeratorBadTwist_periodic u a b r hr x y h72,
    movingNumeratorRow_periodic r hr x y hrxy]

theorem rowTwist_eq_actualPeriodicRow_primary (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n := by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ m f z n hn,hx,
      idealRowHom_factor_numerator u a b r n hr hpr hn hpn]
    change _=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    ring
  · rw [rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]
    change 0=((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*movingNumeratorRow r hr n
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn,mul_zero,zero_mul]

theorem exists_actual_periodic_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(u:Eisˣ)(a b:ℕ)(r:Eis)(hr:Supported (Ideal.span {r})),
      lambda^2∣r-1 ∧ f^4*z=u.val*lambda^a*(2:Eis)^b*r ∧
      (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {m}*Ideal.span {(72:Eis)}*Ideal.span {r})
        (actualPeriodicRow Ψ m u a b r hr) ∧
      (∀n,‖actualPeriodicRow Ψ m u a b r hr n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=actualPeriodicRow Ψ m u a b r hr n) := by
  obtain ⟨u,a,b,r,hr,hpr,hx⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  refine ⟨u,a,b,r,hr,hpr,hx,?_,actualPeriodicRow_periodic Ψ Q hΨ m u a b r hr,
    actualPeriodicRow_norm Ψ hΨnorm m u a b r hr,?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hQ (by
      simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hm))
      (by simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot];norm_num)) hr.1
  · exact fun n hpn=>rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn

end CanonicalRowCompletion

namespace CompletedGauss

section
open ActualEisensteinCubic IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def completedReflectionPool (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  (primeSupport (I*Q)).filter (fun P=>lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q)

lemma mem_completedReflectionPool (I Q P:Ideal Eis) (hI:I≠0) (hQ:Q≠0) :
    P∈completedReflectionPool I Q ↔
      Prime P ∧ P∣I*Q ∧ lambda∉P ∧ ringChar (Eis⧸P)≠2 ∧ ¬P∣rowResidualPart I Q := by
  simp only [completedReflectionPool,Finset.mem_filter,primeSupport,Multiset.mem_toFinset,
    UniqueFactorizationMonoid.mem_normalizedFactors_iff (mul_ne_zero hI hQ)]
  aesop

lemma completedReflectionPool_maximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    P.val.IsMaximal := by
  have hm: P.val∈normalizedFactors (I*Q):=
    Multiset.mem_toFinset.mp (Finset.mem_filter.mp P.property).1
  have hp:=prime_of_normalized_factor P.val hm
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

lemma completedReflectionPool_good (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    lambda∉P.val := (Finset.mem_filter.mp P.property).2.1

lemma completedReflectionPool_odd (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ringChar (Eis⧸P.val)≠2 := (Finset.mem_filter.mp P.property).2.2.1

lemma completedReflectionPool_nonresidual (I Q:Ideal Eis) (P:completedReflectionPool I Q) :
    ¬P.val∣rowResidualPart I Q := (Finset.mem_filter.mp P.property).2.2.2

lemma completedReflectionPool_divides (I Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (P:completedReflectionPool I Q) : P.val∣I*Q :=
  ((mem_completedReflectionPool I Q P.val hI hQ).mp P.property).2.1

lemma completedReflectionPool_coprime (I Q:Ideal Eis) :
    Pairwise (fun P R:completedReflectionPool I Q=>IsCoprime P.val R.val) := by
  let (P:completedReflectionPool I Q):P.val.IsMaximal:=completedReflectionPool_maximal I Q P
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)

theorem completedReflectionPool_eq_on_fiber (I J Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q) :
    completedReflectionPool I Q=completedReflectionPool J Q := by
  ext P
  rw [mem_completedReflectionPool I Q P hI hQ,mem_completedReflectionPool J Q P hJ hQ]
  constructor
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivJ,hresJ,_⟩:=nonresidual_prime_transport I J 1 Q P hI hJ hP hA hT hdiv hres
    exact ⟨hP,hdivJ,hgood,hodd,hresJ⟩
  · rintro ⟨hP,hdiv,hgood,hodd,hres⟩
    obtain ⟨hdivI,hresI,_⟩:=nonresidual_prime_transport J I 1 Q P hJ hI hP hA.symm hT.symm hdiv hres
    exact ⟨hP,hdivI,hgood,hodd,hresI⟩

lemma completedReflectionPool_exponent_eq (I J F Q:Ideal Eis)
    (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:completedReflectionPool I Q) :
    completedLocalExponent I F P.val=completedLocalExponent J F P.val := by
  rcases (mem_completedReflectionPool I Q P.val hI hQ).mp P.property with
    ⟨hP,hdiv,_,_,hres⟩
  exact (nonresidual_prime_transport I J F Q P.val hI hJ hP hA hT hdiv hres).2.2

theorem completedBranchScale_eq_on_fiber {ι:Type*} [Fintype ι]
    (K X:ℝ) (I J F Q:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J)
    (hT:rowMaskPart I Q=rowMaskPart J Q)
    (P:ι→Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι→Fin 3) :
    completedBranchScale K X I F Q P e=completedBranchScale K X J F Q P e := by
  have hj:(fun i=>completedLocalExponent I F (P i))=(fun i=>completedLocalExponent J F (P i)):=by
    funext i
    exact completedReflectionPool_exponent_eq I J F Q hI hJ hQ hA hT ⟨P i,hP i⟩
  simp only [completedBranchScale,completedResidualScale_eq_on_fiber K I J Q hA hT,hj]

end

section

def reflectionSixActive (e:Fin 6) : Prop := 3≤e.val

def reflectionSixLabel (e:Fin 6) : Fin 3 := ⟨e.val%3,Nat.mod_lt _ (by decide)⟩

def reflectionSixValid {ι:Type*} (e:ι→Fin 6) : Prop :=
  ∀i,e i=0 ∨ reflectionSixActive (e i)

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) : ι→Fin 6 := fun i=>
  if h:i∈x.1 then ⟨3+(x.2 ⟨i,h⟩).val,by have ht:=(x.2 ⟨i,h⟩).isLt; omega⟩ else 0

def reflectionSixSupport (e:ι→Fin 6) : Finset ι :=
  Finset.univ.filter (fun i=>reflectionSixActive (e i))

def decodeReflectionSix (e:ι→Fin 6) : ΣA:Finset ι,A→Fin 3 :=
  ⟨reflectionSixSupport e,fun i=>reflectionSixLabel (e i.val)⟩

omit [Fintype ι] in
lemma reflectionSixActive_encode (x:ΣA:Finset ι,A→Fin 3) (i:ι) :
    reflectionSixActive (encodeReflectionSix x i) ↔ i∈x.1 := by
  by_cases hi:i∈x.1
  · simp [encodeReflectionSix,hi,reflectionSixActive]
  · simp [encodeReflectionSix,hi,reflectionSixActive]

omit [Fintype ι] in
lemma encodeReflectionSix_valid (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixValid (encodeReflectionSix x) := by
  intro i
  by_cases hi:i∈x.1
  · exact Or.inr ((reflectionSixActive_encode x i).mpr hi)
  · left
    simp [encodeReflectionSix,hi]

lemma reflectionSixSupport_encode (x:ΣA:Finset ι,A→Fin 3) :
    reflectionSixSupport (encodeReflectionSix x)=x.1 := by
  ext i
  simp only [reflectionSixSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    reflectionSixActive_encode]

lemma encodeReflectionSix_injective :
    Function.Injective (encodeReflectionSix (ι:=ι)) := by
  intro x y hxy
  have hsets:x.1=y.1:=by
    rw [←reflectionSixSupport_encode x,←reflectionSixSupport_encode y,hxy]
  rcases x with ⟨A,e⟩
  rcases y with ⟨B,f⟩
  dsimp only at hsets
  subst B
  congr 1
  funext i
  have he:=congrFun hxy i.val
  simp only [encodeReflectionSix,dite_eq_left i.property] at he
  apply Fin.ext
  have hv:=congrArg Fin.val he
  exact Nat.add_left_cancel hv

lemma encode_decodeReflectionSix (e:ι→Fin 6) (he:reflectionSixValid e) :
    encodeReflectionSix (decodeReflectionSix e)=e := by
  funext i
  by_cases hi:reflectionSixActive (e i)
  · have him:i∈reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    dsimp only [encodeReflectionSix, decodeReflectionSix]
    rw [dite_eq_left him]
    apply Fin.ext
    change 3 + (e i).val % 3 = (e i).val
    have hl:=(e i).isLt
    dsimp only [reflectionSixActive] at hi
    omega
  · have him:i∉reflectionSixSupport e:=by simp [reflectionSixSupport,hi]
    have hz:e i=0:=(he i).resolve_right hi
    simp [encodeReflectionSix,decodeReflectionSix,him,hz]

lemma decode_encodeReflectionSix (x:ΣA:Finset ι,A→Fin 3) :
    decodeReflectionSix (encodeReflectionSix x)=x :=
  encodeReflectionSix_injective (encode_decodeReflectionSix _ (encodeReflectionSix_valid x))

def reflectionSixEquiv : (ΣA:Finset ι,A→Fin 3) ≃ {e:ι→Fin 6 // reflectionSixValid e} where
  toFun x:=⟨encodeReflectionSix x,encodeReflectionSix_valid x⟩
  invFun e:=decodeReflectionSix e.val
  left_inv:=decode_encodeReflectionSix
  right_inv e:=Subtype.ext (encode_decodeReflectionSix e.val e.property)

theorem sum_active_exceptional_eq_six {V:Type*} [AddCommMonoid V]
    (F:∀A:Finset ι,(A→Fin 3)→V) :
    (∑A:Finset ι,∑e:A→Fin 3,F A e)=
      ∑e:ι→Fin 6,if reflectionSixValid e then
        F (decodeReflectionSix e).1 (decodeReflectionSix e).2 else 0 := by
  have he:=Equiv.sum_comp (reflectionSixEquiv (ι:=ι))
    (fun e:{e:ι→Fin 6 // reflectionSixValid e}=>
      F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2)
  have hs:(∑x:ΣA:Finset ι,A→Fin 3,F x.1 x.2)=
      ∑e:{e:ι→Fin 6 // reflectionSixValid e},F (decodeReflectionSix e.val).1 (decodeReflectionSix e.val).2 := by
    calc
      _=∑x:ΣA:Finset ι,A→Fin 3,
          F (decodeReflectionSix (encodeReflectionSix x)).1
            (decodeReflectionSix (encodeReflectionSix x)).2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact (congrArg (fun y:ΣA:Finset ι,A→Fin 3=>F y.1 y.2)
          (decode_encodeReflectionSix x)).symm
      _=_ := he
  rw [Fintype.sum_sigma] at hs
  rw [hs,←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter reflectionSixValid)
    (by simp) (fun e:ι→Fin 6=>F (decodeReflectionSix e).1 (decodeReflectionSix e).2)).symm

end
section

open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance reflectionWeightField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P
noncomputable local instance reflectionWeightFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def reflectionStratumWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) : ℂ :=
  (∏i∈A,(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
    phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i))*
  (∏i∈(Finset.univ:Finset ι)\A,zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i))

lemma reflectionStratumWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) :
    ‖reflectionStratumWeight P hg j ψ σ ε A‖≤1 := by
  have hactive (i:ι) : ‖(((actualSextic (P i) (hg i))⁻¹)^2) (σ A i)*
      phase (actualSextic (P i) (hg i)) (ψ A i) (j i) (ε A i)‖=1 := by
    rw [norm_mul,FiniteRayExpansion.norm_char_unit]
    simpa only [one_mul,actualSextic] using canonical_phase_norm (P i) (hg i) (hc i)
      (ψ A i) (hψ A i) (j i) (hj i) (ε A i)
  have hinactive (i:ι) : ‖zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)‖≤1 := by
    by_cases hi:j i=0
    · rw [hi]
      exact zeroFourierCoefficient_zero_norm_le_one _
    · have he:=canonical_zeroFourierCoefficient (P i) (hg i) (hc i) (j i) (hj i)
      have hz:zeroFourierCoefficient (actualSextic (P i) (hg i)) (j i)=0 := by
        simpa only [actualSextic,ite_eq_right hi] using he
      rw [hz]
      simp
  rw [reflectionStratumWeight,norm_mul,norm_prod,norm_prod]
  simp only [hactive,Finset.prod_const_one,one_mul]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hinactive i)

def reflectionSixWeight (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionStratumWeight P hg j ψ σ ε (reflectionSixSupport e) else 0

lemma reflectionSixWeight_norm_le_one (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (hc:∀i,ringChar (Eis⧸P i)≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ) (hψ:∀A i,(ψ A i).IsPrimitive)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (e:ι→Fin 6) :
    ‖reflectionSixWeight P hg j ψ σ ε e‖≤1 := by
  unfold reflectionSixWeight
  split_ifs
  · exact reflectionStratumWeight_norm_le_one P hg hc j hj ψ hψ σ ε _
  · simp

theorem sum_reflectionStratumWeight_eq_six (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ)
    (G:∀A:Finset ι,(A→Fin 3)→ℂ) :
    (∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*G A e)=
      ∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*
        G (decodeReflectionSix e).1 (decodeReflectionSix e).2 := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e <;> simp [reflectionSixWeight,he,decodeReflectionSix]

theorem stratum_weighted_brackets_eq_branches (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (A:Finset ι) (n b:Eis) :
    reflectionStratumWeight P hg j ψ σ ε A*
      (∏i:A,bracket (actualSextic (P i.val) (hg i.val)) (j i.val)
        (Ideal.Quotient.mk (P i.val) (n*b^3)))=
    ∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
      reflectedBranch (fun i:A=>P i.val) (fun i=>hg i.val) (fun i=>j i.val) e n b := by
  rw [prod_bracket_eq_full_branches,Finset.mul_sum]
  apply Finset.sum_congr
  · ext e
    simp
  · intro e _
    rfl

theorem sum_reflectionSixWeight_unpad (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (G:(ι→Fin 6)→ℂ) :
    (∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*G e)=
      ∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
        G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_reflectionStratumWeight_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [encode_decodeReflectionSix e he]
  · simp only [reflectionSixWeight,ite_eq_right he,zero_mul]

end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def reflectionChoiceValue (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:Ideal Eis) : Fin 6 :=
  if h:P∈completedReflectionPool I Q then e ⟨P,h⟩ else 0

def reflectionActivePool (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q e P))

lemma reflectionActivePool_subset (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) :
    reflectionActivePool I Q e⊆completedReflectionPool I Q := Finset.filter_subset _ _

lemma mem_reflectionActivePool (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:completedReflectionPool I Q) :
    P.val∈reflectionActivePool I Q e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dite_eq_left P.property]

lemma reflectionActivePool_encode (I Q:Ideal Eis)
    (A:Finset (completedReflectionPool I Q)) (e:A→Fin 3) :
    reflectionActivePool I Q (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:completedReflectionPool I Q:=⟨P,reflectionActivePool_subset I Q _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)

def reflectionActiveLabel (I Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6)
    (P:reflectionActivePool I Q e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q e P.property⟩)

def sixReflectedBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6)
    (amplitude:ℕ→Ideal Eis→Ideal Eis→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q e
  maximal:=fun P=>completedReflectionPool_maximal I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  good:=fun P=>completedReflectionPool_good I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=completedReflectionPool_maximal I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
    let : R.val.IsMaximal:=completedReflectionPool_maximal I Q ⟨R.val,reflectionActivePool_subset I Q e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>completedReflectionPool_divides I Q hI hQ ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  nonresidual:=fun P=>completedReflectionPool_nonresidual I Q ⟨P.val,reflectionActivePool_subset I Q e P.property⟩
  label:=reflectionActiveLabel I Q e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k

def sixFixedCuspBranch (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q hI hQ K levelBound levelScale hlevel hbound e
    (fixedConjugateCuspArray cusp u) (fixedConjugateCuspArray_norm_le_one cusp u) rowPhase hrow).withExtractedFixedCuspArray cusp u rowPhase hrow

lemma sixFixedCuspBranch_primes (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u rowPhase hrow).primes=
      reflectionActivePool I Q e := rfl

lemma sixFixedCuspBranch_scale (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:completedReflectionPool I Q→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixFixedCuspBranch I F Q hI hQ K levelBound levelScale hlevel hbound e cusp u rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q e=>P.val) (reflectionActiveLabel I Q e) := rfl

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximal (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P
noncomputable local instance poolField (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintype (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

def reflectionInactiveStratumWeight (I F Q:Ideal Eis) (A:Finset (completedReflectionPool I Q)) : ℂ :=
  ∏P∈(Finset.univ:Finset (completedReflectionPool I Q))\A,
    zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
      (completedLocalExponent I F P.val)

lemma reflectionInactiveStratumWeight_norm_le_one (I F Q:Ideal Eis)
    (A:Finset (completedReflectionPool I Q)) : ‖reflectionInactiveStratumWeight I F Q A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro P _
  by_cases hj:completedLocalExponent I F P.val=0
  · rw [hj]
    exact zeroFourierCoefficient_zero_norm_le_one _
  · have he:=canonical_zeroFourierCoefficient P.val (completedReflectionPool_good I Q P)
      (completedReflectionPool_odd I Q P) (completedLocalExponent I F P.val)
      (Nat.mod_lt _ (by decide : 0<6))
    have hz:zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
        (completedLocalExponent I F P.val)=0 := by
      simpa only [actualSextic,ite_eq_right hj] using he
    rw [hz]
    simp

def reflectionSixInactiveWeight (I F Q:Ideal Eis) (e:completedReflectionPool I Q→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q (reflectionSixSupport e) else 0

lemma reflectionSixInactiveWeight_norm_le_one (I F Q:Ideal Eis)
    (e:completedReflectionPool I Q→Fin 6) : ‖reflectionSixInactiveWeight I F Q e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm_le_one I F Q _
  · simp

lemma sum_reflectionSixInactiveWeight_unpad (I F Q:Ideal Eis)
    (G:(completedReflectionPool I Q→Fin 6)→ℂ) :
    (∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*G e)=
      ∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [ite_eq_left he,encode_decodeReflectionSix e he]
    simp only [reflectionSixInactiveWeight,ite_eq_left he,decodeReflectionSix]
  · simp only [ite_eq_right he,reflectionSixInactiveWeight,zero_mul]

abbrev SixReflectionIndex (rays:ℕ) (I Q:Ideal Eis) :=
  Fin rays×(completedReflectionPool I Q→Fin 6)

def sixFixedCuspFiber (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=completedReflectionPool I Q
  maximal:=completedReflectionPool_maximal I Q
  divides:=completedReflectionPool_divides I Q hI hQ
  branch:=fun x=>sixFixedCuspBranch I F Q hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q x.2)

theorem sixFixedCuspFiber_value (rays:ℕ) (I F Q:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q→Fin 3) (unit:SixReflectionIndex rays I Q→Eisˣ)
    (rayWeight:SixReflectionIndex rays I Q→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixFixedCuspFiber rays I F Q hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (completedReflectionPool I Q),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:completedReflectionPool I Q→Fin 6,reflectionSixInactiveWeight I F Q e*
      (rayWeight (t,e)*(sixFixedCuspBranch I F Q hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss

end

end OAI

end

