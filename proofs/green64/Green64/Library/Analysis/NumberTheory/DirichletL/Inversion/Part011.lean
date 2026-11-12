module

public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.InitialCompletePool
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part020
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part021

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedPool
open InverseInitialOverlap InverseInitialCommonTuples InverseInitialCompletePool InverseInitialPoissonBridge
local notation "O"=>ActualEisensteinCubic.O

def outside (E:Finset (Ideal O))(I:Ideal O):Prop:=∀P∈E,¬P∣I

def originalOutside (A E:Finset (Ideal O)):Finset (Ideal O):=A.filter (outside E)

theorem column_outside (A E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)
    (hA:∀n∈A,outside E n)(hc:c∈columns A P j):outside E c := by
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
  obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  intro Q hQ hd
  rcases (hE Q hQ).dvd_mul.mp hd with hn|hpr
  · exact hA n hnA Q hQ (hn.trans (idealQuotient_dvd hjn))
  · exact hP Q hQ (hpr.trans (idealQuotient_dvd hj))

theorem admissible_mem_excluded_complete (E:Finset (Ideal O)){I:Ideal O}
    (hI:Admissible I)(hout:outside E I)(D:ℕ)(hD:I.absNorm≤D):
    I∈InitialMeanSquare.outsideSquarefreeIdeals E D := by
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,hD,hout⟩,hI.2.1⟩
  exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1)

theorem exists_excluded_complete_pool {κ:Type*}(A E:Finset (Ideal O))(T:Finset κ)
    (P:κ→Ideal O)(j:Ideal O)(hE:∀Q∈E,Prime Q)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (hA:∀n∈A,Squarefree n→Supported n)(bmax Xmax:ℝ)(hb:0≤bmax)(_hX:0≤Xmax):
    ∃D:ℕ,tupleColumns (originalOutside A E) T P j⊆
      InitialMeanSquare.outsideSquarefreeIdeals E D ∧
      ∀b X:ℝ,0≤b→b≤bmax→0≤X→X≤Xmax→b*X≤(D:ℝ) := by
  let D:=max (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊
  refine ⟨D,?_,?_⟩
  · intro c hc
    obtain ⟨k,hk,hc⟩:=Finset.mem_biUnion.mp hc
    have hcA:c∈columns A (P k) j:=by
      obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hc
      refine Finset.mem_image.mpr ⟨n,?_,he⟩
      obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
      exact mem_original.mpr ⟨(Finset.mem_filter.mp hnA).1,hns,hg⟩
    apply admissible_mem_excluded_complete E
      (columns_admissible A (hP k hk) (hj k hk) hA hcA)
      (column_outside _ E hE (hj k hk) (hPE k hk)
        (fun n hn=>(Finset.mem_filter.mp hn).2) hc)
    exact (original_column_norm_bound A (hP k hk) (hj k hk) hcA).trans
      ((Nat.mul_le_mul_left (A.sup Ideal.absNorm)
        (Finset.le_sup (f:=fun k=>(P k).absNorm) hk)).trans (le_max_left _ _))
  · intro b X hb0 hbb hX0 hXX
    apply (mul_le_mul hbb hXX hX0 hb).trans
    exact (Nat.le_ceil (bmax*Xmax)).trans (by exact_mod_cast (le_max_right
      (A.sup Ideal.absNorm*T.sup (fun k=>(P k).absNorm)) ⌈bmax*Xmax⌉₊))

end SevenEighths.InverseInitialExcludedPool

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily InverseInitialExcludedPolynomial
local notation "O"=>ActualEisensteinCubic.O

theorem reconstruct_outside (E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)(hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (idealQuotient_dvd hres))

theorem columns_filter (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P):
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem deleted_zero_outside (χ:Character)(E:Finset (Ideal O))
    (hE:∀Q∈E,Prime Q)(I:Ideal O)(hn:¬outside E I):
    idealCoeff (χ.excludePrimes E hE) I=0 := by
  rw [idealCoeff_excludePrimes]
  apply ite_eq_right
  intro hc
  apply hn
  intro Q hQ hd
  have hu:IsUnit Q:=(hc Q hQ).isRelPrime hd (dvd_refl Q)
  exact (hE Q hQ).not_isUnit hu

theorem residual_filtered (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hout:outside E c
  · rw [ite_eq_left hout]
  · rw [ite_eq_right hout]
    simp only [overlapResidualCoefficient,hη c hout,mul_zero,zero_mul]

theorem residual_deleted_filtered (χ:Character)(A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j
      (idealCoeff (χ.excludePrimes E hE)).toMonoidHom a W Z r z G u :=
  residual_filtered A E hE hPs hj hP _ (deleted_zero_outside χ E hE) a W Z r z G u

end SevenEighths.InverseInitialExcludedOverlap

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialExcludedForcing -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedOverlap
open InverseInitialCommonTuples InverseInitialCommonTransform
local notation "O"=>ActualEisensteinCubic.O

theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=>i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))

theorem residual_excluded_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    {P j:Ideal O}(hP:Admissible P)(hj:j∣P)(hPE:outside E P)
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:columns (originalOutside (originalSource Z r b) E) P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(u:O):
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_filtered _ E hE hP.2.1 hj hPE η hη,
    residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:=common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j):=by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  have hmem:((∏i∈A,i.val)∈columns (originalOutside (originalSource Z r b) E) P j)↔
      ((∏i∈A,i.val)∈columns (originalSource Z r b) P j):=by
    rw [columns_filter _ E hE hP.2.1 hj hPE,Finset.mem_filter]
    exact and_iff_left (pool_product_outside F E hE hFE A)
  dsimp only
  simp only [hm,hmem]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

variable {κ:Type*}
theorem original_tuples_excluded_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:tupleColumns (originalOutside (originalSource Z r b) E) T P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(a:κ→ℂ)(u:O) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_excluded_forcing W Z r z G b hZ hW E hE (hP k hk) (hj k hk) (hPE k hk) F hF hFE
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η hη u]
  ring

end SevenEighths.InverseInitialExcludedForcing

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialExcludedFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedForcing
theorem original_tuples_excluded_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal Eis))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (hPE:∀q∈I.pi L,outside E (j*survivingProduct I q))
    (η:Ideal Eis→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_excluded_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2) E hE
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) hPE F hF hFE hsub η hη (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialExcludedFourier

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialResidualPool -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialResidualPool
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow
local notation "O"=>ActualEisensteinCubic.O

theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0<Z)(hBtree:0≤Btree)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (Real.rpow_nonneg hZ.le _)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (Real.rpow_nonneg hZ.le _) le_rfl,hcover⟩

end SevenEighths.InverseInitialResidualPool

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialResidualTupleEnergy -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualTupleEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_tuple_energy
    (Woriginal W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let _p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let _hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
    ∀(lo hi:σ→ℝ)(jlo jhi:ℝ),
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc jlo jhi→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (lo i) (hi i))→
      (∀v:σ→ℝ,∀yj yc:ℝ,(∀i∈all\assigned,v i∈Set.Icc (lo i) (hi i))→
        yj∈Set.Icc jlo jhi→0<yc→Woriginal (yj*yc/(∏i∈all\assigned,v i))≠0→W yc=1)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
      tupleColumns (originalOutside (originalSource Z r bo) (reflectionExcludedPrimes q))
        ((all\assigned).pi L) (fun t=>j*survivingProduct (all\assigned) t) j⊆F→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalFourier.original_fourier_energy_bound
    (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo)
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan lo hi jlo jhi hjratio hL hcoeff hFresh hP hcopTuple hPE hsub θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hdisPool:(all:Set σ).PairwiseDisjoint (fun i=>poolList F (L i)):=by
    intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro P hPi hPk
    exact (Finset.disjoint_left.mp (hdis hi hk hik))
      (Finset.mem_filter.mp hPi).2 (Finset.mem_filter.mp hPk).2
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK
    (fun i=>poolList F (L i)) Hslot (fun i P=>coeff i P.val) hdisPool hHs
    (fun i hi P hP=>hPs i hi P.val (Finset.mem_filter.mp hP).2)
    (fun i hi P hP=>hac i hi P.val (Finset.mem_filter.mp hP).2)
    qelem z al bl primeW hz hqe hprimeW hprimeLive (elementCharacter χ) hχ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    (fun i P=>Real.log (slotRatio Z z i P.val)) (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) θ
  have hsum:∑i∈all\assigned,z i=assignedCenter all z-assignedCenter assigned z:=by
    have hh:=Finset.sum_sdiff (f:=z) hassigned
    dsimp [assignedCenter]
    linarith
  have hgj:Ideal.span {primaryGenerator j}=Ideal.span {assignedElement assigned qelem}:=
    (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1.trans hspan.symm
  have hid (u:O):
      (∑t∈(all\assigned).pi L,(∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u)=
      ∫t:ℝ,density (frequencyTwist (CubicReflectionKernel.logSchwartz Woriginal ao bo hao hso hWo) θ)
        (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ (elementCharacter χ)
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) (fun i=>poolList F (L i))
            (fun i P=>coeff i P.val*logPhase (-t) (Real.log (slotRatio Z z i P.val))))
            (childLogTest W t) Z D) u):=by
    have hh:=InverseInitialExcludedFourier.original_tuples_excluded_fourier
      (childLogTest Woriginal θ) W ao bo hao
      ((InverseInitialOriginalHeight.child_support Woriginal θ).trans hso)
      (InverseInitialOriginalHeight.child_smooth Woriginal ao bo hao hso hWo θ)
      (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (all\assigned) L hL coeff j hj.1 hP hcopTuple hPE χ hout u Z r
      (assignedCenter all z) (assignedCenter assigned z) hZp z lo hi hsum jlo jhi hjratio hcoeff
      (fun v yj yc hv hyj hyc hn=>hFresh v yj yc hv hyj hyc
        (InverseInitialOriginalHeight.child_support Woriginal θ hn))
      F hFa (fun I hI=>(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2) hsub
    rw [hh,InverseInitialOriginalHeight.logSchwartz_child]
    simp only [←hDeq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [InverseInitialInputReindex.input_puncture_span p hg Finset.univ (elementCharacter χ)
      (primaryGenerator j) (assignedElement assigned qelem) hgj]
  simpa only [hid] using he

end SevenEighths.InverseInitialResidualTupleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialResidualUniformEnergy -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualUniformEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_uniform_energy
    (Woriginal:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨W,A,B,Bnorm,hA,hAB,hBn,hWc,hWs,hWb,hFresh⟩:=
    InverseInitialUniformFresh.exists_uniform_fresh K ao bo hao hab
  have hs:Function.support (W:ℝ→ℂ)⊆Set.Icc A B:=(subset_tsupport (W:ℝ→ℂ)).trans hWs
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialResidualTupleEnergy.original_residual_tuple_energy
    Woriginal W ao bo hao hso hWo A B 1 hA le_rfl hs (W.smooth ⊤) Φ hΦ hone Bnorm hBn hWb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan hjratio hL hcoeff hP hcopTuple hPE θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  obtain ⟨Dpool,hfloor,hcover⟩:=InverseInitialResidualPool.exists_original_complete_pool
    q Z r bo cap Btree hZp (zero_le_one.trans hBtree) ((all\assigned).pi L)
    (fun t=>j*survivingProduct (all\assigned) t) j hP (fun t _=>dvd_mul_right j _) hPE
  exact henergy Z hZ Dpool hfloor all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan (fun _=>1) (fun _=>2) 1 ((2:ℝ)^K) hjratio hL hcoeff
    (hFresh (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK) Woriginal hso)
    hP hcopTuple hPE hcover θ

end SevenEighths.InverseInitialResidualUniformEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PlainGlobalBound -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.CenteredMomentPlainGlobalBound
open HeckeFamily HeckeDyadic

 theorem weighted_central (χ:Character)(W:ℝ→ℂ)(D freq C K T:ℝ)
    (hD:0<D)(hC:0≤C)(hK:0≤K)(hT:0≤T)
    (hm:∀t:ℝ,(1+|t|)^4*‖mellin W (((1/2:ℝ):ℂ)+t*I)‖≤C)
    (hs:∀t∈Icc (-T) T,‖series χ false (((1/2:ℝ):ℂ)+t*I+shift 0 freq)‖≤K*(1+|t|)^2):
    ‖∫t:ℝ in -T..T,integrand χ false W D 0 freq (((1/2:ℝ):ℂ)+t*I)‖≤C*K*Real.pi:=by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint:=integrable_inv_one_add_sq.const_mul (C*K)
  calc
    _≤∫t:ℝ in Ioc (-T) T,(C*K)*(1+t^2)⁻¹:=by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ false W D 0 freq hD]
      have hm':(1+|t|)^2*(‖mellin W (((1/2:ℝ):ℂ)+t*I)‖*(1+|t|)^2)≤C:=by
        nlinarith only [hm t]
      have hb:=CubicReflectionKernel.weighted_two_to_cauchy
        (mul_nonneg (norm_nonneg _) (sq_nonneg _)) t hm'
      have hh:=mul_le_mul_of_nonneg_left (hs t ⟨ht.1.le,ht.2⟩)
        (norm_nonneg (mellin W (((1/2:ℝ):ℂ)+t*I)))
      have hbK:=mul_le_mul_of_nonneg_right hb hK
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero]
      norm_num only [add_zero,sub_self,Real.rpow_zero,mul_one]
      apply hh.trans
      convert hbK using 1 <;> ring
    _≤∫t:ℝ,(C*K)*(1+t^2)⁻¹:=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _=_:=by rw [integral_const_mul,integral_univ_inv_one_add_sq]

 theorem finite_strip_bound (χ:Character)(hχ:χ.residue≠1)(W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hWs:Function.support W⊆Icc a b)(hW:ContDiff ℝ ∞ W)
    (D freq C K:ℝ)(hD:1≤D)(hC:0≤C)(hK:0≤K)
    (hm:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,(1+|t|)^6*‖mellin W ((x:ℂ)+t*I)‖≤C)
    (hs:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,
      ‖series χ false ((x:ℂ)+t*I+shift 0 freq)‖≤K*(1+|t|)^2):
    ‖polynomial χ false W D 0 freq‖≤(1/(2*Real.pi))*
      (C*K*Real.pi+3*C*K+C*HeckeReciprocalBound.bound 2*Real.pi):=by
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hm4 (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      (1+|t|)^4*‖mellin W ((x:ℂ)+t*I)‖≤C:=by
    apply le_trans _ (hm x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · norm_num
  have hcent:=weighted_central χ W D freq C K D hD0 hC hK hD0.le
    (hm4 _ (by norm_num)) (fun t _=>hs _ (by norm_num) t)
  have hg (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(y:ℝ)(hy:|y|=D):
      ‖series χ false ((x:ℂ)+y*I+shift 0 freq)‖≤K*(1+D)^2:=by
    simpa only [hy] using hs x hx y
  have hlo:=horizontal_join_bound χ false W D 0 freq (1/2) 2 (-D) C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=>hm4 x hx (-D))
    (fun x hx=>hg x hx (-D) (by simp [abs_of_nonneg hD0.le]))
  have hhi:=horizontal_join_bound χ false W D 0 freq (1/2) 2 D C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=>hm4 x hx D)
    (fun x hx=>hg x hx D (abs_of_nonneg hD0.le))
  have htail:=absolute_tail_bound χ false W D 2 0 freq C D 4 hD0 (by norm_num) hC hD0.le
    (hm _ (by norm_num))
  have hpower:D^(3/2:ℝ)≤(1+D)^2:=by
    have hp:D^(3/2:ℝ)≤D^(2:ℝ):=Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
    rw [Real.rpow_two] at hp
    nlinarith
  have hratio:D^(3/2:ℝ)/(1+D)^2≤1:=(div_le_one (by positivity)).mpr hpower
  have hratio4:D^(3/2:ℝ)/(1+D)^4≤1:=by
    apply (div_le_one (by positivity)).mpr
    apply hpower.trans
    exact pow_le_pow_right₀ (by linarith : 1≤1+D) (by norm_num : 2≤4)
  have hj:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)≤(3/2)*C*K:=by
    have he:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)=
        ((3/2)*C*K)*(D^(3/2:ℝ)/(1+D)^2):=by field_simp
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio
  have ht:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi≤
      C*HeckeReciprocalBound.bound 2*Real.pi:=by
    have hb:0≤HeckeReciprocalBound.bound 2:=tsum_nonneg (fun _=>norm_nonneg _)
    have he:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi=
        (C*HeckeReciprocalBound.bound 2*Real.pi)*(D^(3/2:ℝ)/(1+D)^4):=by ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio4
  norm_num only [add_zero,show (2:ℝ)-1/2=3/2 by norm_num,show |(2:ℝ)-1/2|=3/2 by norm_num,
    abs_neg,abs_of_nonneg hD0.le] at hlo hhi htail
  rw [polynomial_finite_shift χ hχ false W a b ha hWs hW D 0 freq (1/2) 2 D hD0
    (by norm_num) hD0.le (by intro s hs h; cases h),norm_mul]
  have hnorm:‖(1/(2*Real.pi):ℂ)‖=(1/(2*Real.pi):ℝ):=by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left ((norm_four_sides _ _ _ _).trans ?_) (by positivity)
  simp only [ofReal_neg] at hlo
  linarith [hlo.trans hj,hhi.trans hj,htail.trans ht]

end SevenEighths.CenteredMomentPlainGlobalBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PlainGlobalActual -/

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.CenteredMomentPlainGlobalActual
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalBound

 theorem global_polynomial_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,1≤D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,Cm,hCm,hm⟩:=profile_strip_decay a b ha (1/2) 2 6
  obtain ⟨Cg,hCg,hg⟩:=original_upper_strip (3/10) (by norm_num)
  let E:=HeckeReciprocalBound.bound 2
  have hE:0≤E:=tsum_nonneg (fun _=>norm_nonneg _)
  let C:ℝ:=Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)
  have hC:0<C:=div_pos (mul_pos hCm (add_pos_of_pos_of_nonneg
    (mul_pos hCg (by positivity)) (mul_nonneg hE Real.pi_pos.le))) (by positivity)
  refine ⟨S,C,hC,?_⟩
  intro W hWs χ hχ D freq hD
  let Q:ℝ:=χ.modulus.absNorm
  let V:ℝ:=3+|freq|
  let B:ℝ:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB:0≤B:=apply_nonneg _ _
  have hQ:1≤Q:=by
    dsimp [Q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤V:=by dsimp [V]; linarith [abs_nonneg freq]
  have hQ0:0≤Q:=zero_le_one.trans hQ
  have hrad:((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)≤Q:=radical_norm_le_modulus χ
  have hrad0:0≤((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ):=Nat.cast_nonneg _
  have hcost:Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)≤Q:=by
    calc
      _≤Q^(3/5:ℝ)*Q^((1/10+(3/10)):ℝ):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hrad0 hrad (by norm_num)) (Real.rpow_nonneg hQ0 _)
      _=Q:=by rw [←Real.rpow_add (zero_lt_one.trans_le hQ)]; norm_num
  have hgrowth (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      ‖series χ false ((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)‖≤(Cg*Q*V^2)*(1+|t|)^2:=by
    have hs:-(1/10:ℝ)≤(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).re:=by simp [HeckeDyadic.shift]; linarith [hx.1]
    have hh:=hg χ hχ _ hs
    have him:(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).im=t-freq:=by simp [HeckeDyadic.shift,sub_eq_add_neg]
    rw [him] at hh
    have ht:3+|t-freq|≤V*(1+|t|):=by
      dsimp [V]
      have hab:=abs_sub t freq
      nlinarith [abs_nonneg t,abs_nonneg freq,mul_nonneg (abs_nonneg t) (abs_nonneg freq)]
    apply hh.trans
    change Cg*Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)*
      (3+|t-freq|)^2≤_
    have hc:=mul_le_mul (mul_le_mul_of_nonneg_left hcost hCg.le)
      (pow_le_pow_left₀ (by positivity) ht 2) (by positivity) (mul_nonneg hCg.le hQ0)
    convert hc using 1 <;> ring
  have hb:=finite_strip_bound χ hχ W a b ha hWs (W.smooth ⊤) D freq (Cm*B) (Cg*Q*V^2)
    hD (mul_nonneg hCm.le hB) (by positivity) (hm W hWs) hgrowth
  have hQV:1≤Q*V^2:=one_le_mul_of_one_le_of_one_le hQ (one_le_pow₀ hV)
  have he:E≤E*(Q*V^2):=le_mul_of_one_le_right hE hQV
  apply hb.trans
  dsimp only [C]
  change _≤Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)*B*Q*V^2
  have hCe: Cm*B*E*Real.pi≤Cm*B*(E*(Q*V^2))*Real.pi:=by gcongr
  dsimp only [E] at hCe ⊢
  calc
    _≤(1/(2*Real.pi))*
      (Cm*B*(Cg*Q*V^2)*Real.pi+3*(Cm*B)*(Cg*Q*V^2)+
       Cm*B*(HeckeReciprocalBound.bound 2*(Q*V^2))*Real.pi):=
      mul_le_mul_of_nonneg_left (add_le_add_right hCe _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentPlainGlobalActual

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedProfileMeasure
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem actual_profile_separation (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier (CompletedHeight.normTwistedSource W t)
          (s*Real.exp y)=∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨n,hn⟩ := CenteredMomentComparisonReflection.reflected_profile_height_control
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨(C+1)*D,by positivity,?_⟩
  intro t s hs0
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : ContDiffOn ℝ ∞ (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Set.Ioi 0) := by
    rw [←he]
    exact paperRadialFourier_contDiffOn _
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep _ hF (D*(1+‖t‖)^n) (by positivity)
    (fun j hj x hx=>hDb t j hj x hx.le) s hs0
  refine ⟨density,?_,hi,hm.trans ?_,fun v=>(hp v).trans ?_⟩
  · intro y
    simpa using hid (fun _ : Unit=>y)
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]

theorem row_density_energy {ι : Type*} [Fintype ι]
    (density φ : ι→ℝ→ℂ) (rho : ℝ→ℝ) (w : ℝ→ℝ)
    (hrho : ∀v,0< rho v) (hw : ∀v,0<w v)
    (hpoint : ∀i v,‖density i v‖≤ rho v)
    (hint : ∀i,Integrable (fun v=>density i v*φ i v))
    (hmeasure : Integrable (fun v=>rho v*w v))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀v,(∑i,‖φ i v‖^2)≤E*(w v)^2) :
    (∑i,‖∫v : ℝ,density i v*φ i v‖^2)≤E*(∫v : ℝ,rho v*w v)^2 := by
  let B (v : ℝ) : ℂ := (rho v*w v:ℝ)
  let F (i : ι) (v : ℝ) : ℂ := density i v/B v*φ i v
  have hB0 (v : ℝ) : B v≠0 := Complex.ofReal_ne_zero.mpr (mul_pos (hrho v) (hw v)).ne'
  have hBn (v : ℝ) : ‖B v‖=rho v*w v := by
    exact Complex.norm_of_nonneg (mul_pos (hrho v) (hw v)).le
  have he (i : ι) (v : ℝ) : B v*F i v=density i v*φ i v := by
    dsimp only [F]
    field_simp [hB0 v]
  have hFn (i : ι) (v : ℝ) : ‖F i v‖≤‖φ i v‖/w v := by
    dsimp only [F]
    rw [norm_mul,norm_div,hBn]
    calc
      _≤(rho v/(rho v*w v))*‖φ i v‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hpoint i v) (mul_pos (hrho v) (hw v)).le) (norm_nonneg _)
      _=_ := by field_simp [(hrho v).ne', (hw v).ne']
  have hb (v : ℝ) : (∑i,‖F i v‖^2)≤E := by
    calc
      _≤∑i,(‖φ i v‖/w v)^2 := Finset.sum_le_sum (fun i _=>
        pow_le_pow_left₀ (norm_nonneg _) (hFn i v) 2)
      _=(∑i,‖φ i v‖^2)/(w v)^2 := by simp only [div_pow,Finset.sum_div]
      _≤E := (div_le_iff₀ (sq_pos_of_pos (hw v))).mpr (henergy v)
  have hh := CompletedGauss.finite_integral_energy_bound B F E hE
    (by simpa only [hBn] using hmeasure) (fun i=>by simpa only [he] using hint i) hb
  simpa only [he,hBn] using hh

theorem row_density_energy_two {ι : Type*} [Fintype ι]
    (b₁ b₂ : ι→ℝ→ℂ) (φ : ι→ℝ→ℝ→ℂ) (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0< rho₁ v) (hr₂ : ∀v,0< rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤ rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤ rho₂ v)
    (hi₁ : ∀i,Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)))
    (hi₂ : ∀i x,Integrable (fun y=>b₂ i y*φ i x y))
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (hb : ∀x y,(∑i,‖φ i x y‖^2)≤E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖∫x : ℝ,b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  have hh := row_density_energy b₁ (fun i x=>∫y : ℝ,b₂ i y*φ i x y)
    rho₁ w₁ hr₁ hw₁ hp₁ hi₁ hm₁ (E*(∫y : ℝ,rho₂ y*w₂ y)^2) (by positivity) (by
      intro x
      have ht := row_density_energy b₂ (fun i y=>φ i x y) rho₂ w₂ hr₂ hw₂
        hp₂ (fun i=>hi₂ i x) hm₂ (E*(w₁ x)^2) (by positivity) (hb x)
      exact ht.trans_eq (by ring))
  exact hh.trans_eq (by ring)

def logWindow (V : ℝ→ℂ) (x : ℝ) : ℂ := if 0<x then V (Real.log x) else 0

theorem finite_annular_separation (V F : ℝ→ℂ) (s X : ℝ) (hX : 0<X)
    (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v)
    (η : Character) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0)
    (hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  have hnorm (I : Ideal O) (hI : I∈S) : 0<(I.absNorm:ℝ)/X := by
    apply div_pos _ hX
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hi (I : Ideal O) : Integrable (fun v : ℝ=>
      density v*(HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    have ht := ((density.integrable (μ:=volume)).mul_bdd
      (logPhase_continuous_left (Real.log ((I.absNorm:ℝ)/X))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v=>le_of_eq (logPhase_norm v _)))).mul_const
        (HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X))
    apply ht.congr
    filter_upwards [] with v
    ring
  have hp (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 0 S
    (fun I hI h=>hc I hI (mul_ne_zero_iff.mp h).1)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_self,neg_zero,
    Complex.cpow_zero,mul_one]
  simp_rw [hp]
  have he : (fun v : ℝ=>density v*((X:ℂ)^(-(1/2:ℂ))*
      ∑I∈S,HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) =
      (fun v=>(X:ℂ)^(-(1/2:ℂ))*∑I∈S,density v*(HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    funext v
    rw [←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum S (fun I _=>hi I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hh := hsep (Real.log ((I.absNorm:ℝ)/X))
  rw [Real.exp_log (hnorm I hI)] at hh
  simp only [logWindow,ite_eq_left (hnorm I hI)]
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

lemma logWindow_support (V : ℝ→ℂ) (M : ℝ)
    (hV : ∀y,V y≠0 → |y|≤M) :
    Function.support (logWindow V)⊆Set.Icc (Real.exp (-M)) (Real.exp M) := by
  intro x hx
  change logWindow V x≠0 at hx
  by_cases hxp : 0<x
  · have hv : V (Real.log x)≠0 := by simpa only [logWindow,ite_eq_left hxp] using hx
    have hh := abs_le.mp (hV _ hv)
    constructor
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.1
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.2
  · exact False.elim (hx (by simp only [logWindow,ite_eq_right hxp]))

theorem plain_annular_separation (V F : ℝ→ℂ) (M s X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v) (η : Character) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  exact finite_annular_separation V F s X hX density hsep η S hs hc

theorem actual_plain_profile_measure (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀(η : Character)(X : ℝ),0<X →
          HeckeDyadic.polynomial η false (fun x=>logWindow V x*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)) X 0 0 =
          ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A J
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro t s hs0
  obtain ⟨density,hsep,hi,hm,hp⟩ := hb t s hs0
  exact ⟨density,(fun η X hX=>plain_annular_separation V _ M s X hX hV density hsep η),hi,hm,hp⟩

end SevenEighths.CenteredMomentReflectedProfileMeasure

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedPairEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure
local notation "O" => HeckeFamily.O

lemma plain_frequency_control (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  have he (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hs I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    rw [he,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  obtain ⟨hc,K,hK⟩ := plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)

theorem paired_profile_energy {ι : Type*} [Fintype ι]
    (χ ψ : ι→Character) (P : ι→ℂ) (V₁ V₂ : ℝ→ℂ) (M₁ M₂ : ℝ)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (F₁ F₂ : ι→ℝ→ℂ) (s₁ s₂ X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i) (hX₂ : ∀i,0<X₂ i)
    (b₁ b₂ : ι→𝓢(ℝ,ℂ))
    (hsep₁ : ∀i y,V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*b₁ i v)
    (hsep₂ : ∀i y,V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*b₂ i v)
    (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0< rho₁ v) (hr₂ : ∀v,0< rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤ rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤ rho₂ v)
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
      HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
        E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖HeckeDyadic.polynomial (χ i) false (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) (X₁ i) 0 0 *
      HeckeDyadic.polynomial (ψ i) false (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) (X₂ i) 0 0 * P i‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  let T₁ (i : ι) (x : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)
  let T₂ (i : ι) (y : ℝ) := HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)
  let φ (i : ι) (x y : ℝ) := T₁ i x*T₂ i y*P i
  have hi₂ (i : ι) (x : ℝ) : Integrable (fun y=>b₂ i y*φ i x y) := by
    have hi := (plain_density_integrable V₂ M₂ (X₂ i) (hX₂ i) hV₂ (ψ i) (b₂ i)).const_mul (T₁ i x*P i)
    apply hi.congr
    filter_upwards [] with y
    dsimp [φ,T₂]
    ring
  have he₂ (i : ι) (x : ℝ) : (∫y : ℝ,b₂ i y*φ i x y)=
      T₁ i x*(∫y : ℝ,b₂ i y*T₂ i y)*P i := by
    rw [←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [φ]
    ring
  have hi₁ (i : ι) : Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)) := by
    simp_rw [he₂]
    have hi := (plain_density_integrable V₁ M₁ (X₁ i) (hX₁ i) hV₁ (χ i) (b₁ i)).mul_const
      ((∫y : ℝ,b₂ i y*T₂ i y)*P i)
    apply hi.congr
    filter_upwards [] with x
    dsimp [T₁]
    ring
  have hh := row_density_energy_two (fun i=>(b₁ i:ℝ→ℂ)) (fun i=>(b₂ i:ℝ→ℂ)) φ
    rho₁ rho₂ w₁ w₂ hr₁ hr₂ hw₁ hw₂ hp₁ hp₂ hi₁ hi₂ hm₁ hm₂ E hE henergy
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [plain_annular_separation V₁ (F₁ i) M₁ (s₁ i) (X₁ i) (hX₁ i) hV₁ (b₁ i) (hsep₁ i) (χ i),
      plain_annular_separation V₂ (F₂ i) M₂ (s₂ i) (X₂ i) (hX₂ i) hV₂ (b₂ i) (hsep₂ i) (ψ i)]
  simp_rw [he₂]
  congr 1
  rw [←integral_mul_const,←integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [T₁,T₂]
  ring

end SevenEighths.CenteredMomentReflectedPairEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedUniformPair -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedUniformPair
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy

def heightScale (A n : ℕ) (s t : ℝ) : ℝ := (1+s)^A/(1+‖t‖)^n

def normalizedReflected (V W : ℝ→ℂ) (A n : ℕ) (s t x : ℝ) : ℂ :=
  logWindow V x*((heightScale A n s t:ℝ):ℂ)*
    paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)

def envelope (C : ℝ) (J : ℕ) (v : ℝ) : ℝ := C/(1+v^2)/(1+‖v‖)^J

lemma heightScale_pos (A n : ℕ) (s t : ℝ) (hs : 0<s) : 0<heightScale A n s t := by
  unfold heightScale
  positivity

lemma envelope_pos (C : ℝ) (hC : 0<C) (J : ℕ) (v : ℝ) : 0<envelope C J v := by
  unfold envelope
  positivity

lemma envelope_weight (C : ℝ) (J : ℕ) (v : ℝ) :
    envelope C J v*(1+‖v‖)^J=C/(1+v^2) := by
  unfold envelope
  field_simp

lemma envelope_integrable (C : ℝ) (J : ℕ) :
    Integrable (fun v : ℝ=>envelope C J v*(1+‖v‖)^J) := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  exact integrable_inv_one_add_sq.const_mul C

lemma envelope_integral (C : ℝ) (J : ℕ) :
    (∫v : ℝ,envelope C J v*(1+‖v‖)^J)=C*Real.pi := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  rw [integral_const_mul,integral_univ_inv_one_add_sq]

lemma normalized_density_bound (A n J : ℕ) (s t C : ℝ) (hs : 0<s)
    (b : 𝓢(ℝ,ℂ))
    (hp : ∀v : ℝ,(1+s)^A*(1+‖v‖)^(J+2)*‖b v‖≤C*(1+‖t‖)^n) :
    ∀v : ℝ,‖(((heightScale A n s t:ℝ):ℂ) • b) v‖≤envelope C J v := by
  intro v
  have ht : 0<(1+‖t‖)^n := by positivity
  have hv : 0<(1+‖v‖)^J := by positivity
  have hh : (1+‖v‖)^2*((1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖)≤C := by
    rw [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (heightScale_pos A n s t hs).le]
    unfold heightScale
    have hh := (div_le_iff₀ ht).mpr (hp v)
    convert hh using 1 ; rw [pow_add] ; ring
  have hnorm : 0≤(1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖ := by positivity
  have hb := CubicReflectionKernel.weighted_two_to_cauchy hnorm v hh
  apply (le_div_iff₀ hv).mpr
  simpa only [envelope,mul_comm] using hb

theorem actual_pair_uniform (V₁ V₂ : ℝ→ℂ) (M₁ M₂ a₁ b₁ a₂ b₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂) (A J₁ J₂ : ℕ) :
    ∃n₁ n₂ : ℕ,∀W₁ W₂ : ℝ→ℂ,
      Function.support W₁⊆Set.Icc a₁ b₁ → ContDiff ℝ ∞ W₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₂ →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s₁ s₂ t₁ t₂ X₁ X₂ : ι→ℝ),
        (∀i,0<s₁ i) → (∀i,0<s₂ i) → (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      ∀E : ℝ,0≤E →
      (∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
        HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
          E*((1+‖x‖)^J₁)^2*((1+‖y‖)^J₂)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)) (X₁ i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false (normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)) (X₂ i) 0 0 * P i‖^2)≤C*E := by
  obtain ⟨n₁,h₁⟩ := actual_profile_separation V₁ M₁ a₁ b₁ hM₁ hV₁ ha₁ A (J₁+2)
  obtain ⟨n₂,h₂⟩ := actual_profile_separation V₂ M₂ a₂ b₂ hM₂ hV₂ ha₂ A (J₂+2)
  refine ⟨n₁,n₂,?_⟩
  intro W₁ W₂ hs₁ hW₁ hs₂ hW₂
  obtain ⟨C₁,hC₁,hb₁⟩ := h₁ W₁ hs₁ hW₁
  obtain ⟨C₂,hC₂,hb₂⟩ := h₂ W₂ hs₂ hW₂
  refine ⟨(C₁*Real.pi)^2*(C₂*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s₁ s₂ t₁ t₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ E hE henergy
  choose d₁ hid₁ hi₁ hm₁ hp₁ using fun i=>hb₁ (t₁ i) (s₁ i) (hs₁ i)
  choose d₂ hid₂ hi₂ hm₂ hp₂ using fun i=>hb₂ (t₂ i) (s₂ i) (hs₂ i)
  let e₁ (i : ι) : ℂ := heightScale A n₁ (s₁ i) (t₁ i)
  let e₂ (i : ι) : ℂ := heightScale A n₂ (s₂ i) (t₂ i)
  let F₁ (i : ι) (x : ℝ) := e₁ i*paperRadialFourier (CompletedHeight.normTwistedSource W₁ (t₁ i)) x
  let F₂ (i : ι) (x : ℝ) := e₂ i*paperRadialFourier (CompletedHeight.normTwistedSource W₂ (t₂ i)) x
  have hsep₁ (i : ι) (y : ℝ) : V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*(e₁ i • d₁ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₁ y*logPhase v y)*(e₁ i*d₁ i v))=
        (fun v=>e₁ i*((V₁ y*logPhase v y)*d₁ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₁ i y]
    dsimp [F₁]
    ring
  have hsep₂ (i : ι) (y : ℝ) : V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*(e₂ i • d₂ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₂ y*logPhase v y)*(e₂ i*d₂ i v))=
        (fun v=>e₂ i*((V₂ y*logPhase v y)*d₂ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₂ i y]
    dsimp [F₂]
    ring
  have hh := paired_profile_energy χ ψ P V₁ V₂ M₁ M₂ hV₁ hV₂ F₁ F₂ s₁ s₂ X₁ X₂ hX₁ hX₂
    (fun i=>e₁ i • d₁ i) (fun i=>e₂ i • d₂ i) hsep₁ hsep₂
    (envelope C₁ J₁) (envelope C₂ J₂) (fun x=>(1+‖x‖)^J₁) (fun y=>(1+‖y‖)^J₂)
    (envelope_pos C₁ hC₁ J₁) (envelope_pos C₂ hC₂ J₂) (by intro x;positivity) (by intro y;positivity)
    (fun i=>normalized_density_bound A n₁ J₁ (s₁ i) (t₁ i) C₁ (hs₁ i) (d₁ i) (hp₁ i))
    (fun i=>normalized_density_bound A n₂ J₂ (s₂ i) (t₂ i) C₂ (hs₂ i) (d₂ i) (hp₂ i))
    (envelope_integrable C₁ J₁) (envelope_integrable C₂ J₂) E hE henergy
  rw [envelope_integral,envelope_integral] at hh
  have heq : E*(C₁*Real.pi)^2*(C₂*Real.pi)^2=((C₁*Real.pi)^2*(C₂*Real.pi)^2)*E := by ring
  rw [heq] at hh
  have hf₁ (i : ι) : normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)=
      (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₁,e₁]
    ring
  have hf₂ (i : ι) : normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)=
      (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₂,e₂]
    ring
  simp_rw [hf₁,hf₂]
  exact hh

end SevenEighths.CenteredMomentReflectedUniformPair

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ScaleSupremum -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def scaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ inv W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ inv W S) (scaleSum χ inv (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ inv J) using 1
    · rfl
    · change coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ inv J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ inv W S l=polynomial χ inv W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

def scaleTest (W : ℝ→ℂ) (j : Fin 2) : ℝ→ℂ :=
  if j=0 then W else scaleProfile W

lemma scaleTest_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (j : Fin 2) :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

lemma scaleTest_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) (j : Fin 2) :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 0 *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 0 * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    scaleSum (χ i) false (scaleTest W j) S x *
      scaleSum (ψ i) false (scaleTest V k) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) false (scaleTest W j) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    scaleSum_eq_polynomial (ψ i) false (scaleTest V k) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((scaleSum_continuous (χ i) false _ S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((scaleSum_continuous (ψ i) false _ T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (scaleSum_deriv (χ i) false W S (hW.differentiable (by simp)) x).mul_const
        (scaleSum (ψ i) false (scaleTest V k) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((scaleSum_deriv (ψ i) false V T (hV.differentiable (by simp)) y).const_mul
        (scaleSum (χ i) false (scaleTest W j) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 0 *
          polynomial (ψ i) false V (Real.exp y) 0 0 * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    scaleSum (χ i) false W S p.1 * scaleSum (ψ i) false V T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((scaleSum_continuous (χ i) false W S hW.continuous).comp continuous_fst).mul
      ((scaleSum_continuous (ψ i) false V T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      F i (x,y)=polynomial (χ i) false W (Real.exp x) 0 0 *
        polynomial (ψ i) false V (Real.exp y) 0 0 * P i := by
    dsimp only [F]
    rw [scaleSum_eq_polynomial (χ i) false W S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      scaleSum_eq_polynomial (ψ i) false V T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge FourierBridge
open CenteredMomentScaleSupremum (scaleTest scaleTest_continuous scaleTest_support)
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def frequencyScaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem frequencyScaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (frequencyScaleSum χ inv W freq S) := by
  unfold frequencyScaleSum
  fun_prop

theorem frequencyScaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (frequencyScaleSum χ inv W freq S) (frequencyScaleSum χ inv (scaleProfile W) freq S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-t)))
        ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))) using 1
    · rfl
    · change (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [frequencyScaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [frequencyScaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

lemma ratio_frequency_phase (x l freq : ℝ) (hx : 0<x) :
    (((x/Real.exp l : ℝ):ℂ)^(-shift 0 freq))=
      logPhase (freq/(2*Real.pi)) (-l)*logPhase (freq/(2*Real.pi)) (Real.log x) := by
  have ht : 2*Real.pi*(freq/(2*Real.pi))=freq := by field_simp
  have hh := norm_phase x (Real.exp l) hx (Real.exp_pos l) 0 (freq/(2*Real.pi))
  rw [ht] at hh
  simp only [neg_zero,Complex.cpow_zero,one_mul,zero_re,zero_im,sub_zero] at hh
  rw [←hh,Real.log_div hx.ne' (Real.exp_pos l).ne',Real.log_exp]
  rw [show Real.log x-l=(-l)+Real.log x by ring,logPhase_add]

theorem frequencyScaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    polynomial χ inv W (Real.exp l) 0 freq=
      logPhase (freq/(2*Real.pi)) (-l)*frequencyScaleSum χ inv W freq S l := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 freq S hc,scale_normalization]
  unfold frequencyScaleSum
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : J=0
  · subst J
    simp only [coefficient_zero,zero_mul,mul_zero]
  have hpos : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  rw [ratio_frequency_phase _ l freq hpos,Real.exp_neg,div_eq_mul_inv]
  ring

theorem frequencyScaleSum_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    ‖frequencyScaleSum χ inv W freq S l‖=‖polynomial χ inv W (Real.exp l) 0 freq‖ := by
  rw [frequencyScaleSum_eq_polynomial χ inv W freq S l hc,norm_mul,logPhase_norm,one_mul]

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 (freq₁ i) *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 (freq₂ i) * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x *
      frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    frequencyScaleSum_norm (χ i) false (scaleTest W j) (freq₁ i) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    frequencyScaleSum_norm (ψ i) false (scaleTest V k) (freq₂ i) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((frequencyScaleSum_continuous (χ i) false _ (freq₁ i) S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((frequencyScaleSum_continuous (ψ i) false _ (freq₂ i) T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (frequencyScaleSum_deriv (χ i) false W (freq₁ i) S (hW.differentiable (by simp)) x).mul_const
        (frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((frequencyScaleSum_deriv (ψ i) false V (freq₂ i) T (hV.differentiable (by simp)) y).const_mul
        (frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,norm_mul,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  simp only [norm_mul]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
          polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    frequencyScaleSum (χ i) false W (freq₁ i) S p.1 * frequencyScaleSum (ψ i) false V (freq₂ i) T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((frequencyScaleSum_continuous (χ i) false W (freq₁ i) S hW.continuous).comp continuous_fst).mul
      ((frequencyScaleSum_continuous (ψ i) false V (freq₂ i) T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      ‖F i (x,y)‖^2=‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2 := by
    dsimp only [F]
    simp only [norm_mul]
    rw [frequencyScaleSum_norm (χ i) false W (freq₁ i) S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      frequencyScaleSum_norm (ψ i) false V (freq₂ i) T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ freq₁ freq₂ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentFrequencyScaleSupremum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RadialPolynomialEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentRadialPolynomialEnergy
open HeckeFamily HeckeDyadic CenteredMomentFrequencyScaleSupremum
open CenteredMomentPositiveSummability ConcreteTraceCRT
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

lemma polynomial_bounded (W : ℝ→ℂ) (a b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,∀t : ℝ,‖polynomial χ false W X 0 t‖≤B := by
  let l:=Real.log X
  let S:=scaleSupport l b
  have hx : Real.exp l=X := Real.exp_log hX
  have hc : ∀I : Ideal O,I≠0 → W ((I.absNorm:ℝ)/Real.exp l)≠0 → I∈S :=
    scaleSupport_cover W a b l l hb hs le_rfl
  let B:=‖Complex.exp (-(l:ℂ)/2)‖*∑I∈S,‖W ((I.absNorm:ℝ)*Real.exp (-l))‖
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro χ t
  rw [←hx,frequencyScaleSum_eq_polynomial χ false W t S l hc,norm_mul,
    FourierBridge.logPhase_norm,one_mul]
  unfold frequencyScaleSum
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul,norm_mul,FourierBridge.logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_norm_le χ false I)

lemma pair_radial_summable (χ : O→Character) (P : O→ℂ) (t omega : O→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a b c d X Y Pbound : ℝ)
    (hb : 0≤b) (hd : 0≤d) (hX : 0<X) (hY : 0<Y)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc c d)
    (hP : ∀z,‖P z‖≤Pbound) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then
      ‖polynomial (χ z) false W₁ X 0 (t z)*polynomial (χ z) false W₂ Y 0 (omega z)*P z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B₁,hB₁,h₁⟩:=polynomial_bounded W₁ a b X hb hX hs₁
  obtain ⟨B₂,hB₂,h₂⟩:=polynomial_bounded W₂ c d Y hd hY hs₂
  apply bounded_radial_summable _ (B₁*B₂*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (h₁ _ _) (h₂ _ _) (norm_nonneg _) hB₁)
    (hP z) (norm_nonneg _) (mul_nonneg hB₁ hB₂)

lemma single_radial_summable (χ : O→Character) (P : O→ℂ) (t : O→ℝ)
    (W : ℝ→ℂ) (a b X Pbound : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) (hP : ∀z,‖P z‖≤Pbound)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then ‖polynomial (χ z) false W X 0 (t z)*P z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB,hh⟩:=polynomial_bounded W a b X hb hX hs
  apply bounded_radial_summable _ (B*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul]
  exact mul_le_mul (hh _ _) (hP z) (norm_nonneg _) hB

end SevenEighths.CenteredMomentRadialPolynomialEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SlotRemoval -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRemoval

theorem whole_slot_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      (∑ i ∈ R, length i) ≤ min (∑ i ∈ s, length i) (F/(6*κ)+η) ∧
      (R=s ∨ F ≤ 6*κ*(∑ i ∈ R, length i)) := by
  have hthreshold : 0 ≤ F/(6*κ) := div_nonneg hF (by positivity)
  by_cases htotal : (∑ i ∈ s, length i) ≤ F/(6*κ)
  · refine ⟨s,Finset.Subset.refl _,le_min le_rfl ?_,Or.inl rfl⟩
    linarith
  · have htarget : 0 ≤ (∑ i ∈ s, length i)-F/(6*κ) := by linarith
    obtain ⟨T,hTs,hTupper,hTlower⟩ := HeckeDetectorSlotSelection.whole_slots
      s length (fun _ => 1) 1 η (by norm_num) hη hL hmesh
      (by intros; norm_num) (by intros; norm_num) 1
      ((∑ i ∈ s, length i)-F/(6*κ)) (by norm_num) (by norm_num)
      htarget (by linarith) (by simp)
    simp only [one_mul,mul_one] at hTlower
    have hsum : (∑ i ∈ s, length i)=(∑ i ∈ s\T, length i)+(∑ i ∈ T, length i) :=
      (Finset.sum_sdiff hTs).symm
    have hTnonneg : 0 ≤ ∑ i ∈ T, length i := Finset.sum_nonneg (fun i hi => hL i (hTs hi))
    refine ⟨s\T,Finset.sdiff_subset,le_min (by linarith) (by linarith),Or.inr ?_⟩
    have hremove : F/(6*κ) ≤ ∑ i ∈ s\T, length i := by linarith
    exact (div_le_iff₀ (by positivity : 0 < 6*κ)).mp hremove |>.trans_eq (mul_comm _ _)

theorem removal_cost {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      κ*(∑ i ∈ R, length i) ≤ F/6+κ*η ∧
      (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) := by
  obtain ⟨R,hRs,hR,hpay⟩ := whole_slot_removal s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,?_,hpay.imp_right sub_nonpos.mpr⟩
  have hh := mul_le_mul_of_nonneg_left (hR.trans (min_le_right _ _)) hκ.le
  have he : κ*(F/(6*κ)+η)=F/6+κ*η := by field_simp
  rwa [he] at hh

theorem actual_product_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧ (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) ∧
      ∀ (Z : ℝ), 1 ≤ Z → ∀ (C : α → ℝ), (∀ i ∈ s, 0 ≤ C i) →
      ∀ (Q : α → ℂ), (∀ i ∈ s, ‖Q i‖^2 ≤ C i*Z^(κ*length i)) →
      ‖∏ i ∈ s, Q i‖^2 ≤
        (∏ i ∈ R, C i)*Z^(F/6+κ*η)*‖∏ i ∈ s\R, Q i‖^2 := by
  obtain ⟨R,hRs,hcost,hpay⟩ := removal_cost s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,hpay,?_⟩
  intro Z hZ C hC Q hQ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hremoved : ‖∏ i ∈ R, Q i‖^2 ≤ (∏ i ∈ R, C i)*Z^(F/6+κ*η) := by
    rw [norm_prod,← Finset.prod_pow]
    calc
      _ ≤ ∏ i ∈ R, C i*Z^(κ*length i) :=
        Finset.prod_le_prod₀ (fun i hi => sq_nonneg _) (fun i hi => hQ i (hRs hi))
      _ = (∏ i ∈ R, C i)*Z^(κ*(∑ i ∈ R, length i)) := by
        rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.rpow_sum_of_pos hZpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hcost) (Finset.prod_nonneg (fun i hi => hC i (hRs hi)))
  have he : (∏ i ∈ s, Q i)=(∏ i ∈ s\R, Q i)*(∏ i ∈ R, Q i) :=
    (Finset.prod_sdiff hRs).symm
  rw [he,norm_mul,mul_pow,mul_comm (‖∏ i ∈ s\R, Q i‖^2)]
  exact mul_le_mul_of_nonneg_right hremoved (sq_nonneg _)

end SevenEighths.CenteredMomentSlotRemoval

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.TwistedReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open CenteredMomentReflectionDeletion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma polynomial_twisted_source (χ : Character) (W : ℝ→ℂ) (X t : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

theorem actual_original_twisted_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(_ha : 0<a)(_hs : Function.support W⊆Set.Icc a b)
        (_hW : ContDiff ℝ ∞ W)(omega X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 omega=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false
                (paperRadialFourier (CompletedHeight.normTwistedSource W (omega/(2*Real.pi))))
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,hreflect⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W a b ha hs hW omega X hX
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi)) : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W (omega/(2*Real.pi)) := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW _ x
  have hh := hreflect (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi))) X hX
  rw [he] at hh
  have ht : 2*Real.pi*(omega/(2*Real.pi))=omega := by field_simp
  rw [←ht,polynomial_twisted_source χ W X (omega/(2*Real.pi)) hX]
  simpa only [ht] using hh

end SevenEighths.CenteredMomentTwistedReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionEnergy
open HeckeFamily CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentComparisonReflection
open EisensteinSchwartzPoisson

lemma polynomial_inverse_plain (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false W X 0 0=
      conj (HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0) := by
  rw [polynomial_plain _ _ _ hX,polynomial_plain _ _ _ hX,map_mul,map_inv₀,
    Complex.conj_ofReal,Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro I
  rw [map_mul,idealCoeff_inverse_conj,Complex.conj_conj]

lemma polynomial_inverse_norm (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    ‖HeckeDyadic.polynomial χ.inverse false W X 0 0‖=
      ‖HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0‖ := by
  rw [polynomial_inverse_plain χ W X hX,Complex.norm_conj]

theorem actual_one_uniform (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s t X Y omega : ι→ℝ)(Wshort : ℝ→ℂ),
        (∀i,0<s i) → (∀i,0<X i) →
      ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V W A n (s i) (t i)) (X i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤C*E := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A (J+2)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨(C*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s t X Y omega Wshort hs hX E hE henergy
  choose d hid hi hm hp using fun i=>hb (t i) (s i) (hs i)
  let e (i : ι) : ℂ := heightScale A n (s i) (t i)
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (CompletedHeight.normTwistedSource W (t i)) x
  let Q (i : ι) := HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*Q i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*FourierBridge.logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*FourierBridge.logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*FourierBridge.logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (normalizedReflected V W A n (s i) (t i)) (X i) 0 0*Q i=
      ∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : normalizedReflected V W A n (s i) (t i)=
        (fun x=>logWindow V x*F i (s i*x)) := by
      funext x
      dsimp [normalizedReflected,F,e]
      ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (Q i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope C J)
    (fun v=>(1+‖v‖)^J) (envelope_pos C hC J) (by intro v;positivity)
    (fun i=>normalized_density_bound A n J (s i) (t i) C (hs i) (d i) (hp i)) hint
    (envelope_integrable C J) E hE (by
      intro v
      simpa only [φ,Q,mul_assoc] using henergy v)
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  simpa only [Q,mul_assoc,mul_comm E] using hh

end SevenEighths.CenteredMomentOneReflectionEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentReflectedNormalization
open HeckeFamily CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson

lemma actual_log_window :
    CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow=
      (fun x : ℝ=>(annulus x:ℂ)) := by
  funext x
  unfold CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow
  split_ifs with hx
  · rw [Real.exp_log hx]
  · rw [annulus_zero_low x (by linarith)]
    rfl

lemma polynomial_const (χ : Character) (W : ℝ→ℂ) (X : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X 0 0=
      c*HeckeDyadic.polynomial χ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  have he (I : HeckeDyadic.NonzeroIdeal) :
      HeckeDyadic.summand χ false (fun x=>c*W x) X 0 0 I=
        c*HeckeDyadic.summand χ false W X 0 0 I := by
    unfold HeckeDyadic.summand
    ring
  simp_rw [he,tsum_mul_left]
  ring

lemma normalized_profile_actual (W : ℝ→ℂ) (B n : ℕ) (s t x : ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n s t x=
      (heightScale B n s t:ℂ)*CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) s x := by
  unfold normalizedReflected
  rw [actual_log_window]
  unfold CenteredMomentReflectedAnnuli.annularProfile
  ring

theorem actual_annular_normalization (χ : Character) (W : ℝ→ℂ) (B n : ℕ)
    (k : ℤ) (t Y : ℝ) :
    (Real.sqrt (dyadicScale k):ℂ)*HeckeDyadic.polynomial χ false
      (CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k))
      (dyadicScale k*Y) 0 0=
      (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
        HeckeDyadic.polynomial χ false
          (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t)
          (dyadicScale k*Y) 0 0 := by
  have hf : normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t=
      (fun x=>(heightScale B n (dyadicScale k) t:ℂ)*
        CenteredMomentReflectedAnnuli.annularProfile
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k) x) :=
    funext (normalized_profile_actual W B n (dyadicScale k) t)
  rw [hf,polynomial_const]
  have hh : (1+‖t‖)^n*CenteredMomentReflectedAnnuli.annularMass B k*
      heightScale B n (dyadicScale k) t=Real.sqrt (dyadicScale k) := by
    unfold CenteredMomentReflectedAnnuli.annularMass heightScale
    have ht : (1+‖t‖)^n≠0 := ne_of_gt (by positivity)
    have hs : (1+dyadicScale k)^B≠0 := ne_of_gt (by have := dyadicScale_pos k;positivity)
    field_simp
  have hc : (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
      (heightScale B n (dyadicScale k) t:ℂ)=(Real.sqrt (dyadicScale k):ℂ) := by
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,hh]
  rw [←mul_assoc _ (heightScale B n (dyadicScale k) t:ℂ),hc]

end SevenEighths.CenteredMomentReflectedNormalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

lemma annular_inverse_frequency_norm (χ : Character) (X v : ℝ) (hX : 0<X) :
    ‖polynomial χ.inverse false
      (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
      X 0 (2*Real.pi*v)‖=
    ‖polynomial χ false (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v)‖ := by
  rw [actual_log_window]
  have hh := HeckeInverseAmplification.polynomial_inverse_norm χ false
    (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v) hX
  simpa only [Complex.conj_ofReal,neg_mul,neg_neg] using hh

theorem actual_one_rowwise_scales (a b : ℝ) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)
      (s t lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Icc lo hi) → (∀i,ly i∈Icc low high) →
      (∀i,0<s i) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Icc lo hi,∀y∈Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong A n (s i) (t i))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionEnergy.actual_one_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) a b hlog hwindow ha A J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hbound⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ χ P s t lx ly omega Wshort c d lo hi low high E hd hshort hshortsmooth
    hlh hlw hlx hly hspos hE henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i).inverse false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by
      rw [←pow_mul,Nat.mul_comm J 2]
    calc
      _ = ∑i,‖polynomial (χ i) false (fun z : ℝ=>(annulus z:ℂ))
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [norm_mul,annular_inverse_frequency_norm (χ i) _ v (Real.exp_pos _)]
      _ ≤ (1+2*(hi-lo))*((1+2*(high-low))*(E*(1+‖v‖)^(2*J))) := hh
      _ = _ := by rw [hp];ring
  have hh := hbound (fun i=>(χ i).inverse) χ P s t (fun i=>Real.exp (lx i))
    (fun i=>Real.exp (ly i)) omega Wshort hspos (fun i=>Real.exp_pos _)
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) (mul_nonneg hdx (mul_nonneg hdy hE)) hfixed
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectedChoiceEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentReflectionDeletion CenteredMomentReflectionTailMass
open CenteredMomentNaturalPrimitive CenteredMomentReflectionRetainedLength
open Filter

local notation "O" => HeckeFamily.O

theorem actual_independent_profile_choices (a b : ℝ) (ha : 0<a) (B J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (t ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong B n (s i (u i)) (t i))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionScaleEnergy.actual_one_rowwise_scales a b ha B J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ α χ P s X keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hE henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb χ P' (fun i=>s i (u i)) t lx ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hE he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0<Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤dyadicScale u.2*Y ∧
      0≤Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=>hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0<Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

end SevenEighths.CenteredMomentReflectedChoiceEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RetainedReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma masked_decayTwo (F : ℝ→ℂ) (hF : DecayTwo F) (w : ℝ→ℝ)
    (hw : ∀x,0≤w x ∧ w x≤1) : DecayTwo (fun x=>(w x:ℂ)*F x) := by
  obtain ⟨D,hD,hb⟩ := hF
  refine ⟨D,hD,?_⟩
  intro x hx
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x).1]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) (hw x).2) (sq_nonneg x)).trans (hb x hx)

lemma column_retained_discarded (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false F Y 0 0=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0+
      HeckeDyadic.polynomial η false (fun x=>(discardedWeight R x:ℂ)*F x) Y 0 0 := by
  have hr := plain_summable η _ (masked_decayTwo F hF _ (retainedWeight_bounds R)) Y hY
  have hd := plain_summable η _ (masked_decayTwo F hF _ (discardedWeight_bounds R)) Y hY
  simp only [CenteredMomentReflectionDeletion.norm] at hr hd
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,
    ←mul_add,←hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro I
  have hp := retained_add_discarded R (norm I/Y) (div_pos (norm_pos I) hY)
  simp only [CenteredMomentReflectionDeletion.norm] at hp ⊢
  rw [←mul_add,←add_mul,←Complex.ofReal_add,hp,Complex.ofReal_one,one_mul]

lemma bounded_columns (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F) :
    ∃C : ℝ,0≤C ∧ ∀Y U : ℝ,0<Y → Y≤U →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*U^(3/2:ℝ) := by
  obtain ⟨D,hD,hF⟩ := hF
  obtain ⟨C,hC,hb⟩ := plain_rapid_bound 2 (by omega)
  refine ⟨C*D,by positivity,?_⟩
  intro Y U hY hYU
  apply (hb η F D Y hD hY hF).trans
  rw [normalized_power_eq Y hY 2]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY.le hYU (by norm_num)) (by positivity)

lemma reflected_column_summable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η ηi χ : Character) (F : ℝ→ℂ) (hF : DecayTwo F) (Q X : ℝ)
    (hQ : 0<Q) (hX : 0<X) (D : Finset (Ideal O)) (hD : D∈S.powerset) :
    Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
      HeckeDyadic.polynomial χ false F
        (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0) := by
  obtain ⟨C,hC,hb⟩ := bounded_columns χ F hF
  obtain ⟨K,hK,hKb⟩ := coefficient_column_bound 1 (by norm_num)
  let U := Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X
  have hu : 0<U := div_pos (mul_pos hQ (subset_product_norm_pos S hS)) hX
  exact (hKb S hS η ηi (fun E H=>HeckeDyadic.polynomial χ false F
    (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*U^(3/2:ℝ)) (by positivity) (by
      intro E hE H
      have hscale := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X U hQ hX (by
        dsimp [U]
        rw [div_mul_cancel₀ _ hX.ne'])
      exact hb _ U hscale.1 hscale.2)).1 D hD

theorem original_retained_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X R : ℝ)(_hX : 0<X),
        let Q := (ψ.modulus.absNorm:ℝ)
        let Y := fun (D : Finset (Ideal O))(H : SmoothIdeal S)=>Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)
        HeckeDyadic.polynomial χ false W X 0 0=
          G*((∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0)+
            ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0) := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W X R hX
  dsimp only
  rw [heq W X hX]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo W
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  rw [←hr.tsum_add hd]
  apply tsum_congr
  intro H
  have hY := (dual_scale_bounds _ D hS (Finset.mem_powerset.mp hD) H
    (ψ.modulus.absNorm:ℝ) X ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈redundantSet χ.modulus ψ.modulus,P):ℝ)/X)
    hQ hX (by rw [div_mul_cancel₀ _ hX.ne'])).1
  change coefficient ψ ψ.inverse _ D H*HeckeDyadic.polynomial χ.inverse false
    (paperRadialFourier W) _ 0 0=_
  rw [column_retained_discarded χ.inverse _ hF R _ hY,mul_add]

end SevenEighths.CenteredMomentRetainedReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open CenteredMomentRetainedReflection CenteredMomentTwistedReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def finiteAnnularColumn (η : Character) (F : ℝ→ℂ) (R Y : ℝ) : ℂ :=
  if hY : 0<Y then ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
    HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0

lemma finiteAnnularColumn_eq (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) : finiteAnnularColumn η F R Y=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0 := by
  rw [finiteAnnularColumn,dite_eq_left hY]
  exact (retained_finite_series η F hF R Y hY).symm

def retainedOriginal (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
    finiteAnnularColumn χ.inverse
      (paperRadialFourier (CompletedHeight.normTwistedSource W t)) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val))

lemma radical_le_original (χ ψ : Character)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)

theorem actual_original_retained_approximation (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(χ : Character),χ.residue≠1 →
        ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
        ∀(X t Z : ℝ),0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
          ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
            G*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
            C*(χ.modulus.absNorm:ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_deleted_discarded_negligible a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro χ hχ
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_retained_reflection χ hχ
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro X t Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  let Wt := CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t
  have heWt : (Wt : ℝ→ℂ)=CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : DecayTwo (paperRadialFourier (CompletedHeight.normTwistedSource W t)) := by
    rw [←heWt]
    exact reflected_decayTwo Wt
  have hret : retainedOriginal χ ψ W X (Z^(xi/2)) t=
      ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(retainedWeight (Z^(xi/2)) x:ℂ)*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
    unfold retainedOriginal
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro H
    rw [finiteAnnularColumn_eq _ _ hF _ _
      (dual_scale_bounds S D hS (Finset.mem_powerset.mp hD) H _ X _ hQ hX hcap').1]
  have hsource := heq Wt X (Z^(xi/2)) hX
  dsimp only at hsource
  rw [heWt] at hsource
  rw [polynomial_twisted_source χ W X t hX,hsource,←hret]
  rw [mul_add,add_sub_cancel_left,norm_mul,hG,one_mul]
  have hb := (hCb S hS ψ ψ.inverse χ.inverse t _ X Z hZ hQ hX hcap').2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hε.le

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionEnergy
open HeckeFamily CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_sq_comparison (a b : ℂ) : ‖a‖^2≤2*‖b‖^2+2*‖a-b‖^2 := by
  have he : a=b+(a-b) := by ring
  have hh : ‖a‖≤‖b‖+‖a-b‖ := by nth_rw 1 [he];exact norm_add_le _ _
  nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (a-b),sq_nonneg (‖b‖-‖a-b‖)]

theorem actual_original_energy_to_retained (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(X t : ι→ℝ)(P : ι→ℂ)(T Z Rcap : ℝ),0≤T → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,‖t i‖≤T) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2)≤
            2*(∑i,‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2)+
            C*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_original_retained_approximation a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro X t P T Z Rcap hT hZ hR hX ht hmod hsource
  let B := C*Rcap^ε*(1+T)^n*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)-
        G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)‖≤B := by
    apply (happrox i (X i) (t i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le) hC.le)
      (pow_le_pow_left₀ (by positivity) (by simpa only [Real.norm_eq_abs,add_comm] using add_le_add_left (ht i) 1) n) (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2≤
      2*‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i)
      ((G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i-
        (G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz,←pow_mul]
    rw [Nat.mul_comm n 2]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentOriginalReflectionEnergy

end

end OAI

end

