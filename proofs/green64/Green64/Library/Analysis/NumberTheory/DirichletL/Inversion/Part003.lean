module

public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.InitialKernelBridge
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

def elementCharacter (η : Ideal O →* ℂ) : O →* ℂ where
  toFun x := η (Ideal.span {x})
  map_one' := by rw [Ideal.span_singleton_one, ←Ideal.one_eq_top, map_one]
  map_mul' x y := by rw [←Ideal.span_singleton_mul_span_singleton,map_mul]

theorem elementCharacter_product {ι : Type*} (η : Ideal O →* ℂ)
    (p : ι → O) (A : Finset ι) :
    elementCharacter η (∏ i ∈ A,p i) = η (∏ i ∈ A,Ideal.span {p i}) := by
  change η (Ideal.span {∏ i ∈ A,p i}) = _
  rw [FiniteGaussPhase.span_finset_prod]

def reconstructedSelector (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j))) : ℂ :=
  if (∏ i ∈ A,i.val) ∈ columns S P j then a (reconstruct P j (∏ i ∈ A,i.val)) else 0

theorem poolPrimary_injective (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I) :
    Function.Injective (fun i : primePool F => Ideal.span {poolPrimary F i}) := by
  intro i k he
  change Ideal.span {poolPrimary F i} = Ideal.span {poolPrimary F k} at he
  rw [poolPrimary_span F hF,poolPrimary_span F hF] at he
  exact Subtype.ext he

theorem poolPrimary_primary (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (i : primePool F) : goodLambda^2 ∣ poolPrimary F i-1 :=
  (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2

theorem selected_mask (F : Finset (Ideal O)) (j : Ideal O) (hj : Admissible j)
    (A : Finset (primePool F)) (hcop : IsCoprime (∏ i ∈ A,i.val) j) :
    rowCoprimeMask (fun i : primePool F => i.val) A (primaryGenerator j)=1 := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  unfold rowCoprimeMask
  split_ifs with h
  · obtain ⟨i,hi,hm⟩ := h
    have hd : i.val ∣ ∏ k ∈ A,k.val := Finset.dvd_prod_of_mem _ hi
    have hjd : i.val ∣ j := by
      rw [Ideal.dvd_iff_le,←hspan]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have hp : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    exact False.elim (hp.not_isUnit (hcop.isRelPrime hd hjd))
  · rfl

theorem selected_conjugate_row (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (hcop : ∀ I ∈ F,IsCoprime I j) (η : Ideal O →* ℂ) (H : Ideal O → ℂ) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  erw [initial_input_row]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    rw [selected_mask F j hj A (hcop _ hAF),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_input (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    let F := columns S P j
    let hF : ∀ I ∈ F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      (Z^(-(r+z-2*G)/2) : ℝ)*
        inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (fun A => reconstructedSelector S P j a A *
            residualOverlapWindow P j W Z z G
              ((Ideal.absNorm (∏ i ∈ A,i.val) : ℝ)/Z^(r+z-2*G))) u := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold residualNormalizedPolynomial
  congr 1
  have hc : ∀ I ∈ F,IsCoprime I j := fun I hI => ((mem_columns hP.2.1 hj).mp hI).2.1
  have ht := selected_conjugate_row F hF j (admissible_of_dvd hP hj) hc η
    (fun I => a (reconstruct P j I)*residualOverlapWindow P j W Z z G
      ((Ideal.absNorm I : ℝ)/Z^(r+z-2*G))) u
  convert ht using 1
  · apply Finset.sum_congr rfl
    intro I hI
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  · congr 1
    funext A
    unfold reconstructedSelector
    dsimp only [F]
    split_ifs <;> simp only [zero_mul]

section RayModes
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})
open FirstPassCubeLabels (primeProductNorm primeProductNorm_union)

def initialTest (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (A : Finset ι) : ℂ :=
  σ A*V (primeProductNorm p A/Z^D)

def initialBeta (Ψ : O →* ℂ) (j : O) (G : Finset ι) : ℂ :=
  (‖Ψ (∏ i ∈ G,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) G j‖^2 : ℝ)

theorem initial_overlap_weight (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι → ℂ) (V : ℝ → ℂ) (Z D : ℝ) (G U T : Finset ι) :
    overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T =
      initialBeta p Ψ j G *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
        (supportMobius (fun i => Ideal.span {p i}) T *
          secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
        star (V (primeProductNorm p (G∪U)/Z^D))*V (primeProductNorm p (G∪T)/Z^D) := by
  have hrow (A : Finset ι) :
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A 1 = 1 :=
    finiteSquarefreeRow_one _ hg A
  simp only [overlapPairWeight,secondInputCoefficient,initialBeta,initialTest,
    hrow,one_pow,mul_one,star_mul]
  ring

theorem initial_pair_rays
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j e h : O) (σ : Finset ι → ℂ)
    (G U T : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) :
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) U) *
      (supportMobius (fun i => Ideal.span {p i}) T *
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) T) *
      activeGaussRowFactor p hp hinj hg T U e h =
    ∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i) e h
        (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i) e (-h)
        (fun A => σ (G∪A)) T := by
  have hm (A : Finset ι) (hAG : Disjoint A G) :
      secondInputCoefficient p hg Ψ (j*∏ i ∈ G,p i) 1 1 (fun A => σ (G∪A)) A =
        secondInputCoefficient p hg Ψ j 1 1 (fun A => σ (G∪A)) A := by
    erw [secondInputCoefficient_fixed_mask,commonProduct_mask p hg hinj]
    simp only [hAG,ite_true,one_mul]
  have he := second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ Ψ
    (j*∏ i ∈ G,p i) 1 1 e h (fun A => σ (G∪A)) (fun A => σ (G∪A)) U T hUT
  rw [hm U hGU.symm,hm T hGT.symm] at he
  simpa only [Fintype.sum_prod_type,secondRayCoefficient,secondRayMinus,secondRayPlus,
    initialColumn_eq_secondPre] using he

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem initial_product_kernel (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) (h : O) :
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h) =
    ((Z^(-D) : ℝ) : ℂ)*star (V (primeProductNorm p (G∪U)/Z^D))*
      V (primeProductNorm p (G∪T)/Z^D)*
      ((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ) *
      (1/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) := by
  have hn := active_norm_sq_disjoint p U T hUT
  have hr : Real.sqrt (primeProductNorm p U*primeProductNorm p T) =
      ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ := by
    rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have he : (Ideal.absNorm (sourceIdeal p E) : ℝ) =
      ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 := by
    rw [primeSubsetGenerator_norm_sq,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  have hnorm (A : Finset ι) : (Ideal.absNorm (sourceIdeal p A) : ℝ)=primeProductNorm p A :=
    (eisEmbedding_norm_sq_eq_absNorm_span _).symm
  unfold physicalKernel physicalCoordinates
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    hnorm,map_one,Nat.cast_one,mul_one,one_pow]
  rw [hr,←hnorm E,he,hn]
  rw [primeProductNorm_union p G U hGU,primeProductNorm_union p G T hGT]
  push_cast
  ring_nf

def initialPhysicalMode (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι) (h : O) : ℂ :=
  initialBeta p Ψ j G * (moebius (sourceIdeal p E) : ℂ) *
    (∑ ρ : SecondRayIndex,secondRayCoefficient ρ *
      star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h (fun A => σ (G∪A)) U) *
      initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i ∈ G,p i)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (-h) (fun A => σ (G∪A)) T) *
    physicalKernel (fun x => star (V x)) V Φ Z D m
      (physicalCoordinates (sourceIdeal p G) (sourceIdeal p E) 1
        (sourceIdeal p U) (sourceIdeal p T) h)

theorem normalized_overlap_mode
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) (G U T E : Finset ι)
    (hGU : Disjoint G U) (hGT : Disjoint G T) (hUT : Disjoint U T) (h : O) :
    ((Z^(-D) : ℝ) : ℂ)*
      overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T *
      (((Z^m : ℝ) : ℂ)/(‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖ : ℂ)) *
      ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ)) *
      (paperRadialFourier Φ (Z^m*‖eisEmbedding h‖^2/
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T U,p i.val)‖^2)) *
        activeGaussRowFactor p hp hinj hg T U
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E) h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h := by
  rw [initial_overlap_weight]
  unfold initialPhysicalMode
  rw [←initial_pair_rays p hp hcop hg hinj hc hpr Ψ j _ h σ G U T hGU hGT hUT,
    initial_product_kernel p V Φ Z D m G U T E hGU hGT hUT h]
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  ring

theorem initial_input_physical
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (F : Finset ι) (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2) : ℝ) : ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ)) =
    ∑ G ∈ F.powerset,∑ U ∈ (F\G).powerset,∑ T ∈ (F\G).powerset,
      if Disjoint U T then ∑ E ∈ G.powerset,∑' h : O,
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h else 0 := by
  have hn := norm_rpow_half_sq hZ D
  simp only [norm_mul,mul_pow,hn,Complex.ofReal_mul]
  have hs : (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (((Z^(-D) : ℝ) : ℂ)*(‖inputConjugateRow p hg F Ψ j 1 1
        (initialTest p σ V Z D) u‖^2 : ℝ))) =
      ((Z^(-D) : ℝ) : ℂ)*(∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖inputConjugateRow p hg F Ψ j 1 1 (initialTest p σ V Z D) u‖^2 : ℝ)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro u
    ring
  rw [hs,inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ j 1 1
    (initialTest p σ V Z D) Φ (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hUT : Disjoint U T
  · simp only [hUT,ite_true]
    have hGU : Disjoint G U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    unfold maskedSecondDual
    simp only [Finset.mul_sum,←tsum_mul_left]
    apply Finset.sum_congr rfl
    intro E hE
    apply tsum_congr
    intro h
    convert normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
      Z D m G U T E hGU hGT hUT h using 1
    ring
  · simp only [hUT,ite_false,mul_zero]

theorem initialPhysicalMode_summable
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    Summable (initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E) := by
  have hs := secondPairRadialMode_summable p hp hg hinj U T
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E) (primeSubsetGenerator_ne_zero _ _)
    Φ (Z^m) (Real.rpow_pos_of_pos hZ m)
  have hs' := (hs.mul_left ((moebius (∏ i ∈ E,Ideal.span {p i}) : ℂ)/
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 : ℝ))).mul_left
    (((Z^(-D) : ℝ) : ℂ)*overlapPairWeight p hg Ψ j 1 1 (initialTest p σ V Z D) G U T)
  apply hs'.congr
  intro h
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ V Φ
    Z D m G U T E hGU hGT hUT h]
  unfold secondPairRadialMode
  ring

theorem initialPhysicalMode_zero_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι → ℂ)
    (V : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) {Z : ℝ} (hZ : 0<Z) (D m : ℝ)
    (G U T E : Finset ι) (hGU : Disjoint G U) (hGT : Disjoint G T)
    (hUT : Disjoint U T) :
    (∑' h : O,initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h) =
      initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E 0 +
      ∑' h : O,if h=0 then 0 else
        initialPhysicalMode p hp hcop hg Ψ j σ V Φ Z D m G U T E h :=
  (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j σ V Φ hZ D m
    G U T E hGU hGT hUT).tsum_eq_add_tsum_ite 0

end RayModes

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F,Admissible I)
    (A : Finset (primePool F)) :
    FirstPassCubeLabels.primeProductNorm (poolPrimary F) A = (Ideal.absNorm (∏ i ∈ A,i.val) : ℝ) := by
  unfold FirstPassCubeLabels.primeProductNorm
  rw [eisEmbedding_norm_sq_eq_absNorm_span,FiniteGaussPhase.span_finset_prod]
  simp only [poolPrimary_span F hF]

theorem reconstructedSelector_support (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j)))
    (hA : reconstructedSelector S P j a A≠0) : (∏ i ∈ A,i.val)∈columns S P j := by
  by_contra h
  exact hA (by simp only [reconstructedSelector,h,ite_false])

theorem reconstructedSelector_original (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j∣P) (a : Ideal O → ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : reconstructedSelector S P j a A≠0) :
    Squarefree (∏ i ∈ A,i.val) ∧ IsCoprime (∏ i ∈ A,i.val) j ∧
      residual P j ∣ (∏ i ∈ A,i.val) ∧ reconstruct P j (∏ i ∈ A,i.val)∈S :=
  (mem_columns hP hj).mp (reconstructedSelector_support S P j a A hA)

theorem reconstructedSelector_empty (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (h : columns S P j=∅) (A : Finset (primePool (columns S P j))) :
    reconstructedSelector S P j a A=0 := by simp only [reconstructedSelector,h,Finset.notMem_empty,ite_false]

theorem residual_empty (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ)
    (h : columns S P j=∅) (u : O) :
    residualNormalizedPolynomial S P j η a W Z r z G u=0 := by
  simp only [residualNormalizedPolynomial,h,Finset.sum_empty,mul_zero]

theorem residual_eq_initialTest (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P)
    (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2) : ℝ) : ℂ)*inputConjugateRow (poolPrimary F)
        (poolPrimary_good F hF) Finset.univ (elementCharacter η) (primaryGenerator j) 1 1
        (initialTest (poolPrimary F) (reconstructedSelector S P j a)
          (residualOverlapWindow P j W Z z G) Z (r+z-2*G)) u := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [residual_eq_input S hP hj hS η a W Z r z G u]
  congr 2
  funext A
  simp only [initialTest,poolPrimary_norm F hF]
  rfl

theorem residual_initial_physical_rays (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P)
    (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
    ∑ C ∈ (Finset.univ : Finset (primePool F)).powerset,
      ∑ U ∈ (Finset.univ\C).powerset,∑ T ∈ (Finset.univ\C).powerset,
        if Disjoint U T then ∑ E ∈ C.powerset,∑' h : O,
          initialPhysicalMode (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) (elementCharacter η) (primaryGenerator j)
            (reconstructedSelector S P j a) (residualOverlapWindow P j W Z z G)
            Φ Z (r+z-2*G) m C U T E h else 0 := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  simp_rw [residual_eq_initialTest S hP hj hS η a W Z r z G]
  exact initial_input_physical (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_injective F hF)
    (poolPrimary_odd F hF) (poolPrimary_primary F hF) Finset.univ (elementCharacter η)
    (primaryGenerator j) (reconstructedSelector S P j a) (residualOverlapWindow P j W Z z G)
    Φ hZ (r+z-2*G) m

theorem idealPair_product_transport (F : Finset (Ideal O))
    (hF : ∀ I∈F,Admissible I) (I J : Ideal O) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) I J Φ Y =
      GaussGeneratorTransport.squarefreePairProductPoissonKernel (poolPrimary F)
        (poolPrimary_ne_zero F hF) (poolPrimary_injective F hF) (poolPrimary_good F hF)
        (idealSupport F I) (idealSupport F J) Φ Y := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  have ht := GaussGeneratorTransport.squarefreePairPoissonKernel_eq_product
    (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_injective F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J) Φ Y
  simpa only [he,idealPairPoissonKernel] using ht

end SevenEighths.InverseInitialRayAttachment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialRayAttachment
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def conjugateIdealCharacter (η : Ideal O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (η I)
  map_one' := by rw [map_one,star_one]
  map_mul' I J := by simp [map_mul]

@[simp] theorem conjugateIdealCharacter_apply (η : Ideal O →* ℂ) (I : Ideal O) :
    conjugateIdealCharacter η I = star (η I) := rfl

theorem reconstructedSelector_conjugate (S : Finset (Ideal O)) (P j : Ideal O)
    (a : Ideal O → ℂ) (A : Finset (primePool (columns S P j))) :
    reconstructedSelector S P j (fun I => star (a I)) A =
      star (reconstructedSelector S P j a A) := by
  unfold reconstructedSelector
  split_ifs <;> simp

theorem overlapResidualCoefficient_conjugate (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal O) :
    overlapResidualCoefficient P j (conjugateIdealCharacter η)
        (fun I => star (a I)) (fun x => star (W x)) Z r z G c =
      star (overlapResidualCoefficient P j η a W Z r z G c) := by
  simp [overlapResidualCoefficient, star_mul, mul_comm, mul_left_comm, mul_assoc]

def conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (u : O) : ℂ :=
  residualNormalizedPolynomial S P j (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) Z r z G u

theorem star_conjugatedResidual (S : Finset (Ideal O)) (P j : Ideal O)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : O) :
    star (conjugatedResidual S P j η a W Z r z G u) =
      (Z^(-(r+z-2*G)/2) : ℝ) *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  unfold conjugatedResidual residualNormalizedPolynomial
  simp_rw [overlapResidualCoefficient_conjugate]
  simp [rowPolynomial, mul_comm]

theorem originalFixedPolynomial_eq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    originalFixedPolynomial S P j η a W Z r z u =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * (Z^(-G) : ℝ) *
        η j^2 * (idealRowHom u j)^2 * star (conjugatedResidual S P j η a W Z r z G u) := by
  rw [originalFixedPolynomial_eq S hP hj η a W hZ r z G,
    star_conjugatedResidual]
  unfold overlapPrefactor
  ring

theorem originalFixedPolynomial_norm_sq_conjugatedResidual (S : Finset (Ideal O))
    {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      Z^(-2*G) * ‖η j‖^4 * ‖idealRowHom u j‖^4 *
        ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_eq_conjugatedResidual S hP hj η a W hZ r z G]
  have hjn : ‖(moebius j : ℂ)‖=1 := by simp [(hP.squarefree_of_dvd hj).moebius_eq]
  have hpn : ‖(moebius (residual P j) : ℂ)‖=1 := by simp [(residual_squarefree hP hj).moebius_eq]
  have hp : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  simp only [norm_mul,norm_pow,norm_star,hjn,hpn,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ (-G)),mul_pow]
  rw [hp]
  ring

theorem admissible_row_four_le_one (I : Ideal O) (hI : Admissible I) (u : O) :
    ‖idealRowHom u I‖^4 ≤ 1 := by
  have he := norm_idealRowHom_four_eq_two I hI u
  have hs : 0≤‖idealRowHom u I‖^2 := sq_nonneg _
  have ht : ‖idealRowHom u I‖^4=(‖idealRowHom u I‖^2)^2 := by ring
  rw [ht] at he ⊢
  nlinarith

theorem originalFixedPolynomial_norm_sq_le (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z) (r z G : ℝ) (u : O) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 ≤
      Z^(-2*G) * ‖η j‖^4 * ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  rw [originalFixedPolynomial_norm_sq_conjugatedResidual S hP.2.1 hj η a W hZ r z G]
  have hm := admissible_row_four_le_one j (admissible_of_dvd hP hj) u
  have hz := (Real.rpow_pos_of_pos hZ (-2*G)).le
  nlinarith [mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4),
    mul_nonneg (mul_nonneg hz (pow_nonneg (norm_nonneg (η j)) 4))
      (sq_nonneg ‖conjugatedResidual S P j η a W Z r z G u‖)]

theorem finite_weighted_triangle {α β : Type*} (J : Finset α) (R : Finset β)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ) :
    (∑ u ∈ R,w u * ‖∑ j ∈ J,F j u‖^2) ≤
      (∑ j ∈ J,Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2))^2 := by
  let v (j : α) : EuclideanSpace ℂ R :=
    WithLp.toLp 2 (fun u => (Real.sqrt (w u) : ℂ)*F j u)
  have hv (j : α) : ‖v j‖^2=∑ u ∈ R,w u*‖F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [v,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖F j u‖^2)
  have hsum : ‖∑ j ∈ J,v j‖^2=∑ u ∈ R,w u*‖∑ j ∈ J,F j u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,v,←Finset.mul_sum,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hw _)]
    exact Finset.sum_coe_sort R (fun u => w u*‖∑ j ∈ J,F j u‖^2)
  have hs := norm_sum_le J v
  have hn (j : α) : ‖v j‖=Real.sqrt (∑ u ∈ R,w u*‖F j u‖^2) := by
    rw [←hv,Real.sqrt_sq (norm_nonneg _)]
  have hh := pow_le_pow_left₀ (norm_nonneg _) hs 2
  simpa only [hsum,hn] using hh

theorem weighted_overlap_triangle {α β : Type*} (J : Finset α)
    (w : β → ℝ) (hw : ∀ u,0≤w u) (F : α → β → ℂ)
    (hs : ∀ j∈J,Summable (fun u => w u*‖F j u‖^2)) :
    Summable (fun u => w u*‖∑ j∈J,F j u‖^2) ∧
      (∑' u,w u*‖∑ j∈J,F j u‖^2) ≤
        (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
  have hn (u : β) : 0≤w u*‖∑ j∈J,F j u‖^2 := mul_nonneg (hw u) (sq_nonneg _)
  have hb (R : Finset β) : (∑ u∈R,w u*‖∑ j∈J,F j u‖^2) ≤
      (∑ j∈J,Real.sqrt (∑' u,w u*‖F j u‖^2))^2 := by
    refine (finite_weighted_triangle J R w hw F).trans ?_
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    exact (hs j hj).sum_le_tsum R (fun u _ => mul_nonneg (hw u) (sq_nonneg _))
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

def radialWeight (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (u : O) : ℝ :=
  (Φ (‖eisEmbedding u‖^2/Y)).re

def smoothedEnergy (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (f : O → ℂ) : ℝ :=
  ∑' u,radialWeight Φ Y u*‖f u‖^2

theorem radialWeight_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (u : O) : 0≤ radialWeight Φ Y u :=
  hΦ _ (div_nonneg (sq_nonneg _) hY.le)

theorem smoothedEnergy_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (f : O → ℂ) : 0≤ smoothedEnergy Φ Y f :=
  tsum_nonneg (fun u => mul_nonneg (radialWeight_nonneg Φ hΦ hY u) (sq_nonneg _))

theorem original_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalFixedPolynomial S P j η a W Z r z u‖^2) := by
  have hs := original_fixed_overlap_smoothed_summable S hP hj hS η a W hZ r z G Φ Y hY
  simpa only [radialWeight,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem conjugatedResidual_energy_summable (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖conjugatedResidual S P j η a W Z r z G u‖^2) := by
  have hs := residual_normalized_smoothed_summable S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G Φ Y hY
  simpa only [radialWeight,conjugatedResidual,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using (Complex.hasSum_re hs.hasSum).summable

theorem original_smoothed_mask_identity (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j∣P) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    smoothedEnergy Φ Y (originalFixedPolynomial S P j η a W Z r z) =
      Z^(-2*G)*‖η j‖^4 * ∑' u,radialWeight Φ Y u*‖idealRowHom u j‖^4*
        ‖conjugatedResidual S P j η a W Z r z G u‖^2 := by
  unfold smoothedEnergy
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  rw [originalFixedPolynomial_norm_sq_conjugatedResidual S hP hj η a W hZ r z G]
  ring

theorem original_smoothed_contraction (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z G : ℝ) (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalFixedPolynomial S P j η a W Z r z) ≤
      Z^(-2*G)*‖η j‖^4 * smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z G) := by
  unfold smoothedEnergy
  rw [←tsum_mul_left]
  apply (original_energy_summable S hP hj hS η a W hZ r z G Φ hY).tsum_le_tsum _
    ((conjugatedResidual_energy_summable S hP hj hS η a W hZ r z G Φ hY).mul_left _)
  intro u
  have hh := mul_le_mul_of_nonneg_left
    (originalFixedPolynomial_norm_sq_le S hP hj η a W hZ r z G u)
    (radialWeight_nonneg Φ hΦ hY u)
  convert hh using 1
  ring

theorem sqrt_overlap_prefactor {Z : ℝ} (hZ : 0<Z) (G : ℝ) (ηj : ℂ) (E : ℝ) :
    Real.sqrt (Z^(-2*G)*‖ηj‖^4*E) = Z^(-G)*‖ηj‖^2*Real.sqrt E := by
  have hz : (Z^(-G))^2=Z^(-2*G) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    ring
  have hp : Z^(-2*G)*‖ηj‖^4=(Z^(-G)*‖ηj‖^2)^2 := by
    rw [mul_pow,hz]
    ring
  rw [hp,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]

def originalTotalPolynomial (S : Finset (Ideal O)) (P : Ideal O) (η : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n∈S,(moebius n : ℂ)*heckeIdealCharacter η u n*
    heckeIdealCharacter η u P*a n*W ((Ideal.absNorm n : ℝ)/Z^r)

theorem originalTotalPolynomial_eq_sectors (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z : ℝ) (G : Ideal O → ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u =
      ∑ j∈idealDivisors P,originalFixedPolynomial S P j η a W Z r z u := by
  unfold originalTotalPolynomial
  rw [original_normalized_polynomial_hecke_rows S hP η a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  exact (originalFixedPolynomial_eq S hP ((mem_idealDivisors hP.ne_zero).mp hj)
    η a W hZ r z (G j) u).symm

theorem original_smoothed_overlap_triangle (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    Summable (fun u => radialWeight Φ Y u*‖originalTotalPolynomial S P η a W Z r z u‖^2) ∧
    Real.sqrt (smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z)) ≤
      ∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt (smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j))) := by
  have hjd (j : Ideal O) (hj : j∈idealDivisors P) : j∣P := (mem_idealDivisors hP.1).mp hj
  have hs := weighted_overlap_triangle (idealDivisors P) (radialWeight Φ Y)
    (radialWeight_nonneg Φ hΦ hY) (fun j => originalFixedPolynomial S P j η a W Z r z)
    (fun j hj => original_energy_summable S hP (hjd j hj) hS η a W hZ r z (G j) Φ hY)
  simp_rw [←originalTotalPolynomial_eq_sectors S hP.2.1 η a W hZ r z G] at hs
  refine ⟨hs.1,?_⟩
  have hb := Real.sqrt_le_sqrt hs.2
  rw [Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))] at hb
  refine hb.trans (Finset.sum_le_sum (fun j hj => ?_))
  have hc := Real.sqrt_le_sqrt (original_smoothed_contraction S hP (hjd j hj) hS
    η a W hZ r z (G j) Φ hΦ hY)
  rwa [sqrt_overlap_prefactor hZ] at hc

theorem real_smoothed_sum_eq (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → (Φ x).im=0) {Y : ℝ} (hY : 0<Y) (f : O → ℂ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Y)*(‖f u‖^2 : ℝ)) =
      (smoothedEnergy Φ Y f : ℂ) := by
  unfold smoothedEnergy
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro u
  have he : Φ (‖eisEmbedding u‖^2/Y) = (radialWeight Φ Y u : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hΦ _ (div_nonneg (sq_nonneg _) hY.le)
  rw [he,Complex.ofReal_mul]

theorem original_smoothed_overlap_bound (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z) ≤
      (∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt (smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j))))^2 := by
  have ht := (original_smoothed_overlap_triangle S hP hS η a W hZ r z G Φ hΦ hY).2
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
  rwa [Real.sq_sqrt (smoothedEnergy_nonneg Φ hΦ hY _)] at hb

def conjugatePhysicalSum (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    (Z r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) : ℂ :=
  let F := columns S P j
  let hF : ∀ I∈F,Admissible I := fun I hI => columns_admissible S hP hj hS hI
  letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  ∑ C ∈ (Finset.univ : Finset (primePool F)).powerset,
    ∑ U ∈ (Finset.univ\C).powerset,∑ T ∈ (Finset.univ\C).powerset,
      if Disjoint U T then ∑ E ∈ C.powerset,∑' h : O,
        initialPhysicalMode (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) (elementCharacter (conjugateIdealCharacter η)) (primaryGenerator j)
          (reconstructedSelector S P j (fun I => star (a I)))
          (InverseInitialKernelBridge.residualOverlapWindow P j (fun x => star (W x)) Z z G)
          Φ Z (r+z-2*G) m C U T E h else 0

theorem conjugatedResidual_physical (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖conjugatedResidual S P j η a W Z r z G u‖^2 : ℝ)) =
      conjugatePhysicalSum S hP hj hS η a W Z r z G m Φ := by
  exact residual_initial_physical_rays S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G m Φ

theorem conjugatedResidual_energy_physical (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ)) :
    smoothedEnergy Φ (Z^m) (conjugatedResidual S P j η a W Z r z G) =
      (conjugatePhysicalSum S hP hj hS η a W Z r z G m Φ).re := by
  have hs := residual_normalized_smoothed_summable S hP hj hS (conjugateIdealCharacter η)
    (fun I => star (a I)) (fun x => star (W x)) hZ r z G Φ (Z^m) (Real.rpow_pos_of_pos hZ m)
  have he := congrArg Complex.re (conjugatedResidual_physical S hP hj hS η a W hZ r z G m Φ)
  change Summable (fun u : O => Φ (‖eisEmbedding u‖^2/Z^m)*
    (‖conjugatedResidual S P j η a W Z r z G u‖^2 : ℝ)) at hs
  rw [Complex.re_tsum hs] at he
  simpa only [smoothedEnergy,radialWeight,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using he

theorem original_fixed_physical_contraction (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z G m : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) :
    smoothedEnergy Φ (Z^m) (originalFixedPolynomial S P j η a W Z r z) ≤
      Z^(-2*G)*‖η j‖^4*(conjugatePhysicalSum S hP hj hS η a W Z r z G m Φ).re := by
  rw [←conjugatedResidual_energy_physical S hP hj hS η a W hZ r z G m Φ]
  exact original_smoothed_contraction S hP hj hS η a W hZ r z G Φ hΦ
    (Real.rpow_pos_of_pos hZ m)

theorem original_physical_overlap_triangle (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z m : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) :
    Real.sqrt (smoothedEnergy Φ (Z^m) (originalTotalPolynomial S P η a W Z r z)) ≤
      ∑ j : idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt ((conjugatePhysicalSum S hP ((mem_idealDivisors hP.1).mp j.property)
          hS η a W Z r z (G j) m Φ).re) := by
  have ht := (original_smoothed_overlap_triangle S hP hS η a W hZ r z G Φ hΦ
    (Real.rpow_pos_of_pos hZ m)).2
  rw [←Finset.sum_coe_sort] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [conjugatedResidual_energy_physical S hP ((mem_idealDivisors hP.1).mp j.property)
    hS η a W hZ r z (G j) m Φ]

theorem original_smoothed_overlap_cauchy (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0<Z)
    (r z : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) {Y : ℝ} (hY : 0<Y) :
    smoothedEnergy Φ Y (originalTotalPolynomial S P η a W Z r z) ≤
      (∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2) *
        ∑ j∈idealDivisors P,Z^(-G j)*‖η j‖^2*
          smoothedEnergy Φ Y (conjugatedResidual S P j η a W Z r z (G j)) := by
  refine (original_smoothed_overlap_bound S hP hS η a W hZ r z G Φ hΦ hY).trans ?_
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro j _
    exact mul_nonneg (Real.rpow_nonneg hZ.le _) (sq_nonneg _)
  · intro j _
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (sq_nonneg _))
      (smoothedEnergy_nonneg Φ hΦ hY _)
  · intro j _
    rw [mul_pow,Real.sq_sqrt (smoothedEnergy_nonneg Φ hΦ hY _)]
    nlinarith

theorem original_complex_physical_overlap_bound (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Admissible P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0<Z) (r z m : ℝ) (G : Ideal O → ℝ) (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re) (hΦreal : ∀ x : ℝ,0≤x → (Φ x).im=0) :
    ‖∑' u : O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖originalTotalPolynomial S P η a W Z r z u‖^2 : ℝ)‖ ≤
      (∑ j : idealDivisors P,Z^(-G j)*‖η j‖^2*
        Real.sqrt ((conjugatePhysicalSum S hP ((mem_idealDivisors hP.1).mp j.property)
          hS η a W Z r z (G j) m Φ).re))^2 := by
  have hY := Real.rpow_pos_of_pos hZ m
  rw [real_smoothed_sum_eq Φ hΦreal hY,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ hΦ hY _)]
  have ht := original_physical_overlap_triangle S hP hS η a W hZ r z m G Φ hΦ
  have hb := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
  rwa [Real.sq_sqrt (smoothedEnergy_nonneg Φ hΦ hY _)] at hb

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSelector -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialEnergyCallerSelector
local notation "Eis" => ActualEisensteinCubic.O

theorem mask_nonzero_coprime (F : Finset (Ideal Eis)) (j : Ideal Eis) (hj : Admissible j)
    (A : Finset (primePool F))
    (hm : rowCoprimeMask (fun i : primePool F=>i.val) A (primaryGenerator j)≠0) :
    IsCoprime (∏ i∈A,i.val) j := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : i.val.IsMaximal) htop
    (show (i.val : Ideal Eis) ≤ (i.val : Ideal Eis) ⊔ j from le_sup_left)
  have hmem : primaryGenerator j∈i.val := by
    rw [he]
    apply (show j ≤ (i.val : Ideal Eis) ⊔ j from le_sup_right)
    have hjmem : primaryGenerator j ∈ Ideal.span {primaryGenerator j} :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hspan] at hjmem
    exact hjmem
  apply hm
  unfold rowCoprimeMask
  exact ite_eq_left ⟨i,hi,hmem⟩

theorem reconstructedSelector_profile
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) * (if residual P j∣(∏ i∈A,i.val) then 1 else 0) *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) := by
  by_cases hm : rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero,zero_mul]
  by_cases hW : W (∏ i∈A,i.val)=0
  · simp only [hW,mul_zero]
  have hcop := mask_nonzero_coprime (columns S P j) j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏ i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA,hcop,hd,hcover hd hW hcop⟩
    simp only [reconstructedSelector,hmem,ite_true,hd,mul_one]
  · have hn : (∏ i∈A,i.val)∉columns S P j := by
      intro h
      exact hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [reconstructedSelector,hn,ite_false,hd,mul_zero,zero_mul]

theorem singleton_primeMark {ι : Type*} [DecidableEq ι] (B A : Finset ι) :
    primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A = if B⊆A then 1 else 0 := by
  classical
  simp only [primeMark,primeSlot,Finset.sum_singleton]
  by_cases h : B⊆A
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    exact ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (ite_eq_right hn)

theorem forcing_primeMark {ι : Type*} [DecidableEq ι]
    (Q : ι→Ideal Eis) [∀ i,(Q i).IsMaximal] (hinj : Function.Injective Q)
    (B A : Finset ι) :
    primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A =
      if (∏ i∈B,Q i)∣(∏ i∈A,Q i) then 1 else 0 := by
  classical
  have hd : (∏ i∈B,Q i)∣(∏ i∈A,Q i) ↔ B⊆A := by
    constructor
    · intro h i hi
      exact (FirstCauchyArithmetic.family_prime_dvd_product_iff Q hinj A i).mp
        ((Finset.dvd_prod_of_mem Q hi).trans h)
    · intro h
      exact Finset.prod_dvd_prod_of_subset B A Q h
  rw [singleton_primeMark,hd]
  split_ifs <;> rfl

theorem reconstructedSelector_forced_mark
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (B A : Finset (primePool (columns S P j)))
    (hB : (∏ i∈B,i.val)=residual P j)
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) * primeMark B (fun i=>{i}) (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) := by
  rw [forcing_primeMark (fun i : primePool (columns S P j)=>i.val) Subtype.val_injective B A,hB]
  exact reconstructedSelector_profile S hP hj a W A hA hcover

end SevenEighths.InverseInitialEnergyCallerSelector

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerPool -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialEnergyCallerSelector
namespace SevenEighths.InverseInitialEnergyCallerPool
local notation "Eis" => ActualEisensteinCubic.O

theorem residual_factors_in_pool (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty)
    {Q : Ideal Eis} (hQ : Q∈normalizedFactors (residual P j)) :
    Q∈primePool (columns S P j) := by
  obtain ⟨c,hc⟩ := hne
  obtain ⟨hcs,_,hPc,_⟩ := (mem_columns hP hj).mp hc
  apply mem_primePool_iff.mpr
  refine ⟨c,hc,?_⟩
  exact Multiset.mem_of_le
    ((dvd_iff_normalizedFactors_le_normalizedFactors
      (residual_squarefree hP hj).ne_zero hcs.ne_zero).mp hPc) hQ

def forcedSlots (S : Finset (Ideal Eis)) (P j : Ideal Eis) :
    Finset (primePool (columns S P j)) := idealSupport (columns S P j) (residual P j)

theorem forcedSlots_image (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty) :
    (forcedSlots S P j).image Subtype.val = IdealMobiusDivisorSum.primeSupport (residual P j) := by
  ext Q
  constructor
  · rintro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact Multiset.mem_toFinset.mpr ((mem_idealSupport_iff _ _ i).mp hi)
  · intro hQ
    have hf : Q∈normalizedFactors (residual P j) := Multiset.mem_toFinset.mp hQ
    let i : primePool (columns S P j) := ⟨Q,residual_factors_in_pool S hP hj hne hf⟩
    exact Finset.mem_image.mpr ⟨i,(mem_idealSupport_iff _ _ i).mpr hf,rfl⟩

theorem forcedSlots_product (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hne : (columns S P j).Nonempty) :
    (∏ i∈forcedSlots S P j,i.val)=residual P j := by
  calc
    _ = ∏ Q∈(forcedSlots S P j).image Subtype.val,Q := by
      rw [Finset.prod_image]
      exact fun a _ b _ h=>Subtype.val_injective h
    _ = _ := by rw [forcedSlots_image S hP hj hne]
                exact squarefree_support_product_self (residual_squarefree hP hj)

theorem original_selector_forced_slots
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns S P j).Nonempty) (a : Ideal Eis→ℂ) (W : Ideal Eis→ℂ)
    (A : Finset (primePool (columns S P j)))
    (hA : Squarefree (∏ i∈A,i.val))
    (hcover : residual P j∣(∏ i∈A,i.val) → W (∏ i∈A,i.val)≠0 →
      IsCoprime (∏ i∈A,i.val) j → reconstruct P j (∏ i∈A,i.val)∈S) :
    reconstructedSelector S P j a A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      SevenEighths.InverseMoment.primeMark (forcedSlots S P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns S P j)=>i.val) A (primaryGenerator j) *
      W (∏ i∈A,i.val) :=
  reconstructedSelector_forced_mark S hP hj a W (forcedSlots S P j) A
    (forcedSlots_product S hP.2.1 hj hne) hA hcover

end SevenEighths.InverseInitialEnergyCallerPool

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialZeroMode -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem marked_coefficient_mass (eps b B:ℝ)(heps:0<eps)(hb:0<b)(_hB:0≤B):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X:ℝ,0<X→
      (∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)≤C*X^(1+eps) := by
  obtain ⟨Cm,hCm,hm⟩:=finite_primeMark_small_power (eps/2) (by positivity)
  refine ⟨128*b*(Cm*b^(eps/2)*B)^2+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  let T:=pool.powerset.filter (fun A=>W (primeProductNorm p A/X)≠0)
  have hXb:0<b*X:=mul_pos hb hX
  have hnorm:∀A∈T,primeProductNorm p A≤b*X:=by
    intro A hA
    exact (div_le_iff₀ hX).mp (hs _ (Finset.mem_filter.mp hA).2)
  have hcard:(T.card:ℝ)≤128*(b*X):=by
    by_cases hsmall:1≤b*X
    · apply (Nat.cast_le.mpr (Finset.card_le_card (show T⊆boundedPrimeSupports p pool (b*X) from ?_))).trans
        (boundedPrimeSupports_card p hinj pool (b*X) hsmall)
      intro A hA
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,hnorm A hA⟩
    · have hz:T=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A hA
        exact hsmall ((primeProductNorm_ge_one p hp A).trans (hnorm A hA))
      rw [hz]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  have he:(∑A∈pool.powerset,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2)=
      ∑A∈T,‖secondInputCoefficient p hg Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖^2:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro A hA hn
    have hz:W (primeProductNorm p A/X)=0:=by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
    simp only [secondInputCoefficient,hz,mul_zero,norm_zero,zero_pow (by decide:2≠0)]
  have hcoeff:∀A∈T,‖secondInputCoefficient p hg Ψ m c d
      (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) A‖≤Cm*(b*X)^(eps/2)*B:=by
    intro A hA
    apply (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d _ A).trans
    rw [norm_mul]
    apply mul_le_mul _ (hW _) (norm_nonneg _) (by positivity)
    exact (hm p hp hcop slots lists a hdis ha A).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (primeProductNorm_pos p hp A).le (hnorm A hA) (by positivity)) hCm.le)
  rw [he]
  calc
    _≤∑_A∈T,(Cm*(b*X)^(eps/2)*B)^2:=by
      apply Finset.sum_le_sum
      intro A hA
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff A hA) 2
    _=(T.card:ℝ)*(Cm*(b*X)^(eps/2)*B)^2:=by simp
    _≤(128*(b*X))*(Cm*(b*X)^(eps/2)*B)^2:=mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _=(128*b*(Cm*b^(eps/2)*B)^2)*X^(1+eps):=by
      rw [Real.mul_rpow hb.le hX.le,Real.rpow_add hX,Real.rpow_one]
      have hh:(X^(eps/2))^2=X^eps:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hX.le]
        congr 1
        norm_num
      calc
        _=(128*b*(Cm*b^(eps/2)*B)^2)*(X*(X^(eps/2))^2):=by ring
        _=_:=by rw [hh]
    _≤_:=by nlinarith [Real.rpow_nonneg hX.le (1+eps)]

theorem marked_normalized_zero (eps b B:ℝ)(heps:0<eps)(hb:0<b)(hB:0≤B)
    (Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(m c d:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→∀X Y:ℝ,0<X→0<Y→
      ∀K:Finset ι→Finset ι→Finset O,
      (∀G∈pool.powerset,∀E∈G.powerset,(0:O)∈K G E)→
      ‖(X⁻¹:ℂ)*truncatedSecondZero p hg pool Ψ m c d
        (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K‖≤C*Y*X^eps := by
  obtain ⟨Cm,hCm,hm⟩:=marked_coefficient_mass eps b B heps hb hB
  refine ⟨Cm*‖paperRadialFourier Φ 0‖+1,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X Y hX hY K hK
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hX]
  have hz:=truncatedSecondZero_norm_le p hg hinj pool Ψ m c d
    (fun A=>primeMark slots lists a A*W (primeProductNorm p A/X)) Φ Y K hK
  rw [abs_of_pos hY] at hz
  apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hX.le)).trans
  have hm':=hm p hp hcop hg hinj pool Ψ hΨ m c d slots lists a hdis ha W hW hs X hX
  calc
    _≤X⁻¹*(Y*‖paperRadialFourier Φ 0‖*(Cm*X^(1+eps))):=by gcongr
    _=(Cm*‖paperRadialFourier Φ 0‖)*Y*X^eps:=by
      rw [Real.rpow_add hX,Real.rpow_one]
      field_simp
    _≤_:=by nlinarith [mul_nonneg hY.le (Real.rpow_nonneg hX.le eps)]

end SevenEighths.InverseInitialZeroMode

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialZeroModePhysical -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment FirstCauchyArithmetic
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,λ₀∉Ideal.span {p i})(hinj:Function.Injective (fun i=>Ideal.span {p i}))
  (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,λ₀^2∣p i-1)

include hinj hc hpr

theorem physical_zero_off_diagonal
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G U T E:Finset ι)(hGU:Disjoint G U)(hGT:Disjoint G T)(hUT:Disjoint U T)(hne:U≠T):
    initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E 0=0 := by
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m
    G U T E hGU hGT hUT 0,
    activeGaussRowFactor_zero_of_ne p hp hg hinj T U hne.symm]
  simp

theorem physical_zero_empty
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G E:Finset ι):
    initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G ∅ ∅ E 0=
    ((Z^(-D):ℝ):ℂ)*(Z^m:ℝ)*paperRadialFourier Φ 0*
      ((‖secondInputCoefficient p hg Ψ j 1 1 (fun _=>1) G‖^2:ℝ):ℂ)*
      star (initialTest p σ W Z D G)*initialTest p σ W Z D G*
      ((UniqueFactorizationMonoid.moebius (∏i∈E,Ideal.span {p i}):ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)‖^2:ℝ)) := by
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m
    G ∅ ∅ E (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_left _) 0,
    activeGaussRowFactor_empty (p := p) (hp := hp) (hg := hg) (hinj := hinj)]
  have hcoef (H:Finset ι→ℂ):secondInputCoefficient p hg Ψ j 1 1 H ∅=H ∅:=by
    simp [secondInputCoefficient,rowCoprimeMask,finiteSquarefreeRow]
  have hμ:supportMobius (fun i=>Ideal.span {p i}) ∅=(1:ℂ):=by
    change (UniqueFactorizationMonoid.moebius (1:Ideal O):ℂ)=1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [overlapPairWeight,hcoef,hμ,one_mul,Finset.union_empty]
  have hempty:activeSupport (∅:Finset ι) ∅=∅:=by simp [activeSupport]
  let:IsEmpty (activeSupport (∅:Finset ι) ∅):=⟨fun ⟨x,hx⟩=>by
    simp only [activeSupport,Finset.sdiff_self,Finset.union_self,Finset.notMem_empty] at hx⟩
  simp only [Fintype.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
    zero_pow (by decide:2≠0),mul_zero,zero_div,mul_one]
  ring

theorem physical_zero_sum
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E 0 else 0)=
      ((Z^(-D):ℝ):ℂ)*truncatedSecondZero p hg pool Ψ j 1 1
        (initialTest p σ W Z D) Φ (Z^m) (fun _ _=>{0}) := by
  unfold truncatedSecondZero
  simp only [Finset.mem_singleton,ite_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp only [Finset.disjoint_empty_left,ite_true]
      rw [←Finset.sum_coe_sort (s:=G.powerset) (f:=fun E=>
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G ∅ ∅ E 0)]
      apply Finset.sum_congr rfl
      intro E hE
      rw [physical_zero_empty p hp hcop hg hinj hc hpr]
      ring
    · intro T hT hne
      simp only [Finset.disjoint_empty_left,ite_true]
      apply Finset.sum_eq_zero
      intro E hE
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G ∅ T E
        (Finset.disjoint_empty_right _) (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff)
        (Finset.disjoint_empty_left _) hne.symm
    · simp
  · intro U hU hne
    apply Finset.sum_eq_zero
    intro T hT
    split_ifs with hUT
    · apply Finset.sum_eq_zero
      intro E hE
      have hneq:U≠T:=by
        intro he
        subst T
        exact hne (by simpa using Finset.disjoint_iff_inter_eq_empty.mp hUT)
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G U T E
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hUT hneq
    · rfl
  · simp

end SevenEighths.InverseInitialZeroMode

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialZeroModeBudget -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

theorem physical_marked_zero_bound (loss L b B:ℝ)(hloss:0<loss)(hL:0≤L)
    (hb:0<b)(hB:0≤B)(Φ:𝓢(ℝ,ℂ)):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,λ₀∉Ideal.span {p i})(_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(_hpr:∀i,λ₀^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)(j:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      ∀(W:ℝ→ℂ),(∀x,‖W x‖≤B)→(∀x,W x≠0→x≤b)→
      ∀Z D m:ℝ,1≤Z→D≤L→
      ‖∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,
          initialPhysicalMode p hp hcop hg Ψ j (primeMark slots lists a)
            W Φ Z D m G U T E 0 else 0‖≤C*Z^(m+loss) := by
  let eps:=loss/(L+1)
  have heps:0<eps:=div_pos hloss (by linarith)
  obtain ⟨C,hC,hbound⟩:=marked_normalized_zero eps b B heps hb hB Φ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr pool Ψ hΨ j slots lists a hdis ha W hW hs Z D m hZ hD
  have hZ0:0<Z:=lt_of_lt_of_le zero_lt_one hZ
  rw [physical_zero_sum p hp hcop hg hinj hc hpr]
  have heq:((Z^(-D):ℝ):ℂ)=((Z^D:ℝ):ℂ)⁻¹:=by
    rw [Real.rpow_neg hZ0.le,Complex.ofReal_inv]
  rw [heq]
  have hb':=hbound p hp hcop hg hinj pool Ψ hΨ j 1 1 slots lists a hdis ha
    W hW hs (Z^D) (Z^m) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (fun _ _=>{0}) (by intros; simp)
  change ‖_‖≤C*Z^(m+loss)
  apply hb'.trans
  rw [←Real.rpow_mul hZ0.le, mul_assoc,←Real.rpow_add hZ0]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ ?_) hC.le
  have hprod:D*eps≤loss:=by
    apply (mul_le_mul_of_nonneg_right hD heps.le).trans
    dsimp [eps]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith:0<L+1)).mpr
    nlinarith
  linarith

end SevenEighths.InverseInitialZeroMode

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.PrincipalEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InversePrincipalEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open SecondPassArithmetic FirstPassCubeLabels IdealMobiusDivisorSum
open InverseMoment
local notation "Eis" => ActualEisensteinCubic.O

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem zero_norm_le (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ ≤
      Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 := by
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d H W Y K hzero).trans
  rw [abs_of_nonneg hY]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY (norm_nonneg _))
  exact Finset.sum_le_sum (fun G _ => pow_le_pow_left₀ (norm_nonneg _)
    (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d H G) 2)

def supportIdeal (G : Finset ι) : Ideal Eis := ∏ i ∈ G, Ideal.span {p i}

omit [DecidableEq ι] in
lemma supportIdeal_ne_zero (G : Finset ι) : supportIdeal p G ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))

omit [DecidableEq ι] in
lemma supportIdeal_norm_pos (G : Finset ι) : 0 < (Ideal.absNorm (supportIdeal p G) : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (supportIdeal_ne_zero p G))

include hinj in

theorem mask_card_le_divisors (G : Finset ι) :
    G.powerset.card ≤ (idealDivisors (supportIdeal p G)).card := by
  apply Finset.card_le_card_of_injOn (supportIdeal p)
  · intro E hE
    apply (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr
    exact Finset.prod_dvd_prod_of_subset E G (fun i => Ideal.span {p i}) (Finset.mem_powerset.mp hE)
  · intro E _ D _ h
    exact FirstCauchyArithmetic.family_product_injective (fun i => Ideal.span {p i}) hinj h

def principalFrequency (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ (∅ : Finset ι) ∪ ∅, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p ((∅ : Finset ι) ∪ ∅))) *
    secondGaussTerm p hp hg hinj Ψ Ψ m r c d e k H₁ H₂ ∅ ∅

theorem principalFrequency_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hinj hp Ψ m r c d e k H₁ H₂ W Y =
      (Y : ℂ) * paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 / ‖eisEmbedding e‖ ^ 2) *
        (star (H₁ ∅) * H₂ ∅) := by
  simp only [principalFrequency, Finset.union_empty, Finset.prod_empty, map_one, norm_one,
    Complex.ofReal_one, div_one, primeProductNorm, one_pow, mul_one,
    secondGaussTerm_empty (p := p) (hp := hp) (hg := hg) (hinj := hinj)]

theorem principalFrequency_eq_secondFrequencyKernel_empty
    (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    principalFrequency p hg hinj hp Ψ m r c d e k H₁ H₂ W Y =
      secondFrequencyKernel p hp hg hinj ∅ Ψ Ψ m r c d e k H₁ H₂ W Y := by
  simp only [secondFrequencyKernel, Finset.powerset_empty, Finset.sum_singleton,
    Finset.disjoint_empty_left, ite_true, principalFrequency]

def restorationTerm (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d G E.val *
    principalFrequency p hg hinj hp Ψ m
      (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

theorem restorationTerm_eq_principal_kernel (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ)
    (m c d : Eis) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hinj hp Ψ m c d H W Y G E k =
      secondSourceCommonCoefficient p hg Ψ m c d G E.val *
        secondFrequencyKernel p hp hg hinj ∅ Ψ Ψ m
          (secondMaskQuotient p E.val G (Finset.mem_powerset.mp E.property)) c d
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) k
          (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [restorationTerm, principalFrequency_eq_secondFrequencyKernel_empty]

theorem restorationTerm_eq (hp : ∀ i, p i ≠ 0) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (G : Finset ι) (E : G.powerset) (k : Eis) :
    restorationTerm p hg hinj hp Ψ m c d H W Y G E k =
      (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
      (‖H G‖ ^ 2 : ℝ) * (UniqueFactorizationMonoid.moebius (supportIdeal p E.val) : ℂ) *
      ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ) : ℝ) : ℂ) *
      paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2) := by
  rw [restorationTerm, principalFrequency_eq]
  simp only [Finset.union_empty, secondSourceCommonCoefficient, primeSubsetGenerator_norm_sq]
  have hh : star (H G) * H G = (‖H G‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hh]
  simp only [supportIdeal, Complex.ofReal_div]
  have harg : Y * ‖eisEmbedding k‖ ^ 2 / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ) =
      (Y / (Ideal.absNorm (∏ i ∈ E.val, Ideal.span {p i}) : ℝ)) * ‖eisEmbedding k‖ ^ 2 := by ring
  rw [harg]
  ring

theorem restorationTerm_mask_norm_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (k : Eis) (θ : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖θ * restorationTerm p hg hinj hp Ψ m c d H W Y G E k‖ ≤
      ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2)‖ := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have ha : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d G).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one (supportIdeal p E.val)
  rw [restorationTerm_eq]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm, abs_of_pos ht]
  calc
    _ ≤ 1 * (1 * ‖H G‖ ^ 2 * 1 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k‖ ^ 2)‖) := by gcongr
    _ = _ := by ring

theorem restorationTerm_mask_summable_norm (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    Summable (fun k : {k : Eis // k ≠ 0} =>
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => restorationTerm_mask_norm_le p hg hinj hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
    (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))

theorem restoration_divisor_abs_le (hp : ∀ i, p i ≠ 0)
    (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (G : Finset ι) (E : G.powerset) (θ : Eis → ℂ)
    (hθ : ∀ k : {k : Eis // k ≠ 0}, ‖θ k.val‖ ≤ 1) :
    (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
        QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2 := by
  have ht := div_pos hY (supportIdeal_norm_pos p E.val)
  have hs := (paperRadialFourier_lattice_summable_norm W _ ht).subtype (fun k : Eis => k ≠ 0)
  have hb : (∑' k : {k : Eis // k ≠ 0},
      ‖θ k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
      ∑' k : {k : Eis // k ≠ 0}, ‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        ‖paperRadialFourier W ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖ :=
    Summable.tsum_le_tsum
      (fun k : {k : Eis // k ≠ 0} => restorationTerm_mask_norm_le p hg hinj hp Ψ hΨ m c d H W Y hY G E k.val (θ k.val) (hθ k))
      (restorationTerm_mask_summable_norm p hg hinj hp Ψ hΨ m c d H W Y hY G E θ hθ)
      (hs.mul_left (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))))
  apply hb.trans
  calc
    _ = (‖H G‖ ^ 2 * (Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ))) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖) :=
      tsum_mul_left
    _ = ‖H G‖ ^ 2 * ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) *
        (∑' k : {k : Eis // k ≠ 0}, ‖paperRadialFourier W
          ((Y / (Ideal.absNorm (supportIdeal p E.val) : ℝ)) * ‖eisEmbedding k.val‖ ^ 2)‖)) := mul_assoc _ _ _
    _ ≤ ‖H G‖ ^ 2 * QuadraticInitialBound.pvControl W :=
      mul_le_mul_of_nonneg_left (QuadraticInitialBound.pv_lattice_bound W _ ht) (sq_nonneg ‖H G‖)
    _ = _ := mul_comm _ _

def principalRestoration (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (θ : Finset ι → Finset ι → Eis → ℂ) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
    θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val

theorem principalRestoration_abs_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ∑' k : {k : Eis // k ≠ 0},
      ‖θ G E.val k.val * restorationTerm p hg hinj hp Ψ m c d H W Y G E k.val‖) ≤
      QuadraticInitialBound.pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro G hG
  calc
    _ ≤ ∑ E : G.powerset, QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2 :=
      Finset.sum_le_sum (fun E _ => restoration_divisor_abs_le p hg hinj hp Ψ hΨ m c d H W Y hY G E
        (θ G E.val) (hθ G hG E))
    _ = (G.powerset.card : ℝ) * (QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2) := by simp
    _ ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) *
        (QuadraticInitialBound.pvControl W * ‖H G‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast mask_card_le_divisors p hinj G)
        (mul_nonneg (QuadraticInitialBound.pvControl_nonneg W) (sq_nonneg _))
    _ = _ := by ring

theorem principalRestoration_norm_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖principalRestoration p hg hinj hp F Ψ m c d H W Y θ‖ ≤
      QuadraticInitialBound.pvControl W *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply (norm_sum_le _ _).trans
  apply le_trans _ (principalRestoration_abs_le p hg hinj hp F Ψ hΨ m c d H W Y hY θ hθ)
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E _
  exact norm_tsum_le_tsum_norm (restorationTerm_mask_summable_norm p hg hinj hp Ψ hΨ m c d H W Y hY G E
    (θ G E.val) (hθ G hG E))

def markedRadial {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X : ℝ) (G : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ G) * V (primeProductNorm p G / X)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma markedRadial_support {σ : Type*} [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ) (hX : 0 < X)
    (hV : ∀ t, V t ≠ 0 → t ≤ Real.exp M) (G : Finset ι)
    (hG : markedRadial p slots lists a A V X G ≠ 0) :
    primeProductNorm p G ≤ X * Real.exp M := by
  have hv : V (primeProductNorm p G / X) ≠ 0 := by
    intro hz
    exact hG (by simp [markedRadial, hz])
  simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hv)

include hinj in

theorem radial_mass_from_pointwise (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (H : Finset ι → ℂ) (U ε D : ℝ)
    (hU : 0 < U) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hs : ∀ G, H G ≠ 0 → primeProductNorm p G ≤ U)
    (hb : ∀ G, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 ≤
      D * (primeProductNorm p G) ^ ε) :
    (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) ≤
      128 * D * U ^ (1 + ε) := by
  let T := boundedPrimeSupports p F U
  have he : (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) =
      ∑ G ∈ T, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro G hG hn
    have hz : H G = 0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hG, hs G hh⟩)
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ G ∈ T, D * U ^ ε := by
      apply Finset.sum_le_sum
      intro G hG
      exact (hb G).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (primeProductNorm_pos p hp G).le (Finset.mem_filter.mp hG).2 hε) hD)
    _ = (T.card : ℝ) * (D * U ^ ε) := by simp
    _ ≤ (128 * U) * (D * U ^ ε) := mul_le_mul_of_nonneg_right
      (boundedPrimeSupports_card_positive p hp hinj F U hU) (by positivity)
    _ = 128 * D * U ^ (1 + ε) := by rw [Real.rpow_add hU, Real.rpow_one]; ring

omit [DecidableEq ι] in
lemma mass_le_divisor_mass (F : Finset ι) (H : Finset ι → ℂ) :
    (∑ G ∈ F.powerset, ‖H G‖ ^ 2) ≤
      ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro G _
  have ho : (1 : Ideal Eis) ∈ idealDivisors (supportIdeal p G) :=
    (mem_idealDivisors (supportIdeal_ne_zero p G)).mpr (one_dvd _)
  have hc : (1 : ℝ) ≤ ((idealDivisors (supportIdeal p G)).card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1, ho⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg ‖H G‖)

end

theorem marked_radial_divisor_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (V : 𝓢(ℝ, ℂ)) (X M : ℝ), 0 < X →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2) ≤
        C * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε) := by
  obtain ⟨Cm, hCm, hm⟩ := finite_primeMark_extracted_bound (ε / 4) (by positivity)
  obtain ⟨Cd, hCd, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨128 * Cd * Cm ^ 2, by positivity, ?_⟩
  intro ι σ _ _ p hp _ hinj hcop slots lists a hslots ha A F V X M hX hV
  have hpoint (G : Finset ι) :
      ((idealDivisors (supportIdeal p G)).card : ℝ) *
        ‖markedRadial p slots lists a A V X G‖ ^ 2 ≤
      (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
        (primeProductNorm p G)^ε := by
    have hn := primeProductNorm_pos p hp G
    have hmark := hm p hp hcop slots lists a hslots ha A G
    have hv := V.norm_le_seminorm ℝ (primeProductNorm p G / X)
    have hdiv := hd (supportIdeal p G) (supportIdeal_ne_zero p G)
    rw [show (Ideal.absNorm (supportIdeal p G) : ℝ) = primeProductNorm p G from
      (primeProductNorm_eq_ideal_norm p G).symm] at hdiv
    have hpow : (primeProductNorm p G) ^ (ε / 2) * ((primeProductNorm p G) ^ (ε / 4))^2 =
        (primeProductNorm p G)^ε := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
      congr 1
      ring
    calc
      _ ≤ (Cd * (primeProductNorm p G)^(ε/2)) *
          (((2 : ℝ)^A.card * Cm * (primeProductNorm p G)^(ε/4)) *
            SchwartzMap.seminorm ℝ 0 0 V)^2 := by
        apply mul_le_mul hdiv _ (sq_nonneg _) (by positivity)
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [markedRadial, norm_mul]
        exact mul_le_mul hmark hv (norm_nonneg _) (by positivity)
      _ = (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2) *
          ((primeProductNorm p G)^(ε/2) * ((primeProductNorm p G)^(ε/4))^2) := by ring
      _ = _ := by rw [hpow]
  have hb := radial_mass_from_pointwise p hinj hp F (markedRadial p slots lists a A V X)
    (X * Real.exp M) ε (Cd * ((2 : ℝ)^A.card * Cm * SchwartzMap.seminorm ℝ 0 0 V)^2)
    (by positivity) hε.le (by positivity)
    (markedRadial_support p slots lists a A V X M hX hV) hpoint
  have h4 : ((2 : ℝ)^A.card)^2 = (4 : ℝ)^A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  convert hb using 1 ; (rw [mul_pow, mul_pow, h4]; ring)

lemma radial_support_of_annular (V : 𝓢(ℝ, ℂ)) (a M : ℝ)
    (hV : tsupport V ⊆ Set.Icc a (Real.exp M)) :
    ∀ t, V t ≠ 0 → t ≤ Real.exp M := by
  intro t ht
  exact (hV (subset_closure ht)).2

def outsideCutoff {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ K G E then 0 else 1

lemma outsideCutoff_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis) :
    ‖outsideCutoff K G E k‖ ≤ 1 := by
  unfold outsideCutoff
  split_ifs <;> norm_num

lemma outsideCutoff_mul_norm_le_one {ι : Type*} [DecidableEq ι]
    (K : Finset ι → Finset ι → Finset Eis) (G E : Finset ι) (k : Eis)
    (θ : ℂ) (hθ : ‖θ‖ ≤ 1) : ‖outsideCutoff K G E k * θ‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (outsideCutoff_norm_le_one K G E k) hθ
    (norm_nonneg _) zero_le_one

theorem uniform_row_control :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      ‖paperRadialFourier W 0‖ + QuadraticInitialBound.pvControl W ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 0
  refine ⟨s ∪ QuadraticInitialBound.pvSeminorms,
    C + QuadraticInitialBound.pvConstant, add_pos hC QuadraticInitialBound.pvConstant_pos, ?_⟩
  intro W
  have h₁ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_left (s₁ := s) (s₂ := QuadraticInitialBound.pvSeminorms))) W
  have h₂ := Seminorm.le_def.mp (Finset.sup_mono (f := schwartzSeminormFamily ℝ ℝ ℂ)
    (Finset.subset_union_right (s₁ := s) (s₂ := QuadraticInitialBound.pvSeminorms))) W
  have hz : ‖paperRadialFourier W 0‖ ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    simpa only [pow_zero, one_mul] using hb W 0 le_rfl
  calc
    _ ≤ C * (s ∪ QuadraticInitialBound.pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W +
        QuadraticInitialBound.pvConstant *
          (s ∪ QuadraticInitialBound.pvSeminorms).sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
      add_le_add (hz.trans (mul_le_mul_of_nonneg_left h₁ hC.le))
        (mul_le_mul_of_nonneg_left h₂ QuadraticInitialBound.pvConstant_pos.le)
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem principal_energy_le (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ z, ‖Ψ z‖ ≤ 1) (m c d : Eis)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 1 ≤ Y)
    (K : Finset ι → Finset ι → Finset Eis)
    (hzero : ∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E)
    (θ : Finset ι → Finset ι → Eis → ℂ)
    (hθ : ∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) :
    ‖truncatedSecondZero p hg F Ψ m c d H W Y K‖ +
        ‖principalRestoration p hg hinj hp F Ψ m c d H W Y θ‖ ≤
      Y * (‖paperRadialFourier W 0‖ + QuadraticInitialBound.pvControl W) *
        ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hd : 0 ≤ ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
    Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  calc
    _ ≤ Y * ‖paperRadialFourier W 0‖ * ∑ G ∈ F.powerset, ‖H G‖ ^ 2 +
        QuadraticInitialBound.pvControl W *
          ∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2 :=
      add_le_add (zero_norm_le p hg hinj F Ψ hΨ m c d H W Y hY0.le K hzero)
        (principalRestoration_norm_le p hg hinj hp F Ψ hΨ m c d H W Y hY0 θ hθ)
    _ ≤ Y * ‖paperRadialFourier W 0‖ *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) +
        Y * QuadraticInitialBound.pvControl W *
          (∑ G ∈ F.powerset, ((idealDivisors (supportIdeal p G)).card : ℝ) * ‖H G‖ ^ 2) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (mass_le_divisor_mass p F H) (mul_nonneg hY0.le (norm_nonneg _))
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_left (QuadraticInitialBound.pvControl_nonneg W) hY) hd
    _ = _ := by ring

end

theorem marked_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis) (V W : 𝓢(ℝ, ℂ)) (X M Y : ℝ), 0 < X → 1 ≤ Y →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ∀ K : Finset ι → Finset ι → Finset Eis,
      (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : Eis) ∈ K G E) →
      ∀ θ : Finset ι → Finset ι → Eis → ℂ,
      (∀ G ∈ F.powerset, ∀ E : G.powerset, ∀ k : {k : Eis // k ≠ 0}, ‖θ G E.val k.val‖ ≤ 1) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y K‖ +
        ‖principalRestoration p hg hinj hp F Ψ m c d (markedRadial p slots lists a A V X) W Y θ‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s, Cr, hCr, hr⟩ := uniform_row_control
  obtain ⟨Cm, hCm, hm⟩ := marked_radial_divisor_mass ε hε
  refine ⟨s, Cr * Cm, mul_pos hCr hCm, ?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hslots ha A F Ψ hΨ m c d V W X M Y hX hY hV K hzero θ hθ
  apply (principal_energy_le p hg hinj hp F Ψ hΨ m c d
    (markedRadial p slots lists a A V X) W Y hY K hzero θ hθ).trans
  have hb := hm p hp hinj hcop slots lists a hslots ha A F V X M hX hV
  calc
    _ ≤ Y * (Cr * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (Cm * (4 : ℝ)^A.card * (SchwartzMap.seminorm ℝ 0 0 V)^2 *
          (X * Real.exp M)^(1 + ε)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hr W) (le_trans zero_le_one hY)) hb
        (Finset.sum_nonneg (fun G _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        (mul_nonneg (le_trans zero_le_one hY) (mul_nonneg hCr.le (apply_nonneg _ _)))
    _ = _ := by ring

end SevenEighths.InversePrincipalEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PrincipalChild -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma zero_mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : 0 ≤ R) :
    (0 : Eis) ∈ childFrequencyBall a R := by
  apply (mem_childFrequencyBall a ha R 0).mpr
  simpa using hR

def secondPhysicalCutoff {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (d : Eis) (R : ℝ) (_G E : Finset ι) : Finset Eis :=
  childFrequencyBall (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E) R

def secondPhysicalMask {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (d : Eis) (R : ℝ) (_G E : Finset ι) (k : Eis) : ℂ :=
  if k ∈ nonzeroChildFrequencyBall
    (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E) R then 1 else 0

lemma secondPhysicalMask_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (d : Eis) (R : ℝ) (G E : Finset ι) (k : Eis) :
    ‖secondPhysicalMask p d R G E k‖ ≤ 1 := by
  unfold secondPhysicalMask
  split_ifs <;> norm_num

lemma secondPhysicalMask_exact {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (d : Eis) (hd : d ≠ 0) (R : ℝ) (G E : Finset ι) (k : Eis) :
    secondPhysicalMask p d R G E k =
      if 0 < ‖ConcreteTraceCRT.eisEmbedding
          (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E * k)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding
          (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E * k)‖^2 ≤ R
      then 1 else 0 := by
  unfold secondPhysicalMask
  have he := mem_nonzeroChildFrequencyBall
    (d * primeSubsetGenerator (fun i => Ideal.span {p i}) E)
    (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) R k
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ (he.mp h₁)).elim
  · exact (h₁ (he.mpr h₂)).elim
  · rfl

theorem physical_child_principal_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (Ψ : Eis →* ℂ), (∀ z, ‖Ψ z‖ ≤ 1) →
      ∀ (m c d : Eis), d ≠ 0 → ∀ (V W : 𝓢(ℝ, ℂ)) (X M Y R : ℝ),
      0 < X → 1 ≤ Y → 0 ≤ R →
      (∀ t, V t ≠ 0 → t ≤ Real.exp M) →
      ‖truncatedSecondZero p hg F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (secondPhysicalMask p d R)‖ ≤
      C * (4 : ℝ)^A.card *
        (s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 V)^2) *
        Y * (X * Real.exp M)^(1 + ε) := by
  obtain ⟨s,C,hC,he⟩ := marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists a hs ha A F Ψ hΨ m c d hd V W X M Y R hX hY hR hV
  apply he p hp hg hinj hcop slots lists a hs ha A F Ψ hΨ m c d V W X M Y hX hY hV
  · intro G hG E hE
    exact zero_mem_childFrequencyBall _ (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) R hR
  · intro G hG E k
    exact secondPhysicalMask_norm_le_one p d R G E.val k.val

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.SecondFibers -/

section

namespace OAI

namespace SevenEighths.InverseSecondFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open InverseInitialFibers (divisor_card_mul_le divisor_card_pos)
open scoped BigOperators Classical
noncomputable section

@[ext] structure OuterTriple where
  q0 : Ideal O
  quotient : Ideal O
  residual : Ideal O

@[ext] structure SecondTuple (Jo Jn : ℕ) where
  outer : OuterTriple
  core : Fin 8 → Ideal O
  commonResidual : Ideal O
  cubeResidual : Ideal O
  secondCube : Ideal O
  extractedCommon : Ideal O
  frequency : O
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → SmoothMobiusCorrection.PrimeIdeal

structure Valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (γ : OuterTriple) (f : Ideal O) (k : O) : Prop where
  outer_eq : x.outer = γ
  label : x.core 0 * x.core 1 * x.core 2 * x.commonResidual = f
  j_split : x.core 3 * x.cubeResidual = x.core 0
  b_split : x.core 4 * x.secondCube = γ.q0^2 * x.cubeResidual^2 * x.core 3
  a1 : x.core 5 ∣ (x.core 4 * x.secondCube).radical
  a2 : x.core 6 ∣ (x.core 4 * x.secondCube).radical
  d : x.core 7 ∣ x.core 1 * (x.core 4 * x.secondCube).radical
  extracted_eq : x.core 2 * γ.residual = x.extractedCommon
  generator_d : primaryGenerator (x.core 7) ≠ 0
  generator_d2 : primaryGenerator (x.core 2) ≠ 0
  row_eq : primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency = k
  old_dvd : ∀ i, (x.oldAssigned i).val ∣ γ.q0 * f * γ.quotient
  new_dvd : ∀ i, (x.newAssigned i).val ∣ f * γ.residual

lemma poisson_divisor_source (d C R rest B : Ideal O)
    (hR : R * rest = B.radical) (hd : d ∣ C * rest) : d ∣ C * B.radical := by
  apply hd.trans
  rw [← hR]
  exact mul_dvd_mul_left C (dvd_mul_left rest R)

lemma core_dvd_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 4) :
    x.core ⟨i.val, by omega⟩ ∣ f := by
  have hJ : x.core 0 ∣ f := by
    rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  fin_cases i
  · exact hJ
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact (show x.core 3 ∣ x.core 0 from ⟨x.cubeResidual, hx.j_split.symm⟩).trans hJ

lemma common_label_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 1 * x.core 0 ∣ f := by
  refine ⟨x.core 2 * x.commonResidual, ?_⟩
  rw [← hx.label]
  ring

lemma cube_product_dvd_square {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 * x.secondCube ∣ (γ.q0 * x.core 0)^2 := by
  refine ⟨x.core 3, ?_⟩
  rw [hx.b_split, ← hx.j_split]
  ring

lemma cube_radical_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    (x.core 4 * x.secondCube).radical ∣ γ.q0 * x.core 0 := by
  apply Ideal.dvd_iff_le.mpr
  have hle := Ideal.radical_mono (Ideal.dvd_iff_le.mp (cube_product_dvd_square hx))
  rw [Ideal.radical_pow (γ.q0 * x.core 0) (by decide : (2 : ℕ) ≠ 0)] at hle
  exact Ideal.le_radical.trans hle

lemma cube_factor_dvd_target {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 ∣ (γ.q0 * f)^2 :=
  (dvd_mul_right _ _).trans ((cube_product_dvd_square hx).trans
    (pow_dvd_pow_of_dvd (mul_dvd_mul_left _ (core_dvd_label hx 0)) 2))

lemma core_dvd_outer_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 3) :
    x.core ⟨i.val+5, by omega⟩ ∣ γ.q0 * f := by
  have hrad : (x.core 4 * x.secondCube).radical ∣ γ.q0 * f :=
    (cube_radical_dvd hx).trans (mul_dvd_mul_left _ (core_dvd_label hx 0))
  fin_cases i
  · exact hx.a1.trans hrad
  · exact hx.a2.trans hrad
  · apply hx.d.trans
    apply (mul_dvd_mul_left (x.core 1) (cube_radical_dvd hx)).trans
    convert mul_dvd_mul_left γ.q0 (common_label_dvd hx) using 1
    ring

lemma core_ne_zero {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (i : Fin 8) : x.core i ≠ 0 := by
  have hd : x.core i ∣ (γ.q0*f)^2 := by
    by_cases hi : i.val < 4
    · exact (core_dvd_label hx ⟨i.val, hi⟩).trans
        ((dvd_mul_left _ _).trans (dvd_pow_self _ (by decide : 2 ≠ 0)))
    · by_cases hi4 : i.val = 4
      · have he : i = 4 := Fin.ext hi4
        simpa only [he] using cube_factor_dvd_target hx
      · have he : (⟨(i.val-5)+5, by omega⟩ : Fin 8) = i := by
          apply Fin.ext
          dsimp
          omega
        exact (he ▸ core_dvd_outer_label hx ⟨i.val-5, by omega⟩).trans
          (dvd_pow_self _ (by decide : 2 ≠ 0))
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact (pow_ne_zero 2 (mul_ne_zero hq hf)) hd

theorem valid_key_injective {Jo Jn : ℕ} (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) {x y : SecondTuple Jo Jn}
    (hx : Valid x γ f k) (hy : Valid y γ f k)
    (hc : x.core = y.core) (ho : x.oldAssigned = y.oldAssigned)
    (hn : x.newAssigned = y.newAssigned) : x = y := by
  have hcore (i : Fin 8) : x.core i = y.core i := congrFun hc i
  have hv : x.commonResidual = y.commonResidual := by
    apply mul_left_cancel₀ (mul_ne_zero
      (mul_ne_zero (core_ne_zero hx hf hq 0) (core_ne_zero hx hf hq 1))
      (core_ne_zero hx hf hq 2))
    exact hx.label.trans (by simpa only [hcore] using hy.label.symm)
  have hj : x.cubeResidual = y.cubeResidual := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 3)
    exact hx.j_split.trans (by simpa only [hcore] using hy.j_split.symm)
  have hb : x.secondCube = y.secondCube := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 4)
    exact hx.b_split.trans (by simpa only [hcore, hj] using hy.b_split.symm)
  have hg : x.extractedCommon = y.extractedCommon := by
    rw [← hx.extracted_eq, ← hy.extracted_eq, hcore]
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ (mul_ne_zero hx.generator_d hx.generator_d2)
    exact hx.row_eq.trans (by simpa only [hcore] using hy.row_eq.symm)
  exact SecondTuple.ext (hx.outer_eq.trans hy.outer_eq.symm) hc hv hj hb hg hr ho hn

theorem valid_tuple_card_le {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^4 * (idealDivisors ((γ.q0*f)^2)).card *
      (idealDivisors (γ.q0*f)).card^3 *
      (idealDivisors (γ.q0*f*γ.quotient)).card^Jo *
      (idealDivisors (f*γ.residual)).card^Jn := by
  let D := idealDivisors f
  let E := idealDivisors ((γ.q0*f)^2)
  let F := idealDivisors (γ.q0*f)
  let A := idealDivisors (γ.q0*f*γ.quotient)
  let B := idealDivisors (f*γ.residual)
  let Target := (Fin 4 → D) × E × (Fin 3 → F) × (Fin Jo → A) × (Fin Jn → B)
  let encode (x : T) : Target :=
    (fun i => ⟨x.val.core ⟨i.val, by omega⟩,
      (mem_idealDivisors hf).mpr (core_dvd_label (hT x.val x.property) i)⟩,
    ⟨x.val.core 4, (mem_idealDivisors (pow_ne_zero 2 (mul_ne_zero hq hf))).mpr
      (cube_factor_dvd_target (hT x.val x.property))⟩,
    (fun i => ⟨x.val.core ⟨i.val+5, by omega⟩,
      (mem_idealDivisors (mul_ne_zero hq hf)).mpr (core_dvd_outer_label (hT x.val x.property) i)⟩),
    (fun i => ⟨(x.val.oldAssigned i).val,
      (mem_idealDivisors (mul_ne_zero (mul_ne_zero hq hf) ht)).mpr
        ((hT x.val x.property).old_dvd i)⟩),
    (fun i => ⟨(x.val.newAssigned i).val,
      (mem_idealDivisors (mul_ne_zero hf hr)).mpr ((hT x.val x.property).new_dvd i)⟩))
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply valid_key_injective γ f k hf hq (hT x.val x.property) (hT y.val y.property)
    · funext i
      fin_cases i
      · exact congrArg (fun z : Target => (z.1 0).val) he
      · exact congrArg (fun z : Target => (z.1 1).val) he
      · exact congrArg (fun z : Target => (z.1 2).val) he
      · exact congrArg (fun z : Target => (z.1 3).val) he
      · exact congrArg (fun z : Target => z.2.1.val) he
      · exact congrArg (fun z : Target => (z.2.2.1 0).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 1).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 2).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.1 i).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.2 i).val) he
  simpa only [Target, D, E, F, A, B, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc] using Fintype.card_le_of_injective encode hi

lemma divisor_card_sq_le (I : Ideal O) (hI : I ≠ 0) :
    (idealDivisors (I ^2)).card ≤ (idealDivisors I).card^2 := by
  simpa only [pow_two] using divisor_card_mul_le I I hI hI

theorem valid_tuple_card_le_separated {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^(9+Jo+Jn) * (idealDivisors γ.q0).card^(5+Jo) *
      (idealDivisors γ.quotient).card^Jo * (idealDivisors γ.residual).card^Jn := by
  let df := (idealDivisors f).card
  let dq := (idealDivisors γ.q0).card
  let dt := (idealDivisors γ.quotient).card
  let dr := (idealDivisors γ.residual).card
  have hqf : (idealDivisors (γ.q0*f)).card ≤ dq*df := divisor_card_mul_le _ _ hq hf
  have hsq : (idealDivisors ((γ.q0*f)^2)).card ≤ (dq*df)^2 :=
    (divisor_card_sq_le _ (mul_ne_zero hq hf)).trans (Nat.pow_le_pow_left hqf 2)
  have hold : (idealDivisors (γ.q0*f*γ.quotient)).card ≤ dq*df*dt :=
    (divisor_card_mul_le _ _ (mul_ne_zero hq hf) ht).trans (Nat.mul_le_mul_right _ hqf)
  have hnew : (idealDivisors (f*γ.residual)).card ≤ df*dr := divisor_card_mul_le _ _ hf hr
  apply (valid_tuple_card_le T γ f k hf hq ht hr hT).trans
  calc
    _ ≤ df^4 * (dq*df)^2 * (dq*df)^3 * (dq*df*dt)^Jo * (df*dr)^Jn := by
      gcongr
    _ = _ := by
      dsimp [df, dq, dt, dr]
      simp only [mul_pow, pow_add]
      ring

theorem valid_tuple_card_le_slot_cap {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) := by
  apply (valid_tuple_card_le_separated T γ f k hf hq ht hr hT).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos γ.q0 hq) (by omega)))
    (pow_le_pow_right₀ (divisor_card_pos γ.quotient ht) ho))
    (pow_le_pow_right₀ (divisor_card_pos γ.residual hr) hn)

theorem valid_label_squarefree {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hJ : Squarefree (x.core 0)) (hC : Squarefree (x.core 1))
    (hg : Squarefree x.extractedCommon) (hv : Squarefree x.commonResidual)
    (hJC : IsCoprime (x.core 0) (x.core 1))
    (hgmask : IsCoprime x.extractedCommon (x.core 1 * x.core 0))
    (hvmask : IsCoprime x.commonResidual (x.extractedCommon * x.core 1 * x.core 0)) :
    Squarefree f := by
  have hdg : x.core 2 ∣ x.extractedCommon := ⟨γ.residual, hx.extracted_eq.symm⟩
  have hdJC : IsCoprime (x.core 2) (x.core 0 * x.core 1) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : (x.core 0 * x.core 1) * x.core 2 ∣
      x.extractedCommon * x.core 1 * x.core 0 := by
    convert mul_dvd_mul_left (x.core 0 * x.core 1) hdg using 1
    ring
  have hvJCd := hvmask.of_isCoprime_of_dvd_right hdiv
  rw [← hx.label]
  exact squarefree_mul_iff.mpr ⟨hvJCd.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨hdJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime, hJ, hC⟩,
      hg.squarefree_of_dvd hdg⟩, hv⟩

theorem cube_quotient_norm_sq_le {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) :
    Ideal.absNorm γ.q0 ^ 2 ≤ Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube := by
  have hj0 : x.cubeResidual ≠ 0 := by
    intro hz
    have he := hx.j_split
    rw [hz, mul_zero] at he
    exact core_ne_zero hx hf hq 0 he.symm
  have hp0 : x.core 4 * x.secondCube ≠ 0 := by
    rw [hx.b_split]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hq) (pow_ne_zero 2 hj0))
      (core_ne_zero hx hf hq 3)
  have hdiv : γ.q0^2 ∣ x.core 4 * x.secondCube := by
    rw [hx.b_split]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun hz => hp0 (Ideal.absNorm_eq_zero_iff.mp hz)))
    (map_dvd Ideal.absNorm hdiv)
  simpa only [map_pow, map_mul] using hn

theorem cube_quotient_norm_le {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (N : ℕ)
    (hpair : Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2) :
    Ideal.absNorm γ.q0 ≤ N := by
  have hh := (cube_quotient_norm_sq_le hx hf hq).trans hpair
  nlinarith

def originalSource {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset (SecondTuple Jo Jn) :=
  source.filter fun x => (∀ i, x.oldAssigned i ∈ oldLists i) ∧
    (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x

def sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) : Finset OuterTriple :=
  (originalSource source oldLists newLists keep).image SecondTuple.outer

theorem mem_sourceTriples {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) :
    γ ∈ sourceTriples source oldLists newLists keep ↔
      ∃ x ∈ source, (∀ i, x.oldAssigned i ∈ oldLists i) ∧
        (∀ i, x.newAssigned i ∈ newLists i) ∧ keep x ∧ x.outer = γ := by
  simp only [sourceTriples, originalSource, Finset.mem_image, Finset.mem_filter]
  aesop

theorem sourceTriples_property {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (P : OuterTriple → Prop)
    (hP : ∀ x ∈ originalSource source oldLists newLists keep, P x.outer)
    (γ : OuterTriple) (hγ : γ ∈ sourceTriples source oldLists newLists keep) : P γ := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hγ
  exact hP x hx

theorem sourceTriples_cube_norm_le {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (N : ℕ)
    (hsrc : ∀ x ∈ originalSource source oldLists newLists keep,
      ∃ f k, Valid x x.outer f k ∧ f ≠ 0 ∧ x.outer.q0 ≠ 0 ∧
        Ideal.absNorm (x.core 4) * Ideal.absNorm x.secondCube ≤ N^2)
    (γ : OuterTriple) (hγ : γ ∈ sourceTriples source oldLists newLists keep) :
    Ideal.absNorm γ.q0 ≤ N := by
  apply sourceTriples_property source oldLists newLists keep
    (fun γ => Ideal.absNorm γ.q0 ≤ N) ?_ γ hγ
  intro x hx
  obtain ⟨f, k, hv, hf, hq, hpair⟩ := hsrc x hx
  exact cube_quotient_norm_le hv hf hq N hpair

def secondFiber {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O) :
    Finset (SecondTuple Jo Jn) :=
  (originalSource source oldLists newLists keep).filter (fun x => Valid x γ f k)

theorem secondFiber_outer_mem {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (x : SecondTuple Jo Jn) (hx : x ∈ secondFiber source oldLists newLists keep γ f k) :
    γ ∈ sourceTriples source oldLists newLists keep := by
  obtain ⟨hsrc, hv⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_image.mpr ⟨x, hsrc, hv.outer_eq⟩

theorem secondFiber_empty_of_not_sourceTriple {Jo Jn : ℕ}
    (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hγ : γ ∉ sourceTriples source oldLists newLists keep) :
    secondFiber source oldLists newLists keep γ f k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hγ (secondFiber_outer_mem source oldLists newLists keep γ f k x hx)

theorem secondFiber_card_le {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (secondFiber source oldLists newLists keep γ f k).card ≤
      (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ γ f k hf hq ht hr
    (fun _x hx => (Finset.mem_filter.mp hx).2) K ho hn

theorem secondFiber_weight_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop) (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ secondFiber source oldLists newLists keep γ f k, ‖w x‖ ≤ C) :
    (∑ x ∈ secondFiber source oldLists newLists keep γ f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(9+4*K) *
        ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
        ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
        ((idealDivisors γ.residual).card : ℝ)^(2*K) := by
  calc
    _ ≤ ∑ _x ∈ secondFiber source oldLists newLists keep γ f k, C := Finset.sum_le_sum hw
    _ = ((secondFiber source oldLists newLists keep γ f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
        (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) : ℕ) * C :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (secondFiber_card_le source oldLists newLists keep γ f k hf hq ht hr K ho hn)) hC
    _ = _ := by push_cast; ring

end
end SevenEighths.InverseSecondFibers

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev SecondChild := OuterTriple × Ideal Eis × Eis

def secondChild {Jo Jn : ℕ} (x : SecondTuple Jo Jn) : SecondChild :=
  (x.outer, x.core 0 * x.core 1 * x.core 2 * x.commonResidual,
    primaryGenerator (x.core 7) * primaryGenerator (x.core 2) * x.frequency)

def secondDivisorWeight (K : ℕ) (c : SecondChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (9 + 4*K) *
    ((idealDivisors c.1.q0).card : ℝ) ^ (5 + 2*K) *
    ((idealDivisors c.1.quotient).card : ℝ) ^ (2*K) *
    ((idealDivisors c.1.residual).card : ℝ) ^ (2*K)

theorem secondChild_eq_iff_valid {Jo Jn : ℕ} (x : SecondTuple Jo Jn)
    (hx : Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (c : SecondChild) : secondChild x = c ↔ Valid x c.1 c.2.1 c.2.2 := by
  constructor
  · intro he
    simpa only [he] using hx
  · intro hv
    apply Prod.ext hv.outer_eq
    exact Prod.ext hv.label hv.row_eq

theorem secondChild_fiber_weight {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (c : SecondChild) (hf : c.2.1 ≠ 0) (hq : c.1.q0 ≠ 0)
    (ht : c.1.quotient ≠ 0) (hr : c.1.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1) :
    (∑ x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), w x) ≤
      secondDivisorWeight K c := by
  have hfilter : (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c) =
      secondFiber source oldLists newLists keep c.1 c.2.1 c.2.2 := by
    apply Finset.filter_congr
    intro x hx
    exact secondChild_eq_iff_valid x (hvalid x hx) c
  calc
    _ ≤ ∑ _x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((secondFiber source oldLists newLists keep c.1 c.2.1 c.2.2).card : ℝ) := by rw [hfilter]; simp
    _ ≤ secondDivisorWeight K c := by
      have hh := secondFiber_card_le source oldLists newLists keep c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
      dsimp only [secondDivisorWeight]
      exact_mod_cast hh

theorem second_energy_projection {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℝ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, w x ≤ 1)
    (F : SecondChild → ℂ) :
    (∑ x ∈ originalSource source oldLists newLists keep, w x * ‖F (secondChild x)‖ ^ 2) ≤
      ∑ γ ∈ sourceTriples source oldLists newLists keep,
        ((idealDivisors γ.q0).card : ℝ) ^ (5 + 2*K) *
        ((idealDivisors γ.quotient).card : ℝ) ^ (2*K) *
        ((idealDivisors γ.residual).card : ℝ) ^ (2*K) *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (9 + 4*K) *
          ∑ k ∈ rows, ‖F (γ, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ originalSource source oldLists newLists keep,
      secondChild x ∈ sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows),
      (∑ x ∈ (originalSource source oldLists newLists keep).filter (fun x => secondChild x = c), w x) ≤
        secondDivisorWeight K c := by
    intro c hc
    obtain ⟨hγ, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨hq, ht, hr⟩ := houter c.1 hγ
    exact secondChild_fiber_weight source oldLists newLists keep hvalid c
      (hf c.2.1 (Finset.mem_product.mp hfk).1) hq ht hr K ho hn w hw
  have he := fiber_energy_bound (originalSource source oldLists newLists keep)
    (sourceTriples source oldLists newLists keep ×ˢ (labels ×ˢ rows)) secondChild w
    (secondDivisorWeight K) (fun c => ‖F c‖ ^ 2) hmaps (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, secondDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hfm
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondPass -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem marked_input_smoothed_second_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F A : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : Eis, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖inputConjugateRow p hg F Ψ m c d
        (fun U => H U * primeMark slots lists a (A ∪ U)) z‖ ^ 2 : ℝ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d
          (fun U => H U * primeMark slots lists a (A ∪ U)) G U V *
          maskedSecondDual p hg hp hinj G U V W Y else 0 :=
  inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d _ W Y hY

def canonicalMarkedSplit (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
      (c * e * ∏ i ∈ V, p i) (d * e * k)
      (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V)

theorem secondActualPair_marked_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U / X₁))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U / X₂)) =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z, V) *
        star (canonicalMarkedSplit p hp hcop hg F V A₁ (secondRayMinus Ψ₁ z)
          m r c d e k slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ (secondRayPlus Ψ₂ z)
          m r c d e (-k) slots₂ lists₂ a₂ W₂ X₂ := by
  rw [secondActualPair_eq_children p hp hcop hg hinj hc hpr]
  simp only [secondChildSum_marked_fixed_pool, canonicalMarkedSplit]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstPass -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem marked_dilatedCoreRow_eq_input_family
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (t : ℝ) (z : Eis) :
    dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A ∪ U) * H U))
      V y c d t z =
    ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z :=
  dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative χ Ψ m _ V y c d t z

theorem firstCoreInputRow_marked_priority
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
      (fun U => primeMark slots lists a (A ∪ U) * H U) V y c d r t z =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ D) *
      firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
        (fun U => primeMark (slots \ J) (fun i => lists i \ (A ∪ D)) a U * H U)
        V y c d r t z := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have he := primeMark_priority slots lists a (A ∪ D) U
  simp only [primeMark_residual_lists] at he
  have hset : (D ∪ U) \ (A ∪ D) = U \ (A ∪ D) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  simp only [secondInputCoefficient, firstCoreTest, ← Finset.union_assoc]
  rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum, ← primeMark_residual_lists, hset]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem firstCoreInputRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (c d : Eis) (r : FirstCoreIndex) (t : ℝ) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z =
      inputConjugateRow p hg F (firstCoreTwist negative χ Ψ r)
        ((m * b0Label p B v ε₁ ε₂) * ∏ i ∈ D, p i)
        (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D)
        (if negative then -z else z) :=
  inputConjugateRow_fixed_pool p hg hinj F D _ _ _ _ _ _

end
end SevenEighths.InverseMoment

end OAI

end

