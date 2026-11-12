module

public import Green64.Library.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part014
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part008

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part018

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondActivePhysicalDictionary -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondActivePhysicalDictionary
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorColumns
open CenteredMomentSecondSectorFrequency CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth
local notation "O"=>HeckeFamily.O

 theorem sectorPool_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β:Ideal O→ℂ):
    sectorPool C hC (activeSource S β)=(sectorPool C hC S).filter (fun I=>β (C*I)≠0):=by
  ext I
  simp only [sectorPool,Finset.mem_filter,mem_residualPool,supportedColumns_active]
  tauto

 theorem sector_sum_active (C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(β f:Ideal O→ℂ)
    (hf:∀I,β (C*I)=0→f I=0):
    (∑I∈sectorPool C hC (activeSource S β),f I)=∑I∈sectorPool C hC S,f I:=by
  rw [sectorPool_active,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h:β (C*I)=0
  · simp only [h,ne_eq,not_true_eq_false,ite_false,hf I h]
  · simp only [h,ne_eq,not_false_eq_true,ite_true]

 theorem sector_pair_sum_active (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(f:Ideal O→Ideal O→ℂ)
    (hleft:∀I J,β (C*I)=0→f I J=0)(hright:∀I J,β (D*J)=0→f I J=0):
    (∑I∈sectorPool C hC (activeSource S β),∑J∈sectorPool D hD (activeSource S β),f I J)=
      ∑I∈sectorPool C hC S,∑J∈sectorPool D hD S,f I J:=by
  simp_rw [sector_sum_active D hD S β _ (fun J h=>hright _ J h)]
  apply sector_sum_active C hC S β
  intro I h
  exact Finset.sum_eq_zero (fun J hJ=>hleft I J h)

 theorem sectorFrequency_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(F:O→Ideal O→Ideal O→ℂ)(z:O):
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal O→Ideal O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dite_eq_left hc,dite_eq_left hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=>physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

 theorem normalizedBlock_active (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    normalizedBlock η t S β C D hC hD U R rows W K n=
      normalizedBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold normalizedBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun _ I J=>wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
      (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((I.absNorm:ℝ)/dyadicScale (n 2)))
      (Real.log ((J.absNorm:ℝ)/dyadicScale (n 3)))) _

end SevenEighths.CenteredMomentSecondActivePhysicalDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondBlockSupport -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorFrequency CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

theorem normalizedBlock_zero_of_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hz:∀z∈rows,idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)=0) :
    normalizedBlock η t S β C D hC hD U R rows W K n=0 := by
  unfold normalizedBlock
  apply Finset.sum_eq_zero
  intro z hzr
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z) (hz z hzr)
  simpa only [sectorFrequency,F,mul_zero] using congrArg (fun x:ℂ=>retainedScalar C D U R z*x) he

theorem normalizedBlock_nonzero_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:normalizedBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  by_contra hn
  push Not at hn
  apply hne
  exact normalizedBlock_zero_of_common η t S β C D hC hD hCD U R rows W K n
    (fun z hz=>by simpa only [mul_assoc] using hn z hz)

theorem physicalBlock_nonzero_common (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  exact normalizedBlock_nonzero_common η t S β C D hC hD hCD U R rows W K n
    (right_ne_zero_of_mul hne)

end SevenEighths.CenteredMomentSecondBlockSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondPhysicalCost -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondPhysicalCost
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentCanonicalFirst CenteredMomentLogDyadic CenteredMomentSupport
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

theorem actual_normalized_prefactor (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K:ℝ) (n:Fin 4→ℤ) :
    outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))=
      K*(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)/
        (Real.sqrt (C.absNorm:ℝ)*Real.sqrt (D.absNorm:ℝ)*(∏P∈U,P.val).absNorm) := by
  have hcp:0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hdp:0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:=Real.sqrt_pos.mpr (dyadicScale_pos (n 2))
  have hy:=Real.sqrt_pos.mpr (dyadicScale_pos (n 3))
  rw [normalizer,actual_partitionNormalizer C D hC,outerScalar,
    Real.sqrt_mul (dyadicScale_pos (n 2)).le]
  field_simp

lemma logb_sqrt (Z x:ℝ) (hx:0<x) : Real.logb Z (Real.sqrt x)=Real.logb Z x/2 := by
  rw [Real.sqrt_eq_rpow,Real.logb_rpow_eq_mul_logb_of_pos hx]
  ring

theorem actual_prefactor_log (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (K Z:ℝ) (hK:0<K) (n:Fin 4→ℤ) :
    Real.logb Z (outerScalar C D K n*normalizer C D U*
      Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))=
      Real.logb Z K+
      Real.logb Z (Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ)-
      (Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/2-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ) := by
  have hc:0<(C.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hg:0<(Ideal.absNorm (Ideal.span {commonFrequencyGenerator C D}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by simpa only [Ideal.span_singleton_eq_bot] using commonFrequencyGenerator_ne_zero C D hC))
  have hu:0<((∏P∈U,P.val).absNorm:ℝ) := by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  rw [actual_normalized_prefactor C D hC hD,
    Real.logb_div (mul_pos hK hg).ne' (mul_pos (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd)) hu).ne',
    Real.logb_mul hK.ne' hg.ne',
    Real.logb_mul (mul_pos (Real.sqrt_pos.mpr hc) (Real.sqrt_pos.mpr hd)).ne' hu.ne',
    Real.logb_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hd).ne',
    logb_sqrt Z _ hc,logb_sqrt Z _ hd]
  ring

end SevenEighths.CenteredMomentSecondPhysicalCost

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondRetainedPair -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedPair
open CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentSecondWholeKernel CenteredMomentFirstLocalization CenteredMomentSectorLocalization
open CenteredMomentSecondLocalization CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem physical_pair_summable (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    Summable (fun j : O=>idealCorrelation (C*I) (D*J) hI hJ j*physicalKernel C D W K R j I J) := by
  have hk : 0<K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)) :=
    div_pos hK (mul_pos (CenteredMomentFirstScale.norm_pos _ hI.1) (CenteredMomentFirstScale.norm_pos _ hJ.1))
  have hc (j : O) : ‖idealCorrelation (C*I) (D*J) hI hJ j‖≤
      (Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J) := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le _ _
      ((supported_span_primaryGenerator_iff _).mpr hI) ((supported_span_primaryGenerator_iff _).mpr hJ) j
    simpa only [idealCorrelation,primary_span_supported _ hI,primary_span_supported _ hJ] using hh
  have hs := weighted_fourier_summable W _ hk (fun j=>idealCorrelation (C*I) (D*J) hI hJ j)
    (fun j=>(retainedWeight R (normValue j):ℂ)) _ hc (fun j=>retained_complex_norm R _)
  have he (j : O) : K*‖eisEmbedding j‖^2/‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2=
      (K/((Ideal.absNorm (C*I):ℝ)*Ideal.absNorm (D*J)))*normValue j := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ hI,primary_norm_sq _ hJ,normValue_eq_embedding]
    ring
  convert hs.mul_left
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ))) using 1
  funext j
  dsimp only [physicalKernel]
  rw [he]
  ring

theorem retainedPair_positive_frequency (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedPair I J hI hJ W K Tsec Z ξ=
      ∑' j : O,idealCorrelation I J hI hJ j*physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J := by
  have he := (Equiv.neg O).tsum_eq (fun j : O=>idealCorrelation I J hI hJ j*
    physicalKernel 1 1 W K (frequencyRadius Tsec Z ξ) j I J)
  simp only [Equiv.neg_apply,physicalKernel,one_mul,map_neg,norm_neg,
    normValue_eq_embedding] at he
  simp only [physicalKernel,one_mul,normValue_eq_embedding]
  rw [←he]
  unfold secondRetainedPair
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [idealCorrelation,normValue_eq_embedding]
  ring

end SevenEighths.CenteredMomentSecondRetainedPair

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSourceRetained -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondLocalization CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentCompleteCommon CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained CenteredMomentSecondRetainedPair
open CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  if hI : Supported I then if hJ : Supported J then secondRetainedPair I J hI hJ W K Tsec Z ξ else 0 else 0

theorem retainedKernel_eq (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel I J W K Tsec Z ξ=secondRetainedPair I J hI hJ W K Tsec Z ξ := by
  simp only [retainedKernel,dite_eq_left hI,dite_eq_left hJ]

theorem retainedEnergy_common_sectors (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
            retainedKernel q.1 q.2 W K Tsec Z ξ := by
  let F := fun I J : Ideal O=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
    retainedKernel I J W K Tsec Z ξ
  have he : secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,F I J := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [F]
    rw [retainedKernel_eq I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2]
  rw [he]
  have hj (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort _ _
  simp_rw [hj]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I=>∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ F

theorem retained_sector_independent (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ I : sectorPool C hC S,∑ J : sectorPool D hD S,
          if IsCoprime (I:Ideal O) (J:Ideal O) then
            ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
              retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0 := by
  rw [←independent_sector_pools C D hC hD hCD S
    (fun I J=>((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
      retainedKernel (C*I) (D*J) W K Tsec Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((β I*heightCoeff η t I)*star (β J*heightCoeff η t J))*
      retainedKernel I J W K Tsec Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

theorem retainedKernel_physical (C D I J : Ideal O) (hI : Supported (C*I)) (hJ : Supported (D*J))
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) :
    retainedKernel (C*I) (D*J) W K Tsec Z ξ=
      ∑' j : O,idealCorrelation (C*I) (D*J) hI hJ j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J := by
  rw [retainedKernel_eq _ _ hI hJ,retainedPair_positive_frequency]
  simp only [physicalKernel,one_mul]

end SevenEighths.CenteredMomentSecondSourceRetained

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondSourceFrequency -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceFrequency
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentSecondSourceRetained CenteredMomentFirstSectors
open CenteredMomentSecondSectorColumns CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorRetained
open CenteredMomentSecondRetainedPair CenteredMomentSecondSectorFrequency CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem retained_sector_eq_physical (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑' j : O,sectorFrequency η t S β C D hC hD
          (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j := by
  rw [retained_sector_independent η t S β C D hC.1 hD.1 hCD]
  congr 1
  let c := fun I : sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
  let d := fun J : sectorPool D hD.1 S=>β (D*J)*heightCoeff η t J
  have hci (I : sectorPool C hC.1 S) : Supported (C*(I:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩
  have hdj (J : sectorPool D hD.1 S) : Supported (D*(J:Ideal O)) :=
    (supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩
  let f := fun (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) (j : O)=>
    if IsCoprime (I:Ideal O) (J:Ideal O) then
      (c I*star (d J))*(idealCorrelation (C*I) (D*J) (hci I) (hdj J) j*
        physicalKernel C D W K (frequencyRadius Tsec Z ξ) j I J) else 0
  have hs (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) : Summable (f I J) := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simpa only [f,ite_eq_left hc] using (physical_pair_summable C D I J (hci I) (hdj J)
        W K (frequencyRadius Tsec Z ξ) hK).mul_left (c I*star (d J))
    · simp only [f,ite_eq_right hc];exact summable_zero
  have hp (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*
          retainedKernel (C*I) (D*J) W K Tsec Z ξ else 0)=∑' j : O,f I J j := by
    by_cases hc : IsCoprime (I:Ideal O) (J:Ideal O)
    · simp only [f,ite_eq_left hc]
      rw [retainedKernel_physical C D I J (hci I) (hdj J),tsum_mul_left]
    · simp only [f,ite_eq_right hc,tsum_zero]
  have hf (j : O) : sectorFrequency η t S β C D hC hD
      (physicalKernel C D W K (frequencyRadius Tsec Z ξ)) j=
      ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,f I J j := by
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    dsimp only [f,c,d]
    split_ifs <;> ring
  simp_rw [hp]
  rw [tsum_congr hf, Summable.tsum_finsetSum (fun I _=>summable_sum (fun J _=>hs I J))]
  exact Finset.sum_congr rfl (fun I _=>(Summable.tsum_finsetSum (fun J _=>hs I J)).symm)

theorem original_retained_sector_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff η t q.1)*star (β q.2*heightCoeff η t q.2))*
        retainedKernel q.1 q.2 W K Tsec Z ξ)=
      heightCoeff η t C*star (heightCoeff η t D)*
        ∑ U : Finset (CommonIndex C D),∑' h : O,
          if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
            sectorFrequency η t S β C D hC hD
              (physicalKernel C D W K (frequencyRadius Tsec Z ξ))
              ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*h) else 0 := by
  rw [retained_sector_eq_physical η t S β C D hC hD hCD W K Tsec Z ξ hK,
    actual_retained_sector_GV η t S β C D hC hD hCD W K (frequencyRadius Tsec Z ξ) hK]

end SevenEighths.CenteredMomentSecondSourceFrequency

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondRetainedAggregate -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSourceRetained CenteredMomentSecondSourceFrequency
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentHeckeColumnWindow CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O

theorem commonLabels_supported (S : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported C ∧ Supported D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  have hp' := Finset.mem_product.mp hp
  exact ⟨commonPart_supported _ _ (Finset.mem_filter.mp hp'.1).2,
    commonPart_supported _ _ (Finset.mem_filter.mp hp'.2).2⟩

theorem original_retained_energy_GV (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
          ∑ U : Finset (CommonIndex p.val.1 p.val.2),∑' h : O,
            if canonicalPartition p.val.1 p.val.2 U
                (nonunitFrequencyGenerator p.val.1 p.val.2 U*h) then
              sectorFrequency η t S β p.val.1 p.val.2
                (commonLabels_supported S _ _ p.property).1
                (commonLabels_supported S _ _ p.property).2
                (physicalKernel p.val.1 p.val.2 W K (frequencyRadius Tsec Z ξ))
                ((commonFrequencyGenerator p.val.1 p.val.2*
                  nonunitFrequencyGenerator p.val.1 p.val.2 U)*h) else 0 := by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  exact original_retained_sector_GV η t S β p.val.1 p.val.2
    (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2
    (commonLabels_data _ _ _ _ p.property).2.2 W K Tsec Z ξ hK

end SevenEighths.CenteredMomentSecondRetainedAggregate

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondRetainedRows -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

def retainedRows (R : ℝ) (A : O) : Finset O := rowNormDisk (Nat.ceil (4*R/normValue A))

theorem retained_mem_rows (R : ℝ) (A h : O) (hA : A≠0)
    (hh : retainedWeight R (normValue (A*h))≠0) : h∈retainedRows R A := by
  have he := retainedWeight_enclosure R _ hh
  have hAh : A*h≠0 := by
    intro hz
    have hn : normValue (A*h)=0 := by simp [hz,normValue]
    linarith [he.1]
  have hh0 : h≠0 := right_ne_zero_of_mul hAh
  apply mem_rowNormDisk.mpr
  constructor
  · have hn := normValue_pos h hh0
    unfold normValue at hn
    exact_mod_cast hn
  · have hbound : normValue h≤4*R/normValue A := by
      apply (le_div_iff₀ (normValue_pos A hA)).mpr
      simpa only [normValue_mul,mul_comm] using he.2
    have hb := hbound.trans (Nat.le_ceil (4*R/normValue A))
    unfold normValue at hb
    exact_mod_cast hb

theorem physical_sector_zero_of_weight (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (j : O)
    (hj : retainedWeight R (normValue j)=0) :
    sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) j=0 := by
  simp only [sectorFrequency,physicalKernel,hj,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem physical_partition_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (A : O) (hA : A≠0) (part : O→Prop) :
    (∑' h : O,if part h then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if part h then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  apply tsum_eq_sum
  intro h hh
  by_cases hp : part h
  · rw [ite_eq_left hp]
    apply physical_sector_zero_of_weight η t S β C D hC hD W K R (A*h)
    by_contra hn
    exact hh (retained_mem_rows R A h hA hn)
  · rw [ite_eq_right hp]

theorem actual_GV_finite_rows (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) :
    let A := commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑' h : O,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑ h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
        sectorFrequency η t S β C D hC hD (physicalKernel C D W K R) (A*h) else 0 := by
  dsimp only
  exact physical_partition_finite_rows η t S β C D hC hD W K R _
    (mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)) _

end SevenEighths.CenteredMomentSecondRetainedRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicAssembly -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstReduced CenteredMomentFirstColumns CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentRowNorm
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentPrimitive
local notation "O"=>ActualEisensteinCubic.O

def retainedBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def retainedIndices (R:ℝ):Finset ℤ := (finite_retained_integral_dyads R).toFinset

lemma mem_retainedIndices (R:ℝ)(n:ℤ):
    n∈retainedIndices R↔Retained R n ∧ ∃q:ℝ,1≤q ∧ dyadicWeight n q≠0 :=
  (finite_retained_integral_dyads R).mem_toFinset

lemma retained_partition (R q:ℝ)(hq:1≤q):
    (∑n∈retainedIndices R,dyadicWeight n q)=retainedWeight R q :=by
  unfold retainedWeight
  rw [tsum_eq_sum (s:=retainedIndices R) (fun n hn=>by
    split_ifs with hr
    · by_contra hh
      exact hn ((mem_retainedIndices R n).mpr ⟨hr,q,hq,hh⟩)
    · rfl)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ite_eq_left ((mem_retainedIndices R n).mp hn).1]

def bands (K R A B:ℝ):Fin 4→Finset ℤ :=
  ![indices K K,retainedIndices R,indices 1 A,indices 1 B]

abbrev Blocks (K R A B:ℝ):=∀i:Fin 4,↥(bands K R A B i)

lemma product_partition (K R A B h a b:ℝ)(hK:0<K)(hh:1≤h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B,∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i))=
      retainedWeight R h :=by
  have he (i:Fin 4):
      (∑n:bands K R A B i,dyadicWeight n (![K,h,a,b] i))=
        (if i=1 then retainedWeight R h else 1):=by
    fin_cases i
    · change (∑n:indices K K,dyadicWeight n K)=1
      rw [Finset.sum_coe_sort (indices K K) (fun n:ℤ=>dyadicWeight n K)]
      exact dyadic_partition_on_interval K K K hK ⟨le_rfl,le_rfl⟩
    · change (∑n:retainedIndices R,dyadicWeight n h)=retainedWeight R h
      rw [Finset.sum_coe_sort (retainedIndices R) (fun n:ℤ=>dyadicWeight n h)]
      exact retained_partition R h hh
    · change (∑n:indices 1 A,dyadicWeight n a)=1
      rw [Finset.sum_coe_sort (indices 1 A) (fun n:ℤ=>dyadicWeight n a)]
      exact dyadic_partition_on_interval 1 A a (by norm_num) ha
    · change (∑n:indices 1 B,dyadicWeight n b)=1
      rw [Finset.sum_coe_sort (indices 1 B) (fun n:ℤ=>dyadicWeight n b)]
      exact dyadic_partition_on_interval 1 B b (by norm_num) hb
  rw [←Fintype.prod_sum (fun (i:Fin 4)(n:bands K R A B i)=>
    dyadicWeight n (![K,h,a,b] i))]
  simp_rw [he]
  norm_num [Fin.prod_univ_four]

lemma windows_partition (K R A B h a b:ℝ)(hK:0<K)(hh:1≤h)
    (ha:a∈Set.Icc (1:ℝ) A)(hb:b∈Set.Icc (1:ℝ) B):
    (∑n:Blocks K R A B, windows (fun _=>logAnnulus) K h a b
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)))=
      (retainedWeight R h:ℂ):=by
  calc
    _ = ∑n:Blocks K R A B,((∏i:Fin 4,dyadicWeight (n i) (![K,h,a,b] i):ℝ):ℂ):=by
      apply Finset.sum_congr rfl
      intro n hn
      simpa [Fin.prod_univ_four] using
        (actual_product_windows K h a b hK (zero_lt_one.trans_le hh)
          (zero_lt_one.trans_le ha.1) (zero_lt_one.trans_le hb.1) (fun i=>n i)).symm
    _ = _ :=by
      rw [←Complex.ofReal_sum,product_partition K R A B h a b hK hh ha hb]

def effectiveScale (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ):ℝ:=
  (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2)/
    ‖eisEmbedding (activeConductor C D)‖^2

lemma effectiveScale_pos (C D:Ideal O)(E:Finset (CommonIndex C D))(K:ℝ)(hK:0<K):
    0<effectiveScale C D E K:=by
  unfold effectiveScale
  apply div_pos (div_pos hK ?_) ?_
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _)))

lemma element_norm (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    ‖eisEmbedding (element C D hD S a)‖^2=((a:Ideal O).absNorm:ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

lemma element_norm_ge_one (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    1≤‖eisEmbedding (element C D hD S a)‖^2:=by
  rw [element_norm]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (column_supported C D hD S a).1)

lemma element_norm_le (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S)
    (c:Ideal O→ℂ)(H:ℝ)(hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H)(ha:c (D*a)≠0):
    ‖eisEmbedding (element C D hD S a)‖^2≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  rw [element_norm]
  apply (le_div_iff₀ hDpos).mpr
  simpa only [map_mul,Nat.cast_mul,mul_comm] using hcap (D*a) ha

theorem retainedBlock_eq_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(hrows:∀h∈rows,h≠0)(W:𝓢(ℝ,ℂ))(K R H:ℝ)(hK:0<K)
    (hcap:∀I,c I≠0→(I.absNorm:ℝ)≤H):
    retainedBlock η m A t S c C D hC hD E rows W K R=
      ∑n:Blocks (effectiveScale C D E K) R (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)),
        block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
          (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  unfold retainedBlock block
  dsimp only
  rw [←Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true]
    by_cases hca:c (C*(a:Ideal O))=0
    · simp [coefficient,hca]
    by_cases hcb:c (D*(b:Ideal O))=0
    · simp [coefficient,hcb]
    have hnorm:1≤‖eisEmbedding h‖^2:=by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hrows h hh)))
    have hpart:=windows_partition (effectiveScale C D E K) R
      (H/(C.absNorm:ℝ)) (H/(D.absNorm:ℝ)) (‖eisEmbedding h‖^2)
      (‖eisEmbedding (element C C hC.1 S a)‖^2) (‖eisEmbedding (element C D hD.1 S b)‖^2)
      (effectiveScale_pos C D E K hK) hnorm
      ⟨element_norm_ge_one C C hC.1 S a,element_norm_le C C hC.1 S a c H hcap hca⟩
      ⟨element_norm_ge_one C D hD.1 S b,element_norm_le C D hD.1 S b c H hcap hcb⟩
    rw [←Finset.sum_mul,←Finset.mul_sum]
    congr 1
    congr 1
    exact hpart.symm
  · simp [hab]

lemma block_retained (K R A B:ℝ)(n:Blocks K R A B):Retained R (n 1):=
  ((mem_retainedIndices R (n 1)).mp (n 1).property).1

def retainedInfiniteBlock (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑'h:O,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (retainedWeight R (‖eisEmbedding h‖^2):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

lemma retained_rows_nonzero (R:ℝ):
    ∀h∈CenteredMomentSecondRetainedRows.retainedRows R 1,h≠0:=by
  intro h hh hz
  have hn:=(mem_rowNormDisk.mp hh).1
  subst h
  simp at hn

theorem retainedInfiniteBlock_eq_finite
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedInfiniteBlock η m A t S c C D hC hD E W K R=
      retainedBlock η m A t S c C D hC hD E
        (CenteredMomentSecondRetainedRows.retainedRows R 1) W K R:=by
  unfold retainedInfiniteBlock retainedBlock
  dsimp only
  congr 1
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (‖eisEmbedding h‖^2)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul,normValue_eq_embedding] using hn
  simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

theorem original_retained_dyadic
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K R:ℝ)(hK:0<K):
    retainedInfiniteBlock s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) C D hC hD E W K R=
      ∑n:Blocks (effectiveScale C D E K) R
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
          (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
        block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
          C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
          (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)):=by
  rw [retainedInfiniteBlock_eq_finite]
  exact retainedBlock_eq_blocks s.η m A t S _ C D hC hD E _
    (retained_rows_nonzero R) W K R _ hK
    (fun I hI=>(CenteredMomentOriginalCommonHarmonic.original_column_norm s Rbad seed I hz₁ hz₂ hI).2)

end SevenEighths.CenteredMomentFirstPhysicalDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicCount -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentDyadicCount

lemma indices_mono_upper (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hbc : b≤ c) :
    indices a b ⊆ indices a c := by
  intro n hn
  rw [mem_indices_iff_scale a c ha (hb.trans_le hbc)]
  have h := (mem_indices_iff_scale a b ha hb n).mp hn
  exact ⟨h.1,h.2.trans (by linarith)⟩

lemma blocks_card_le (K R H nC nD : ℝ) (hH : 0<H)
    (hC : 1≤nC) (hD : 1≤nD) :
    Fintype.card (Blocks K R (H/nC) (H/nD)) ≤
      Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
        (![K,max 1 R,max 1 H,max 1 H] i))) := by
  have hcol (n : ℝ) (hn : 1≤n) : indices 1 (H/n) ⊆ indices 1 (max 1 H) := by
    apply indices_mono_upper _ _ _ (by norm_num) (div_pos hH (zero_lt_one.trans_le hn))
    exact (div_le_self hH.le hn).trans (le_max_right _ _)
  have hs (i : Fin 4) : bands K R (H/nC) (H/nD) i ⊆
      indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i) := by
    fin_cases i
    · exact Finset.Subset.refl _
    · intro n hn
      obtain ⟨hr,q,hq,hne⟩ := (mem_retainedIndices R n).mp hn
      exact retained_integral_mem R q hq n hr hne
    · exact hcol nC hC
    · exact hcol nD hD
  let f : Blocks K R (H/nC) (H/nD) →
      (∀i:Fin 4,↥(indices (![K,1,1,1] i) (![K,max 1 R,max 1 H,max 1 H] i))) :=
    fun x i => ⟨x i,hs i (x i).property⟩
  apply Fintype.card_le_of_injective f
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrArg (fun z => (z i).val) hxy

theorem blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀K R H nC nD : ℝ,0<K → 0<H → 1≤nC → 1≤nD →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower (max 1 Cr) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro K R H nC nD hK hH hnC hnD hR hHcap
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hbound : 1≤ max 1 Cr*Z^(B+L) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) hp
  have hR' : max 1 R≤ max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hR.trans (mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (Real.rpow_nonneg hz.le _) (by positivity))
  have hH' : max 1 H≤ max 1 Cr*Z^(B+L) := by
    apply max_le hbound
    exact hHcap.trans ((Real.rpow_le_rpow_of_exponent_le hZ (by linarith : B≤B+L)).trans
      (le_mul_of_one_le_left (zero_le_one.trans hp) (le_max_left _ _)))
  have hfour := hcount ![K,1,1,1] ![K,max 1 R,max 1 H,max 1 H]
    (by intro i;fin_cases i <;> simp [hK])
    (by intro i;fin_cases i <;> simp)
    (by intro i;fin_cases i
        · simpa [div_self hK.ne'] using hbound
        · simpa using hR'
        · simpa using hH'
        · simpa using hH')
  exact (show (Fintype.card (Blocks K R (H/nC) (H/nD)):ℝ)≤
    Fintype.card (∀i:Fin 4,↥(indices (![K,1,1,1] i)
      (![K,max 1 R,max 1 H,max 1 H] i))) by
      exact_mod_cast blocks_card_le K R H nC nD hH hnC hnD).trans hfour

theorem original_blocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D : Ideal ActualEisensteinCubic.O), C≠0 → D≠0 →
      ∀(E : Finset (CenteredMomentCanonicalFirst.CommonIndex C D))
        (K R H : ℝ),0<K → 0<H → R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (Blocks (effectiveScale C D E K) R
        (H/Ideal.absNorm C) (H/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  obtain ⟨C₀,hC₀,hcount⟩ := blocks_subpower B L Cr ε hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount] with Z hcount
  intro C D hC hD E K R H hK hH hR hHcap
  have norm_one (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
      (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hcount _ _ _ _ _ (effectiveScale_pos C D E K hK) hH
    (norm_one C hC) (norm_one D hD) hR hHcap

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstRetainedPhysical -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedPhysical
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentSourceRow
open CenteredMomentFirstRetainedSector CenteredMomentFirstCommonFourierTransport
open CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

 theorem original_sector_columns (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:C≠0)(hD:D≠0)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      ∑a:columns C C hC S,∑b:columns C D hD S,
        if IsCoprime (a:Ideal O) (b:Ideal O) then
          (coefficient η m A t c C a*star (coefficient η m A t c D b))*
            retainedKernel (C*a) (D*b) W K X Z ξ else 0:=by
  rw [←original_pool_restriction C D hC hD S
    (fun a b=>(coefficient η m A t c C a*star (coefficient η m A t c D b))*
      retainedKernel (C*a) (D*b) W K X Z ξ)]
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI=>(Finset.mem_filter.mp hI).2.1) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun I J=>((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedKernel I J W K X Z ξ)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [coefficient,map_mul,star_mul,mul_zero]
  ring

def fixedRetainedSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0

theorem original_sector_fixed (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)=
    rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
      fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=by
  rw [original_sector_columns η m A t S c C D hC.1 hD.1 hCD W K X Z ξ]
  congr 1
  let F:=fun (a:columns C C hC.1 S) (b:columns C D hD.1 S) (E:Finset (CommonIndex C D))=>
    if IsCoprime (a:Ideal O) (b:Ideal O) then
      (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
    else 0
  calc
    _=∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
      · simp only [F,hab,ite_true]
        rw [retainedKernel_fixed C D a b hC hD (column_supported C C hC.1 S a)
          (column_supported C D hD.1 S b) hCD (Finset.mem_filter.mp a.property).2
          (Finset.mem_filter.mp b.property).2 hab W K X Z ξ,Finset.mul_sum]
        rfl
      · simp only [F,hab,ite_false,Finset.sum_const_zero]
    _=∑a:columns C C hC.1 S,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
      ∑b:columns C D hD.1 S,F a b E:=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=fixedRetainedSector η m A t S c C D hC hD W K X Z ξ:=Finset.sum_comm

end SevenEighths.CenteredMomentFirstRetainedPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstRetainedBlock -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedBlock
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CompletedGauss CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstCommonFourierTransport
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentSectorLocalization CenteredMomentFirstScale
local notation "O"=>ActualEisensteinCubic.O

lemma retained_tsum (R:ℝ)(f:O→ℂ):
    (∑'h:O,(retainedWeight R (normValue h):ℂ)*f h)=
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (retainedWeight R (normValue h):ℂ)*f h:=by
  apply tsum_eq_sum
  intro h hh
  have hz:retainedWeight R (normValue h)=0:=by
    by_contra hn
    apply hh
    apply CenteredMomentSecondRetainedRows.retained_mem_rows R 1 h one_ne_zero
    simpa only [one_mul] using hn
  simp only [hz,Complex.ofReal_zero,zero_mul]

lemma retainedFourierTerm_finite (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r ha hb hr χa χb G e E W K R=
      (UniqueFactorizationMonoid.moebius E:ℂ)*
      ∑h∈CenteredMomentSecondRetainedRows.retainedRows R 1,
        (tripleRow a b r χa χb G e *
          (((K/normValue e)/normValue (a*(b*r)):ℝ):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h)*
        (retainedWeight R (normValue h):ℂ)*
        EisensteinSchwartzPoisson.paperRadialFourier W
          ((K/normValue e)*normValue h/normValue (a*(b*r))):=by
  unfold retainedFourierTerm
  dsimp only
  simp_rw [mul_assoc (retainedWeight R (normValue _):ℂ)]
  rw [retained_tsum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [show (K/normValue e)/normValue (a*(b*r))*normValue h=
    (K/normValue e)*normValue h/normValue (a*(b*r)) by ring]
  ring

lemma finite_pair_row_sum {α β:Type*}[Fintype α][Fintype β]
    (rows:Finset O)(p:α→β→Prop)[DecidableRel p]
    (c:α→β→ℂ)(μ:ℂ)(f:α→β→O→ℂ):
    (∑a:α,∑b:β,if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
      μ*∑h∈rows,∑a:α,∑b:β,if p a b then c a b*f a b h else 0:=by
  have hp (a:α)(b:β):
      (if p a b then c a b*(μ*∑h∈rows,f a b h) else 0)=
        ∑h∈rows,μ*(if p a b then c a b*f a b h else 0):=by
    by_cases hab:p a b
    · simp only [hab,ite_true,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    · simp [hab]
  simp_rw [hp,Finset.mul_sum]
  calc
    _=∑a:α,∑h∈rows,∑b:β,μ*(if p a b then c a b*f a b h else 0):=by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _=_:=Finset.sum_comm

theorem fixed_sector_term_block
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    (∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
          fixedRetainedTerm C D hC (element C C hC.1 S a) (element C D hD.1 S b)
            (element_supported C C hC.1 S a) (element_supported C D hD.1 S b) E W K X Z ξ
      else 0)=
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedTerm
  generalize_proofs
  simp_rw [retainedFourierTerm_finite]
  rw [finite_pair_row_sum]
  rw [retainedInfiniteBlock_eq_finite]
  unfold retainedBlock inactiveWeight
  dsimp only
  simp only [normValue_eq_embedding]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> ring

theorem fixed_sector_blocks
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    fixedRetainedSector η m A t S c C D hC hD W K X Z ξ=
      ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
        retainedInfiniteBlock η m A t S c C D hC hD E W K
          (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ):=by
  unfold fixedRetainedSector
  apply Finset.sum_congr rfl
  intro E hE
  exact fixed_sector_term_block η m A t S c C D hC hD E W K X Z ξ

end SevenEighths.CenteredMomentFirstRetainedBlock

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstRetainedAssembly -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedAssembly
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedPhysical CenteredMomentFirstRetainedSector
open CenteredMomentFirstRetainedBlock CenteredMomentFirstSectorTransform CenteredMomentFirstSectors
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation CenteredMomentHeckeExpansion
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
local notation "O"=>ActualEisensteinCubic.O

def infiniteSector (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    retainedInfiniteBlock η m A t S c C D hC hD E W K
      (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem retained_energy_blocks (η:Character)(m A:O)(t:ℝ)
    (S:Finset (Ideal O))(c:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedEnergy η m A t S c W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          infiniteSector η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retainedEnergy_common_sectors]
  rw [←Finset.sum_coe_sort _ (fun p:Ideal O×Ideal O=>
    ∑q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
        retainedKernel q.1 q.2 W K X Z ξ)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [original_sector_fixed η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K X Z ξ]
  exact congrArg (fun z=>rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*z)
    (fixed_sector_blocks η m A t S c p.val.1 p.val.2
      (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ)

def physicalSector {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

theorem original_retained_physical
    {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S
      (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed) W K X Z ξ=
      ∑p:commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
          physicalSector s Rbad seed m A t S p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K X Z ξ:=by
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg
  unfold infiniteSector physicalSector
  apply Finset.sum_congr rfl
  intro E hE
  exact original_retained_dyadic s Rbad seed hz₁ hz₂ m A t S p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2 E W K _ hK

end SevenEighths.CenteredMomentFirstRetainedAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstRetainedNorm -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstRetainedNorm
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentHeckeExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSourceRow CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentRowNorm
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstScale CenteredMomentLogDyadic
open CenteredMomentActiveSource (activeSource)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def sector (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))

def sectorMass (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℝ:=
  ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets C D,
    let R:=frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ
    ∑n:Blocks (effectiveScale C D E K) R
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(C.absNorm:ℝ))
        (CenteredMomentOriginalCommonHarmonic.sourceRadius s/(D.absNorm:ℝ)),
      ‖block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed)
        C D hC hD E (CenteredMomentSecondRetainedRows.retainedRows R 1) W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
        (dyadicScale (n 2)) (dyadicScale (n 3))‖

omit [DecidableEq ι] in
theorem sector_norm (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    ‖sector s Rbad seed m A t S C D hC hD W K X Z ξ‖≤
      sectorMass s Rbad seed m A t S C D hC hD W K X Z ξ:=by
  unfold sector sectorMass
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro E hE
  exact norm_sum_le _ _

theorem original_active_sectors (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed
    let T:=activeSource S β
    CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ=
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)*
        sector s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [←retained_energy_active s.η m A t S _ W K X Z ξ]
  exact original_retained_physical s Rbad seed hz₁ hz₂ m A t _ W K X Z ξ hK

theorem original_retained_norm (s:CenteredMomentCommonRadialData.Input ι)(Rbad seed:Ideal O)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(m A:O)(t:ℝ)(S:Finset (Ideal O))
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ)(hK:0<K):
    let β:=CenteredMomentOriginalCommonHarmonic.coefficient s Rbad seed
    let T:=activeSource S β
    ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A t S β W K X Z ξ‖≤
      ∑p:commonLabels (supportedColumns T) (supportedColumns T),
        sectorMass s Rbad seed m A t T p.val.1 p.val.2
          (commonLabels_supported T p).1 (commonLabels_supported T p).2 W K X Z ξ:=by
  dsimp only
  rw [original_active_sectors s Rbad seed hz₁ hz₂ m A t S W K X Z ξ hK]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  have hw:‖rowWeight s.η m A 1 t p.val.1*star (rowWeight s.η m A 1 t p.val.2)‖≤1:=by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one _ _ _ _ _ _
        (commonLabels_supported _ p).1.1)).trans
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one _ _ _ _ _ _
        (commonLabels_supported _ p).2.1)
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans (sector_norm s Rbad seed m A t _ _ _ _ _ W K X Z ξ)

end SevenEighths.CenteredMomentFirstRetainedNorm

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondActiveDyadic -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => ActualEisensteinCubic.O

def sourceLower (C D : Ideal O) (A : O) (K : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,1,1,1]

def sourceUpper (C D : Ideal O) (A : O) (K R H : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,max 1 (4*R/normValue A),
    max 1 (H/(Ideal.absNorm C:ℝ)),max 1 (H/(Ideal.absNorm D:ℝ))]

def dyadicKernel (C D : Ideal O) (A : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (n : Fin 4→ℤ) (h : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
    (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
    (retainedWeight R (normValue (A*h)):ℂ)*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue h/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))

theorem active_sector_norm (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (H : ℝ) (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C : Ideal O) (hC : C≠0) (I : sectorPool C hC (activeSource S β)) :
    (Ideal.absNorm (I:Ideal O):ℝ)∈Set.Icc 1 (max 1 (H/(Ideal.absNorm C:ℝ))) := by
  have hh := residualPool_data S β H hH C hC I (Finset.mem_filter.mp I.property).1
  exact ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.trans (le_max_right _ _)⟩

theorem sourceLower_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : ∀i,0<sourceLower C D A K i := by
  intro i
  fin_cases i
  · exact secondEffectiveScale_pos C D hC hD A hA K hK
  all_goals norm_num [sourceLower]

theorem active_physical_kernel_partition (_η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        dyadicKernel C D A W K R (fun i=>n i) h I J := by
  by_cases hw : retainedWeight R (normValue (A*h))=0
  · simp only [physicalKernel,dyadicKernel,hw,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  have he := retainedWeight_enclosure R _ hw
  have hh : h≠0 := by
    intro hz
    subst h
    simp [normValue] at he
  have hrow : normValue h≤4*R/normValue A := by
    apply (le_div_iff₀ (normValue_pos A hA)).mpr
    simpa only [normValue_mul,mul_comm] using he.2
  have hb : ∀i, (![secondEffectiveScale C D A K,normValue h,
      (Ideal.absNorm (I:Ideal O):ℝ),(Ideal.absNorm (J:Ideal O):ℝ)] : Fin 4→ℝ) i∈
        Set.Icc (sourceLower C D A K i) (sourceUpper C D A K R H i) := by
    intro i
    fin_cases i
    · exact ⟨le_rfl,le_rfl⟩
    · exact ⟨normValue_ge_one h hh,hrow.trans (le_max_right _ _)⟩
    · exact active_sector_norm S β H hH C hC.1 I
    · exact active_sector_norm S β H hH D hD.1 J
  exact physical_kernel_dyadic_partition C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK _ _ (sourceLower_pos C D hC.1 hD.1 A hA K hK) hb

end SevenEighths.CenteredMomentSecondActiveDyadic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondBlockAggregate -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondBlockAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentCanonicalFirst
open CenteredMomentSecondLocalization CenteredMomentSecondSectorFrequency
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentHeckeColumnWindow
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondPhysicalBlock CenteredMomentSecondWholeKernel
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  ↥(commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)))

abbrev SourceBlocks (C D : Ideal O) (U : Finset (CommonIndex C D)) (K R H : ℝ) :=
  Blocks (sourceLower C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)
    (sourceUpper C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K R H)

lemma retainedRows_ne_zero (R : ℝ) (A z : O) (hz : z∈retainedRows R A) : z≠0 := by
  have hp := (mem_rowNormDisk.mp hz).1
  intro h
  simp [h] at hp

theorem active_kernel_windows (η : Character)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (I : sectorPool C hC.1 (activeSource S β)) (J : sectorPool D hD.1 (activeSource S β))
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    physicalKernel C D W K R (A*h) I J=
      ∑ n : Blocks (sourceLower C D A K) (sourceUpper C D A K R H),
        physicalKernel C D W K R (A*h) I J*
          ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
            dyadicWeight (n 2) (Ideal.absNorm (I:Ideal O):ℝ)*
            dyadicWeight (n 3) (Ideal.absNorm (J:Ideal O):ℝ):ℝ):ℂ) := by
  refine (active_physical_kernel_partition η S β H hH C D hC hD I J A h hA W K R hK).trans ?_
  apply Finset.sum_congr rfl
  intro n hn
  exact (physical_kernel_dyadic C D I J hC hD
    (sectorPool_supported C hC.1 _ I) (sectorPool_supported D hD.1 _ J)
    A h hA hh W K R hK (fun i=>n i)).symm

theorem sector_finite_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (H : ℝ)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (U : Finset (CommonIndex C D)) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
    (∑h∈retainedRows R A,if canonicalPartition C D U (nonunitFrequencyGenerator C D U*h) then
      sectorFrequency η t (activeSource S β) β C D hC hD (physicalKernel C D W K R) (A*h) else 0)=
      ∑n : SourceBlocks C D U K R H,
        physicalBlock η t (activeSource S β) β C D hC hD U R (retainedRows R A) W K
          (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*h)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [active_kernel_windows η S β H hH C D hC hD I J _ h hA
      (retainedRows_ne_zero R _ h hh) W K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

theorem original_secondRetainedEnergy_blocks (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p : ActiveLabel S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (retainedRows (frequencyRadius Tsec Z ξ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              W K (fun i=>(n i:ℤ)) := by
  rw [←secondRetainedEnergy_active η t S β W K Tsec Z ξ,
    original_retained_energy_GV η t (activeSource S β) β W K Tsec Z ξ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact sector_finite_blocks η t S β H hH _ _ _ _ U W K _ hK

lemma common_height_norm_le_one (η : Character) (t : ℝ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) :
    ‖heightCoeff η t C*star (heightCoeff η t D)‖≤1 := by
  rw [norm_mul,norm_star]
  have hc := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t C hC
  have hd := CenteredMomentSourceSecondZeroEnergy.heightCoeff_norm_le_one η t D hD
  nlinarith [norm_nonneg (heightCoeff η t C),norm_nonneg (heightCoeff η t D)]

theorem original_secondRetainedEnergy_norm_le (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ H : ℝ) (hK : 0<K)
    (hH : ∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H) :
    ‖secondRetainedEnergy η t S β W K Tsec Z ξ‖≤
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
            (commonLabels_supported (activeSource S β) _ _ p.property).1
            (commonLabels_supported (activeSource S β) _ _ p.property).2 U
            (frequencyRadius Tsec Z ξ)
            (retainedRows (frequencyRadius Tsec Z ξ)
              (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
            W K (fun i=>(n i:ℤ))‖ := by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end SevenEighths.CenteredMomentSecondBlockAggregate

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondBlockCount -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondBlockCount
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondWholeKernel
open CenteredMomentSecondActiveDyadic CenteredMomentSecondDyadicPartition
open CenteredMomentSecondBlockAggregate CenteredMomentSecondActiveCount
open CenteredMomentSecondSectorFrequency CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondSectorColumns CenteredMomentSecondRetainedAggregate
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentDyadicCount
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentActiveSource
local notation "O" => ActualEisensteinCubic.O

lemma ideal_norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma sourceLower_le_upper (C D : Ideal O) (A : O) (K R H : ℝ) :
    ∀i,sourceLower C D A K i≤ sourceUpper C D A K R H i := by
  intro i
  fin_cases i
  · exact le_rfl
  all_goals exact le_max_left _ _

lemma source_ratio_bound (B L Cr Z : ℝ) (hB : 0≤B) (hL : 0≤L)
    (_hCr : 0<Cr) (hZ : 1≤Z)
    (C D : Ideal O) (hC : C≠0) (hD : D≠0) (A : O) (hA : A≠0)
    (K R H : ℝ) (hK : 0<K) (hR : R≤Cr*Z^L) (hH : H≤Z^B) :
    ∀i,sourceUpper C D A K R H i/sourceLower C D A K i≤
      max 1 (4*Cr)*Z^(B+L) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^(B+L) := Real.one_le_rpow hZ (add_nonneg hB hL)
  have hc : 1≤ max 1 (4*Cr) := le_max_left _ _
  have hq : 1≤ max 1 (4*Cr)*Z^(B+L) := one_le_mul_of_one_le_of_one_le hc hp
  have hN := normValue_ge_one A hA
  have hNC := ideal_norm_ge_one C hC
  have hND := ideal_norm_ge_one D hD
  have hBpow : Z^B≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hLpow : Z^L≤Z^(B+L) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hH' : H≤ max 1 (4*Cr)*Z^(B+L) :=
    hH.trans (hBpow.trans (le_mul_of_one_le_left (zero_le_one.trans hp) hc))
  have hR' : 4*R≤ max 1 (4*Cr)*Z^(B+L) := by
    calc
      _≤4*Cr*Z^L := by linarith
      _≤ max 1 (4*Cr)*Z^(B+L) :=
        mul_le_mul (le_max_right _ _) hLpow (Real.rpow_nonneg hz.le _) (by positivity)
  have hn (x d : ℝ) (hd : 1≤d) (hx : x≤ max 1 (4*Cr)*Z^(B+L)) :
      max 1 (x/d)≤ max 1 (4*Cr)*Z^(B+L) := by
    apply max_le hq
    apply (div_le_iff₀ (zero_lt_one.trans_le hd)).mpr
    exact hx.trans (le_mul_of_one_le_right (by positivity) hd)
  intro i
  fin_cases i
  · simpa [sourceUpper,sourceLower,
      div_self (secondEffectiveScale_pos C D hC hD A hA K hK).ne'] using hq
  · simpa [sourceUpper,sourceLower] using hn (4*R) (normValue A) hN hR'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm C) hNC hH'
  · simpa [sourceUpper,sourceLower] using hn H (Ideal.absNorm D) hND hH'

theorem sourceBlocks_subpower (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃D₀:ℝ,0<D₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(C D:Ideal O),Supported C → Supported D →
      ∀(U:Finset (CommonIndex C D))(K R H:ℝ),0<K →
      R≤Cr*Z^L → H≤Z^B →
      (Fintype.card (SourceBlocks C D U K R H):ℝ)≤D₀*Z^ε := by
  obtain ⟨D₀,hD₀,hcount⟩ := four_indices_subpower (max 1 (4*Cr)) (B+L) ε
    (le_max_left _ _) (add_nonneg hB hL) hε
  refine ⟨D₀,hD₀,?_⟩
  filter_upwards [hcount,Filter.eventually_ge_atTop (1:ℝ)] with Z hc hZ
  intro C D hC hD U K R H hK hR hH
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
      (nonunitFrequencyGenerator_ne_zero C D hC U)
  exact hc _ _ (sourceLower_pos C D hC.1 hD.1 _ hA K hK)
    (sourceLower_le_upper C D _ K R H)
    (source_ratio_bound B L Cr Z hB hL hCr hZ C D hC.1 hD.1 _ hA K R H hK hR hH)

abbrev CommonSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :=
  (p : commonShell S β Y) × Finset (CommonIndex p.val.1 p.val.2)

lemma commonSubset_support (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    U.image Subtype.val⊆IdealMobiusDivisorSum.primeSupport (commonRadical C D) := by
  intro P hP
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
  rw [commonRadical_support]
  exact Q.property

def commonSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (q : CommonSubsets S β Y) : partitionLabels S β Y :=
  ⟨(q.1.val,q.2.image Subtype.val),
    (mem_partitionLabels S β Y _).mpr ⟨q.1.property,commonSubset_support _ _ q.2⟩⟩

lemma commonSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Function.Injective (commonSubsetLabel S β Y) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=>x.val.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective (congrArg (fun x=>x.val.2) he)
  cases hU
  rfl

lemma commonSubsets_card_le (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ) :
    Fintype.card (CommonSubsets S β Y)≤(partitionLabels S β Y).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (commonSubsetLabel S β Y) (commonSubsetLabel_injective S β Y)

abbrev BlockLabels (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y K R H : ℝ) :=
  (q : CommonSubsets S β Y) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

lemma blockLabels_card_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y K R H : ℝ) :
    (Fintype.card (BlockLabels S β Y K R H):ℝ)=
      ∑p : commonShell S β Y,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ) := by
  calc
    _ = ∑q : CommonSubsets S β Y,
        (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ) := by
      exact_mod_cast Fintype.card_sigma (ι:=CommonSubsets S β Y)
        (α:=fun q=>SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H)
    _ = _ := Fintype.sum_sigma _

theorem actual_block_count (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀p s₀:ℝ,0≤p → p≤B →
      ∀s:Ideal O,Squarefree s → s≠0 → Z^s₀≤(Ideal.absNorm s:ℝ) →
      ∀(S:Finset (Ideal O)) (β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → s∣I) →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤Z^B) →
      (Fintype.card (BlockLabels S β (Z^p) K R H):ℝ)≤C₀*Z^(p-s₀+ε) := by
  obtain ⟨C₁,hC₁,hpart⟩ := actual_partition_count B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩ := sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₁*C₂,by positivity,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro p s₀ hp hpB s hs hs0 hNs S β hmask K R H hK hR hH hsource
  have hcount : (Fintype.card (CommonSubsets S β (Z^p)):ℝ)≤C₁*Z^(p-s₀+ε/2) := by
    apply (Nat.cast_le.mpr (commonSubsets_card_le S β (Z^p))).trans
    exact hpart Z p s₀ hZ hp hpB s hs hs0 hNs S β hmask hsource
  have hbc (q : CommonSubsets S β (Z^p)) :
      (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ)≤C₂*Z^(ε/2) := by
    have hd := commonLabels_supported (activeSource S β) q.1.val.1 q.1.val.2
      (Finset.mem_filter.mp q.1.property).1
    exact hb _ _ hd.1 hd.2 q.2 K R H hK hR hH
  calc
    _ = ∑q : CommonSubsets S β (Z^p),
        (Fintype.card (SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H):ℝ) := by
      exact_mod_cast Fintype.card_sigma (ι:=CommonSubsets S β (Z^p))
        (α:=fun q=>SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H)
    _ ≤ ∑q : CommonSubsets S β (Z^p),C₂*Z^(ε/2) := Finset.sum_le_sum (fun q _=>hbc q)
    _ = (Fintype.card (CommonSubsets S β (Z^p)):ℝ)*(C₂*Z^(ε/2)) := by simp
    _ ≤ (C₁*Z^(p-s₀+ε/2))*(C₂*Z^(ε/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C₁*C₂)*Z^(p-s₀+ε) := by
      rw [mul_mul_mul_comm,←Real.rpow_add (zero_lt_one.trans_le hZ)]
      congr 2
      ring

end SevenEighths.CenteredMomentSecondBlockCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondBlockHarmonicMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondBlockHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
local notation "O" => ActualEisensteinCubic.O

abbrev ActiveSubsets (S : Finset (Ideal O)) (β : Ideal O→ℂ) :=
  (p : ActiveLabel S β) × Finset (CommonIndex p.val.1 p.val.2)

abbrev ActiveBlocks (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :=
  (q : ActiveSubsets S β) × SourceBlocks q.1.val.1 q.1.val.2 q.2 K R H

def pairWeight (C D : Ideal O) : ℝ := 1/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)

lemma pairWeight_nonneg (C D : Ideal O) : 0≤pairWeight C D := by
  unfold pairWeight
  positivity

def activeSubsetLabel (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (q : ActiveSubsets S β) : Label := (q.1.val,q.2.image Subtype.val)

lemma activeSubsetLabel_injective (S : Finset (Ideal O)) (β : Ideal O→ℂ) :
    Function.Injective (activeSubsetLabel S β) := by
  rintro ⟨p,U⟩ ⟨q,V⟩ he
  have hp : p=q := Subtype.ext (congrArg (fun x=>x.1) he)
  cases hp
  have hU : U=V := Finset.image_injective Subtype.val_injective
    (congrArg (fun x=>x.2) he)
  cases hU
  rfl

lemma active_common_shell (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (p : ActiveLabel S β) :
    p.val∈commonShell S β Y := by
  have hs := commonLabels_supported (activeSource S β) _ _ p.property
  have hn := commonLabel_norm_bounds S β Y hN _ _ p.property
  exact Finset.mem_filter.mpr ⟨p.property,
    (commonRadical_norm_le _ _ hs.1.1 hs.2.1).trans ((min_le_left _ _).trans hn.1)⟩

lemma activeSubsetLabel_mem (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) (q : ActiveSubsets S β) :
    activeSubsetLabel S β q∈partitionLabels S β Y := by
  exact (mem_partitionLabels S β Y _).mpr
    ⟨active_common_shell S β Y hN q.1,commonSubset_support _ _ q.2⟩

lemma active_mass_le_partition (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      pairWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,pairWeight v.1.1 v.1.2 := by
  have he : (∑q : ActiveSubsets S β,pairWeight q.1.val.1 q.1.val.2)=
      ∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2 := Fintype.sum_sigma _
  rw [←he]
  let f := activeSubsetLabel S β
  calc
    _ = ∑v∈Finset.univ.image f,pairWeight v.1.1 v.1.2 := by
      rw [Finset.sum_image]
      · rfl
      · exact (activeSubsetLabel_injective S β).injOn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv;obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hv
          exact activeSubsetLabel_mem S β Y hN q)
      (fun v _ _=>pairWeight_nonneg _ _)

lemma active_blocks_sum_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*pairWeight p.val.1 p.val.2 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Fintype.sum_sigma _

theorem actual_active_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        pairWeight p.val.1 p.val.2)≤C*Z^δ/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=common_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn
  apply (active_mass_le_partition S β (Z^B) hn).trans
  apply hb Z hZ seed hs hs0 (partitionLabels S β (Z^B))
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β (Z^B) v).mp hv
    have hh:=active_common_data S β seed hs hm (Z^B) v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hn _ _
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^B) v).mp hv).1).1

theorem actual_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks S β K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₁,hC₁,hmass⟩:=actual_active_harmonic_mass B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩:=sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (2:ℝ)] with Z hb hZ
  intro seed hs hs0 S β hm hn K R H hK hR hH
  have hsum:=hmass Z hZ seed hs hs0 S β hm hn
  rw [active_blocks_sum_eq]
  calc
    _ ≤ ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (C₂*Z^(ε/2))*pairWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
      exact mul_le_mul_of_nonneg_right
        (hb _ _ hsupp.1 hsupp.2 U K R H hK hR hH) (pairWeight_nonneg _ _)
    _ = (C₂*Z^(ε/2))*(∑p : ActiveLabel S β,
        ∑U : Finset (CommonIndex p.val.1 p.val.2),pairWeight p.val.1 p.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (C₂*Z^(ε/2))*(C₁*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (C₂*C₁)*Z^ε/(seed.absNorm:ℝ) := by
      calc
        _ = (C₂*C₁)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z),add_halves]

theorem actual_original_block_harmonic_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι] (s:CenteredMomentCommonRadialData.Input ι),
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀puncture seed:Ideal O,Squarefree seed → seed≠0 →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s puncture seed) K R H,pairWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=actual_block_harmonic_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  intro ι inst inst' s hz₁ hz₂ hcap puncture seed hs hs0 K R H hK hR hH
  exact hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap)
    K R H hK hR hH

end SevenEighths.CenteredMomentSecondBlockHarmonicMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondBlockRadicalHarmonicMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondBlockRadicalHarmonicMass
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedAggregate CenteredMomentSourceMass
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockCount
open CenteredMomentSecondActiveCount CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSecondCanonicalNonunit CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondBlockHarmonicMass (ActiveSubsets ActiveBlocks activeSubsetLabel activeSubsetLabel_injective activeSubsetLabel_mem)
local notation "O" => ActualEisensteinCubic.O

def radicalWeight (C D:Ideal O):ℝ:=1/(Ideal.absNorm (commonRadical C D):ℝ)

lemma radicalWeight_nonneg (C D:Ideal O):0≤ radicalWeight C D:=by
  unfold radicalWeight
  positivity

lemma active_mass_le_partition (S : Finset (Ideal O)) (β : Ideal O→ℂ) (Y : ℝ)
    (hN : ∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Y) :
    (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
      radicalWeight p.val.1 p.val.2)≤
    ∑v∈partitionLabels S β Y,radicalWeight v.1.1 v.1.2 := by
  have he : (∑q : ActiveSubsets S β,radicalWeight q.1.val.1 q.1.val.2)=
      ∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        radicalWeight p.val.1 p.val.2 := Fintype.sum_sigma _
  rw [←he]
  let f := activeSubsetLabel S β
  calc
    _ = ∑v∈Finset.univ.image f,radicalWeight v.1.1 v.1.2 := by
      rw [Finset.sum_image]
      · rfl
      · exact (activeSubsetLabel_injective S β).injOn
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro v hv;obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hv
          exact activeSubsetLabel_mem S β Y hN q)
      (fun v _ _=>radicalWeight_nonneg _ _)

lemma active_blocks_sum_eq (S : Finset (Ideal O)) (β : Ideal O→ℂ) (K R H : ℝ) :
    (∑q : ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2)=
      ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (Fintype.card (SourceBlocks p.val.1 p.val.2 U K R H):ℝ)*radicalWeight p.val.1 p.val.2 := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Fintype.sum_sigma _

theorem actual_active_radical_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z → ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      (∑p : ActiveLabel S β,∑_U : Finset (CommonIndex p.val.1 p.val.2),
        radicalWeight p.val.1 p.val.2)≤C*Z^δ/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=CenteredMomentCommonRadicalHarmonicMass.common_radical_harmonic_mass B δ hB hδ
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn
  apply (active_mass_le_partition S β (Z^B) hn).trans
  apply hb Z hZ seed hs hs0 (partitionLabels S β (Z^B))
  · intro v hv
    obtain ⟨hp,hU⟩:=(mem_partitionLabels S β (Z^B) v).mp hv
    have hh:=active_common_data S β seed hs hm (Z^B) v.1 hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hU⟩
  · intro v hv
    exact commonLabel_norm_bounds S β (Z^B) hn _ _
      (Finset.mem_filter.mp ((mem_partitionLabels S β (Z^B) v).mp hv).1).1

theorem actual_block_radical_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀seed:Ideal O,Squarefree seed → seed≠0 →
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0 → seed∣I) →
      (∀I∈S,β I≠0 → (I.absNorm:ℝ)≤Z^B) →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₁,hC₁,hmass⟩:=actual_active_radical_mass B (ε/2) hB (by positivity)
  obtain ⟨C₂,hC₂,hblocks⟩:=sourceBlocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨C₂*C₁,mul_pos hC₂ hC₁,?_⟩
  filter_upwards [hblocks,Filter.eventually_ge_atTop (2:ℝ)] with Z hb hZ
  intro seed hs hs0 S β hm hn K R H hK hR hH
  have hsum:=hmass Z hZ seed hs hs0 S β hm hn
  rw [active_blocks_sum_eq]
  calc
    _ ≤ ∑p : ActiveLabel S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
        (C₂*Z^(ε/2))*radicalWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
      exact mul_le_mul_of_nonneg_right
        (hb _ _ hsupp.1 hsupp.2 U K R H hK hR hH) (radicalWeight_nonneg _ _)
    _ = (C₂*Z^(ε/2))*(∑p : ActiveLabel S β,
        ∑U : Finset (CommonIndex p.val.1 p.val.2),radicalWeight p.val.1 p.val.2) := by
      simp only [Finset.mul_sum]
    _ ≤ (C₂*Z^(ε/2))*(C₁*Z^(ε/2)/(seed.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (C₂*C₁)*Z^ε/(seed.absNorm:ℝ) := by
      calc
        _ = (C₂*C₁)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm:ℝ) := by ring
        _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z),add_halves]

theorem actual_original_block_radical_mass (B L Cr ε : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hCr : 0<Cr) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀(ι:Type*) [Fintype ι] [DecidableEq ι] (s:CenteredMomentCommonRadialData.Input ι),
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀puncture seed:Ideal O,Squarefree seed → seed≠0 →
      ∀K R H:ℝ,0<K → R≤Cr*Z^L → H≤Z^B →
      (∑q : ActiveBlocks (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s puncture seed) K R H,radicalWeight q.1.1.val.1 q.1.1.val.2)≤
        C*Z^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hb⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with Z hZ
  intro ι inst inst' s hz₁ hz₂ hcap puncture seed hs hs0 K R H hK hR hH
  exact hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap)
    K R H hK hR hH

end SevenEighths.CenteredMomentSecondBlockRadicalHarmonicMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstInactiveRadicalMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstInactiveRadicalMass
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonRadialData CenteredMomentRankinRadical
open CenteredMomentSecondBlockAggregate CenteredMomentSupportedCorrelation
open ConcretePrimeRowBridge
local notation "O"=>ActualEisensteinCubic.O

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):ℝ:=
  ‖(UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)‖/
    ((Ideal.absNorm (∏P∈E,P.val):ℝ)^a)

lemma inactiveWeight_nonneg (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ):
    0 ≤ inactiveWeight C D E a:=by
  unfold inactiveWeight
  exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma inactiveWeight_le_one (C D:Ideal O)(E:Finset (CommonIndex C D))(a:ℝ)(ha:0≤a):
    inactiveWeight C D E a≤1:=by
  have hE:(∏P∈E,P.val)≠(0:Ideal O):=by
    have he:=primeSubsetGenerator_ne_zero (fun P:CommonIndex C D=>P.val) E
    have hh:=Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,
      Ideal.zero_eq_bot] using hh
  have hn:1≤(Ideal.absNorm (∏P∈E,P.val):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hp:1≤(Ideal.absNorm (∏P∈E,P.val):ℝ)^a:=Real.one_le_rpow hn ha
  unfold inactiveWeight
  exact (div_le_self (norm_nonneg _) hp).trans (QuadraticInitialBound.norm_ideal_moebius_le_one _)

theorem actual_inactive_radical_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀seed:Ideal O,Squarefree seed→seed≠0→
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→(∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B)→
      ∀a:ℝ,0≤a→
      (∑p:ActiveLabel S β,∑E∈inactiveSubsets p.val.1 p.val.2,
        inactiveWeight p.val.1 p.val.2 E a/
          (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_active_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn a ha
  apply le_trans _ (hb Z hZ seed hs hs0 S β hm hn)
  apply Finset.sum_le_sum
  intro p hp
  calc
    _≤∑_E∈inactiveSubsets p.val.1 p.val.2,radicalWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro E hE
      exact div_le_div_of_nonneg_right (inactiveWeight_le_one _ _ E a ha) (Nat.cast_nonneg _)
    _≤∑_E:Finset (CommonIndex p.val.1 p.val.2),radicalWeight p.val.1 p.val.2:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _=>radicalWeight_nonneg _ _)

theorem original_input_inactive_radical_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι),
      s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      ∀puncture seed:Ideal O,Squarefree seed→seed≠0→∀a:ℝ,0≤a→
      (∑p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools)) (coefficient s puncture seed),
        ∑E∈inactiveSubsets p.val.1 p.val.2,
          inactiveWeight p.val.1 p.val.2 E a/
            (Ideal.absNorm (commonRadical p.val.1 p.val.2):ℝ))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_inactive_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ ι _ _ s hz₁ hz₂ hcap puncture seed hs hs0 a ha
  exact hb Z hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap) a ha

end SevenEighths.CenteredMomentFirstInactiveRadicalMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstActiveRadicalBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstActiveRadicalBudget
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentRankinRadical CenteredMomentFirstInactiveRadicalMass
open CenteredMomentSupportedCorrelation
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
local notation "O"=>ActualEisensteinCubic.O

lemma active_exponent_budget (i j:ℕ)(hi:0 < i)(hj:0 < j):
    2+(if netExponent i j≠0 then 1 else 0) ≤ i+j:=by
  unfold netExponent
  split_ifs <;> omega

theorem radical_squared_active_dvd (I J:Ideal O):
    commonRadical I J^2*Ideal.span {activeConductor I J}∣commonPart I J*commonPart J I:=by
  have hr:commonRadical I J=∏P:CommonIndex I J,P.val:=by
    exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P=>P)).symm
  have ha:Ideal.span {activeConductor I J}=
      ∏P:CommonIndex I J,if netExponent (leftExponent I J P) (rightExponent I J P)≠0 then P.val else 1:=by
    rw [activeConductor,span_finitePrimeModulus]
    change (∏P:ActiveIndex I J,P.val.val)=_
    rw [Finset.prod_coe_sort]
    simp only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.prod_filter]
  rw [hr,ha,←Finset.prod_pow,←Finset.prod_mul_distrib,
    commonPart_left_product,commonPart_right_product,←Finset.prod_mul_distrib]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  have hh:=active_exponent_budget (leftExponent I J P) (rightExponent I J P)
    (leftExponent_pos I J P) (rightExponent_pos I J P)
  rw [←pow_add]
  convert pow_dvd_pow P.val hh using 1
  split_ifs <;> simp [pow_succ]

theorem radical_active_norm (I J:Ideal O)(hI:I≠0)(hJ:J≠0):
    (Ideal.absNorm (commonRadical I J):ℝ)^2*
      (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(I.absNorm:ℝ)*J.absNorm:=by
  have hd:commonRadical I J^2*Ideal.span {activeConductor I J}∣I*J:=
    (radical_squared_active_dvd I J).trans (mul_dvd_mul (commonPart_dvd I J hI) (commonPart_dvd J I hJ))
  have hn:=Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hI hJ)))
    (map_dvd Ideal.absNorm hd)
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using (show
    (Ideal.absNorm (commonRadical I J^2*Ideal.span {activeConductor I J}):ℝ)≤
      (Ideal.absNorm (I*J):ℝ) by exact_mod_cast hn)

theorem active_root_le_radical (I J:Ideal O)(hI:I≠0)(hJ:J≠0):
    Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)/
      Real.sqrt ((I.absNorm:ℝ)*J.absNorm)≤1/(Ideal.absNorm (commonRadical I J):ℝ):=by
  have hR:0<(Ideal.absNorm (commonRadical I J):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonRadical_ne_zero I J))
  have hN:0<(I.absNorm:ℝ)*J.absNorm:=mul_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
  have hh:=Real.sqrt_le_sqrt (radical_active_norm I J hI hJ)
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hR.le] at hh
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hN) hR).mpr (by simpa [mul_comm] using hh)

theorem actual_first_weighted_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀seed:Ideal O,Squarefree seed→seed≠0→
      ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
      (∀I∈S,β I≠0→seed∣I)→(∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B)→
      ∀a:ℝ,0≤a→
      (∑p:ActiveLabel S β,∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        inactiveWeight p.val.1 p.val.2 E a*
          (Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor p.val.1 p.val.2}):ℝ)/
            Real.sqrt ((p.val.1.absNorm:ℝ)*p.val.2.absNorm)))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_inactive_radical_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ seed hs hs0 S β hm hn a ha
  apply le_trans _ (hb Z hZ seed hs hs0 S β hm hn a ha)
  apply Finset.sum_le_sum
  intro p hp
  have hsupp:=commonLabels_supported (activeSource S β) _ _ p.property
  apply Finset.sum_le_sum
  intro E hE
  exact (mul_le_mul_of_nonneg_left (active_root_le_radical _ _ hsupp.1.1 hsupp.2.1)
    (inactiveWeight_nonneg _ _ E a)).trans_eq (by ring)

theorem original_first_weighted_mass (B ε:ℝ)(hB:0≤B)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,2≤Z→∀(ι:Type*)[Fintype ι][DecidableEq ι](s:Input ι),
      s.W₁ 0=0→s.W₂ 0=0→sourceRadius s≤Z^B→
      ∀puncture seed:Ideal O,Squarefree seed→seed≠0→∀a:ℝ,0≤a→
      (∑p:ActiveLabel (finiteColumns (Fintype.piFinset s.pools)) (coefficient s puncture seed),
        ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
          inactiveWeight p.val.1 p.val.2 E a*
            (Real.sqrt (Ideal.absNorm (Ideal.span {activeConductor p.val.1 p.val.2}):ℝ)/
              Real.sqrt ((p.val.1.absNorm:ℝ)*p.val.2.absNorm)))≤C*Z^ε/(seed.absNorm:ℝ):=by
  obtain ⟨C,hC,hb⟩:=actual_first_weighted_mass B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Z hZ ι _ _ s hz₁ hz₂ hcap puncture seed hs hs0 a ha
  exact hb Z hZ seed hs hs0 _ _
    (fun I _ hI=>original_column_mask s puncture seed I hI)
    (fun I _ hI=>(original_column_norm s puncture seed I hz₁ hz₂ hI).2.trans hcap) a ha

end SevenEighths.CenteredMomentFirstActiveRadicalBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

def liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ):Finset (ActiveLabel S β):=
  Finset.univ.filter (fun p=>idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0)

lemma mem_liveLabels (η:Character) (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β):
    p∈liveLabels η S β ↔ idealCoeff η p.val.1≠0 ∧ idealCoeff η p.val.2≠0:=by
  simp only [liveLabels,Finset.mem_filter,Finset.mem_univ,true_and]

lemma common_height_zero_of_not_live (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:idealCoeff η p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

def liveRows (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O):Finset O:=
  rows.filter (fun z=>retainedWeight R
    (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0)

lemma liveRows_weight (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0:=
  (Finset.mem_filter.mp hz).2

lemma liveRows_geometry (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    0<R ∧ z≠0 ∧ 1≤normValue z ∧ normValue z≤
      4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)):=by
  obtain ⟨hr,hg,hv,hz0,h1,hbound,hmax⟩:=CenteredMomentSecondRetainedWidth.retained_geometry R
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U R rows z hz)
  exact ⟨hr,hz0,h1,hbound⟩

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

lemma physicalBlock_row_split (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ) (p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter p) W K n+
      physicalBlock η t S β C D hC hD U R ((liveRows C D U R rows).filter (fun z=>¬p z)) W K n:=by
  rw [physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not _ p _).symm

theorem original_live_blocks (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H:ℝ) (hK:0<K)
    (hH:∀I∈S,β I≠0 → (Ideal.absNorm I:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
        ∑U:Finset (CommonIndex p.val.1 p.val.2),
          ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
            physicalBlock η t (activeSource S β) β p.val.1 p.val.2
              (commonLabels_supported (activeSource S β) _ _ p.property).1
              (commonLabels_supported (activeSource S β) _ _ p.property).2 U
              (frequencyRadius Tsec Z ξ)
              (liveRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)
                (retainedRows (frequencyRadius Tsec Z ξ)
                  (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)))
              W K (fun i=>(n i:ℤ)):=by
  rw [original_secondRetainedEnergy_blocks η t S β W K Tsec Z ξ H hK hH]
  trans ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (retainedRows (frequencyRadius Tsec Z ξ)
            (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
          W K (fun i=>(n i:ℤ))
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p hp hn
    rw [common_height_zero_of_not_live η t S β p hn,zero_mul]
  · apply Finset.sum_congr rfl
    intro p hp
    apply congrArg (fun x : ℂ => heightCoeff η t p.val.1 * star (heightCoeff η t p.val.2) * x)
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_live_rows _ _ _ _ _ _ _ _ _ _ _ _ _ _

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondDyadicRowSupport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicRowSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst
local notation "O"=>HeckeFamily.O

 def dyadicRows (rows:Finset O) (n:Fin 4→ℤ):Finset O:=
  rows.filter (fun z=>dyadicWeight (n 1) (normValue z)≠0)

 theorem mem_dyadicRows (rows:Finset O)(n:Fin 4→ℤ)(z:O):
    z∈dyadicRows rows n ↔ z∈rows ∧ dyadicWeight (n 1) (normValue z)≠0:=
  Finset.mem_filter

 theorem dyadicRows_subset (rows:Finset O)(n:Fin 4→ℤ):dyadicRows rows n⊆rows:=
  Finset.filter_subset _ _

 theorem dyadicRows_norm (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):
    dyadicScale (n 1)/4<normValue z ∧ normValue z<dyadicScale (n 1):=
  dyadicWeight_support (n 1) ((mem_dyadicRows rows n z).mp hz).2

 theorem dyadicRows_nonzero (rows:Finset O)(n:Fin 4→ℤ)(z:O)(hz:z∈dyadicRows rows n):z≠0:=by
  have hn:0<normValue z:=(div_pos (dyadicScale_pos (n 1)) (by norm_num)).trans
    (dyadicRows_norm rows n z hz).1
  intro he
  simp only [he,normValue_eq_embedding,map_zero,norm_zero,zero_pow (by decide : 2≠0)] at hn
  exact (lt_irrefl 0) hn

 theorem dyadicRows_power_cap (rows:Finset O)(n:Fin 4→ℤ)(Z:ℝ)(hZ:1<Z)
    (z:O)(hz:z∈dyadicRows rows n):
    (Ideal.absNorm (Ideal.span {z}):ℝ)≤Z^(Real.logb Z (dyadicScale (n 1))):=by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos (n 1))]
  exact (dyadicRows_norm rows n z hz).2.le

 theorem physicalBlock_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows rows n) W K n:=by
  unfold physicalBlock dyadicRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hd:dyadicWeight (n 1) (normValue z)=0
  · simp only [hd,ne_eq,not_true_eq_false,mul_zero,zero_mul,
      Complex.ofReal_zero,Finset.sum_const_zero,ite_self]
  · simp only [hd,ne_eq,not_false_eq_true,ite_true]

 theorem dyadicRows_liveRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (rows:Finset O)(n:Fin 4→ℤ):
    dyadicRows (liveRows C D U R rows) n=liveRows C D U R (dyadicRows rows n):=by
  ext z
  simp only [dyadicRows,liveRows,Finset.mem_filter]
  tauto

 theorem physicalBlock_live_dyadic_rows (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (dyadicRows (liveRows C D U R rows) n) W K n:=
  (physicalBlock_live_rows η t S β C D hC hD U R rows W K n).trans
    (physicalBlock_dyadic_rows η t S β C D hC hD U R _ W K n)

end SevenEighths.CenteredMomentSecondDyadicRowSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=>HeckeFamily.O

lemma physicalBlock_filter_split (η:Character)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)(p:O→Prop):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (rows.filter p) W K n+
      physicalBlock η t S β C D hC hD U R (rows.filter (fun z=>¬p z)) W K n:=by
  unfold physicalBlock
  exact (Finset.sum_filter_add_sum_filter_not rows p _).symm

def sourceRows (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  liveRows C D U R (retainedRows R (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U))

lemma sourceRows_nonzero (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ)
    (z:O)(hz:z∈sourceRows C D U R):z≠0:=
  (liveRows_geometry C D U R _ z hz).2.1

def partRows (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):Finset O:=
  (sourceRows C D U R).filter (fun z=>if exceptional then
    CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z
    else nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)

lemma partRows_false (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)
    (C D:Ideal O)(U:Finset (CommonIndex C D))(R:ℝ):
    partRows false η χ Q m C D U R=(sourceRows C D U R).filter (fun z=>
      ¬CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z):=by
  ext z
  simp only [partRows,Bool.false_eq_true,ite_false,Finset.mem_filter,nonexceptional]
  exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,sourceRows_nonzero C D U R z h.1,h.2⟩⟩

def partEnergy (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):ℂ:=
  ∑p∈liveLabels η S β,heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)*
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))

theorem original_energy_split (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ)(hK:0<K)
    (hH:∀I∈S,β I≠0→(I.absNorm:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      partEnergy true η χ Q m t S β W K Tsec Z ξ H+
      partEnergy false η χ Q m t S β W K Tsec Z ξ H:=by
  rw [original_live_blocks η t S β W K Tsec Z ξ H hK hH]
  unfold partEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [partRows_false]
  exact physicalBlock_filter_split η t (activeSource S β) β p.val.1 p.val.2 _ _ U
    (frequencyRadius Tsec Z ξ) (sourceRows p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ)) W K _ _

theorem partEnergy_norm_le (exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖≤
  ∑p∈liveLabels η S β,
    ∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
          (commonLabels_supported (activeSource S β) _ _ p.property).1
          (commonLabels_supported (activeSource S β) _ _ p.property).2 U
          (frequencyRadius Tsec Z ξ)
          (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          W K (fun i=>(n i:ℤ))‖
 :=by
  unfold partEnergy
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _)
    (common_height_norm_le_one η t _ _
      (commonLabels_supported (activeSource S β) _ _ p.property).1.1
      (commonLabels_supported (activeSource S β) _ _ p.property).2.1)).trans
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro U hU
  exact norm_sum_le _ _

end SevenEighths.CenteredMomentSecondEnergySplit

end

end OAI

end

