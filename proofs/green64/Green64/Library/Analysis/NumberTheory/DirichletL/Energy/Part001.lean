module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part028
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part034
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part030
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part027
public import Green64.Library.OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part022
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part020
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part021
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part019

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Energy / Part001

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstHighFourCoefficients -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstHighFourCoefficients
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

open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentEnergyFirstHighExceptionalPowers

theorem actual_main_high_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤ sigma)(heps:0≤eps)(_hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    ∀j:Fin 4,Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
      (allowance C D Z) Kmain (sigma/3) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j≤
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
      (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ))
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector,neg_div] using hh
  · have hh:=actual_main_exceptional_uniform_cap η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve Mwidth hZ hmod hK hV hactual
    have ht:Z^(-sigma/3)*mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve) (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 1≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
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
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 2:=by
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
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) 3≤
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

theorem actual_error_high_cores (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0≤ sigma)(heps:0≤eps)(_hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)
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
      (allowance C D Z) Kerror (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) j≤
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
      (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k)
      hq hV hc hZ (allowance_nonneg _ _ _) (by linarith)
    simpa [lossVector] using hh
  · have hh:=actual_error_exceptional_uniform_cap η τ C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hC hD hCD E rfl
      K V Z 0 sigma delta reserve Mwidth hZ hmod M H Sbad hbad p hp k hk hK hV hactual
    have ht:errorCores p k (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z
        (allowance C D Z) (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
          (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
          (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p k)
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) 1≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
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
        (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k) 3≤
        Z^(Real.logb Z V-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))+
          sigma+delta+reserve)*Z^(-saving):=by
      convert ht using 1 ; dsimp [errorCores,reference] ; ring
    apply hcore.trans
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [lossVector]
    linarith

theorem actual_high_four_coefficients
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (H:Fin 4→ℝ)(hH:∀j,0≤H j):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let main:=mainCores (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
      (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
      (sigma/3) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ));
    let error:=fun (p:elementPool P) (i:Fin 3) (_χ:Ray)=>
      errorCores p (errorIndex i+1) (τ.modulus.absNorm:ℝ) V (C.absNorm:ℝ) Z (allowance C D Z)
        (errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0 (Real.logb Z (C.absNorm:ℝ))
          sigma delta reserve p (errorIndex i+1)) (Mdecl-M0) paid eps saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1));
    ∀j,averagedCoefficients P ((Mamp+2*sigma)/(sigma/6)) H main error j≤
      56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
        Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss) := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hne:(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).Nonempty:=by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (sigma/3-primeLoss)).trans_le hcard
  have hmain:=actual_main_high_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
    Mdecl Mwidth Mcap hK hV hZ hs.le heps hM hcap hactual hwidth hlow hmod
  have herror:=fun (p:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))))
      (i:Fin 3) (χ:Ray)=>
    actual_error_high_cores η τ C D hC hD hCD E K V Z sigma delta reserve paid eps saving
      Mdecl Mwidth Mcap hK hV hZ hs.le heps hM hcap hactual hwidth hlow hmod
      M Hray Sbad hbad p p.property (errorIndex i+1)
      (by fin_cases i <;> norm_num [errorIndex])
  exact averaged_coefficients_bound _ hne
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ=>(primePool_data M Hray Sbad hbad _ _ _ Q hQ).2)
    Z (sigma/3) primeLoss ((Mamp+2*sigma)/(sigma/6)) hZ hloss
    (div_nonneg (by linarith) (by positivity)) hcard H _ _ _ hH
    (by simpa only [neg_div] using hmain) herror

end SevenEighths.CenteredMomentEnergyFirstHighFourCoefficients

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstHighNormalizedGaussianPowers -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstHighNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighFourCoefficients

theorem actual_high_normalized_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:0≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ))
    (fun p i χ=>errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    (fun p i χ=>Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) hV hc hq hz
  have hav:=actual_high_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod H hH
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end SevenEighths.CenteredMomentEnergyFirstHighNormalizedGaussianPowers

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstHighGaussianUniformPowers -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

lemma finite_power_budget (upper nc Z eps Bcommon deficit primeLoss G F seed:ℝ)
    (N:ℕ)(hupper:1≤upper)(hnc:0≤nc)(hZ:1<Z)(heps:0≤eps)(heps1:eps≤1)
    (hncap:nc≤Z^Bcommon)(hG:0≤G)(_hF:0≤F)(_hseed:0<seed)
    (H srcLoss actualLoss:Fin 4→ℝ)(hH:∀j,0≤H j)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    nc^eps*(∑j:Fin 4,(upper^N)^(powers eps j)*
      (G*H j*Z^(deficit+actualLoss j+primeLoss)))≤
      (upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+actualLoss j):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hncPow:nc^eps≤Z^(eps*Bcommon):=by
    have hh:=Real.rpow_le_rpow hnc hncap heps
    simpa only [←Real.rpow_mul hz.le,mul_comm Bcommon eps] using hh
  have hu:1≤upper^N:=one_le_pow₀ hupper
  have hup (j:Fin 4):(upper^N)^(powers eps j)≤upper^N:=by
    have hp:powers eps j≤1:=by fin_cases j <;> simp [powers] <;> linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hu hp
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj0:=hH j
  have hu0:0≤upper:=zero_le_one.trans hupper
  calc
    _≤Z^(eps*Bcommon)*(upper^N*(G*(F*Z^(srcLoss j)/seed)*Z^(deficit+actualLoss j+primeLoss))):=by
      apply mul_le_mul hncPow _ (by positivity) (by positivity)
      apply mul_le_mul (hup j) _ (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      exact mul_le_mul_of_nonneg_left (hbound j) hG
    _=(upper^N*G*F/seed)*Z^(deficit+eps*Bcommon+primeLoss)*Z^(srcLoss j+actualLoss j):=by
      calc
        _=(upper^N*G*F/seed)*(Z^(eps*Bcommon)*Z^(srcLoss j)*Z^(deficit+actualLoss j+primeLoss)):=by ring
        _=_:=by
          rw [←Real.rpow_add hz, ←Real.rpow_add hz]
          rw [show eps*Bcommon + srcLoss j + (deficit+actualLoss j+primeLoss) =
            (deficit+eps*Bcommon+primeLoss)+(srcLoss j+actualLoss j) by ring,
            Real.rpow_add hz]
          ring

theorem actual_high_uniform_four_powers {a b:ℝ}
    (N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:1≤upper)(hb1:0≤b1)(hb2:0≤b2)(hAmax:0≤Amax)(hlo:0<loFloor)
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hCc:0≤Cc)(hcost:0≤ cost)
    (sigma delta reserve paid saving Mcap Mamp primeLoss Bcommon:ℝ)
    (hs:0<sigma)(heps:0≤epsilon)(heps1:epsilon≤1)(hloss:0≤primeLoss)(hMamp:0≤Mamp):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤Kfix→∃Cbound:ℝ,0<Cbound ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      1<Z→0≤height→0≤A→A≤Amax→1≤ seed→0≤C0→0≤C1→
    ∀(M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O)),
    fixedBadPrimes⊆Sbad→
    ∀(η τ:Character)(C D:Ideal O)(_hC:Supported C)(_hD:Supported D),
    primeSupport C=primeSupport D→∀E:Finset (CommonIndex C D),
    ∀K V Mdecl Mwidth:ℝ,0<K→0<V→0≤Mdecl→Mdecl≤Mcap→
    Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth→Mwidth≤Mdecl→
    Real.logb Z V≤Mdecl→
    Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card→
    τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}→
    (C.absNorm:ℝ)≤Z^Bcommon→
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (q:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve q (errorIndex i+1);
    let alpha:=powers epsilon;
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W);
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (q:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers q (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror q i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval q Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) epsilon
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (Cbound*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J/seed)*
        Z^(Mdecl-M0+epsilon*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(losses epsilon deltaSource thetaSource Bcap j+
          lossVector sigma delta reserve paid epsilon Mcap saving j):=by
  obtain ⟨U,J,hweights⟩:=actual_weights N upper b1 b2 Amax loFloor
    Cm Ce Cd Ct Cc cost epsilon deltaSource thetaSource Bcap Jprofile Jchild degree Sp Tchild Sf W
    (zero_le_one.trans hu) hb1 hb2 hAmax hlo hCm hCe hCd hCt hCc hcost
  refine ⟨U,J,?_⟩
  intro Q Kfix hKfix
  obtain ⟨Cweights,hCweights,hw⟩:=hweights Q Kfix hKfix
  let G:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))
  have hG:0<G:=by dsimp [G];positivity
  refine ⟨upper^N*G*Cweights,by positivity,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
    M _ Hray Sbad hbad η τ C D hC hD hCD E K V Mdecl Mwidth hK hV hM hcap hactual hwidth hlow hcard hmod hncap
  dsimp only
  let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree
  let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
    (fixedFactors Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W)
  have hEbase:0≤Ebase:=by
    have hd:=diagonalControl_nonneg W
    dsimp [Ebase]
    positivity
  have hH:∀j,0≤H j:=coefficients_nonneg N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _
    (zero_le_one.trans hu) hb1 hb2 hKfix (zero_le_one.trans hseed)
    (fixedFactors_nonneg Cm Ce Cd Ct Z epsilon deltaSource thetaSource Bcap cost Ebase t loFloor seed Jchild Sf W
      hCm hCe hCd hCt (zero_le_one.trans hZ.le) hcost hEbase hlo.le (zero_le_one.trans hseed))
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid epsilon saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod upper N (zero_le_one.trans hu)
    H hH
  dsimp only at ha
  apply ha.trans
  have hb:=finite_power_budget upper (C.absNorm:ℝ) Z epsilon Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss G
    (Cweights*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J) seed N hu (Nat.cast_nonneg _)
    hZ heps heps1 hncap hG.le (by positivity) (zero_lt_one.trans_le hseed) H
    (losses epsilon deltaSource thetaSource Bcap)
    (lossVector sigma delta reserve paid epsilon Mcap saving) hH
    (hw p Z t height A seed C0 C1 (zero_lt_one.trans hZ) hheight hA hAA hseed hC0 hC1)
  convert hb using 1 ; dsimp only [G] ; ring

theorem actual_high_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstHighNormalizedGaussianPowers.actual_high_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstNormalizedGaussianPowers -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstNormalizedGaussianPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

theorem actual_normalized_four_powers
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
    (upper:ℝ)(N:ℕ)(hupper:0≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)(rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (C.absNorm:ℝ)^eps*∑j:Fin 4,(upper^N)^(alpha j)*
        (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))*H j*
          Z^(Mdecl-M0+lossVector sigma delta reserve paid eps Mcap saving j+primeLoss)) := by
  dsimp only
  have hq:=norm_pos τ.modulus τ.modulus_ne_bot
  have hc:=norm_pos C hC.1
  have hz:=zero_lt_one.trans hZ
  have hn:=actual_power_reference_identity
    (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))) ((Mamp+2*sigma)/(sigma/6))
    upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z (allowance C D Z) eps N H
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    (sigma/3) (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) paid saving rmain
    (fun p i χ=>errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1))
    rerror hV hc hq hz
  have hav:=actual_low_four_coefficients M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod H hH rmain rerror
  dsimp only at hn hav
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [hn j]
  have hpos:0≤(C.absNorm:ℝ)^eps*(upper^N)^(CenteredMomentSecondChildPowerBudget.powers eps j):=by positivity
  exact (mul_le_mul_of_nonneg_left (hav j) hpos).trans_eq (by ring)

end SevenEighths.CenteredMomentEnergyFirstNormalizedGaussianPowers

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstLowHomogeneousPowers -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighGaussianUniformPowers

theorem actual_low_homogeneous_four_powers
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
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed)
    (rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j) := by
  have ha:=CenteredMomentEnergyFirstNormalizedGaussianPowers.actual_normalized_four_powers
    M Hray Sbad hbad η τ C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod
    upper N (zero_le_one.trans hupper) H hH rmain rerror
  dsimp only at ha ⊢
  apply ha.trans
  exact finite_power_budget upper (C.absNorm:ℝ) Z eps Bcommon
    (Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ))) primeLoss
    (56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ))) F seed N
    hupper (Nat.cast_nonneg _) hZ heps heps1 hncap (by positivity) hF hseed H
    srcLoss (lossVector sigma delta reserve paid eps Mcap saving) hH hbound

end SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformReflectionProfile -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentUniformReflectionProfile
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentOneReflectionEnergy

theorem source_separation (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀G : 𝓢(ℝ,ℂ),∀D : ℝ,0<D →
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤D → ∀s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier G (s*Real.exp y)=
          ∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*D ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*D) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨H,K,hK,hEuler⟩ := paperRadialFourier_euler_source_weighted_bound
    A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨H,(C+1)*K,by positivity,?_⟩
  intro G D hD hGD s hs
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep (paperRadialFourier G)
    (paperRadialFourier_contDiffOn G) (K*D) (by positivity)
    (fun j hj x hx=>(hEuler G j hj x hx.le).trans
      (mul_le_mul_of_nonneg_left hGD hK.le)) s hs
  have hconst : C*(K*D)≤((C+1)*K)*D := by nlinarith [mul_pos hK hD]
  exact ⟨density,(fun y=>by simpa using hid (fun _ : Unit=>y)),hi,
    hm.trans hconst,fun v=>(hp v).trans hconst⟩

theorem actual_one_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,K,hK,hb⟩ := source_separation V M hM hV A (J+2)
  refine ⟨H,(K*Real.pi)^2,by positivity,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  choose d hid hi hm hp using fun i=>hb (G i) D hD (hGD i) (s i) (hs i)
  let e (i : ι) : ℂ := (1+s i)^A
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (G i) x
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*P i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (X i) 0 0*P i=∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))=
        (fun x=>logWindow V x*F i (s i*x)) := by funext x;dsimp [F,e];ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (P i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hpoint (i : ι) : ∀v,‖(e i • d i) v‖≤envelope (K*D) J v := by
    have hh := normalized_density_bound A 0 J (s i) 0 (K*D) (hs i) (d i)
      (by simpa using hp i)
    simpa [heightScale,e] using hh
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope (K*D) J)
    (fun v=>(1+‖v‖)^J) (envelope_pos (K*D) (mul_pos hK hD) J)
    (by intro v;positivity) hpoint hint (envelope_integrable (K*D) J) E hE henergy
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  convert hh using 1
  ring

lemma inverse_annular_frequency (χ : Character) (V : ℝ→ℂ)
    (hreal : ∀y,conj (V y)=V y) (X v : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false (logWindow V) X 0 (2*Real.pi*v)=
      conj (HeckeDyadic.polynomial χ false (logWindow V) X 0 (-2*Real.pi*v)) := by
  have hr (x : ℝ) : conj (logWindow V x)=logWindow V x := by
    unfold logWindow
    split_ifs <;> simp [hreal]
  have ht : (fun x=>conj (CompletedHeight.normTwistedSource (logWindow V) v x))=
      CompletedHeight.normTwistedSource (logWindow V) (-v) := by
    funext x
    simp only [CompletedHeight.normTwistedSource,map_mul,hr]
    exact congrArg (fun z=>z*logWindow V x) (SecondPassIntegration.logPhase_conjugate v _)
  rw [CenteredMomentTwistedReflection.polynomial_twisted_source χ.inverse _ X v hX,
    polynomial_inverse_plain χ _ X hX,ht,
    ←CenteredMomentTwistedReflection.polynomial_twisted_source χ _ X (-v) hX]
  congr 2
  ring

theorem actual_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀D E : ℝ,0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖^2)
        ≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
          (X i) 0 0*P i‖^2)≤C*D^2*E := by
  obtain ⟨H,C,hC,hbound⟩ := actual_one_uniform V M hM hV A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s X hs hX D E hD hE hGD henergy
  apply hbound G (fun i=>(χ i).inverse) P s X hs hX D E hD hE hGD
  intro v
  have he (i : ι) :
      ‖HeckeDyadic.polynomial (χ i).inverse false (logWindow V) (X i) 0 (2*Real.pi*v)*P i‖=
      ‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*P i‖ := by
    rw [inverse_annular_frequency (χ i) V hreal (X i) v (hX i),norm_mul,
      Complex.norm_conj,←norm_mul]
  simpa only [he] using henergy v

lemma paperRadialFourier_real_smul (c : ℝ) (G : 𝓢(ℝ,ℂ)) (x : ℝ) :
    paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) x=(c:ℂ)*paperRadialFourier G x := by
  rw [paperRadialFourier_eq_ray,paperRadialFourier_eq_ray]
  simp only [map_smul,smul_apply,Complex.real_smul]

lemma polynomial_const_mul (χ : Character) (W : ℝ→ℂ) (X σ omega : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X σ omega=
      c*HeckeDyadic.polynomial χ false W X σ omega := by
  unfold HeckeDyadic.polynomial
  have he : (fun I : HeckeDyadic.NonzeroIdeal=>
      HeckeDyadic.summand χ false (fun x=>c*W x) X σ omega I)=
      (fun I=>c*HeckeDyadic.summand χ false W X σ omega I) := by
    funext I
    unfold HeckeDyadic.summand
    ring
  rw [he,tsum_mul_left]
  ring

lemma reflected_polynomial_real_smul (χ : Character) (V : ℝ→ℂ)
    (G : 𝓢(ℝ,ℂ)) (s X c : ℝ) (A : ℕ) :
    HeckeDyadic.polynomial χ false
      (fun x=>logWindow V x*((1+s)^A:ℂ)*paperRadialFourier (c • G : 𝓢(ℝ,ℂ)) (s*x)) X 0 0=
      (c:ℂ)*HeckeDyadic.polynomial χ false
        (fun x=>logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x)) X 0 0 := by
  simp_rw [paperRadialFourier_real_smul]
  have he : (fun x=>logWindow V x*((1+s)^A:ℂ)*((c:ℂ)*paperRadialFourier G (s*x)))=
      (fun x=>(c:ℂ)*(logWindow V x*((1+s)^A:ℂ)*paperRadialFourier G (s*x))) := by
    funext x
    ring
  rw [he,polynomial_const_mul]

theorem detector_source_control (H : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃D : ℝ,0<D ∧ ∀reverse : Bool,∀k : ℕ,k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
        (((1+‖t‖)^n)⁻¹ • CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t)≤D := by
  obtain ⟨n,D,hD,hb⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,D,hD,?_⟩
  intro reverse k hk σ hσ t
  rw [map_smul_eq_mul,Real.norm_of_nonneg (by positivity : 0≤((1+‖t‖)^n)⁻¹)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(1+‖t‖)^n)).mpr
    (by simpa only [mul_comm] using hb reverse k hk σ hσ t)

theorem detector_inverse_uniform (V : ℝ→ℂ) (M : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (hreal : ∀y,conj (V y)=V y) (A J : ℕ) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],
      ∀(reverse : ι→Bool)(k : ι→ℕ)(σ t : ι→ℝ),
      (∀i,k i≤2) → (∀i,σ i∈Set.Icc (0:ℝ) 1) →
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ι→ℝ),
      (∀i,0<s i) → (∀i,0<X i) → ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (-2*Real.pi*v)*
        (((1+‖t i‖)^n:ℝ):ℂ)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i).inverse false
        (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier
          (CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)) (s i*x))
        (X i) 0 0*P i‖^2)≤C*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_inverse_uniform V M hM hV hreal A J
  obtain ⟨n,D,hD,hcontrol⟩ := detector_source_control H
  refine ⟨n,C*D^2,by positivity,?_⟩
  intro ι _ reverse k σ t hk hσ χ P s X hs hX E hE henergy
  let G (i : ι) := CenteredMomentDetectorDictionary.detectorSchwartz (reverse i) (k i) (σ i) (t i)
  let w (i : ι) : ℝ := (1+‖t i‖)^n
  have hw (i : ι) : 0<w i := by dsimp [w];positivity
  have hh := hb (fun i=>(w i)⁻¹ • G i) χ (fun i=>(w i:ℂ)*P i) s X hs hX D E hD hE
    (fun i=>hcontrol (reverse i) (k i) (hk i) (σ i) (hσ i) (t i))
    (by intro v;simpa only [w,mul_assoc] using henergy v)
  have he (i : ι) : HeckeDyadic.polynomial (χ i).inverse false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier ((w i)⁻¹ • G i : 𝓢(ℝ,ℂ)) (s i*x))
      (X i) 0 0*((w i:ℂ)*P i)=
      HeckeDyadic.polynomial (χ i).inverse false
      (fun x=>logWindow V x*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x)) (X i) 0 0*P i := by
    rw [reflected_polynomial_real_smul,Complex.ofReal_inv]
    have hne : (w i:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw i).ne'
    rw [mul_mul_mul_comm,inv_mul_cancel₀ hne,one_mul]
  simp_rw [he] at hh
  simpa only [G] using hh

end SevenEighths.CenteredMomentUniformReflectionProfile

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentRetainedReflection CenteredMomentOriginalReflectionApproximation
open CenteredMomentSectorLocalization CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem discarded_bound (A B : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y R : ℝ),
      0<Y → 0<R →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨H,D,hD,hDb⟩ := paperRadialFourier_euler_source_weighted_bound (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨H,K*D,mul_pos hK hD,?_⟩
  intro G χ Y R hY hR
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier G x‖≤
      D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := by
    intro x hx
    have hh := hDb G 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)
    R (by positivity) hR hf
  exact (hKb χ _ ((D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)/R^A)
    Y (by positivity) hY hm).trans_eq (by ring)

theorem discarded_negligible (xi saving L Cscale : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))(χ : Character)(Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial χ false
        (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨H,C,hC,hbound⟩ := discarded_bound A 2 (by omega)
  refine ⟨H,C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro G χ Y Z hZ hY hYZ
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A :=
      hbound G χ Y _ hY hR
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

theorem deleted_discarded_negligible (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(G : 𝓢(ℝ,ℂ))
      (S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)(η ηi χ : Character)(Q X Z : ℝ),
      1≤Z → 0<Q → 0<X → Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
      let F := fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x
      (∀D∈S.powerset,Summable (fun I : SmoothIdeal S=>coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0)) ∧
      ‖∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient η ηi S D I*
        HeckeDyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
          (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := discarded_negligible xi saving L Cscale hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound epsilon hepsilon
  refine ⟨H,D*C,mul_pos hD hC,?_⟩
  intro G S hS η ηi χ Q X Z hZ hQ hX hcap
  dsimp only
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hh := hDb S hS η ηi
    (fun E I=>HeckeDyadic.polynomial χ false
      (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*paperRadialFourier G x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm I.val)) 0 0)
    (C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving)) (by positivity) (by
      intro E hE I
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) I Q X (Cscale*Z^L) hQ hX hcap
      exact hCb G χ _ Z hZ hy.1 hy.2)
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩

def retainedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    finiteAnnularColumn χ.inverse (paperRadialFourier G) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))

def discardedSchwartz (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
    HeckeDyadic.polynomial χ.inverse false (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0

lemma retainedSchwartz_eq (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    retainedSchwartz χ ψ G X R=
      let S := redundantSet χ.modulus ψ.modulus
      ∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0 := by
  unfold retainedSchwartz
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro I
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ (reflected_decayTwo G) _ _ (by positivity)]

lemma restoration_summable (χ ψ : Character) (G : 𝓢(ℝ,ℂ)) (X R : ℝ) (hX : 0<X) :
    let S := redundantSet χ.modulus ψ.modulus
    ∀D∈S.powerset,
      Summable (fun I : SmoothIdeal S=>coefficient ψ ψ.inverse S D I*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) R
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val))) ∧
      Summable (fun I : SmoothIdeal S=>coefficient ψ ψ.inverse S D I*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier G x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0) := by
  dsimp only
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo G
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  refine ⟨hr.congr ?_,hd⟩
  intro I
  have hN := subset_product_norm_pos D (fun P hP=>hS P ((Finset.mem_powerset.mp hD) hP))
  have hI := norm_pos I.val
  rw [finiteAnnularColumn_eq _ _ hF _ _ (by positivity)]

theorem original_split (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X R : ℝ),0<X →
        HeckeDyadic.polynomial χ false G X 0 0=
          g*(retainedSchwartz χ ψ G X R+discardedSchwartz χ ψ G X R) := by
  obtain ⟨ψ,g,hp,hnp,hg,hcap,h⟩ := original_retained_reflection χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X R hX
  rw [retainedSchwartz_eq χ ψ G X R hX]
  exact h G X R hX

theorem actual_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(G : 𝓢(ℝ,ℂ))(X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := deleted_discarded_negligible xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hsplit⟩ := original_split χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro G X Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  rw [hsplit G X (Z^(xi/2)) hX,mul_add,add_sub_cancel_left,norm_mul,hg,one_mul]
  have hb := (hCb G S hS ψ ψ.inverse χ.inverse _ X Z hZ hQ hX hcap').2
  apply hb.trans
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hepsilon.le

lemma retainedSchwartz_uniformTwisted (χ ψ : Character) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (t X R : ℝ) :
    retainedSchwartz χ ψ (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) X R=
      retainedOriginal χ ψ W X R t := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold retainedSchwartz retainedOriginal
  rw [he]

theorem actual_twisted_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(ha : 0<a)(hs : Function.support W⊆Set.Icc a b)
        (hW : ContDiff ℝ ∞ W)(t X Z : ℝ),0<X → 1≤Z →
        (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
          g*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
          C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)*
            (χ.modulus.absNorm:ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale epsilon hxi hscale hepsilon
  refine ⟨H,C,hC,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hbound⟩ := hb χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro W a b ha hs hW t X Z hX hZ hmod
  have hh := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) X Z hX hZ hmod
  rw [retainedSchwartz_uniformTwisted] at hh
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have ht := CenteredMomentTwistedReflection.polynomial_twisted_source χ W X t hX
  rw [←he] at ht
  rw [←ht] at hh
  exact hh

theorem detector_original_approximation (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 →
      ∃(ψ : Character)(g : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖g‖=1 ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀reverse : Bool,∀k : ℕ,k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t X Z : ℝ,
        0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
        let G := CenteredMomentDetectorDictionary.detectorSchwartz reverse k σ t
        ‖HeckeDyadic.polynomial χ false G X 0 0-
          g*retainedSchwartz χ ψ G X (Z^(xi/2))‖≤
          C*(χ.modulus.absNorm:ℝ)^epsilon*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale epsilon hxi hscale hepsilon
  obtain ⟨n,D,hD,hcontrol⟩ := CenteredMomentDetectorDictionary.detectorSchwartz_uniform H
  refine ⟨n,C*D,mul_pos hC hD,?_⟩
  intro χ hn
  obtain ⟨ψ,g,hp,hnp,hg,hcap,hbound⟩ := hb χ hn
  refine ⟨ψ,g,hp,hnp,hg,hcap,?_⟩
  intro reverse k hk σ hσ t X Z hX hZ hmod
  dsimp only
  apply (hbound _ X Z hX hZ hmod).trans
  have he := hcontrol reverse k hk σ hσ t
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC.le) (by positivity :
      0≤(χ.modulus.absNorm:ℝ)^epsilon)) (by positivity : 0≤Z^(-saving))
  exact hh.trans_eq (by ring)

end SevenEighths.CenteredMomentUniformReflectionApproximation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformOriginalEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformOriginalEnergy
open HeckeFamily CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionEnergy

theorem actual_original_energy_to_retained (xi saving L Cscale ε : ℝ)
     (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(W : ι→𝓢(ℝ,ℂ))(X : ι→ℝ)(P : ι→ℂ)(D Z Rcap : ℝ),0<D → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (W i)≤D) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2)≤
            2*(∑i,‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2)+
            C*Rcap^(2*ε)*D^2*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨H,C,hC,hb⟩ := actual_original_approximation xi saving L Cscale ε hxi hscale hε
  refine ⟨H,2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro W X P D Z Rcap hD hZ hR hX hWD hmod hsource
  let B := C*D*Rcap^ε*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0-
        G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))‖≤B := by
    apply (happrox i (W i) (X i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hWD i) hC.le)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le)
      (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i‖^2≤
      2*‖retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2))*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i)
      ((G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false (W i) (X i) 0 0*P i-
        (G i*retainedSchwartz (χ i) (ψ i) (W i) (X i) (Z^(xi/2)))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*D^2*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentUniformOriginalEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformReflectionScale -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentUniformReflectionScale
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentOneReflectionScaleEnergy CenteredMomentUniformReflectionProfile
open CenteredMomentReflectedNormalization

theorem actual_rowwise_scales (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)
      (s lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Set.Icc lo hi) → (∀i,ly i∈Set.Icc low high) →
      (∀i,0<s i) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i)^A:ℂ)*paperRadialFourier (G i) (s i*x))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  have hreal : ∀y,conj (CenteredMomentReflectedAnnuli.logWindow y)=
      CenteredMomentReflectedAnnuli.logWindow y := by
    intro y
    exact Complex.conj_ofReal _
  obtain ⟨H,C,hC,hbound⟩:=actual_inverse_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow hreal A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ G χ P s lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly hspos hD hE hGD henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i) false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        (polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    rw [actual_log_window]
    simp only [←mul_assoc]
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    apply hh.trans_eq
    rw [hp]
    ring
  have hh:=hbound G χ (fun i=>polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)
    s (fun i=>Real.exp (lx i)) hspos (fun i=>Real.exp_pos _) D
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) hD (mul_nonneg hdx (mul_nonneg hdy hE)) hGD hfixed
  simp only [actual_log_window,←mul_assoc] at hh
  convert hh using 1

end SevenEighths.CenteredMomentUniformReflectionScale

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformReflectionChoices -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformReflectionChoices
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionScale

theorem actual_independent_choices (B J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (fun x=>(annulus x:ℂ)*((1+s i (u i))^B:ℂ)*paperRadialFourier (G i) (s i (u i)*x))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_rowwise_scales B J
  refine ⟨H,C,hC,?_⟩
  intro ι _ α G χ P s X keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hD hE hGD henergy u
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
  have hh := hb G χ P' (fun i=>s i (u i)) lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hD hE hGD he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

end SevenEighths.CenteredMomentUniformReflectionChoices

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformRetainedEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentUniformRetainedEnergy
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentUniformReflectionChoices CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentReflectedUniformPair
open CenteredMomentReflectedNormalization

lemma twisted_zero (W:ℝ→ℂ) : CompletedHeight.normTwistedSource W 0=W := by
  funext x
  simp [CompletedHeight.normTwistedSource,FourierBridge.logPhase]

lemma normalized_zero (G:𝓢(ℝ,ℂ)) (B:ℕ) (s:ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow G B 0 s 0=
      (fun x=>(annulus x:ℂ)*((1+s)^B:ℂ)*paperRadialFourier G (s*x)) := by
  funext x
  simp only [normalizedReflected,heightScale,pow_zero,div_one,twisted_zero,actual_log_window]
  push_cast
  rfl

lemma retained_zero (χ ψ:Character) (G:𝓢(ℝ,ℂ)) (X R:ℝ) :
    retainedOriginal χ ψ G X R 0=retainedSchwartz χ ψ G X R := by
  unfold retainedOriginal retainedSchwartz
  rw [twisted_zero]

theorem actual_retained_uniform_energy (epsilon : ℝ)
    (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(X R ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high D E Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := actual_independent_choices B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R ly omega Wshort c d lo hi low high D E Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp G χ P s Y keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hD hE hGD henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (P' i) (u i)‖^2)≤
        Cp*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,normalized_zero,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun i=>(G i:ℝ→ℂ)) X R (fun _=>0) hX (fun _=>B) 0 P' (fun _=>hB)
    0 Rcap _ le_rfl (fun _=>by simp) hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [retained_zero,P',Nat.mul_zero,pow_zero,mul_one,←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentUniformRetainedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformNaturalRetained -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformNaturalRetained
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentUniformRetainedEnergy CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (epsilon Cscale xi : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort D E Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSchwartz (χ i) (ψ i) (G i) (Z^along) (Z^(xi/4))*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_retained_uniform_energy epsilon hepsilon B J hB
  refine ⟨H,C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ ψ P omega Wshort c d M along bshort D E Rcap hd hshort hshortsmooth
    hnatural hmod hD hE hGD hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hlog : 0≤Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0<dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb G χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    D E Rcap (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hD hE hGD hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end SevenEighths.CenteredMomentUniformNaturalRetained

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformOriginalComparison -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformOriginalComparison
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentUniformNaturalRetained CenteredMomentUniformOriginalEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (epsilon Cscale xi saving L : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→Character)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E S Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0<S → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false (G i) (Z^along) 0 0*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*S^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*S^2*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨H,C,hC,hr⟩ := actual_natural_retained_energy epsilon Cscale xi hepsilon hscale hxi B J hB
  obtain ⟨H',D,hD,ho⟩ := actual_original_energy_to_retained (xi/2) saving L Cscale epsilon
    (by positivity) hscale hepsilon
  refine ⟨H∪H',2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ P omega Wshort c d M along bshort E S Rcap hχ hd hshort hshortsmooth
    hML hmod hE hS hGS hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hG1 (i:ι):H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S :=
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left : H⊆H∪H')) (G i)).trans (hGS i)
  have hG2 (i:ι):H'.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤S :=
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right : H'⊆H∪H')) (G i)).trans (hGS i)
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal G (fun _=>Z^along) Q S Z Rcap hS hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) hG2 hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 G χ ψ P omega Wshort c d M along bshort S E Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hS hE hG1 hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentUniformOriginalComparison

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformRadialComparison -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentUniformRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
local notation "O" => HeckeFamily.O

theorem actual_original_radial_comparison (epsilon Cscale xi saving L : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(G:O→𝓢(ℝ,ℂ))(χ : O→Character)(P : O→ℂ)(omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E Src Rcap : ℝ),
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → (∀z,‖P z‖≤Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0<Src → (∀z,keep z → H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G z)≤Src) → 1≤Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*Src^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*Src^2*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformOriginalComparison.actual_original_comparison
    epsilon Cscale xi saving L hepsilon hscale hxi B J hB
  refine ⟨H,C,D,hC,hD,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro G χ P omega keep Φ K Pbound Wshort c d M along bshort E Src Rcap hK hΦ hP hχ
    hd hshort hshortsmooth hML hmod hE hSrc hGS hRcap hcap henergy
  have hz : 0<Z:=by linarith [hZ.1]
  have hshortsum:=single_radial_summable χ P omega Wshort c d (Z^bshort) Pbound hd
    (Real.rpow_pos_of_pos hz _) hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let weightedP (z : ↥S) : ℂ:=P z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hmem (z : ↥S) : keep (z:O):=(Finset.mem_filter.mp z.property).2
  have hh:=hZ.2 (fun z:↥S=>G z) (fun z:↥S=>χ z) weightedP (fun z=>omega z)
    Wshort c d M along bshort E Src Rcap (fun z=>hχ z (hmem z)) hd hshort hshortsmooth
    hML (fun z=>hmod z (hmem z)) hE hSrc (fun z=>hGS z (hmem z)) hRcap
    (fun z=>hcap z (hmem z)) ?_
  · simp only [weightedP,←mul_assoc] at hh
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false (G z) (Z^along) 0 0*polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ,
      finite_weighted rows keep (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ] at hh
    apply hh.trans
    apply add_le_add
    · apply le_of_eq;ring
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  · intro v j k x hx
    have hschild:=pair_radial_summable χ P (fun _=>-2*Real.pi*v) omega
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (scaleTest Wshort k)
      (1/4) 1 c d (Real.exp x) (Z^bshort) Pbound (by norm_num) hd
      (Real.exp_pos _) (Real.rpow_pos_of_pos hz _)
      (scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j)
      (scaleTest_support _ _ _ hshort k) hP keep Φ K hK
    simp only [weightedP,←mul_assoc]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) Φ K hΦ]
    exact (hschild.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (henergy v j k x hx)

end SevenEighths.CenteredMomentUniformRadialComparison

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonMaskRadialEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentCommonMaskRadialEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentUniformReflectionProfile
local notation "O" => HeckeFamily.O

lemma naturalSlot_bounded (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,‖naturalSlot χ pool β P‖≤B := by
  refine ⟨‖(Real.sqrt P:ℂ)⁻¹‖*∑I∈pool,‖β I‖,by positivity,?_⟩
  intro χ
  unfold naturalSlot
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma slots_bounded {α : Type*} (F : Finset α) (pool : α→Finset (Ideal O))
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,‖∏j∈F,naturalSlot χ (pool j) (β j) (P j)‖≤B := by
  choose B hB hb using fun j=>naturalSlot_bounded (pool j) (β j) (P j)
  refine ⟨∏j∈F,B j,Finset.prod_nonneg (fun j _=>hB j),?_⟩
  intro χ
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hb j χ)

theorem actual_radial_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,he⟩:=actual_shared_energy F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hp hP hβ hs hK hΦ hE hchild
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let q (z : ↥S) : ℂ:=(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=he R hR (fun z:↥S=>χ z) (fun z=>q z • W₁) (fun _=>W₂)
    (fun _=>X₁) (fun _=>X₂) (fun _=>pool) (fun _=>β) (fun _=>P)
    (fun _=>hX₁) (fun _=>hX₂) (fun _=>hp) (fun _=>hP)
    (fun _=>hβ) (fun _=>hs) E hE ?_
  · have hid (χ₀ : Character) (z : ↥S) (X : ℝ) :
        polynomial χ₀ false (q z • W₁ : 𝓢(ℝ,ℂ)) X 0 0=q z*polynomial χ₀ false W₁ X 0 0 := by
      exact polynomial_const_mul χ₀ W₁ X 0 0 (q z)
    simp_rw [hid] at hh
    have halg (z : ↥S) (u v w : ℂ) : q z*u*v*w=(u*v*w)*q z := by ring
    simp_rw [halg] at hh
    exact (finite_weighted rows keep _ Φ K hΦ).symm.trans_le hh
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈R.powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      apply Nat.cast_pos.mpr
      exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hI=>(hR I (Finset.mem_powerset.mp hD hI)).ne_zero)))
    obtain ⟨PB,hPB,hbound⟩:=slots_bounded (F\J) pool β P
    have hsum:=pair_radial_summable χ
      (fun z=>∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j))
      (fun _=>0) (fun _=>0) W₁ W₂ a₁ b₁ a₂ b₂
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
      hb₁ hb₂ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) hs₁ hs₂
      (fun z=>hbound (χ z)) keep Φ K hK
    have hid (χ₀ : Character) (z : ↥S) (X : ℝ) :
        polynomial χ₀ false (q z • W₁ : 𝓢(ℝ,ℂ)) X 0 0=q z*polynomial χ₀ false W₁ X 0 0 :=
      polynomial_const_mul χ₀ W₁ X 0 0 (q z)
    simp_rw [hid]
    have halg (z : ↥S) (u v w : ℂ) : q z*u*v*w=(u*v*w)*q z := by ring
    simp_rw [halg]
    dsimp only [q]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false W₁
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
      polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
      ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) Φ K hΦ]
    exact (hsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (hchild D₁ hD₁ D₂ hD₂ J hJ)
end SevenEighths.CenteredMomentCommonMaskRadialEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalRadial
open HeckeFamily HeckeDyadic ConcreteTraceCRT MeasureTheory
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskRadialEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O

lemma profile_support (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) :
    Function.support (V.profile U hU t : ℝ→ℂ)⊆Set.Icc (V.a/max 1 V.b) (max 1 V.b) := by
  by_cases h : 1≤U*V.b
  · rw [V.profile_retained U hU t h]
    exact (retainedProfile_support V.W V.a V.b V.a_pos V.support V.smooth U hU h t).trans
      (fun _ hx=>⟨hx.1,hx.2.trans (le_max_right _ _)⟩)
  · rw [V.profile_zero U hU t (lt_of_not_ge h)]
    simp

def naturalCharacter (η : Character) (z : O) : Character :=
  if h : z≠0 then (naturalRow η z h).character else η

lemma naturalCharacter_eq (η : Character) (z : O) (hz : z≠0) :
    naturalCharacter η z=(naturalRow η z hz).character := by simp [naturalCharacter,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

def Shared (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,∀F : Finset T,
      Shared F (fun i=>b i) (fun i=>M i) C ε := by
  have he (T : Finset α) (F : Finset T) : ∃C : ℝ,0<C ∧ Shared F (fun i=>b i) (fun i=>M i) C ε :=
    actual_radial_shared_energy F (fun i=>b i) (fun i=>M i) (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,∑F : Finset T,C T F
  have hp (T : Finset α) : 0≤∑F : Finset T,C T F:=Finset.sum_nonneg (fun F _=>(hC T F).le)
  refine ⟨B,by have hh : 0≤∑T : Finset α,∑F : Finset T,C T F:=Finset.sum_nonneg (fun T _=>hp T);dsimp [B];linarith,?_⟩
  intro T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild
  have hCB : C T F≤B := by
    have h₁:=Finset.single_le_sum (fun G _=>(hC T G).le) (Finset.mem_univ F)
    have h₂:=Finset.single_le_sum (fun T _=>hp T) (Finset.mem_univ T)
    dsimp [B];linarith
  exact (hb T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

def commonChild (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (left : Bool) (z : O) (D₁ D₂ : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : ℂ :=
  let d:=commonData (withHeight s τ v) C R B
  if left then child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma common_rawScale (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    rawScale L a (commonData (withHeight s τ v) C R B).X₁ 0=
      s.X₁/(Ideal.absNorm (B.val (Sum.inr 0)*CenteredMomentDivisorRectangle.selectedPlain L a 0):ℝ) := by
  simp only [rawScale,commonData,withHeight,map_mul,Nat.cast_mul,div_div]

theorem common_allocated_normalized (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (hRC : R*C≠0) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (hV₁ : V₁.W=s.W₁) (hV₂ : V₂.W=s.W₂) (z : O) (hz : z≠0) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a d.W₁ d.W₂ d.X₁ d.X₂=
      (((clippedScale (rawScale L a d.X₁ 0)):ℂ)^(Complex.I*v)*
       ((clippedScale (rawScale L a d.X₂ 1)):ℂ)^(Complex.I*v))*
       (polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₁.profile _ (rawScale_pos L a d.X₁ d.X₁_pos 0) v) (clippedScale (rawScale L a d.X₁ 0)) 0 0*
        polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₂.profile _ (rawScale_pos L a d.X₂ d.X₂_pos 1) v) (clippedScale (rawScale L a d.X₂ 1)) 0 0*
        ∏i∈liveIndices L a,naturalSlot (excluded (naturalCharacter τ z) (R*C))
          (d.slots i) (heightCoefficient (d.coefficient i) v) (d.P i)) := by
  dsimp only
  rw [naturalCharacter_eq τ z hz]
  have hh:=allocated_normalized τ z hz (R*C) hRC L a V₁ V₂
    (commonData (withHeight s τ v) C R B).slots
    (commonData (withHeight s τ v) C R B).coefficient
    (commonData (withHeight s τ v) C R B).P
    (commonData (withHeight s τ v) C R B).P_pos v
    (commonData (withHeight s τ v) C R B).X₁ (commonData (withHeight s τ v) C R B).X₂
    (commonData (withHeight s τ v) C R B).X₁_pos (commonData (withHeight s τ v) C R B).X₂_pos
  simpa only [hV₁,hV₂,commonData,withHeight] using hh

theorem allocated_radial_bound (b M : α→ℝ) (C₀ ε : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (hb : Shared (liveIndices D a) b M C₀ ε)
    (η : Character) (R : Ideal O) (hR : R≠0) (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hprime : ∀i,∀I∈pool i,Prime I) (hP : ∀i,0<P i)
    (hβ : ∀i,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (r : Radial) (hkeep : ∀z,r.keep z → z≠0) (E : ℝ) (hE : 0≤E)
    (hchild : ∀D₁∈(CompletedGauss.primeSupport R).powerset,
      ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
      radialEnergy (fun z=>child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂
        hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale≤E) :
    radialEnergy (fun z=>allocatedPositiveRow η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂) r.keep r.profile r.scale≤
        C₀*(Ideal.absNorm R.radical:ℝ)^ε*E := by
  have hh:=hb (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₁ 0)) (clippedScale (rawScale D a X₂ 1))
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    pool (fun i=>heightCoefficient (β i) t) P r.keep r.profile r.scale E
    (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)
    (by positivity) (by positivity) (profile_support V₁ _ _ t) (profile_support V₂ _ _ t)
    (fun i _=>hprime i) (fun i _=>hP i)
    (fun i _ I hi=>by rw [heightCoefficient_norm _ _ _ (hprime i I hi).ne_zero];exact hβ i I hi)
    (fun i _ I hi hn=>hs i I hi (left_ne_zero_of_mul hn)) r.scale_pos r.nonneg hE hchild
  rw [←primeSupport_product_radical R hR]
  convert hh using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  split_ifs with hz
  · dsimp only
    rw [allocated_normalized η z (hkeep z hz) R hR D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂,
      naturalCharacter_eq η z (hkeep z hz)]
    have hphase (U : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
      positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
    simp only [excluded,norm_mul,hphase,one_mul]
  · rfl

theorem natural_child_summable (η : Character) (R : Ideal O)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆CompletedGauss.primeSupport R)
    (hD₂ : D₂⊆CompletedGauss.primeSupport R) (J : Finset α) (r : Radial) :
    Summable (fun z=>if r.keep z then
      ‖child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J‖^2*
        (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) := by
  have hn (S : Finset (Ideal O)) (hS : S⊆CompletedGauss.primeSupport R) :
      (0:ℝ)<Ideal.absNorm (∏I∈S,I) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hI=>(support_prime R I (hS hI)).ne_zero)))
  obtain ⟨PB,hPB,hbound⟩:=slots_bounded (liveIndices D a\J) pool (fun i=>heightCoefficient (β i) t) P
  exact pair_radial_summable (naturalCharacter η)
    (fun z=>∏i∈liveIndices D a\J,naturalSlot (naturalCharacter η z) (pool i) (heightCoefficient (β i) t) (P i))
    (fun _=>0) (fun _=>0)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
    (by positivity) (by positivity) (div_pos (by unfold clippedScale;positivity) (hn D₁ hD₁))
    (div_pos (by unfold clippedScale;positivity) (hn D₂ hD₂))
    (profile_support V₁ _ _ t) (profile_support V₂ _ _ t) (fun z=>hbound (naturalCharacter η z))
    r.keep r.profile r.scale r.scale_pos

omit [DecidableEq α] in
lemma common_nonzero (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←(Finset.mem_filter.mp B.property).2]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

lemma child_energy_eq_radial (s : Data α) (r : Radial) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    childEnergy s r D a=
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.X₁ s.X₂) r.keep r.profile r.scale+
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.Y₁ s.Y₂) r.keep r.profile r.scale := by
  have hx:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  have hy:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  unfold childEnergy radialEnergy
  rw [←hx.tsum_add hy]
  apply tsum_congr
  intro z
  unfold Radial.weight
  split_ifs <;> ring

def CommonBound (b M : α→ℝ) (C₀ ε : ℝ) : Prop :=
  ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀r : Radial,(∀z,r.keep z → z≠0) →
    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂)

theorem actual_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ CommonBound b M C₀ ε := by
  obtain ⟨C₀,hC₀,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  let d:=commonData (withHeight s τ v) C R B
  have hRC : R*C≠0:=mul_ne_zero hR (common_nonzero s C B)
  have hb:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (liveIndices L a)
  have hc:= (commonSlots s C B).controls
  have hβ : ∀i,∀I∈d.slots i,‖d.coefficient i I‖≤M i := by
    intro i I _
    exact (hc.1 i I).trans (hMs i)
  have hs : ∀i,∀I∈d.slots i,d.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*d.P i := by
    intro i I _ hn
    exact (hc.2 i I hn).trans (mul_le_mul_of_nonneg_right (hhi i) (s.P_pos i).le)
  have hl:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.X₁ d.X₂ d.X₁_pos d.X₂_pos r hkeep E₁ hE₁ hleft
  have hr:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos r hkeep E₂ hE₂ hright
  rw [child_energy_eq_radial]
  have hh:=add_le_add hl hr
  rw [←mul_add] at hh
  simpa only [d,commonData,withHeight,hV₁,hV₂] using hh

lemma nonexceptional_nonzero (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A z : O)
    (hz : CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A z) : z≠0 := hz.1

theorem uniform_initial_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀T : Finset α,CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε := by
  have he (T : Finset α) : ∃C₀ : ℝ,0<C₀ ∧ CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε :=
    actual_common_radial_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let C₀ : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨C₀,by dsimp [C₀];linarith,?_⟩
  intro T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  have hCB : C T≤C₀ := by
    have hh:=Finset.single_le_sum (fun T _=>(hC T).le) (Finset.mem_univ T)
    dsimp [C₀];linarith
  exact (hb T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (add_nonneg hE₁ hE₂))

lemma common_raw_same_product (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let d:=commonData (withHeight s τ v) C R B
    rawScale L a d.X₁ 0*rawScale L a d.X₂ 1=rawScale L a d.Y₁ 0*rawScale L a d.Y₂ 1 :=
  raw_same_product L a _ _ _ _ (commonData (withHeight s τ v) C R B).same_product.symm

theorem original_nonexceptional_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀(η : Character) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m A : O)
      (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
      (hΦ : ∀z : O,0≤(Φ (CenteredMomentSectorLocalization.normValue z/H)).re),
    let r:=CenteredMomentSecondOriginalChildren.sourceRadial
      (CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A) Φ H hH hΦ

    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C₀,hC₀,hb⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ η χ Q m A Φ H hH hΦ r
    E₁ E₂ hE₁ hE₂ hleft hright
  exact hb s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r
    (fun _ hz=>hz.1) E₁ E₂ hE₁ hE₂ hleft hright

end SevenEighths.CenteredMomentAllocatedNaturalRadial

end

end OAI

end

