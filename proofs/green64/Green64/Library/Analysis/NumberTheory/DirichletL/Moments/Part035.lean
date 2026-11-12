module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part024
public import Green64.Library.Analysis.NumberTheory.DirichletL.Energy.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part021
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part031
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part029
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part026
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part034
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part025
public import Green64.Library.Analysis.NumberTheory.DirichletL.Dictionary.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part013
public import Green64.Library.OAI.NumberTheory.DirichletL.Energy.FirstGaussianProfileWeights
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part005

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part035

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalMaskedFloor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalMaskedFloor
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentPlainPositiveEnergy CenteredMomentPlainGlobalEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentCoreFloor CenteredMomentLattice CenteredMomentTwist
open CenteredMomentAllocatedNaturalSource HeckeInverseAmplification
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

theorem excluded_pair (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (χ : O→Character) (r : Radial) (R : Ideal O) (Q X₁ X₂ : ℝ), R≠0 →
      0≤Q → 0<X₁ → 0<X₂ →
      (∀z,r.keep z→(χ z).residue≠1) →
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Q) →
    radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4 := by
  obtain ⟨S,C,hC,hpair⟩ := actual_radial_pair_bound a b ha
  obtain ⟨Cd,hCd,hdel⟩ := actual_radial_shared_energy (∅ : Finset (Fin 0))
    (fun _=>0) (fun _=>0) (by simp) ε hε
  refine ⟨S,Cd*C*3^8,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Q X₁ X₂ hR hQ hX₁ hX₂ hχ hmod
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4*3^8
  have hdiag := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hh := hdel (CompletedGauss.primeSupport R) (support_prime R) χ W₁ W₂
    X₁ X₂ a b a b (fun _=>∅) (fun _ _=>0) (fun _=>1) r.keep r.profile r.scale E
    hX₁ hX₂ hb hb hs₁ hs₂ (by simp) (by simp) (by simp) (by simp)
    r.scale_pos r.nonneg hE ?_
  · simp only [Finset.prod_empty,mul_one] at hh
    rw [primeSupport_product_radical R hR] at hh
    change radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤ _ at hh
    exact hh.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    have he := hpair W₁ W₂ hs₁ hs₂ χ r Q
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0
      hQ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) hχ hmod
    norm_num only [abs_zero,add_zero,show (3:ℝ)^4=81 by norm_num] at he
    simpa only [Finset.empty_sdiff,Finset.prod_empty,mul_one] using he.trans_eq (by dsimp [E]; ring)

lemma twist_polynomial (χ : Character) (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (t X : ℝ) :
    polynomial χ false (normPowerProfile W a b ha hs (W.smooth ⊤) t) X 0 0 =
      polynomial χ false W X 0 t := by
  have hp : (normPowerProfile W a b ha hs (W.smooth ⊤) t:ℝ→ℂ)=twistProfile W 0 t := by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm Complex.I (t:ℂ)]
    ring
  rw [hp,polynomial_twistProfile]

theorem natural_masked_floor (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (η : Character) (Q R : Ideal O) (r : Radial) (bΦ : ℝ), R≠0 → 0≤bΦ →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η Q (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
    ∀ (Z m q ρ t X₁ X₂ : ℝ), 1≤Z → 0≤ m → 0≤q → r.scale=Z^m →
      m+q≤ρ → 0<X₁ → 0<X₂ → (η.modulus.absNorm:ℝ)≤Z^q →
    zeroEnergy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂ X₁ X₂ r ≤
      C*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(1+‖t‖)^n*Z^(m+q+4*ρ) := by
  obtain ⟨S,C,hC,hpair⟩ := excluded_pair a b ε ha hb hε
  obtain ⟨n,T,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha S
  let F : ℝ := fixedConductorFactor
  have hF : 0<F := by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨4*n,T,C*Ct^4*F^4,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q R r bΦ hR hbΦ hsΦ hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hρ hX₁ hX₂ hη
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let χ : O→Character := fun z=>if hz:z≠0 then (naturalRow η z hz).character else η
  have hχ (z:O) (h:r'.keep z) : (χ z).residue≠1 := by
    have hn := hz z h.1
    have hc : χ z=(naturalRow η z hn).character := by simp [χ,hn]
    exact (congrArg (fun ψ : Character=>ψ.residue≠1) hc).mpr
      ((naturalRow η z hn).nonprincipal hn Q R hR (hex z h.1))
  have hmod (z:O) (h:r'.keep z) : ((χ z).modulus.absNorm:ℝ)≤F*bΦ*Z^(m+q) := by
    have hn := hz z h.1
    have hh : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ h.2)
    simpa only [χ,dite_eq_left hn,add_comm q m] using
      (naturalRow η z hn).modulus_power_bound Z q m bΦ (zero_lt_one.trans_le hZ) hbΦ hη hh
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hpair V₁ V₂ hv₁ hv₂ χ r' R (F*bΦ*Z^(m+q)) X₁ X₂ hR
    (by positivity) hX₁ hX₂ hχ hmod
  have hid : zeroEnergy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂ X₁ X₂ r =
      radialEnergy (fun z=>polynomial (excluded (χ z) R) false V₁ X₁ 0 0 *
        polynomial (excluded (χ z) R) false V₂ X₂ 0 0) r'.keep r'.profile r'.scale := by
    unfold zeroEnergy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · have hn := hz z hk
        simp only [r',hk,true_and,ite_true]
        rw [zero_row_norm η (excluded (χ z) R) _ 1 z
          (by simpa only [χ,dite_eq_left hn,one_mul] using (naturalRow η z hn).masked_element R hR)
          W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ hX₁ hX₂]
        rw [norm_mul,twist_polynomial,twist_polynomial]
        split_ifs with h
        · rfl
        · exact False.elim (h hp)
    · simp [r',hk]
  rw [←hid] at he
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    exact hh.trans_eq (by dsimp [V₁,V₂]; rw [Nat.mul_comm 4 n,pow_mul]; ring)
  have hp : Z^m*(Z^(m+q))^4≤Z^(m+q+4*ρ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ),←Real.rpow_add (zero_lt_one.trans_le hZ)]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd := diagonalControl_nonneg r.profile
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at he
  apply he.trans
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*Z^m*
      ((Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n))*(F*bΦ*Z^(m+q))^4 := by
        gcongr
    _ = (C*Ct^4*F^4*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2*(1+‖t‖)^(4*n))*(Z^m*(Z^(m+q))^4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentNaturalMaskedFloor

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.State -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentFiniteProfileExceptional
open CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

structure NaturalState (Z Bmask bΦ:ℝ) where
  character : Character
  fixedModulus : Ideal O
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  base_ge_one : 1≤Z
  row_nonneg : 0≤ rowWidth
  character_nonneg : 0≤ characterWidth
  scale_eq : radial.scale=Z^rowWidth
  modulus_bound : (character.modulus.absNorm:ℝ)≤Z^characterWidth
  puncture_ne_zero : puncture≠0
  puncture_bound : (puncture.absNorm:ℝ)≤Z^Bmask
  radial_support : Function.support (radial.profile:ℝ→ℂ)⊆Set.Iic bΦ
  row_ne_zero : ∀z,radial.keep z→z≠0
  nonexceptional : ∀z,radial.keep z→
    ¬FixedInducingRow character fixedModulus
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture) 1 z

namespace NaturalState
variable {Z Bmask bΦ:ℝ}
def width (s:NaturalState Z Bmask bΦ):ℝ := s.rowWidth+s.characterWidth
lemma width_nonneg (s:NaturalState Z Bmask bΦ):0≤ s.width :=
  add_nonneg s.row_nonneg s.character_nonneg

def mask (s:NaturalState Z Bmask bΦ):O :=
  fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture

def plainEnergy (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):ℝ :=
  energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
    X₁ X₂ s.radial.keep s.radial.profile s.radial.scale

lemma plainEnergy_eq_zero (s:NaturalState Z Bmask bΦ) {a b:ℝ} (p:Profiles a b)
    (t X₁ X₂:ℝ):
    s.plainEnergy p t X₁ X₂=CenteredMomentCoreFloor.zeroEnergy s.character s.mask 1 t
      (p.profile 0) (p.profile 1) X₁ X₂ s.radial :=
  (CenteredMomentCoreFloor.zero_energy_eq _ _ _ _ _ _ _ _ _).symm

lemma radical_bound (s:NaturalState Z Bmask bΦ):
    (s.puncture.radical.absNorm:ℝ)≤Z^Bmask :=by
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=s.puncture))))
end NaturalState

def ZeroBound (Q:Ideal O) (a b bΦ Bmask M ε:ℝ)(degree:ℕ)(S:Finset (ℕ×ℕ))(C Z₀:ℝ):Prop :=
  ∀Z:ℝ,Z₀≤Z→∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→
    s.plainEnergy p t X₁ X₂≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree*
        Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ChildState -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyChildState
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentEnergyState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

lemma ball_support : Function.support (ballProfile:ℝ→ℂ)⊆Set.Iic (2:ℝ):=by
  intro x hx
  by_cases h:0≤x
  · exact (CenteredMomentAmplifiedRetainedRadius.ballProfile_support_upper x h hx).le
  · exact (lt_of_not_ge h).le.trans (by norm_num)

lemma canonical_mask_nonexceptional (τ:Character)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬CenteredExceptionalProfile.FixedInducingRow τ Q
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)

def canonicalState (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)):NaturalState Z Bmask 2 where
  character:=τ
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=>hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

lemma canonicalState_width (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power (Z Bmask:ℝ)(hZ:1<Z)(τ:Character)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring

lemma common_puncture_bound (Z Bmask Bsource:ℝ)(hZ:0<Z)(R C:Ideal O)
    (hR:(R.absNorm:ℝ)≤Z^Bmask)(hC:(C.absNorm:ℝ)≤Z^Bsource):
    ((R*C).absNorm:ℝ)≤Z^(Bmask+Bsource):=by
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hR hC (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

section Actual
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)

include hne in

lemma actual_dyad_ge_one : 1≤dyadicScale (n 1):=by
  obtain ⟨z,_,hz,hz0,_⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U
    radius rows W K n hne
  exact (normValue_ge_one z hz0).trans (dyadicRows_norm rows n z hz).2.le

def actualState (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):NaturalState Z Bmask 2:=
  canonicalState Z Bmask hZ (τ χ) Q R hR hRN n
    (actual_dyad_ge_one t S β radius rows W K n hne)

include h hK in

theorem actualState_width (Z Bmask:ℝ)(hZ:1<Z)(χ:RayCharacter)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask):
    (actualState (τ:=τ) t S β radius rows W K n hne Z Bmask hZ χ Q R hR hRN).width≤
      Real.logb Z radius+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+
        Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)):=by
  exact dyadic_log_budget h t S β radius rows W K hK n hne Z hZ χ

end Actual
end SevenEighths.CenteredMomentEnergyChildState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.Floor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyState
open HeckeFamily CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

theorem exists_zero_floor (a b bΦ Bmask ε:ℝ)(ha:0<a)(hb:0≤b)
    (hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀Q:Ideal HeckeFamily.O,ZeroBound Q a b bΦ Bmask (ε/16) ε degree S C 1:=by
  let e:ℝ:=ε/(4*(Bmask+1))
  have he:0<e:=div_pos hε (by positivity)
  have hbudget:e*Bmask+4*(ε/16)≤ε:=by
    have hcost:e*Bmask≤ε/4:=by
      have hinc:Bmask≤Bmask+1:=by linarith
      have hh:=mul_le_mul_of_nonneg_left hinc he.le
      have hid:e*(Bmask+1)=ε/4:=by dsimp [e];field_simp
      rw [hid] at hh
      exact hh
    linarith
  obtain ⟨degree,S,C,hC,hfloor⟩:=natural_masked_floor a b e ha hb he
  refine ⟨degree,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro Q Z hZ₀ s hQ hs p t X₁ X₂ hX₁ hX₂
  have hZ:=s.base_ge_one
  have hZ0:0<Z:=zero_lt_one.trans_le hZ
  have hrad: (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e):=by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hp:Z^(Bmask*e)*Z^(s.width+4*(ε/16))≤Z^(s.width+ε):=by
    rw [←Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hh:=hfloor (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
    s.character s.fixedModulus s.puncture s.radial bΦ s.puncture_ne_zero hbΦ.le
    s.radial_support s.row_ne_zero s.nonexceptional Z s.rowWidth s.characterWidth
    (ε/16) t X₁ X₂ hZ s.row_nonneg s.character_nonneg s.scale_eq hs hX₁ hX₂ s.modulus_bound
  rw [s.plainEnergy_eq_zero]
  change CenteredMomentCoreFloor.zeroEnergy _ _ _ _ _ _ _ _ _≤_
  apply hh.trans
  have hd:=diagonalControl_nonneg s.radial.profile
  have hc:=p.control_nonneg S
  change C*(s.puncture.radical.absNorm:ℝ)^e*bΦ^4*diagonalControl s.radial.profile*
    (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16))≤_
  calc
    _≤C*Z^(Bmask*e)*bΦ^4*diagonalControl s.radial.profile*
      (p.control S)^2*(1+‖t‖)^degree*Z^(s.width+4*(ε/16)):=by gcongr
    _=(C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+‖t‖)^degree)*
      (Z^(Bmask*e)*Z^(s.width+4*(ε/16))):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentEnergyState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.OriginalSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyOriginalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleMask
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentHeckeHeight
open CenteredMomentDivisorRowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRectangleEnergy
open CenteredMomentPositiveSummability CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance energyOriginalSourceDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def completeInput (s : Data ι) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hν : ∀i I,‖s.ν i I‖≤1) (hW : ∀i x,‖s.W i x‖≤ s.M i)
    (lo hi : ℝ) (hlo : 0<lo) (hl : ∀i,lo≤ s.lo i) (hh : ∀i,s.hi i≤hi) : Input ι where
  toData := s
  plain₁ := plainSupportPool s.b₁ s.X₁ s.Y₁
  plain₂ := plainSupportPool s.b₂ s.X₂ s.Y₂
  plain₁_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  plain₂_ne := by
    intro I hI
    rcases Finset.mem_union.mp hI with hI|hI
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
    · exact (CenteredMomentSourceMass.mem_idealBall _ _).mp hI |>.1
  coverage₁ := plainSupportPool_coverage s.W₁ s.b₁ s.X₁ s.Y₁ hz₁ s.support₁ s.X₁_pos s.Y₁_pos
  coverage₂ := plainSupportPool_coverage s.W₂ s.b₂ s.X₂ s.Y₂ hz₂ s.support₂ s.X₂_pos s.Y₂_pos
  ν_bound := hν
  W_bound := hW
  lower := lo
  upper := hi
  lower_pos := hlo
  lower_le := hl
  upper_ge := hh

omit [DecidableEq ι] in
lemma input_tuplePool (s : Input ι) :
    Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
  ext v
  simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]

lemma input_polynomial_difference (s : Input ι) (R : Ideal O) (z : O) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I)=
    (rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.X₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.X₂-
     rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t s.Y₁*
      rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₂ s.t s.Y₂)*
        ∏i,rowSlot s.η (fixedBadMask*idealGenerator R) 1 z (s.slots i)
          (s.toData.coefficient i) s.t := by
  unfold coefficient
  rw [input_tuplePool]
  rw [source_polynomial_eq_maskedRectangle s.η fixedBadMask 1 z s.t
    (dvd_mul_right _ _) (dvd_mul_left _ _) s.slots s.plain₁ s.plain₂ R 1
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 s.coverage₁ s.coverage₂]
  simp only [map_one,Nat.cast_one,div_one,maskedRectangle,one_dvd,ite_true,one_mul]
  exact actual_slot_rectangle_sum s.η (fixedBadMask*idealGenerator R) 1 z s.slots
    s.toData.coefficient s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos

lemma normalized_input_difference (s : Input ι) (R : Ideal O) (z : O) :
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.X₁ s.X₂-
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂=
    (Real.sqrt (CenteredMomentAmplificationChildInput.volume s):ℂ)⁻¹*
      ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I := by
  rw [input_polynomial_difference]
  unfold positiveSlotRow CenteredMomentAmplificationChildInput.volume
  rw [s.same_product]
  ring

omit [DecidableEq ι] in
lemma input_energy_hasSum (s : Input ι) (R : Ideal O) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O=>
      ‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
        rowWeight s.η fixedBadMask 1 z s.t I‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R 1) Φ K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable Finset.univ
    (sourceGenerator (finiteColumns (Fintype.piFinset s.pools))) (sourceGenerator_supported _)
    (fun I=>coefficient s R 1 I*rowWeight s.η fixedBadMask 1 1 s.t I) Φ K hK).hasSum
  change HasSum _ (rowEnergy _ _ _ Φ K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  simpa only [finiteHeckeEnergy_eq s.η fixedBadMask 1 s.t (dvd_mul_right _ _) (dvd_mul_left _ _),
    finite_hecke_sum_eq_rowPolynomial s.η fixedBadMask 1 _ s.t (dvd_mul_right _ _) (dvd_mul_left _ _)] using hs

theorem kept_difference_energy (s : Input ι) (R : Ideal O)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑'z : O,if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂-
        positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
        (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)=
      CenteredMomentRestrictedSource.sourceRestrictedEnergy keep
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1)
        (CenteredMomentHeckeColumnWindow.heightCoeff s.η s.t) Φ K /
          CenteredMomentAmplificationChildInput.volume s := by
  unfold CenteredMomentRestrictedSource.sourceRestrictedEnergy
    CenteredMomentRestrictedEnergy.restrictedEnergy
  rw [←tsum_div_const]
  apply tsum_congr
  intro z
  rw [height_source_row]
  by_cases hk : keep z
  · rw [ite_eq_left hk,ite_eq_left hk,normalized_input_difference,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _
        (CenteredMomentAmplificationChildInput.volume_pos s)]
    ring
  · simp only [ite_eq_right hk,zero_div]

omit [DecidableEq ι] in
lemma input_positive_summable (s : Input ι) (R : Ideal O) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K X₁ X₂ : ℝ) (hK : 0<K) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    Summable (fun z : O=>if keep z then
      ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t X₁ X₂‖^2*
          (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB⟩ := product_bounded s.η (fixedBadMask*idealGenerator R) 1 s.t
    (Real.sqrt (X₁*X₂*∏i,s.P i):ℂ)⁻¹ s.W₁ s.W₂ s.b₁ s.b₂ X₁ X₂
    s.support₁ s.support₂ hX₁ hX₂ s.slots s.toData.coefficient
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem positive_energy_comparison (s : Input ι) (R : Ideal O)
    (r : CenteredMomentRadialEligibleEnergy.Radial) :
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R 1) r.profile r.scale‖ / CenteredMomentAmplificationChildInput.volume s+
    2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
      s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale := by
  let V := CenteredMomentAmplificationChildInput.volume s
  have hV : 0<V := CenteredMomentAmplificationChildInput.volume_pos s
  let f : O→ℝ := fun z=>
    (‖∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s R 1 I*
      rowWeight s.η fixedBadMask 1 z s.t I‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re)/V
  let g : O→ℝ := fun z=>if r.keep z then
    ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t s.Y₁ s.Y₂‖^2*
      (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0
  have hf := (input_energy_hasSum s R r.profile r.scale r.scale_pos).div_const V
  have hg := input_positive_summable s R r.keep r.profile r.scale s.Y₁ s.Y₂
    r.scale_pos s.Y₁_pos s.Y₂_pos
  have hfn (z : O) : 0≤f z := div_nonneg (mul_nonneg (sq_nonneg _) (r.nonneg z)) hV.le
  have hgn (z : O) : 0≤g z := by
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl
  unfold CenteredMomentInductionEnergy.energy
  apply Real.tsum_le_of_sum_le (fun z=>by
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (r.nonneg z)
    · rfl)
  intro rows
  have hp (z : O) :
      (if r.keep z then
        ‖positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
          s.toData.coefficient s.P s.t s.X₁ s.X₂‖^2*
          (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0) ≤ 2*f z+2*g z := by
    by_cases hk : r.keep z
    · let x := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.X₁ s.X₂
      let y := positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
        s.toData.coefficient s.P s.t s.Y₁ s.Y₂
      have hn : ‖x‖≤‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
      have hsq : ‖x‖^2≤2*‖x-y‖^2+2*‖y‖^2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg x) hn 2
        nlinarith [sq_nonneg (‖x-y‖-‖y‖)]
      dsimp only [x,y] at hsq
      rw [normalized_input_difference,CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hV] at hsq
      have hh := mul_le_mul_of_nonneg_right hsq (r.nonneg z)
      dsimp only [f,g]
      rw [ite_eq_left hk,ite_eq_left hk]
      convert hh using 1 ; ring
    · rw [ite_eq_right hk]
      exact add_nonneg (mul_nonneg (by norm_num) (hfn z)) (mul_nonneg (by norm_num) (hgn z))
  have hb := Finset.sum_le_sum (fun z (_:z∈rows)=>hp z)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hb
  have hs := sum_le_hasSum rows (fun z _=>hfn z) hf
  have ht := sum_le_hasSum rows (fun z _=>hgn z) hg.hasSum
  have he := div_le_div_of_nonneg_right
    (Complex.re_le_norm (finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale)) hV.le
  change ∑z∈rows,f z≤_ at hs
  change ∑z∈rows,g z≤∑'z,g z at ht
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/V+2*∑'z,g z
  rw [mul_div_assoc]
  linarith

section Natural
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
variable {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0<a)
variable (S : ι→Finset (Ideal O)) (hp : ∀i,∀I∈S i,Prime I)
variable (ν : ι→Character) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
variable (hP : ∀i,0<P i) (hM : ∀i,1≤M i)
variable (aslot bslot : ℝ) (haslot : 0<aslot)
variable (hsSlot : ∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
variable (hWslot : ∀i x,‖Wslot i x‖≤M i)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hsame : Y₁*Y₂=X₁*X₂)

def naturalData : Data ι where
  η := state.character
  m := state.mask
  A := 1
  t := t
  slots := S
  prime := hp
  ν := fun i=>idealCoeff (ν i)
  W := Wslot
  lo := fun _=>aslot
  hi := fun _=>bslot
  P := P
  lo_pos := fun _=>haslot
  P_pos := hP
  support := hsSlot
  W₁ := p.profile 0
  W₂ := p.profile 1
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  M := M
  M_ge_one := hM
  coefficient_bound := fun i I _=>by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one (ν i) I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hWslot i ((Ideal.absNorm I:ℝ)/P i))
  b₁ := b
  b₂ := b
  support₁ := fun x hx=>(p.support 0 hx).2
  support₂ := fun x hx=>(p.support 1 hx).2
  X₁_pos := hX₁
  X₂_pos := hX₂
  Y₁_pos := hY₁
  Y₂_pos := hY₂
  same_product := hsame
  rows := ∅
  weight := fun _=>0
  weight_nonneg := fun _ _=>le_refl _

def naturalInput : Input ι :=
  completeInput (naturalData state p S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame)
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 0) a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 1) a b ha (p.support 1))
    (fun i I=>idealCoeff_norm_le_one (ν i) I) hWslot aslot bslot haslot
    (fun _=>le_refl _) (fun _=>le_refl _)

theorem natural_energy_comparison :
    let inp := naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale ≤
    2*‖finiteHeckeEnergy state.character fixedBadMask 1 t
      (finiteColumns (Fintype.piFinset inp.pools)) (coefficient inp state.puncture 1)
      state.radial.profile state.radial.scale‖/(X₁*X₂*∏i,P i)+
    2*CenteredMomentInductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale :=
  positive_energy_comparison
    (naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) state.puncture state.radial

end Natural
end SevenEighths.CenteredMomentEnergyOriginalSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FixedRadialSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyFixedRadialSource
open HeckeFamily CenteredMomentSourceRow CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

lemma norm_le_diagonalControl (Φ:𝓢(ℝ,ℂ))(x:ℝ):‖Φ x‖≤diagonalControl Φ:=by
  have hs:SchwartzMap.seminorm ℝ 0 0 Φ≤
      (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    exact Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (by simp : (0,0)∈Finset.Iic (2,0))) Φ
  apply (SchwartzMap.norm_le_seminorm ℝ Φ x).trans
  apply hs.trans
  unfold diagonalControl
  exact le_mul_of_one_le_left (by positivity) (by nlinarith [Real.pi_nonneg])

theorem exists_fixed_bump (b:ℝ)(_hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ (∀x,(Ψ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) b,Ψ x=1):=by
  have hsub:Set.Icc (0:ℝ) b⊆Set.Ioo (-1) (b+1):=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) (b+1):=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  let Ψ:𝓢(ℝ,ℂ):=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).toSchwartzMap hv
  refine ⟨Ψ,hsupp,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem finite_energy_domination (b:ℝ)(Ψ:𝓢(ℝ,ℂ))
    (hΨ:∀x,0≤(Ψ x).re)(hone:∀x∈Set.Icc (0:ℝ) b,Ψ x=1)
    (Φ:𝓢(ℝ,ℂ))(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic b)
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (K:ℝ)(hK:0<K):
    ‖finiteHeckeEnergy η m A t S c Φ K‖≤
      diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  have hΦ:∀x:ℝ,0≤x→‖Φ x‖≤diagonalControl Φ*(Ψ x).re:=by
    intro x hx
    by_cases h:Φ x=0
    · rw [h,norm_zero]
      exact mul_nonneg (diagonalControl_nonneg Φ) (hΨ x)
    · rw [hone x ⟨hx,hs h⟩,Complex.one_re,mul_one]
      exact norm_le_diagonalControl Φ x
  have hsumΦ:=finite_hecke_energy_summable η m A t S c Φ K hK
  have hsumΨ:=finite_hecke_energy_summable η m A t S c Ψ K hK
  have hre:HasSum (fun z:O=>‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy η m A t S c Ψ K).re:=by
    have hh:=Complex.hasSum_re hsumΨ.hasSum
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      finiteHeckeEnergy] using hh
  calc
    _≤∑'z:O,‖((‖∑I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)‖:=norm_tsum_le_tsum_norm hsumΦ.norm
    _≤∑'z:O,diagonalControl Φ*(‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re):=by
      apply hsumΦ.norm.tsum_le_tsum _ (hre.summable.mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hΦ _ (by positivity)) (sq_nonneg _)).trans_eq (by ring)
    _=diagonalControl Φ*(finiteHeckeEnergy η m A t S c Ψ K).re:=by
      rw [tsum_mul_left,hre.tsum_eq]
    _≤_:=mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ)

theorem fixed_source (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic b→
      ∀(η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)(K:ℝ),0<K→
      ‖finiteHeckeEnergy η m A t S c Φ K‖≤
        diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  obtain ⟨Ψ,hs,hn,_,hone⟩:=exists_fixed_bump b hb
  exact ⟨Ψ,hs,hn,fun Φ hΦ η m A t S c K hK=>finite_energy_domination b Ψ hn hone Φ hΦ η m A t S c K hK⟩

end SevenEighths.CenteredMomentEnergyFixedRadialSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.PhysicalEntry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPhysicalEntry
open HeckeFamily CenteredMomentEnergyOriginalSource CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentExceptionalAmplitudePair
open CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance physicalEntryDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem positive_first_physical_entry (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(R:Ideal O)(r:CenteredMomentRadialEligibleEnergy.Radial),
      volume s.toData≤Z^B→(r.scale)⁻¹≤Z^B→
      energy s.η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*physicalMass s R 1 fixedBadMask 1 r.profile r.scale Z ξ/volume s.toData+
      2*Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*r.scale*Z^ε+
      2*Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*r.scale*Z^(-saving)+
      2*energy s.η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale:=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,h⟩:=
    original_first_physical_reduction hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi R r hV hK
  have hh:=hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi fixedBadMask 1
    (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 r.profile r.scale r.scale_pos hV hK
  have hc:=positive_energy_comparison s R r
  change _≤2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.profile r.scale‖/
      volume s.toData+_ at hc
  rw [mul_div_assoc] at hc ⊢
  linarith

lemma natural_inverse_scale {Z Bmask bΦ:ℝ} (state:NaturalState Z Bmask bΦ)
    (B:ℝ)(hB:0≤B):state.radial.scale⁻¹≤Z^B:=by
  have hscale:1≤ state.radial.scale:=by
    rw [state.scale_eq]
    exact Real.one_le_rpow state.base_ge_one state.row_nonneg
  exact (inv_le_one_of_one_le₀ hscale).trans (Real.one_le_rpow state.base_ge_one hB)

theorem natural_first_physical_entry (a b bslot B ε ξ saving Bmask bΦ:ℝ)
    (ha:0<a)(hb:0≤b)(hbslot:0≤bslot)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(state:NaturalState Z Bmask bΦ)(p:Profiles a b),
    ∀(slots:ι→Finset (Ideal O))(hp:∀i,∀I∈slots i,Prime I)
      (ν:ι→Character)(Wslot:ι→ℝ→ℂ)(P M:ι→ℝ)
      (hP:∀i,0<P i)(hM:∀i,1≤M i)(aslot:ℝ)(haslot:0<aslot)
      (hsSlot:∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
      (hWslot:∀i x,‖Wslot i x‖≤M i)
      (t X₁ X₂ Y₁ Y₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hY₁:0<Y₁)(hY₂:0<Y₂)
      (hsame:Y₁*Y₂=X₁*X₂),X₁*X₂*(∏i,P i)≤Z^B→
    let inp:=naturalInput state p ha slots hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    energy state.character state.mask 1 t (p.profile 0) (p.profile 1) slots
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale≤
    2*physicalMass inp state.puncture 1 fixedBadMask 1 state.radial.profile state.radial.scale Z ξ/
      (X₁*X₂*∏i,P i)+
    2*Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
      Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) state.radial.profile*state.radial.scale*Z^ε+
    2*Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
      Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) state.radial.profile*state.radial.scale*Z^(-saving)+
    2*energy state.character state.mask 1 t (p.profile 0) (p.profile 1) slots
      (fun i I=>idealCoeff (ν i) I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale:=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,h⟩:=positive_first_physical_entry (ι:=ι)
    (fun _=>bslot) a b B ε ξ saving (fun _=>hbslot) ha hb hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro state p slots hp ν Wslot P M hP hM aslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame hV
  exact hZ.2 (naturalInput state p ha slots hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) (p.profile 0) (p.profile 1) rfl rfl
    (p.support 0) (p.support 1) (fun _=>le_refl _) state.puncture state.radial hV
    (natural_inverse_scale state B hB)

end SevenEighths.CenteredMomentEnergyPhysicalEntry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceState -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceState
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

def effectiveRadial (r:Radial):Radial:=
  {r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}

lemma radialEnergy_effective (r:Radial)(f:O→ℂ):
    radialEnergy f (effectiveRadial r).keep r.profile r.scale=
      radialEnergy f r.keep r.profile r.scale:=by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hz:r.profile (‖eisEmbedding z‖^2/r.scale)=0 <;>
    simp [effectiveRadial,hk,hz]

def effectiveState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z Bmask bΦ:=
  {s with radial:=effectiveRadial s.radial
          row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
          nonexceptional:=fun z hz=>s.nonexceptional z hz.1}

lemma effective_row_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^s.rowWidth:=by
  rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
  exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hz.2)

lemma effective_character_nonprincipal {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    (naturalCharacter s.character z).residue≠1:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  exact (naturalRow s.character z hn).nonprincipal hn s.fixedModulus s.puncture
    s.puncture_ne_zero (s.nonexceptional z hz.1)

lemma effective_character_cap {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hbΦ:0≤bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*bΦ*Z^s.width:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  have h:=(naturalRow s.character z hn).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans_le s.base_ge_one) hbΦ s.modulus_bound (effective_row_norm s z hz)
  simpa only [NaturalState.width,add_comm s.characterWidth s.rowWidth] using h

def comparisonFirst (Z M:ℝ):ℝ:=Z^(M/4)
def comparisonSecond (Z M X₁ X₂:ℝ):ℝ:=X₁*X₂/comparisonFirst Z M

lemma comparison_positive (Z M X₁ X₂:ℝ)(hZ:0<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    0<comparisonFirst Z M ∧ 0<comparisonSecond Z M X₁ X₂:=
  ⟨Real.rpow_pos_of_pos hZ _,div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos hZ _)⟩

lemma comparison_same_product (Z M X₁ X₂:ℝ)(hZ:0<Z):
    comparisonFirst Z M*comparisonSecond Z M X₁ X₂=X₁*X₂:=by
  unfold comparisonSecond
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hZ (M/4)).ne'

lemma comparison_second_power (Z M X₁ X₂:ℝ)(hZ:1<Z)(hX₁:0<X₁)(hX₂:0<X₂):
    comparisonSecond Z M X₁ X₂=Z^(Real.logb Z (X₁*X₂)-M/4):=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos hX₁ hX₂)]
  rfl

theorem balanced_reference_geometry (Z M X₁ X₂ ell κ:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M):
    ell≤M/21 ∧
    1≤ comparisonFirst Z M ∧
    comparisonFirst Z M≤ comparisonSecond Z M X₁ X₂ ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4 ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)≤M:=by
  have hkell:7/2*ell≤(6*κ-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  have he:ell≤M/21:=by linarith
  have hlen:M/2≤Real.logb Z (X₁*X₂):=by linarith
  have hupper:Real.logb Z (X₁*X₂)-M/4≤M:=by linarith
  have hlog:Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4:=by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,Real.logb_rpow]
    · exact zero_lt_one.trans hZ
    · exact hZ.ne'
  refine ⟨he,Real.one_le_rpow hZ.le (by linarith),?_,hlog,by rw [hlog];exact hupper⟩
  rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem balanced_reflection_margins (Z M X₁ X₂ ell κ ξ reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤M)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+ξ):
    reflected+M/4+ell≤23*M/30+ξ ∧
    reflected+M/4+ell+(6*κ-1)*ell≤14*M/15+ξ:=by
  have hlog:=(balanced_reference_geometry Z M X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hlarge hcap).2.2.2.1
  rw [hlog] at href
  have hc:=CenteredMomentReflectionRetainedLength.positive_slot_width_drop M
    (Real.logb Z (X₁*X₂)+ell) ell ξ κ hM hell hκ hlarge hcap
  constructor <;> linarith [hc.1,hc.2]

end SevenEighths.CenteredMomentEnergyReferenceState

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=>HeckeFamily.O

lemma conductorFactor_pos : 0<(fixedConductorFactor:ℝ):=by
  unfold fixedConductorFactor
  norm_cast
  apply Nat.mul_pos
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero))
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))

theorem natural_reference_reflection (a b bΦ epsilon xi saving L:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B J:ℕ)(hB:2≤B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→Finset (Ideal O))
        (β:α→Ideal O→ℂ)(P:α→ℝ)(t along bshort E:ℝ),
      s.width≤L+along → 0≤E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,S,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P t along bshort E hlength hE hchildren
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(1+S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=by dsimp [Src];positivity
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=by
    apply (hprofile Wlong hsLong t).trans
    dsimp [Src]
    gcongr
    linarith
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=>G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=>t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=>hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=>hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceDivisors
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyReferenceState
local notation "O"=>HeckeFamily.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1<Z)(hY:0<Y)(hN:0<N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(L Y:ℝ)(hwidth:s.width≤L)(hY:1≤Y)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

theorem balanced_divisor_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(L X₁ X₂ ell κ:ℝ)(hwidth:s.width≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hlarge:5*s.width/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ)
    let long:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    -Bmask≤ short ∧ -Bmask≤long ∧ s.width≤(L+Bmask)+long ∧
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^long=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hfirst:Real.logb Z (comparisonFirst Z s.width)=s.width/4:=by
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hs:=divisor_reflection_range s hZ L (comparisonFirst Z s.width) hwidth hg.2.1 D₁ hD₁
  have hl:=divisor_reflection_range s hZ L (comparisonSecond Z s.width X₁ X₂) hwidth
    (hg.2.1.trans hg.2.2.1) D₂ hD₂
  dsimp only at hs hl ⊢
  rw [hfirst] at hs
  rw [hg.2.2.2.1] at hl
  exact ⟨hs.1,hl.1,hl.2.1,hs.2.2,hl.2.2⟩

end SevenEighths.CenteredMomentEnergyReferenceDivisors

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneous -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceHomogeneous
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceReflection CenteredMomentFiniteProfileExceptional

theorem natural_reference_reflection_homogeneous (a b bΦ epsilon xi saving L:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (B J:ℕ)(hB:2≤B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→Finset (Ideal O))
        (β:α→Ideal O→ℂ)(P:α→ℝ)(t along bshort E:ℝ),
      s.width≤L+along → 0≤E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 t *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖t‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P t along bshort E hlength hE hchildren
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,summand,radialEnergy]
  have hpos:0<sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖t‖)^n
  have hSrc:0<Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤ sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤Src:=
    (hprofile Wlong hsLong t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=>G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=>t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=>hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=>hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) t:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong t] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖t‖)^(2*n)=((1+‖t‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceHomogeneous

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneousError -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceHomogeneousError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalReflectionErrorMass CenteredMomentNaturalFixedRaySource
open CenteredMomentOriginalRadialComparison CenteredMomentUniformReflectionProfile
open CenteredMomentCounting CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem natural_remaining_homogeneous_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort 1 b M*Bshort^2*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (hM j (hT hj)) (hP j hj) (hβ j hj) (hs j hj)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc₀ : (128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hT (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    unfold errorConstant
    simp only [mul_one]
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M*Bshort^2 := by
    calc
      _=((128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*Bshort^2:=by ring
      _≤_:=mul_le_mul_of_nonneg_right hc₀ (sq_nonneg Bshort)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ (errorConstant F bshort 1 b M*Bshort^2)*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
    _ = _ := by ring

theorem natural_reference_error_homogeneous {α:Type*}(F:Finset α)(bshort:ℝ)(b M:α→ℝ)
    (hM:∀i∈F,0≤M i):
    ∃C:ℝ,0<C ∧ ∀(T:Finset α),T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→Character)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) →
      (∀i∈T,∀I∈pool i,Prime I) →
      (∀i∈T,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈T,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  refine ⟨errorConstant F bshort 1 b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT W hsW χ pool β P t X K Φ keep hX hK hP hp hβ hs hΦ
  let A:=(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W
  have hA:0≤A:=apply_nonneg _ _
  have hWA:∀x,‖W x‖≤A:=SchwartzMap.norm_le_seminorm ℝ W
  let R:=fun z:O=>polynomial (χ z) false W X 0 t *
    ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)
  let V:=errorConstant F bshort 1 b M*A^2*X*∏i∈T,P i
  have hV:0≤V:=by
    dsimp only [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg (errorConstant_pos F bshort 1 b M).le
      (sq_nonneg A)) hX.le) (Finset.prod_nonneg (fun i hi=>(hP i hi).le))
  have hr(z:O):‖R z‖^2≤V:=by
    have hh:=natural_remaining_homogeneous_bound F T hT W bshort A b M hA hM hWA hsW
      (χ z) pool (fun i=>heightCoefficient (β i) t) P X t hX hP
      (fun i hi I hI=>by rw [heightCoefficient_norm _ _ _ (hp i hi I hI).ne_zero];exact hβ i hi I hI)
      (fun i hi I hI hn=>hs i hi I hI (left_ne_zero_of_mul hn))
    exact hh
  have hsum:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
  apply (radialEnergy_le_absolute_mass R keep Φ K hΦ hsum).trans
  calc
    _≤∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*V:=hsum.tsum_le_tsum
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
    _=(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=tsum_mul_right
    _≤(diagonalControl Φ*max 1 K)*V:=mul_le_mul_of_nonneg_right
      (radial_weight_lattice_bound_all Φ K hK) hV
    _=_:=by dsimp [V,A];ring

end SevenEighths.CenteredMomentEnergyReferenceHomogeneousError

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceScalarBounds -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarBounds
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource

lemma radical_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(d:ℝ)(hd:0≤d):
    (s.puncture.radical.absNorm:ℝ)^d≤Z^(Bmask*d):=by
  have hh:=Real.rpow_le_rpow (Nat.cast_nonneg _) s.radical_bound hd
  simpa only [←Real.rpow_mul (zero_lt_one.trans_le s.base_ge_one).le] using hh

lemma conductor_power {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap d:ℝ)(hs:s.width≤Mcap)(hd:0≤d):
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))^d*Z^(Mcap*d):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hM:0≤Mcap:=s.width_nonneg.trans hs
  have hz:1≤Z^Mcap:=Real.one_le_rpow s.base_ge_one hM
  have hc:1≤ max 1 ((fixedConductorFactor:ℝ)*bΦ):=le_max_left _ _
  have hbase:max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width)≤
      (max 1 ((fixedConductorFactor:ℝ)*bΦ))*Z^Mcap:=by
    apply max_le
    · nlinarith
    · apply le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hs)
        (zero_le_one.trans hc)
  have hh:=Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase hd
  rw [Real.mul_rpow (zero_le_one.trans hc) (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le] at hh
  exact hh

lemma radial_scale {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    max 1 s.radial.scale≤Z^s.width:=by
  rw [s.scale_eq]
  apply max_le (Real.one_le_rpow s.base_ge_one s.width_nonneg)
  apply Real.rpow_le_rpow_of_exponent_le s.base_ge_one
  exact le_add_of_nonneg_right s.character_nonneg

lemma physical_slot_product {α:Type*}[Fintype α](Z:ℝ)(hZ:1≤Z)(w:α→ℝ)(Mcap:ℝ)
    (hwidth:(∑i,w i)≤Mcap): (∏i,Z^(w i))≤Z^Mcap:=by
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans_le hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ hwidth

lemma short_slot_mass {α:Type*}[Fintype α]{Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (Mcap:ℝ)(hs:s.width≤Mcap)(w:α→ℝ)(hwidth:(∑i,w i)≤Mcap):
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))≤Z^(s.width+5*Mcap/4):=by
  have hz:0<Z:=zero_lt_one.trans_le s.base_ge_one
  calc
    _≤Z^s.width*Z^(Mcap/4)*Z^Mcap:=by
      apply mul_le_mul (mul_le_mul (radial_scale s)
        (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
        (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (physical_slot_product Z s.base_ge_one w Mcap hwidth)
        (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg hz.le _)) (by positivity)
    _=Z^(s.width+5*Mcap/4):=by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

lemma log_interval (Z L d:ℝ)(hZ:1≤Z)(hL:0≤L)(hd:0<d):
    1+2*(L*Real.log Z)≤(1+2*L/d)*Z^d:=by
  have hlog:=Real.log_le_rpow_div (zero_le_one.trans hZ) hd
  have hone:=Real.one_le_rpow hZ hd.le
  have hh:=mul_le_mul_of_nonneg_left hlog (show 0≤2*L by positivity)
  calc
    _≤Z^d+2*L*(Z^d/d):=by nlinarith
    _=(1+2*L/d)*Z^d:=by ring

end SevenEighths.CenteredMomentEnergyReferenceScalarBounds

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceScalarReserve
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarBounds

theorem ledger_bound (Mcap Bmask bΦ L d saving ε:ℝ)
    (hM:0≤Mcap)(_hB:0≤Bmask)(hL:0≤L)(hd:0<d)
    (hmain:d*(Bmask+Mcap+2)≤ε)
    (herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε):
    ∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let A:ℝ:=max 1 ((fixedConductorFactor:ℝ)*bΦ)
  let B:ℝ:=1+2*L/d
  have hA:0<A:=zero_lt_one.trans_le (le_max_left _ _)
  have hBpos:0<B:=by dsimp only [B];positivity
  refine ⟨1+A^d*B+A^(2*d),by positivity,?_⟩
  intro Z hZ s hs α inst w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hr:=radical_power s d hd.le
  have hc:=conductor_power s Mcap d hs hd.le
  have hc₂:=conductor_power s Mcap (2*d) hs (by positivity)
  have hl:=log_interval Z L d hZ hL hd
  have hm:=short_slot_mass s Mcap hs w hw
  have hdirect:(s.puncture.radical.absNorm:ℝ)^d*Z^(s.width+d)≤Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*Z^(s.width+d):=mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hz.le _)
      _=Z^(s.width+d*(Bmask+1)):=by rw [←Real.rpow_add hz];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)
  have hreflect:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
        (1+2*(L*Real.log Z))*Z^(s.width+d))≤A^d*B*Z^(s.width+ε):=by
    calc
      _≤Z^(Bmask*d)*(A^d*Z^(Mcap*d)*(B*Z^d)*Z^(s.width+d)):=by
        gcongr
      _=A^d*B*Z^(s.width+d*(Bmask+Mcap+2)):=by
        calc
          _=A^d*B*(Z^(Bmask*d)*Z^(Mcap*d)*Z^d*Z^(s.width+d)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 2;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  have herrorTerm:(s.puncture.radical.absNorm:ℝ)^d*
      ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
        max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤A^(2*d)*Z^(s.width+ε):=by
    calc
      _=(s.puncture.radical.absNorm:ℝ)^d*
        ((max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          (max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))):=by ring
      _≤Z^(Bmask*d)*(A^(2*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by
        gcongr
      _=A^(2*d)*Z^(s.width+(Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4)):=by
        calc
          _=A^(2*d)*(Z^(Bmask*d)*Z^(Mcap*(2*d))*Z^(-2*saving)*Z^(s.width+5*Mcap/4)):=by ring
          _=_:=by simp only [←Real.rpow_add hz];congr 1;congr 1;ring
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)
  calc
    _≤Z^(s.width+ε)+A^d*B*Z^(s.width+ε)+A^(2*d)*Z^(s.width+ε):=by
      simpa only [mul_add] using add_le_add (add_le_add hdirect hreflect) herrorTerm
    _=_:=by ring

theorem exists_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0< rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*
        (Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
           (1+2*(L*Real.log Z))*Z^(s.width+d)+
         (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
           max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))) ≤C*Z^(s.width+ε):=by
  let d:=ε/(4*(Bmask+Mcap+2))
  let xi:=rho/100
  let saving:=2*Mcap+Bmask*d+2*Mcap*d+1
  let L:=Mcap+Bmask+xi+1
  have hd:0<d:=by dsimp only [d];positivity
  have hxi:0<xi:=by dsimp only [xi];positivity
  have hsave:0<saving:=by dsimp only [saving];positivity
  have hL:0≤L:=by dsimp only [L];positivity
  have hmain:d*(Bmask+Mcap+2)≤ε:=by
    dsimp only [d]
    have hp:0<Bmask+Mcap+2:=by positivity
    field_simp
    nlinarith
  have herror:Bmask*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε:=by
    dsimp only [saving]
    nlinarith [mul_nonneg hB hd.le,mul_nonneg hM hd.le]
  obtain ⟨C,hC,hledger⟩:=ledger_bound Mcap Bmask bΦ L d saving ε hM hB hL hd hmain herror
  exact ⟨d,xi,saving,L,C,hd,hxi,hsave,hC,le_rfl,by dsimp only [L];linarith,hledger⟩

end SevenEighths.CenteredMomentEnergyReferenceScalarReserve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceSource
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def signedCommonSource {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(z:O):ℂ:=
  let χ:=naturalCharacter s.character z
  let R:=CompletedGauss.primeSupport s.puncture
  ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈(Finset.univ:Finset α).powerset,
    signedCoefficient χ R D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
      (polynomial χ false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
       polynomial χ false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
       ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i))

lemma original_row_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(z:O)(hz:z≠0):
    positiveSlotRow s.character s.mask 1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=by
  have hh:=original_positive_deletion s.character z hz s.puncture s.puncture_ne_zero
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool hp β P hP t X₁ X₂ hX₁ hX₂
  dsimp only at hh
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t] at hh
  simpa only [NaturalState.mask,signedCommonSource,naturalCharacter_eq s.character z hz] using hh

theorem original_energy_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale=
    radialEnergy (signedCommonSource s W₁ W₂ pool β P t X₁ X₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  change _=radialEnergy _ (effectiveRadial s.radial).keep _ _
  rw [radialEnergy_effective]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:s.radial.keep z
  · simp only [ite_eq_left hz]
    rw [original_row_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂
      z (s.row_ne_zero z hz),norm_mul,norm_mul,
      positive_height_phase_norm X₁ t hX₁,positive_height_phase_norm X₂ t hX₂,one_mul,one_mul]
  · simp only [ite_eq_right hz]

end SevenEighths.CenteredMomentEnergyReferenceSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceWeightedEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceWeightedEnergy
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison
local notation "O"=>HeckeFamily.O

lemma finite_weighted_energy {ι κ:Type*}[Fintype ι][Fintype κ]
    (a f:ι→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤q j)
    (ha:∀i j,‖a i j‖≤ρ j)(E:ℝ)(hE:0≤E)
    (hf:∀j,∑i,‖f i j‖^2≤E*(q j)^2):
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j*q j)^2*E:=by
  have hb(j:κ):(∑i,‖a i j*f i j‖^2)≤(ρ j*q j*Real.sqrt E)^2:=by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2:=Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2):=(Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*(E*(q j)^2):=mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_:=by rw [mul_pow,Real.sq_sqrt hE];ring
  have hh:=CompletedGauss.finite_tsum_energy_bound (fun j i=>a i j*f i j)
    (fun j=>ρ j*q j*Real.sqrt E) (fun j=>mul_nonneg (mul_nonneg (hρ j) (hq j)) (Real.sqrt_nonneg E))
    (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

theorem radial_weighted_energy {κ:Type*}[Fintype κ]
    (a f:O→κ→ℂ)(ρ q:κ→ℝ)(hρ:∀j,0≤ρ j)(hq:∀j,0≤q j)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K E:ℝ)
    (hΦ:∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re)
    (ha:∀z,keep z→∀j,‖a z j‖≤ρ j)(hE:0≤E)
    (hs:∀j,Summable (fun z:O=>if keep z then ‖f z j‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0))
    (hf:∀j,radialEnergy (fun z=>f z j) keep Φ K≤E*(q j)^2):
    radialEnergy (fun z=>∑j,a z j*f z j) keep Φ K≤(∑j,ρ j*q j)^2*E:=by
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let w(z:S):ℂ:=(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=finite_weighted_energy (fun z:S=>a z) (fun z:S=>fun j=>f z j*w z) ρ q hρ hq
    (fun z=>ha z (Finset.mem_filter.mp z.property).2) E hE ?_
  · have hsum(z:S):(∑j,a z j*(f z j*w z))=(∑j,a z j*f z j)*w z:=by
      rw [Finset.sum_mul];apply Finset.sum_congr rfl;intro j _;ring
    simp_rw [hsum] at hh
    dsimp only [w] at hh
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>∑j,a z j*f z j) Φ K hΦ] at hh
    exact hh
  · intro j
    dsimp only [w]
    rw [CenteredMomentOriginalRadialComparison.finite_weighted rows keep (fun z=>f z j) Φ K hΦ]
    exact ((hs j).sum_le_tsum rows (fun z _=>by
      split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans (hf j)

end SevenEighths.CenteredMomentEnergyReferenceWeightedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceSource CenteredMomentEnergyReferenceWeightedEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonMaskRadialEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem original_energy_weighted_deletion (bslot M:α→ℝ)(hM:∀i,0≤M i)
    (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ a b:ℝ)(s:NaturalState Z Bmask bΦ)
      (W₁ W₂:𝓢(ℝ,ℂ)),0<a → 0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X₁ X₂ E p:ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0<P i) →
      (∀i,∀I∈pool i,‖β i I‖≤M i) →
      (∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤bslot i*P i) →
      0<X₁ → 0<X₂ → 0≤E → p≤1 →
      (∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀J∈(Finset.univ:Finset α).powerset,
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
          polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
          ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i)
            (heightCoefficient (β i) t) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
            ≤E*((∏I∈D₂,I).absNorm:ℝ)^p) →
      energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤C*(s.puncture.radical.absNorm:ℝ)^ε*E:=by
  obtain ⟨C,hC,hmass⟩:=CenteredMomentEnergyReferenceDeletionBudget.weighted_uniform_mass_subpower
    (Finset.univ:Finset α) bslot M (fun i _=>hM i) (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z Bmask bΦ a b s W₁ W₂ ha hb hs₁ hs₂ pool β P t X₁ X₂ E p hp hP hβ hs hX₁ hX₂ hE hple hchildren
  let R:=CompletedGauss.primeSupport s.puncture
  have hR:∀I∈R,Prime I:=support_prime s.puncture
  let κ:={D:Finset (Ideal O)//D∈R.powerset}×
    {D:Finset (Ideal O)//D∈R.powerset}×{J:Finset α//J∈(Finset.univ:Finset α).powerset}
  let cf(z:O)(j:κ):=signedCoefficient (naturalCharacter s.character z) R j.1.val j.2.1.val j.2.2.val
    pool (fun i=>heightCoefficient (β i) t) P
  let f(z:O)(j:κ):=polynomial (naturalCharacter s.character z) false W₁
    (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) 0 t *
    polynomial (naturalCharacter s.character z) false W₂
    (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) 0 t *
    ∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
      (heightCoefficient (β i) t) (P i)
  let ρ(j:κ):=uniformMajorant R j.1.val j.2.1.val j.2.2.val bslot M
  let q(j:κ):=((∏I∈j.2.1.val,I).absNorm:ℝ)^(p/2)
  have hρ(j:κ):0≤ρ j:=uniformMajorant_nonneg _ _ _ _ _ _ (fun i _=>hM i)
  have hq(j:κ):0≤q j:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn(D:Finset (Ideal O))(hD:D∈R.powerset):0<((∏I∈D,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hi=>(hR I (Finset.mem_powerset.mp hD hi)).ne_zero)))
  have hcf(z:O)(j:κ):‖cf z j‖≤ρ j:=by
    apply signedCoefficient_uniform _ R hR _ _ (Finset.mem_powerset.mp j.1.property)
      (Finset.mem_powerset.mp j.2.1.property) _ pool (fun i=>heightCoefficient (β i) t) P bslot M
      (fun i _=>hp i) (fun i _=>hP i) (fun i _=>hM i)
    · intro i _ I hI
      rw [heightCoefficient_norm _ _ _ (hp i I hI).ne_zero]
      exact hβ i I hI
    · intro i _ I hI hnz
      exact hs i I hI (left_ne_zero_of_mul hnz)
  have hsum(j:κ):Summable (fun z:O=>if (effectiveState s).radial.keep z then
      ‖f z j‖^2*(s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)).re else 0):=by
    obtain ⟨B,hB,hbound⟩:=slots_bounded (Finset.univ\j.2.2.val) pool (fun i=>heightCoefficient (β i) t) P
    exact pair_radial_summable (naturalCharacter s.character)
      (fun z=>∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (β i) t) (P i)) (fun _=>t) (fun _=>t) W₁ W₂ a b a b
      (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) B hb hb
      (div_pos hX₁ (hn _ j.1.property)) (div_pos hX₂ (hn _ j.2.1.property)) hs₁ hs₂
      (fun z=>hbound _) (effectiveState s).radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
  have hchild(j:κ):radialEnergy (fun z=>f z j) (effectiveState s).radial.keep
      s.radial.profile s.radial.scale≤E*(q j)^2:=by
    have hh:=hchildren j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property
    have hpow:(q j)^2=((∏I∈j.2.1.val,I).absNorm:ℝ)^p:=by
      dsimp only [q]
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      norm_num
    rw [hpow]
    exact hh
  have he:=radial_weighted_energy cf f ρ q hρ hq (effectiveState s).radial.keep s.radial.profile
    s.radial.scale E s.radial.nonneg (fun z _=>hcf z) hE hsum hchild
  have hid(z:O):(∑j:κ,cf z j*f z j)=signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=
    triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>signedCoefficient (naturalCharacter s.character z) R D₁ D₂ J
        pool (fun i=>heightCoefficient (β i) t) P *
        (polynomial (naturalCharacter s.character z) false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
         polynomial (naturalCharacter s.character z) false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
         ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i) (heightCoefficient (β i) t) (P i)))
  simp_rw [hid] at he
  rw [←original_energy_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂] at he
  have hm:(∑j:κ,ρ j*q j)≤C*((∏I∈R,I).absNorm:ℝ)^(ε/2):=by
    exact (triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J bslot M*((∏I∈D₂,I).absNorm:ℝ)^(p/2))).trans_le
      (hmass R hR (p/2) (by linarith))
  have hr:(((∏I∈R,I).absNorm:ℝ)^(ε/2))^2=(s.puncture.radical.absNorm:ℝ)^ε:=by
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  exact he.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>mul_nonneg (hρ j) (hq j))) hm 2) hE).trans_eq
    (by rw [mul_pow,hr]))

end SevenEighths.CenteredMomentEnergyReferenceDeletionEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.StageReserve -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserve
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyReferenceScalarReserve

theorem exists_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0< rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hze:1≤Z^e:=Real.one_le_rpow hZ he
  have hp:Z^(s.width+e)≤Z^e*Z^(s.width+d):=by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  let A:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))
  let B:ℝ:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hLp:0≤L:=by linarith
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hA:0≤A:=by dsimp [A];positivity
  have hB0:0≤B:=by dsimp [B];positivity
  have hb:B≤Z^e*B:=by nlinarith
  have hh:=add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hp hA)) hb
  have hrad:0≤(s.puncture.radical.absNorm:ℝ)^d:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hh':=(mul_le_mul_of_nonneg_left hh hrad)
  have hend:=mul_le_mul_of_nonneg_left (hledger Z hZ s hwidth α w hw)
    (Real.rpow_nonneg hz.le e)
  calc
    _≤Z^e*((s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+d)+A*Z^(s.width+d)+B)):=by
      convert hh' using 1 ; dsimp [A,B] ; ring
    _≤Z^e*(C*Z^(s.width+ε)):=by
      exact hend
    _=C*Z^(s.width+e+ε):=by
      rw [mul_left_comm,←Real.rpow_add hz]
      congr 2
      ring

lemma inherited_loss_budget (incoming overhead final:ℝ)
    (hin:incoming≤final/2)(hover:overhead≤final/2):incoming+overhead≤final:=by
  linarith

end SevenEighths.CenteredMomentEnergyStageReserve

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.StageReserveBounded -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEnergyStageReserve

theorem exists_bounded_separated_reference_reserve (rho ε Mcap Bmask bΦ:ℝ)
    (hrho:0< rho)(hε:0<ε)(hM:0≤Mcap)(hB:0≤Bmask):
    ∃d xi saving L C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z Bmask bΦ,s.width≤Mcap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤Mcap →
      (s.puncture.radical.absNorm:ℝ)^d*(
        Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(L*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤
        C*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,saving,L,C,hd,hxi,hs,hC,hxr,hL,hledger⟩:=
    exists_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hB
  refine ⟨d,xi,saving,Mcap+Bmask+xi,C,hd,hxi,hs,hC,hxr,le_refl _,by linarith,?_⟩
  intro e he Z hZ s hwidth α _ w hw
  apply le_trans _ (hledger e he Z hZ s hwidth α w hw)
  have hlog:0≤Real.log Z:=Real.log_nonneg hZ
  have hLp:0≤Mcap+Bmask+xi:=by linarith
  gcongr

end SevenEighths.CenteredMomentEnergyStageReserveBounded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.BackwardSourceRanges -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBackwardSourceRanges
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyProfiles
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentEnergyStageReserveBounded

def lengthAt (M B L:ℝ)(depth k:ℕ):ℝ:=range M B L (depth-k)
def lowerAt (a b:ℝ)(depth k:ℕ):ℝ:=lower a b (depth-k)

lemma previous_length (M B L:ℝ)(depth k:ℕ)(hk:k<depth):
    lengthAt M B L depth k=CenteredMomentEnergyWidthRanges.step M B
      (lengthAt M B L depth (k+1)):=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lengthAt,hn,range]

lemma previous_lower (a b:ℝ)(depth k:ℕ)(hk:k<depth):
    lowerAt a b depth k=lowerAt a b depth (k+1)/max 1 b:=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lowerAt,hn,lower]

lemma length_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    0≤lengthAt M B L depth k:=range_nonneg M B L hM hB _

lemma original_length (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    L≤lengthAt M B L depth k:=range_original M B L hM hB _

lemma lower_positive (a b:ℝ)(ha:0<a)(depth k:ℕ):0<lowerAt a b depth k:=
  lower_pos a b ha _

theorem profile_step_support (a b:ℝ)(ha:0<a)(depth k:ℕ)(hk:k<depth)
    (W:Test (lowerAt a b depth (k+1)) b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Function.support
      ((CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).profile:ℝ→ℂ)
      ⊆Set.Icc (lowerAt a b depth k) b:=by
  rw [previous_lower a b depth k hk]
  exact (CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).support

theorem previous_admits (M B L stageCap rho d e Lref:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)(hd:d≤1)(he:e≤1)
    (depth k:ℕ)(hk:k<depth)(hLref:Lref≤ stageCap+B+rho/100):
    lengthAt M B L depth (k+1)≤lengthAt M B L depth k ∧
    Lref≤lengthAt M B L depth k ∧
    max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1≤lengthAt M B L depth k ∧
    2*lengthAt M B L depth (k+1)+e≤lengthAt M B L depth k ∧
    2*(max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1)+e≤lengthAt M B L depth k:=by
  have h:=step_admits M B (lengthAt M B L depth (k+1)) rho d e hM hB
    (length_nonneg M B L hM hB depth (k+1)) hrho hd he
  rw [previous_length M B L depth k hk]
  refine ⟨h.1,?_,?_,h.2.2.2.1,?_⟩
  · exact (show Lref≤M+B+rho/100+1 by linarith).trans h.2.1
  · have hm:max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)≤
        max (lengthAt M B L depth (k+1)) (M+B+2*d):=max_le_max_left _ (by linarith)
    linarith only [hm,h.2.2.1]
  · apply le_trans _ h.2.2.2.2
    gcongr

lemma paired_contours (M B L stageCap rho L₁ L₂:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)
    (depth k:ℕ)(hk:k<depth)
    (h₁:L₁≤ stageCap+B+rho/100)(h₂:L₂≤ stageCap+B+rho/100):
    max L₁ L₂≤lengthAt M B L depth k:=
  (previous_admits M B L stageCap rho 0 0 (max L₁ L₂) hM hB hstage hrho
    (by norm_num) (by norm_num) depth k hk (max_le h₁ h₂)).2.1

lemma source_cap_uniform (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    sourceCap M B L (depth-k)≤ sourceCap M B L depth:=by
  have h:=range_mono M B L hM hB (Nat.sub_le depth k)
  unfold sourceCap
  linarith

lemma scheduled_source_cap (M B L ε:ℝ)(hM:0≤M)(hB:0≤B)(k:ℕ):
    sourceCap M B L (count M ε-k)≤finalSourceCap M B L ε:=
  source_cap_uniform M B L hM hB _ _

theorem actual_reference_reserve_previous
    (M B L stageCap rho ε bΦ:ℝ)(hM:0≤M)(hB:0≤B)(hstage0:0≤ stageCap)
    (hstage:stageCap≤M)(hrho:0< rho)(hrho1:rho≤1)(hε:0<ε)
    (depth k:ℕ)(hk:k<depth):
    ∃d xi saving Lref C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤ rho/100 ∧ stageCap+B+xi≤Lref ∧ Lref≤ stageCap+B+rho/100 ∧
      Lref≤lengthAt M B L depth k ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z B bΦ,s.width≤ stageCap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤ stageCap →
      (s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(Lref*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,hledger⟩:=
    exists_bounded_separated_reference_reserve rho ε stageCap B bΦ hrho hε hstage0 hB
  refine ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,?_,hledger⟩
  exact (previous_admits M B L stageCap rho 0 0 Lref hM hB hstage hrho1
    (by norm_num) (by norm_num) depth k hk hLu).2.1

end SevenEighths.CenteredMomentEnergyBackwardSourceRanges

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule -/

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

def stageLoss (M B ε:ℝ)(k:ℕ):ℝ:=ε/1000+loss M B ε k

lemma stageLoss_pos (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<stageLoss M B ε k:=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  unfold stageLoss loss
  positivity

lemma stageLoss_final (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(hk:k≤ count M ε):stageLoss M B ε k≤ε/500:=by
  have hh:=loss_le_final M B κ ε hM hB hκ hε k hk
  unfold stageLoss
  linarith

lemma successor_with_references (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(er d e d1 d2 theta other highReflection zeroReflection:ℝ)
    (her:er≤ reserve M B ε)(hd:d≤ reserve M B ε)(he:e≤ reserve M B ε)
    (hd1:d1≤ reserve M B ε)(hd2:d2≤ reserve M B ε)(ht:theta≤ reserve M B ε)
    (ho:other≤48*reserve M B ε)
    (hhigh:highReflection≤ reserve M B ε)(hzero:zeroReflection≤ reserve M B ε):
    stageLoss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+
      other+highReflection+zeroReflection≤ stageLoss M B ε (k+1):=by
  have hh:=next_paid_loss M B κ ε hM hB hκ hε k er d e d1 d2 theta
    (other+highReflection+zeroReflection) her hd he hd1 hd2 ht (by linarith)
  unfold stageLoss
  linarith

lemma one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(sourceLoss extra:ℝ)(hsource:sourceLoss≤ε/1000)
    (hextra:extra≤50*reserve M B ε):
    sourceLoss+extra≤ stageLoss M B ε (k+1):=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have hk:0≤(k:ℝ):=Nat.cast_nonneg _
  simp only [stageLoss,loss,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma actual_one_time_with_new_cost (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(df es d theta other A extra:ℝ)
    (hdf:df≤ reserve M B ε)(hes:es≤ reserve M B ε)(hd:d≤ reserve M B ε)
    (ht:theta≤ reserve M B ε)(ho:other≤ reserve M B ε)(he0:0≤es)(hA:A≤M)
    (hextra:extra≤50*reserve M B ε):
    CenteredMomentSuccessorPaidParameters.exceptional (amplification ε) df es d B theta+extra≤
      stageLoss M B ε (k+1) ∧
    CenteredMomentSuccessorPaidParameters.diagonal (amplification ε) d other es A+extra≤
      stageLoss M B ε (k+1):=by
  have hh:=one_time_losses M B κ ε hM hB hκ hε df es d theta other A hdf hes hd ht ho he0 hA
  exact ⟨one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.1 hextra,
    one_time_with_new_cost M B κ ε hM hB hκ hε k _ extra hh.2 hextra⟩

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstStageLossBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentSuccessorPaidParameters
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

def sourcePaid (Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh:ℝ):ℝ:=
  (Bcap+Bcap)*emask+ell+er+(delta+reserveAmp+thetaSource)/6+thetaClip/3+κ*mesh

theorem literal_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hκ:0≤κ)(hε:0<ε)
    (k:ℕ)(ell epsSrc epsMask deltaSrc thetaSrc deltaAmp reserveAmp thetaSource thetaClip
      er primeLoss physicalLoss highReflection zeroReflection saving:ℝ)
    (hell:ell≤ stageLoss M Bcap ε k)
    (he0:0≤epsSrc)(he:epsSrc≤ reserve M Bcap ε)
    (hemask:(Bcap+Bcap)*epsMask≤ reserve M Bcap ε)
    (hdsrc:deltaSrc≤ reserve M Bcap ε)(htsrc:thetaSrc≤ reserve M Bcap ε)
    (hda:0≤deltaAmp)(hra:0≤ reserveAmp)(hts:0≤thetaSource)(htc:0≤thetaClip)
    (hsmall:deltaAmp+reserveAmp+thetaSource≤ reserve M Bcap ε)
    (hclip:thetaClip≤ reserve M Bcap ε)(her:er≤ reserve M Bcap ε)
    (hcommon:epsSrc*Bcommon≤ reserve M Bcap ε)
    (hprime:primeLoss≤ reserve M Bcap ε)(hphysical:physicalLoss≤ reserve M Bcap ε)
    (hhigh:highReflection≤ reserve M Bcap ε)(hzero:zeroReflection≤ reserve M Bcap ε)
    (hsaving:2*amplification ε+deltaAmp+reserveAmp≤ saving):
    ∀j:Fin 4,
      losses epsSrc deltaSrc thetaSrc Bcap j+
        lossVector (amplification ε) deltaAmp reserveAmp
          (sourcePaid Bcap epsMask ell er deltaAmp reserveAmp thetaSource thetaClip κ (mesh M Bcap κ ε))
          epsSrc M saving j+
        epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      stageLoss M Bcap ε (k+1):=by
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< reserve M Bcap ε:=hb.2.2.2.1
  have hs:0≤amplification ε:=hb.1.le
  have hother:epsSrc*Bcommon+primeLoss+physicalLoss≤48*reserve M Bcap ε:=by linarith
  have hextra:epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection≤
      50*reserve M Bcap ε:=by linarith
  have hdf:deltaAmp+reserveAmp≤ reserve M Bcap ε:=by linarith
  have hdelta:deltaAmp≤ reserve M Bcap ε:=by linarith
  have hres:reserveAmp≤ reserve M Bcap ε:=by linarith
  have hmain:=successor_with_references M Bcap κ ε hM hB hκ hε k
    er deltaSrc epsSrc (deltaAmp+reserveAmp+thetaSource) ((Bcap+Bcap)*epsMask) thetaClip
    (epsSrc*Bcommon+primeLoss+physicalLoss) highReflection zeroReflection
    her hdsrc he hsmall hemask hclip hother hhigh hzero
  have hone:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaSrc thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdsrc htsrc hres he0 le_rfl hextra
  have hdiag:=actual_one_time_with_new_cost M Bcap κ ε hM hB hκ hε k
    (deltaAmp+reserveAmp) epsSrc deltaAmp thetaSrc reserveAmp M
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection)
    hdf he hdelta htsrc hres he0 le_rfl hextra
  have htail:=one_time_with_new_cost M Bcap κ ε hM hB hκ hε k 0
    (epsSrc*Bcommon+primeLoss+physicalLoss+highReflection+zeroReflection) (by positivity) hextra
  intro j
  fin_cases j <;> simp only [losses,lossVector,Matrix.cons_val,Fin.reduceFinMk]
  · dsimp [sourcePaid,edge] at hmain ⊢
    linarith
  · dsimp [exceptional] at hone
    linarith [hone.1]
  · dsimp [diagonal] at hdiag
    linarith [hdiag.2]
  · linarith

theorem chosen_four_budget (M Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε;
    let es:=r/(Bcommon+1);
    let em:=r/(Bcap+Bcap+1);
    0<es ∧ es≤1 ∧ 0<em ∧ 0< r/4 ∧ 0<2*amplification ε+1 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
      highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es M (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< reserve M Bcap ε:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:reserve M Bcap ε≤amplification ε/100:=min_le_left _ _
  have hr1:reserve M Bcap ε≤1:=by linarith [hb.2.1]
  have hes:0< reserve M Bcap ε/(Bcommon+1):=by positivity
  have hem:0< reserve M Bcap ε/(Bcap+Bcap+1):=by positivity
  have hesle:reserve M Bcap ε/(Bcommon+1)≤ reserve M Bcap ε:=by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hemscale:(Bcap+Bcap)*(reserve M Bcap ε/(Bcap+Bcap+1))≤ reserve M Bcap ε:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hescale:(reserve M Bcap ε/(Bcommon+1))*Bcommon≤ reserve M Bcap ε:=by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,hesle.trans hr1,hem,by positivity,by positivity,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero
  apply literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    (reserve M Bcap ε/(Bcommon+1)) (reserve M Bcap ε/(Bcap+Bcap+1))
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    (reserve M Bcap ε/4) (reserve M Bcap ε/4) (reserve M Bcap ε/4)
    highReflection zeroReflection (2*amplification ε+1)
    hell hes.le hesle hemscale
  all_goals first | exact hescale | exact hhigh | exact hzero | positivity | linarith

end SevenEighths.CenteredMomentEnergyFirstStageLossBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstDeclaredCapacityLossBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients

lemma lossVector_cap (sigma delta reserveAmp paid es M A saving:ℝ)
    (he:0≤es)(hM:0≤M)(hA:0≤A)(j:Fin 4):
    lossVector sigma delta reserveAmp paid es A saving j≤
      lossVector sigma delta reserveAmp paid es M saving j+es*A:=by
  fin_cases j <;> simp only [lossVector,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg he hM,mul_nonneg he hA]

theorem chosen_declared_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ es*A≤ r/4 ∧ es*Bcommon≤ r/4 ∧
    ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
      highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
      losses es (r/4) (r/4) Bcap j+
        lossVector (amplification ε) (r/4) (r/4)
          (sourcePaid Bcap em ell (r/4) (r/4) (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
          es A (2*amplification ε+1) j+
        es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< r:=hb.2.2.2.1
  have hs:0<amplification ε:=hb.1
  have hrsmall:r≤amplification ε/100:=min_le_left _ _
  have hr1:r≤1:=by linarith [hb.2.1]
  have hden:0<4*(Bcommon+A+1):=by positivity
  have hes:0<es:=by dsimp [es];positivity
  have hesle:es≤ r/4:=by
    dsimp [es]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc,mul_nonneg hr.le hA]
  have hescap:es*A≤ r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hBc]
  have hescommon:es*Bcommon≤ r/4:=by
    dsimp [es]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hr.le hA]
  have hemscale:(Bcap+Bcap)*(r/(Bcap+Bcap+1))≤ r:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  refine ⟨hes,by linarith,by positivity,hescap,hescommon,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hh:=literal_four_budget M Bcap Bcommon κ ε hM hB hκ hε k ell
    es (r/(Bcap+Bcap+1)) (r/4) (r/4) (r/4) (r/4) (r/4) (r/4)
    (r/4) (r/4) (r/4+es*A) highReflection zeroReflection (2*amplification ε+1)
    hell hes.le (by dsimp [r] at *;linarith) hemscale
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    (by dsimp [r] at *;linarith) (by dsimp [r] at *;linarith)
    hhigh hzero (by linarith)
  have hc:=lossVector_cap (amplification ε) (r/4) (r/4)
    (sourcePaid Bcap (r/(Bcap+Bcap+1)) ell (r/4) (r/4) (r/4) (r/4) (r/4)
      κ (mesh M Bcap κ ε)) es M A (2*amplification ε+1) hes.le hM hA j
  have hj:=hh j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_
  linarith only [hj,hc]

end SevenEighths.CenteredMomentEnergyFirstDeclaredCapacityLossBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FirstActualFrequencyBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstDeclaredCapacityLossBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSectorLocalization

theorem eventually_frequency_loss (r:ℝ)(hr:0< r):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤ r/4:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by positivity:0< r/8))) 128,
    eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  have hlog:=Real.logb_le_logb_of_le hZ (by norm_num:(0:ℝ)<128) hpow
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hlog
  refine ⟨hZ,frequencyLoss_nonneg Z 32 (r/4) hZ (by norm_num) (by positivity),?_⟩
  unfold frequencyLoss
  norm_num only [show (4:ℝ)*32=128 by norm_num]
  linarith only [hlog]

lemma paid_frequency_mono
    (sigma delta delta' reserveAmp Bcap emask ell er thetaSource thetaClip κ mesh
      es A saving:ℝ)(hd:delta≤delta')(j:Fin 4):
    lossVector sigma delta reserveAmp
      (sourcePaid Bcap emask ell er delta reserveAmp thetaSource thetaClip κ mesh)
      es A saving j≤
    lossVector sigma delta' reserveAmp
      (sourcePaid Bcap emask ell er delta' reserveAmp thetaSource thetaClip κ mesh)
      es A saving j:=by
  fin_cases j <;>
    simp only [lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    linarith only [hd]

theorem actual_frequency_four_budget (M A Bcap Bcommon κ ε:ℝ)
    (hM:0≤M)(hA:0≤A)(hB:0≤Bcap)(hBc:0≤Bcommon)(hκ:0≤κ)(hε:0<ε):
    let r:=reserve M Bcap ε
    let es:=r/(4*(Bcommon+A+1))
    let em:=r/(Bcap+Bcap+1)
    0<es ∧ es≤1 ∧ 0<em ∧ 0< r/4 ∧ r/4≤amplification ε/4 ∧
    ∀ᶠ Z:ℝ in atTop,1<Z ∧
      0≤frequencyLoss Z 32 (r/4) ∧ frequencyLoss Z 32 (r/4)≤ r/4 ∧
      ∀(k:ℕ)(ell highReflection zeroReflection:ℝ),ell≤ stageLoss M Bcap ε k→
        highReflection≤ r→zeroReflection≤ r→∀j:Fin 4,
        losses es (r/4) (r/4) Bcap j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            (sourcePaid Bcap em ell (r/4) (frequencyLoss Z 32 (r/4))
              (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε))
            es A (2*amplification ε+1) j+
          es*Bcommon+r/4+r/4+highReflection+zeroReflection≤ stageLoss M Bcap ε (k+1):=by
  dsimp only
  let r:=reserve M Bcap ε
  let es:=r/(4*(Bcommon+A+1))
  let em:=r/(Bcap+Bcap+1)
  obtain ⟨hes,hes1,hem,_,_,hbudget⟩:=chosen_declared_four_budget M A Bcap Bcommon κ ε
    hM hA hB hBc hκ hε
  have hb:=bounds M Bcap κ ε hM hB hκ hε
  have hr:0< r:=hb.2.2.2.1
  have hrs:r≤amplification ε/100:=min_le_left _ _
  refine ⟨hes,hes1,hem,by positivity,by linarith [hb.1],?_⟩
  filter_upwards [eventually_frequency_loss r hr] with Z hZ
  refine ⟨hZ.1,hZ.2.1,hZ.2.2,?_⟩
  intro k ell highReflection zeroReflection hell hhigh hzero j
  have hfixed:=hbudget k ell highReflection zeroReflection hell hhigh hzero j
  have hmono:=paid_frequency_mono (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
    (r/4) Bcap em ell (r/4) (r/4) (r/4) κ (mesh M Bcap κ ε) es A
    (2*amplification ε+1) hZ.2.2 j
  change losses es (r/4) (r/4) Bcap j+_+es*Bcommon+r/4+r/4+highReflection+zeroReflection≤_ at hfixed ⊢
  linarith only [hfixed,hmono]

end SevenEighths.CenteredMomentEnergyFirstActualFrequencyBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.StageMargins -/

section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageMargins
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule

def physicalLoss (M B ε:ℝ)(k:ℕ):ℝ:=stageLoss M B ε (k+1)-2*reserve M B ε
def reflectedLoss (M B ε:ℝ)(k:ℕ):ℝ:=physicalLoss M B ε k+reserve M B ε

lemma physicalLoss_eq (M B ε:ℝ)(k:ℕ):
    physicalLoss M B ε k=stageLoss M B ε k+62*reserve M B ε:=by
  unfold physicalLoss stageLoss
  rw [loss_succ]
  ring
lemma reflected_then_zero (M B ε:ℝ)(k:ℕ):
    reflectedLoss M B ε k+reserve M B ε=stageLoss M B ε (k+1):=by
  unfold reflectedLoss physicalLoss
  ring
lemma margins (M B κ ε:ℝ)(hM:0≤M)(hB:0≤B)(hκ:0≤κ)(hε:0<ε)(k:ℕ):
    0<physicalLoss M B ε k ∧
    stageLoss M B ε k≤physicalLoss M B ε k ∧
    reserve M B ε/4≤physicalLoss M B ε k ∧
    physicalLoss M B ε k≤ reflectedLoss M B ε k ∧
    reflectedLoss M B ε k≤ stageLoss M B ε (k+1):=by
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  have he:=stageLoss_pos M B κ ε hM hB hκ hε k
  have hp:=physicalLoss_eq M B ε k
  have hf:=reflected_then_zero M B ε k
  unfold reflectedLoss at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyStageMargins

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.ZeroComparison -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

def smallScale (b:ℝ):ℝ:=1/(2*max 1 b)

lemma smallScale_pos (b:ℝ):0<smallScale b:=by unfold smallScale;positivity

lemma smallScale_le_one (b:ℝ):smallScale b≤1:=by
  unfold smallScale
  apply (div_le_iff₀ (by positivity:0<(2:ℝ)*max 1 b)).mpr
  linarith [le_max_left (1:ℝ) b]

lemma smallScale_strict (b:ℝ):smallScale b*b<1:=by
  have hm:0< max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  unfold smallScale
  have hb:=le_max_right (1:ℝ) b
  rw [div_mul_eq_mul_div,one_mul]
  exact (div_lt_iff₀ (mul_pos (by norm_num) hm)).mpr (by linarith)

def zeroData (s:Input ι):CenteredMomentEligibleEnergy.Data ι := { s.toData with
  Y₁ := smallScale s.b₁
  Y₂ := s.X₁*s.X₂/smallScale s.b₁
  Y₁_pos := smallScale_pos _
  Y₂_pos := div_pos (mul_pos s.X₁_pos s.X₂_pos) (smallScale_pos _)
  same_product := by field_simp [ne_of_gt (smallScale_pos s.b₁)] }

def zeroInput (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):Input ι :=
  completeInput (zeroData s) hz₁ hz₂ s.ν_bound s.W_bound s.lower s.upper
    s.lower_pos s.lower_le s.upper_ge

omit [DecidableEq ι] in
@[simp] lemma zeroInput_volume (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):
    volume (zeroInput s hz₁ hz₂)=volume s:=rfl

omit [DecidableEq ι] in
lemma comparison_row_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(z:O):
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂=0:=by
  unfold positiveSlotRow
  change _*(rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t (smallScale s.b₁)*_*_)=0
  rw [strict_subunit_rowTwistedSum_zero s.η (fixedBadMask*idealGenerator R) 1 z
    s.W₁ s.b₁ s.t (smallScale s.b₁) (smallScale_pos _) s.support₁ (smallScale_strict _)]
  simp only [zero_mul,mul_zero]

omit [DecidableEq ι] in
lemma comparison_energy_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
      r.keep r.profile r.scale=0:=by
  unfold CenteredMomentInductionEnergy.energy
  simp only [comparison_row_zero s hz₁ hz₂ R, norm_zero, zero_pow (by decide : (2:ℕ)≠0),
    zero_mul, ite_self, tsum_zero]

theorem actual_zero_comparison_entry (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
      (coefficient (zeroInput s hz₁ hz₂) R 1) r.profile r.scale‖/volume s:=by
  have hh:=positive_energy_comparison (zeroInput s hz₁ hz₂) R r
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
    s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_scale_caps (b L ε:ℝ)(hL:0≤L)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → s.X₁≤Z^L → s.X₂≤Z^L →
      (zeroInput s hz₁ hz₂).Y₁≤Z^(2*L+ε) ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(2*L+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hX₁ hX₂
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨(smallScale_le_one _).trans (Real.one_le_rpow hZ.le (by positivity)),?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hp:s.X₁*s.X₂≤Z^(2*L):=by
    have hh:=mul_le_mul hX₁ hX₂ s.X₂_pos.le (Real.rpow_pos_of_pos hZ0 L).le
    rw [←Real.rpow_add hZ0] at hh
    simpa only [two_mul] using hh
  have hconst:2*max 1 s.b₁≤Z^ε:=(mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    s.X₁*s.X₂*(2*max 1 s.b₁)≤Z^(2*L)*Z^ε:=
      mul_le_mul hp hconst (by positivity) (Real.rpow_pos_of_pos hZ0 _).le
    _=Z^(2*L+ε):=(Real.rpow_add hZ0 _ _).symm

end SevenEighths.CenteredMomentEnergyZeroComparison

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Energy.FixedRadialEntry -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFixedRadialEntry
open ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSourceMass CenteredMomentSourceRectangleMask
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialSource CenteredMomentSourceRow
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentRadialEligibleEnergy
open CenteredMomentEnergyZeroComparison CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

theorem original_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀R:Ideal O,∀r:Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) Ψ r.scale‖/volume s+
      2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.Y₁ s.Y₂ r.keep r.profile r.scale :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=fixed_source b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s R r hr
  apply (positive_energy_comparison s R r).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (volume_pos s).le
  have h:=mul_le_mul_of_nonneg_left
    (hh r.profile hr s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R 1) r.scale r.scale_pos)
    (by norm_num : (0:ℝ)≤2)
  simpa only [mul_assoc] using h

theorem original_zero_comparison (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      ∀R:Ideal O,∀r:Radial,Function.support (r.profile:ℝ→ℂ)⊆Set.Iic b→
      CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
        s.W₁ s.W₂ s.slots s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale ≤
      2*QuadraticInitialBound.diagonalControl r.profile*
        ‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
          (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
          (coefficient (zeroInput s hz₁ hz₂) R 1) Ψ r.scale‖/volume s :=by
  obtain ⟨Ψ,hs,hn,hh⟩:=original_comparison (ι:=ι) b hb
  refine ⟨Ψ,hs,hn,?_⟩
  intro s hz₁ hz₂ R r hr
  have h:=hh (zeroInput s hz₁ hz₂) R r hr
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P
    (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂ r.keep r.profile r.scale at h
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at h
  exact h
end SevenEighths.CenteredMomentEnergyFixedRadialEntry

end

end OAI

end

