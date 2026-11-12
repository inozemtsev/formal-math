module

public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.Primitive
public import Green64.Library.OAI.NumberTheory.DirichletL.Hecke.Dyadic
public import Green64.Library.Analysis.NumberTheory.DirichletL.Detector.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part020

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.ComparisonReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma residue_nontrivial (c : O) (χ : MulChar (O⧸Ideal.span {c}) ℂ) (hχ : χ≠1) :
    Nontrivial (O⧸Ideal.span {c}) := by
  by_contra h
  have : Subsingleton (O⧸Ideal.span {c}) := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x=1 := Subsingleton.elim _ _
  simp [hx]

lemma residue_zero (c : O) [NeZero c] (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1) (hχ : χ≠1) :
    elementCoeff (character c χ hu) 0=0 := by
  let := residue_nontrivial c χ hχ
  change χ (Ideal.Quotient.mk (Ideal.span {c}) 0)=0
  rw [map_zero,χ.map_zero]

theorem radial_ideal_reindex (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hzero : elementCoeff η 0=0)
    (hs : Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X))) :
    (∑' z : O,elementCoeff η z*W (‖eisEmbedding z‖^2/X))=
      6*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) hs
    (by rw [hzero,zero_mul])
    (fun u z => by rw [elementCoeff_unit_mul,norm_eisEmbedding_unit_mul])
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator η.modulus η.residue η.unit_trivial
    I.property (span_idealGenerator I.val)).symm

lemma bounded_radial_summable (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖)) :
    Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  let : Finite (O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O⧸η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem primitive_plain_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    (∑' I : NI,idealCoeff (character c χ hu) I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' I : NI,idealCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) I.val*
        paperRadialFourier W ((I.val.absNorm:ℝ)/(‖eisEmbedding c‖^2/X)) := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hQ : 0<‖eisEmbedding c‖^2 := sq_pos_of_pos hc
  have hχi : χ⁻¹≠1 := inv_ne_one.mpr hχ
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd : Summable (fun z : O => ‖paperRadialFourier W
      (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X))‖) := by
    convert paperRadialFourier_lattice_summable_norm W (X/‖eisEmbedding c‖^2) (div_pos hX hQ) using 1
    funext z
    congr 2
    field_simp
  have he := TraceCharacter.primitive_radial_paper_poisson_normalized c W X hX χ hp
  have he' : (∑' z : O,elementCoeff (character c χ hu) z*W (‖eisEmbedding z‖^2/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' z : O,elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z*
        paperRadialFourier W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
    change (∑' z : O,χ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X))=_
    rw [he]
    congr 1
    apply tsum_congr
    intro z
    congr 2
    field_simp
  rw [radial_ideal_reindex _ W X (residue_zero c χ hu hχ) (bounded_radial_summable _ W X hs),
    radial_ideal_reindex _ (paperRadialFourier W) _ (residue_zero c χ⁻¹ _ hχi)
      (bounded_radial_summable _ (paperRadialFourier W) _ hd)] at he'
  linear_combination he'/6

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem primitive_normalized_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (character c χ hu) false W X 0 0=
      TraceCharacter.normalizedGauss c χ*
        HeckeDyadic.polynomial (character c χ⁻¹ (inverse_unit_trivial c χ hu)) false
          (paperRadialFourier W) (‖eisEmbedding c‖^2/X) 0 0 := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY : 0<‖eisEmbedding c‖^2/X := div_pos (sq_pos_of_pos hc) hX
  rw [polynomial_plain _ _ _ hX,primitive_plain_reflection c χ hu hp hχ W X hX,
    polynomial_plain _ _ _ hY]
  have hs : Real.sqrt (‖eisEmbedding c‖^2/X)=‖eisEmbedding c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (‖eisEmbedding c‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X:ℂ)⁻¹*((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))=
      TraceCharacter.normalizedGauss c χ*(Real.sqrt (‖eisEmbedding c‖^2/X):ℂ)⁻¹ := by
    rw [hs,Complex.ofReal_div]
    field_simp
    rw [hsq]
  rw [←mul_assoc,hfac,mul_assoc]

theorem reflected_profile_height_control (a b : ℝ) (ha : 0<a) (A K : ℕ) :
    ∃ n : ℕ,∀ (W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t : ℝ,∀j : ℕ,j≤K → ∀x : ℝ,0≤x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) j x‖≤C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  obtain ⟨n,hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDbd⟩ := hn W hs hW
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t j hj x hx
  have hsame : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext y
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t y
  have hb := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) j hj x hx
  rw [hsame] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hDbd t) hC.le).trans_eq (by ring))
end SevenEighths.CenteredMomentComparisonReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

def logWindow (v : ℝ) : ℂ := (annulus (Real.exp v) : ℂ)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logWindow_support : Function.support logWindow ⊆ Icc (-Real.log 4) 0 := by
  intro v hv
  have hn : annulus (Real.exp v) ≠ 0 := by simpa [logWindow] using hv
  have hlow : 1/4 < Real.exp v := lt_of_not_ge (fun h => hn (annulus_zero_low _ h))
  have hhigh : Real.exp v < 1 := lt_of_not_ge (fun h => hn (annulus_zero_high _ h))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  constructor
  · exact (Real.exp_lt_exp.mp (hl ▸ hlow)).le
  · exact (Real.exp_lt_one_iff.mp hhigh).le

theorem logWindow_tsupport : tsupport logWindow ⊆ Icc (-Real.log 4) 0 :=
  closure_minimal logWindow_support isClosed_Icc

theorem logWindow_compact : HasCompactSupport logWindow :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logWindow_support

def logWindowSchwartz : 𝓢(ℝ,ℂ) := logWindow_compact.toSchwartzMap logWindow_smooth

theorem logWindow_derivative_window (i : ℕ) (v : ℝ)
    (hi : ‖iteratedFDeriv ℝ i logWindow v‖ ≠ 0) :
    1/4 ≤ Real.exp v ∧ |v| ≤ Real.log 4 := by
  have hv := logWindow_tsupport (support_iteratedFDeriv_subset i (norm_ne_zero_iff.mp hi))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  refine ⟨hl ▸ Real.exp_le_exp.mpr hv.1, abs_le.mpr ⟨hv.1,?_⟩⟩
  exact hv.2.trans (Real.log_nonneg (by norm_num))

theorem logWindow_derivative_bound (K : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ i≤K, ∀v : ℝ, ‖iteratedFDeriv ℝ i logWindow v‖≤C := by
  let C := 1+∑ i∈Finset.range (K+1), SchwartzMap.seminorm ℝ 0 i logWindowSchwartz
  have hsum := Finset.sum_nonneg (s:=Finset.range (K+1))
    (fun i _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 i) logWindowSchwartz)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro i hi v
  have hb := SchwartzMap.le_seminorm' ℝ 0 i logWindowSchwartz v
  have hc := Finset.single_le_sum (s:=Finset.range (K+1))
    (f:=fun j=>SchwartzMap.seminorm ℝ 0 j logWindowSchwartz)
    (fun j _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 j) logWindowSchwartz)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i logWindowSchwartz v‖≤C
  simpa only [pow_zero, one_mul] using hb.trans (by dsimp [C];linarith)

def reflected (W : ℝ→ℂ) (t : ℝ) : ℝ→ℂ :=
  paperRadialFourier (CompletedHeight.normTwistedSource W t)

theorem reflected_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiffOn ℝ ∞ (reflected W t) (Ioi 0) := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold reflected
  rw [←he]
  exact paperRadialFourier_contDiffOn _

def annularProfile (F : ℝ→ℂ) (s x : ℝ) : ℂ := (annulus x:ℂ)*F (s*x)

def logProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  positiveLogProfile logWindow (reflected W t) s logWindow_compact logWindow_smooth
    (reflected_smooth W a b ha hs hW t) hs0

@[simp] theorem logProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t v : ℝ) :
    logProfile W a b ha hs hW s hs0 t v =
      annularProfile (reflected W t) s (Real.exp v) := rfl

theorem logProfile_tsupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) :
    tsupport (logProfile W a b ha hs hW s hs0 t) ⊆ Icc (-Real.log 4) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply logWindow_support
  intro hz
  exact hv (by change logWindow v*reflected W t (s*Real.exp v)=0;rw [hz,zero_mul])

theorem logProfile_finite_seminorm (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀s : ℝ, ∀hs0 : 0<s, ∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logProfile W a b ha hs hW s hs0 t) ≤
        C*(1+‖t‖)^J/(1+s)^B := by
  let K := H.sup Prod.snd
  obtain ⟨CW,hCW,hwin⟩ := logWindow_derivative_bound K
  obtain ⟨J,hJ⟩ := reflected_profile_height_control a b ha B K
  let D := 1+∑z∈H,(Real.log 4)^z.1*
    (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hD : 0<D := by
    have hn : 0≤∑z∈H,(Real.log 4)^z.1*
        (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW) := by positivity
    dsimp [D];linarith
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hEuler⟩ := hJ W hs hW
  refine ⟨D*CF/(1/4:ℝ)^B,by positivity,?_⟩
  intro s hs0 t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzK : z.2≤K := Finset.le_sup hz
  have hb := positive_log_uniform_seminorm logWindow (reflected W t)
    s (1/4) (Real.log 4) CW (CF*(1+‖t‖)^J) B z.2 z.1
    logWindow_compact logWindow_smooth (reflected_smooth W a b ha hs hW t)
    hs0 (by norm_num) (by norm_num) hlog hCW.le (by positivity)
    (fun i hi v => hwin i (hi.trans hzK) v)
    (fun v hv => by obtain ⟨i,hi,hn⟩:=hv;exact logWindow_derivative_window i v hn)
    (fun i hi x hx => hEuler t i (hi.trans hzK) x hx.le)
  have hd : (Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)≤D := by
    have h := Finset.single_le_sum (s:=H)
      (f:=fun z=>(Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW))
      (fun z _ => by positivity) hz
    dsimp [D];linarith
  have hb' : (1/4:ℝ)^B*(1+s)^B*
      SchwartzMap.seminorm ℝ z.1 z.2 (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J) := by
    apply hb.trans
    rw [←Finset.sum_mul, ←mul_assoc]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hb'' : SchwartzMap.seminorm ℝ z.1 z.2
      (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J)/((1/4:ℝ)^B*(1+s)^B) :=
    (le_div_iff₀ (by positivity)).mpr
      (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb')
  exact hb''.trans_eq (by ring)

theorem annularProfile_support (F : ℝ→ℂ) (s : ℝ) :
    Function.support (annularProfile F s) ⊆ Icc (1/4) 1 := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_low x (le_of_not_ge hn)])
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_high x (le_of_not_ge hn)])

theorem annularProfile_zero (F : ℝ→ℂ) (s x : ℝ)
    (hx : x≤1/4 ∨ 1≤x) : annularProfile F s x=0 := by
  rcases hx with hx|hx
  · simp [annularProfile,annulus_zero_low x hx]
  · simp [annularProfile,annulus_zero_high x hx]

theorem annular_partition (F : ℝ→ℂ) (x : ℝ) (hx : 0<x) :
    (∑' n : ℤ,annularProfile F (dyadicScale n) (x/dyadicScale n))=F x := by
  have he (n : ℤ) : annularProfile F (dyadicScale n) (x/dyadicScale n)=
      (dyadicWeight n x:ℂ)*F x := by
    simp [annularProfile,dyadicWeight,mul_div_cancel₀,ne_of_gt (dyadicScale_pos n)]
  simp_rw [he]
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition x hx]
  simp

theorem normalized_annular_term (η : HeckeFamily.Character) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0<s) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*HeckeDyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp

def annularMass (B : ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (dyadicScale n)/(1+dyadicScale n)^B

theorem annularMass_nonneg (B : ℕ) (n : ℤ) : 0≤annularMass B n := by
  have hp := dyadicScale_pos n
  unfold annularMass
  positivity

lemma sqrt_nat_pow (x : ℝ) (hx : 0≤x) (j : ℕ) :
    Real.sqrt (x^j)=(Real.sqrt x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx j),ih,pow_succ]

theorem annularMass_lower_bound (B j : ℕ) :
    annularMass B (-(j:ℤ))≤(Real.sqrt (1/2:ℝ))^j := by
  have hx := dyadicScale_pos (-(j:ℤ))
  have hd : 1≤(1+dyadicScale (-(j:ℤ)))^B := one_le_pow₀ (by linarith)
  have he : dyadicScale (-(j:ℤ))=(1/2:ℝ)^j := by
    simp [dyadicScale,zpow_neg,inv_pow]
  calc
    annularMass B (-(j:ℤ))≤Real.sqrt (dyadicScale (-(j:ℤ))) :=
      div_le_self (Real.sqrt_nonneg _) hd
    _=(Real.sqrt (1/2:ℝ))^j := by rw [he,sqrt_nat_pow _ (by norm_num)]

theorem annularMass_upper_bound (B A j : ℕ) (hAB : A+1≤B) :
    annularMass B (j:ℤ)≤((2:ℝ)^A)⁻¹^j := by
  have hx : 1≤dyadicScale (j:ℤ) := by
    simp only [dyadicScale,zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hp : 0<dyadicScale (j:ℤ) := dyadicScale_pos _
  have hd : dyadicScale (j:ℤ)^(A+1)≤(1+dyadicScale (j:ℤ))^B :=
    (pow_le_pow_left₀ hp.le (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hAB)
  have hb : annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := by
    unfold annularMass
    exact div_le_div₀ hp.le (Real.sqrt_le_self_iff.mpr (Or.inr hx))
      (by positivity) hd
  calc
    annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := hb
    _=((2:ℝ)^A)⁻¹^j := by
      rw [pow_succ,mul_comm (dyadicScale (j:ℤ)^A),div_mul_cancel_left₀ (ne_of_gt hp)]
      simp only [dyadicScale,zpow_natCast,←pow_mul,inv_pow]
      rw [Nat.mul_comm]

lemma nonnegative_geometric_tail (f : ℕ→ℝ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1)
    (hf : ∀j,0≤f j) (hb : ∀j,f j≤q^j) (L : ℕ) :
    Summable (fun j=>f (j+L)) ∧ (∑'j:ℕ,f (j+L))≤q^L/(1-q) := by
  have hg : Summable (fun j:ℕ=>q^(j+L)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^L)
  have hs := Summable.of_nonneg_of_le (fun j=>hf (j+L)) (fun j=>hb (j+L)) hg
  refine ⟨hs,(hs.tsum_le_tsum (fun j=>hb (j+L)) hg).trans_eq ?_⟩
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1]
  ring

theorem annularMass_lower_tail (B L : ℕ) :
    Summable (fun j:ℕ=>annularMass B (-((j+L:ℕ):ℤ))) ∧
      (∑'j:ℕ,annularMass B (-((j+L:ℕ):ℤ)))≤
        (Real.sqrt (1/2:ℝ))^L/(1-Real.sqrt (1/2:ℝ)) := by
  apply nonnegative_geometric_tail (fun j=>annularMass B (-(j:ℤ)))
    (Real.sqrt (1/2:ℝ)) (Real.sqrt_nonneg _)
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
    (fun j=>annularMass_nonneg _ _) (annularMass_lower_bound B) L

theorem annularMass_upper_tail (B A L : ℕ) (hA : 1≤A) (hAB : A+1≤B) :
    Summable (fun j:ℕ=>annularMass B ((j+L:ℕ):ℤ)) ∧
      (∑'j:ℕ,annularMass B ((j+L:ℕ):ℤ))≤
        (((2:ℝ)^A)⁻¹)^L/(1-((2:ℝ)^A)⁻¹) := by
  have hp : 1<(2:ℝ)^A := by
    calc
      1<(2:ℝ)^1 := by norm_num
      _≤(2:ℝ)^A := pow_le_pow_right₀ (by norm_num) hA
  apply nonnegative_geometric_tail (fun j=>annularMass B (j:ℤ))
    ((2:ℝ)^A)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hp)
    (fun j=>annularMass_nonneg _ _) (fun j=>annularMass_upper_bound B A j hAB) L

theorem annularMass_summable (B : ℕ) (hB : 2≤B) : Summable (annularMass B) := by
  apply Summable.of_nat_of_neg
  · simpa only [Nat.add_zero] using (annularMass_upper_tail B 1 0 (by omega) hB).1
  · simpa only [Nat.add_zero] using (annularMass_lower_tail B 0).1

theorem logProfile_dyadic_seminorm_sum (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) (hB : 2≤B) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
      Summable (fun n:ℤ=>Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)) ∧
      (∑'n:ℤ,Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t))≤
        C*(1+‖t‖)^J := by
  obtain ⟨J,hJ⟩ := logProfile_finite_seminorm a b ha H B
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hbound⟩ := hJ W hs hW
  have hmass := annularMass_summable B hB
  have hmass0 : 0≤∑'n:ℤ,annularMass B n := tsum_nonneg (annularMass_nonneg B)
  refine ⟨CF*(1+∑'n:ℤ,annularMass B n),by positivity,?_⟩
  intro t
  let f := fun n:ℤ=>Real.sqrt (dyadicScale n)*
    H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)
  have hf0 : ∀n,0≤f n := fun n=>
    mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hb : ∀n,f n≤(CF*(1+‖t‖)^J)*annularMass B n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hbound _ (dyadicScale_pos n) t)
      (Real.sqrt_nonneg (dyadicScale n))
    exact h.trans_eq (by unfold annularMass;ring)
  have hg := hmass.mul_left (CF*(1+‖t‖)^J)
  have hf := Summable.of_nonneg_of_le hf0 hb hg
  refine ⟨hf,(hf.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_mul_left]
  nlinarith [show 0≤CF*(1+‖t‖)^J by positivity]

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def norm (I : NI) : ℝ := I.val.absNorm
lemma norm_pos (I : NI) : 0 < norm I := CompletedGauss.nonzeroIdeal_norm_pos I

def outside (S : Finset (Ideal O)) (I : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ I
abbrev SmoothIdeal (S : Finset (Ideal O)) := {I : NI // primeSupport I.val ⊆ S}
abbrev OutsideIdeal (S : Finset (Ideal O)) := {I : NI // outside S I.val}

def extract (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∈ S)).prod
def residual (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∉ S)).prod
lemma extract_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (extract S I) = (normalizedFactors I).filter (· ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (residual S I) = (normalizedFactors I).filter (· ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma extract_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : extract S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : residual S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma reconstruct (S : Finset (Ideal O)) (I : NI) :
    extract S I.val * residual S I.val = I.val := by
  rw [extract, residual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self I.property
lemma extract_smooth (S : Finset (Ideal O)) (I : Ideal O) :
    primeSupport (extract S I) ⊆ S := by
  intro P hP
  have hh : P ∈ normalizedFactors I ∧ P ∈ S := by
    simpa only [primeSupport, extract_factors, Multiset.mem_toFinset, Multiset.mem_filter] using hP
  exact hh.2
lemma outside_iff_factors (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ normalizedFactors I.val, P ∉ S := by
  constructor
  · intro h P hP hPS
    exact h P hPS (dvd_of_mem_normalizedFactors hP)
  · intro h P hPS hd
    exact h P ((mem_normalizedFactors_iff I.property).mpr ⟨hS P hPS, hd⟩) hPS
lemma residual_outside (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    outside S (residual S I) := by
  rw [outside_iff_factors S hS ⟨_, residual_ne_zero S I⟩, residual_factors]
  intro P hP
  exact (Multiset.mem_filter.mp hP).2
lemma split_product (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (D : SmoothIdeal S) (J : OutsideIdeal S) :
    extract S (D.val.val * J.val.val) = D.val.val ∧
      residual S (D.val.val * J.val.val) = J.val.val := by
  have hd : (normalizedFactors D.val.val).filter (· ∈ S) = normalizedFactors D.val.val :=
    Multiset.filter_eq_self.mpr (fun P hP => D.property (Multiset.mem_toFinset.mpr hP))
  have hj : (normalizedFactors J.val.val).filter (· ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact (outside_iff_factors S hS J.val).mp J.property P hP
  have hd' : (normalizedFactors D.val.val).filter (· ∉ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_not.mpr (D.property (Multiset.mem_toFinset.mpr hP))
  have hj' : (normalizedFactors J.val.val).filter (· ∉ S) = normalizedFactors J.val.val :=
    Multiset.filter_eq_self.mpr ((outside_iff_factors S hS J.val).mp J.property)
  simp only [extract, residual, normalizedFactors_mul D.val.property J.val.property,
    Multiset.filter_add, hd, hj, hd', hj', add_zero, zero_add,
    Ideal.prod_normalizedFactors_eq_self D.val.property,
    Ideal.prod_normalizedFactors_eq_self J.val.property, and_self]

def splitEquiv (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    NI ≃ SmoothIdeal S × OutsideIdeal S where
  toFun I := (⟨⟨extract S I.val, extract_ne_zero S I.val⟩, extract_smooth S I.val⟩,
    ⟨⟨residual S I.val, residual_ne_zero S I.val⟩, residual_outside S hS I.val⟩)
  invFun p := ⟨p.1.val.val * p.2.val.val, mul_ne_zero p.1.val.property p.2.val.property⟩
  left_inv I := Subtype.ext (reconstruct S I)
  right_inv p := by
    obtain ⟨hd, hj⟩ := split_product S hS p.1 p.2
    exact Prod.ext (Subtype.ext (Subtype.ext hd)) (Subtype.ext (Subtype.ext hj))

lemma outside_iff_coprime (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ S, IsCoprime I.val P := by
  have he (P : Ideal O) (hP : Prime P) : primeSupport P = {P} := by
    simp only [primeSupport]
    have hf : normalizedFactors P = {P} := by
      simpa using normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
        (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP)
    simp [hf]
  simp only [outside]
  apply forall_congr'
  intro P
  apply forall_congr'
  intro hP
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff I.property (hS P hP).ne_zero,
    he P (hS P hP), Finset.disjoint_singleton_right]
  simp only [primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff I.property, hS P hP, true_and]

lemma deleted_coefficient (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : NI) :
    idealCoeff (η.excludePrimes S hS) I.val =
      if outside S I.val then idealCoeff η I.val else 0 := by
  rw [idealCoeff_excludePrimes, outside_iff_coprime S hS I]
  split_ifs <;> rfl

def DecayTwo (F : ℝ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x^2 * ‖F x‖ ≤ C

lemma schwartz_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo W := by
  refine ⟨SchwartzMap.seminorm ℝ 2 0 W, apply_nonneg _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_of_pos hx] using
    SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 x

lemma reflected_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo (paperRadialFourier W) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro x hx
  exact (mul_le_mul_of_nonneg_right (by nlinarith : x^2 ≤ (1+x)^2)
    (norm_nonneg _)).trans (hb W x hx.le)

lemma inverse_norm_sq_summable : Summable (fun I : NI => (norm I ^ 2)⁻¹) := by
  have h := CompletedGauss.nonzeroIdeal_norm_rpow_summable 2 (by norm_num)
  convert h using 1
  funext I
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI => ‖F (norm I / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (norm_pos I) hX
  have h : ‖F (norm I / X)‖ ≤ C / (norm I / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma plain_summable (η : Character) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => idealCoeff η I.val * F (norm I / X)) := by
  apply Summable.of_norm
  apply (radial_summable_norm F hF X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)

lemma pair_radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : NI × NI => ‖F (norm p.1 * norm p.2 / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  have hs := inverse_norm_sq_summable.mul_of_nonneg inverse_norm_sq_summable
    (fun I => by positivity) (fun I => by positivity)
  apply (hs.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  have hx := div_pos (mul_pos (norm_pos p.1) (norm_pos p.2)) hX
  have h : ‖F (norm p.1 * norm p.2 / X)‖ ≤ C / (norm p.1 * norm p.2 / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma restricted_pair_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val,p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)

lemma outside_plain_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) =
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / X) := by
  have he := tsum_subtype {I : NI | outside S I.val}
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  change (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  rw [deleted_coefficient]
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, idealCoeff η (D.val.val * J.val.val) *
      F (norm D.val * norm J.val / X)) =
    idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  rw [← outside_plain_tsum η S hS F, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [map_mul, mul_assoc]
  congr 2
  field_simp

lemma restoration_plain_summable (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  exact (restricted_pair_summable η S F hF X hX).prod.congr
    (fun D => restoration_inner η S hS F X D)

theorem restoration_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI, idealCoeff η I.val * F (norm I / X)) =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val *
        ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  have hp := (restricted_pair_summable η S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      norm ((splitEquiv S hS).symm p) = norm p.1.val * norm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner η S hS F X D)

lemma normalization_factor (X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt (X/N) : ℂ)⁻¹ = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Real.sqrt_div hX.le, Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

lemma normalized_restoration_term (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (hX : 0<X) (D : SmoothIdeal S) :
    idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D.val))]
  change idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
    ((Real.sqrt (X / norm D.val) : ℂ)⁻¹ *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) = _
  have h := normalization_factor X (norm D.val) hX (norm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val.val *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) * h

theorem normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false F X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 := by
  constructor
  · apply ((restoration_plain_summable η S hS F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm
  · rw [polynomial_plain _ _ _ hX]
    change (Real.sqrt X : ℂ)⁻¹ * (∑' I : NI, idealCoeff η I.val * F (norm I / X)) = _
    rw [restoration_plain η S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm

theorem reflected_normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0 :=
  normalized_restoration η S hS _ (reflected_decayTwo W) X hX

def outsideSum (η : Character) (S : Finset (Ideal O)) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI, (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)

lemma outsideSum_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)
  · simp

lemma outside_mul_prime (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPS : P ∉ S) (I : Ideal O) :
    outside S (P*I) ↔ outside S I := by
  have hn (Q : Ideal O) (hQ : Q ∈ S) : ¬ Q ∣ P := by
    intro hd
    have he : Q = P := associated_iff_eq.mp (((hS Q hQ).dvd_prime_iff_associated hP).mp hd)
    exact hPS (he ▸ hQ)
  simp only [outside]
  apply forall_congr'
  intro Q
  apply forall_congr'
  intro hQ
  rw [(hS Q hQ).dvd_mul, not_or, and_iff_right (hn Q hQ)]

lemma prime_shift_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI, if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) =
    idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  let f : NI → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0
  let g : NI → ℂ := fun I => idealCoeff η P *
    ((if outside S I.val then idealCoeff η I.val else 0) * F (norm I / (X / (P.absNorm : ℝ))))
  let e : NI → NI := fun I => ⟨P*I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI) : f (e I) = g I := by
    have hn : norm (e I) = (P.absNorm : ℝ) * norm I := by
      simp only [norm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      map_mul, g]
    change (if outside S I.val then idealCoeff η P * idealCoeff η I.val else 0) *
      F (norm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J,hJ⟩ := hd
      have hj : J ≠ 0 := by intro hz; exact I.property (by rw [hJ,hz,mul_zero])
      have hei : e ⟨J,hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J,hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J,hj⟩,hg⟩,hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η (insert P S) F X = outsideSum η S F X -
      idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable η S F hF X hX
  have hd : Summable (fun I : NI => if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) := by
    exact hs.indicator {I : NI | P ∣ I.val}
  rw [← prime_shift_tsum η S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

theorem finite_deletion_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η S F X = ∑ D ∈ S.powerset, (-1 : ℂ)^D.card * idealCoeff η (∏ P ∈ D, P) *
      (∑' I : NI, idealCoeff η I.val * F (norm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty => simp [outsideSum, outside]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert η S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, map_mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (η : Character) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (D : NI) :
    idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
      HeckeDyadic.polynomial η false F (X / norm D) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D))]
  change idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
    ((Real.sqrt (X / norm D) : ℂ)⁻¹ *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) = _
  have h := normalization_factor X (norm D) hX (norm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val *
    ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) * h

theorem normalized_finite_deletion (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (-1 : ℂ)^D.card *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [polynomial_plain _ _ _ hX]
  have he : (∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F ((I.val.absNorm : ℝ) / X)) =
      outsideSum η S F X := by
    apply tsum_congr
    intro I
    rw [deleted_coefficient]
    rfl
  rw [he, finite_deletion_plain η S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term η F X hX ⟨∏P∈D,P, subset_product_nonzero D hDS⟩
  dsimp only [norm] at ht
  dsimp only [norm]
  linear_combination -(-1 : ℂ)^D.card * ht

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

theorem normalized_finite_deletion_moebius (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [normalized_finite_deletion η S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]

def reflectedTerm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P) : ℝ) * norm H.val) : ℂ) *
    HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
      (Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val)) 0 0

lemma reflectedTerm_eq (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H =
      ((moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ))) *
      (idealCoeff ηi H.val.val / (Real.sqrt (norm H.val) : ℂ) *
        HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val) 0 0) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem deletion_reflection (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hreflect : ∀ Y : ℝ, 0<Y → HeckeDyadic.polynomial η false W Y 0 0 =
      G * HeckeDyadic.polynomial ηi false F (Q/Y) 0 0)
    (X : ℝ) (hX : 0<X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS F X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm η ηi S hS F X Q D H := by
  have hnorm (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D,P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D,P) : ℂ) *
      (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq η ηi S hS F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius η S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]

theorem primitive_deleted_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS (paperRadialFourier W) X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      TraceCharacter.normalizedGauss c χ *
        ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H := by
  dsimp only
  apply deletion_reflection _ _ S hS W (paperRadialFourier W)
    (schwartz_decayTwo W) (reflected_decayTwo W) _ _ _
    (fun Y hY => primitive_normalized_reflection c χ hu hp hχ W Y hY) X hX
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))

theorem primitive_deleted_reflection_absolute (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,
      ‖reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H‖) := by
  dsimp only
  exact summable_sum (fun D hD =>
    ((primitive_deleted_reflection c χ hu hp hχ S hS W X hX).1 D hD).norm)

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalReflection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

lemma polynomial_coeff_congr (χ ψ : Character)
    (h : ∀I,idealCoeff χ I=idealCoeff ψ I) (W : ℝ→ℂ) (X : ℝ) :
    HeckeDyadic.polynomial χ false W X 0 0=HeckeDyadic.polynomial ψ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [h]

lemma inverse_deletion_coeff (χ ψ : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (h : ∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I)
    (I : Ideal O) : idealCoeff χ.inverse I=idealCoeff (ψ.inverse.excludePrimes S hS) I := by
  rw [idealCoeff_inverse_conj,h,idealCoeff_excludePrimes,idealCoeff_excludePrimes,
    idealCoeff_inverse_conj]
  split_ifs <;> simp

theorem primitive_character_deleted (ψ : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals ψ.residue) (hn : ψ.residue≠1) :
    ∃G : ℂ,‖G‖=1 ∧ ∀(S : Finset (Ideal O))(hS : ∀P∈S,Prime P)
      (W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
      (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
        X (ψ.modulus.absNorm:ℝ) D)) ∧
      HeckeDyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
        G*∑D∈S.powerset,∑'H : SmoothIdeal S,
          reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  rcases ψ with ⟨M,hM,χ,hu,p,hp0,hpm⟩
  obtain ⟨c,hc⟩ := Submodule.IsPrincipal.principal M
  change M=Ideal.span {c} at hc
  subst M
  have hc0 : c≠0 := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hM
  let : NeZero c := ⟨hc0⟩
  refine ⟨TraceCharacter.normalizedGauss c χ,TraceCharacter.normalizedGauss_norm c χ hp,?_⟩
  intro S hS W X hX
  have hh := primitive_deleted_reflection c χ hu hp hn S hS W X hX
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hh
  exact hh

theorem original_natural_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      let hS := redundantSet_prime χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      (∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I) ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
          X (ψ.modulus.absNorm:ℝ) D)) ∧
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  obtain ⟨ψ,hmod,hprim,hne,hsq,hcop,hdvd,hnorm,hcoeff⟩ := exists_natural_primitive χ
  obtain ⟨G,hG,hreflection⟩ := primitive_character_deleted ψ hprim (hne hn)
  refine ⟨ψ,G,hprim,hne hn,hG,hnorm,hcop,hcoeff,?_⟩
  intro W X hX
  have hh := hreflection _ (redundantSet_prime χ.modulus ψ.modulus) W X hX
  exact ⟨hh.1,(polynomial_coeff_congr χ _ hcoeff W X).trans hh.2⟩

theorem original_inverse_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false (paperRadialFourier W)
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hprim,hne,hG,hnorm,hcop,hcoeff,hreflect⟩ := original_natural_reflection χ hn
  refine ⟨ψ,G,hprim,hne,hG,hnorm,?_⟩
  intro W X hX
  rw [(hreflect W X hX).2]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  unfold reflectedTerm
  rw [←polynomial_coeff_congr χ.inverse _
    (inverse_deletion_coeff χ ψ _ (redundantSet_prime χ.modulus ψ.modulus) hcoeff)]

end SevenEighths.CenteredMomentNaturalReflection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedSeries -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

lemma dyadicIdealTerm_norm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm

lemma dyadic_ideal_partition (η : Character) (F : ℝ→ℂ) (Y : ℝ) (hY : 0<Y) (I : NI) :
    (∑'n : ℤ,dyadicIdealTerm η F Y I n)=idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y) := by
  have he (n : ℤ) : dyadicIdealTerm η F Y I n=
      (dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*(idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    unfold dyadicIdealTerm
    ring
  simp_rw [he]
  have hp : 0<(I.val.absNorm:ℝ)/Y := div_pos (HeckeDyadic.norm_pos I) hY
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition _ hp]
  simp

theorem normalized_annular_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false F Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have habs := dyadic_ideal_absolute η F hF Y hY
  have hs := habs.of_norm
  have he (n : ℤ) : (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,dyadicIdealTerm η F Y I n := by
    rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
      polynomial_plain _ _ _ hY]
    congr 1
    apply tsum_congr
    intro I
    simp only [dyadicIdealTerm,dyadicWeight]
    ring
  simp_rw [he]
  refine ⟨hs.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η F Y hY]
  congr 1
  rw [hs.tsum_comm]
  exact tsum_congr (fun I=>(dyadic_ideal_partition η F Y hY I).symm)

theorem actual_reflected_annular_series (η : Character) (W : 𝓢(ℝ,ℂ))
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
        (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
          (dyadicScale n*Y) 0 0 := by
  exact normalized_annular_series η _ (reflected_decayTwo W) Y hY

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem normalized_subseries (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) (A : Set ℤ) :
    Summable (fun n : ℤ=>if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0) ∧
    HeckeDyadic.polynomial η false
      (fun x=>(∑'n : ℤ,if n∈A then dyadicWeight n x else 0:ℝ)*F x) Y 0 0=
      ∑'n : ℤ,if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0 := by
  have hs := (dyadic_ideal_absolute η F hF Y hY).of_norm
  have hi : Summable (fun p : NI×ℤ=>if p.2∈A then dyadicIdealTerm η F Y p.1 p.2 else 0) :=
    hs.indicator {p : NI×ℤ | p.2∈A}
  have he (n : ℤ) : (if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0)=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,if n∈A then dyadicIdealTerm η F Y I n else 0 := by
    split_ifs with hn
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      congr 1
      apply tsum_congr
      intro I
      simp only [dyadicIdealTerm,dyadicWeight]
      ring
    · simp
  simp_rw [he]
  refine ⟨hi.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η _ Y hY]
  congr 1
  rw [hi.tsum_comm]
  apply tsum_congr
  intro I
  have ht (n : ℤ) : (if n∈A then dyadicIdealTerm η F Y I n else 0)=
      ((if n∈A then dyadicWeight n ((I.val.absNorm:ℝ)/Y) else 0:ℝ):ℂ)*
        (idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    split_ifs <;> simp only [dyadicIdealTerm,Complex.ofReal_zero,zero_mul] ; ring
  simp_rw [ht]
  rw [tsum_mul_right,←Complex.ofReal_tsum]
  ring

def retainedAnnuli (R Y : ℝ) (hY : 0<Y) : Finset ℤ :=
  (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).toFinset

lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0<Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset

lemma original_norm_lower (I : NI) (Y : ℝ) (hY : 0<Y) :
    Y⁻¹≤(I.val.absNorm:ℝ)/Y := by
  have hn : (1:ℝ)≤I.val.absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
  simpa only [one_div] using div_le_div_of_nonneg_right hn hY.le

theorem retained_finite_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=
      ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have hh := (normalized_subseries η F hF Y hY {n | Retained R n}).2
  change HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=_ at hh
  rw [hh,tsum_eq_sum (s:=retainedAnnuli R Y hY)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Set.mem_ofPred_eq,ite_eq_left ((retainedAnnuli_mem R Y hY n).mp hn).1]
  · intro n hn
    split_ifs with hr
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      have hz (I : NI) : dyadicWeight n ((I.val.absNorm:ℝ)/Y)=0 := by
        by_contra hne
        exact hn ((retainedAnnuli_mem R Y hY n).mpr ⟨hr,_,original_norm_lower I Y hY,hne⟩)
      have he (I : NI) : idealCoeff η I.val*
          ((annulus (((I.val.absNorm:ℝ)/Y)/dyadicScale n):ℂ)*F ((I.val.absNorm:ℝ)/Y))=0 := by
        change idealCoeff η I.val*((dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F _)=0
        rw [hz,Complex.ofReal_zero,zero_mul,mul_zero]
      simp_rw [he,tsum_zero,mul_zero]
    · rfl

end SevenEighths.CenteredMomentReflectedTruncation

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ReflectionMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

def weight (I : Ideal O) : ℝ := (Real.sqrt (I.absNorm : ℝ))⁻¹
lemma weight_nonneg (I : Ideal O) : 0 ≤ weight I := by unfold weight; positivity
lemma weight_mul (I J : Ideal O) : weight (I*J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring
lemma weight_one : weight (1 : Ideal O) = 1 := by simp [weight]
lemma weight_pow (I : Ideal O) (n : ℕ) : weight (I ^n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ,weight_mul,ih,pow_succ]
lemma weight_prod (S : Finset (Ideal O)) (f : Ideal O → Ideal O) :
    weight (∏ P ∈ S,f P) = ∏ P ∈ S,weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h,weight_mul,ih]
lemma prime_weight_lt_one (P : Ideal O) (hP : Prime P) : weight P < 1 := by
  have h : (1:ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

def exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) (P : S) : ℕ :=
  (normalizedFactors I.val.val).count P.val
lemma reconstruct_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    (∏ P : S,P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)
lemma exponents_injective (S : Finset (Ideal O)) : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I,← reconstruct_exponents S J,h]
lemma weight_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    weight I.val.val = ∏ P : S,weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1-r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (fun n => pow_nonneg (hr none) n)
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

lemma smooth_summable (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    (∑' I : SmoothIdeal S,weight I.val.val) ≤ ∏ P ∈ S,(1-weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq,Finset.prod_coe_sort S (fun P => (1-weight P)⁻¹)] at h
  exact h

lemma deletion_mass (S : Finset (Ideal O)) :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D,P)) = ∏ P ∈ S,(1+weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

def localMass (P : Ideal O) : ℝ := (1+weight P)/(1-weight P)
lemma localMass_nonneg (P : Ideal O) (hP : Prime P) : 0 ≤ localMass P := by
  exact div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le
lemma prime_weight_le (P : Ideal O) (hP : Prime P) : weight P ≤ 3/4 := by
  have hn : (2:ℝ) ≤ P.absNorm := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩ : 2 ≤ P.absNorm)
  have hs : 4/3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith
lemma localMass_le_seven (P : Ideal O) (hP : Prime P) : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]
lemma localMass_le_three (P : Ideal O) (hP : Prime P) (hn : (4:ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1/2 := by
    rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P),
      (∏ P ∈ S,localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S,P) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3:ℝ)))
  let K : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 4 B ≤ (K:ℝ) := Nat.le_ceil _
  refine ⟨(7:ℝ)^smallIdeals.card,by positivity,?_⟩
  intro S hS
  have hpoint (P : Ideal O) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε := by
    have hn : (1:ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hS P hP⟩
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm:ℝ)^ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [ite_eq_left hp]
      exact (localMass_le_seven P (hS P hP)).trans (by nlinarith)
    · have hpk : (K:ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ K := by
          intro h
          apply hp
          exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr ⟨by exact_mod_cast hn,h⟩
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4:ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm:ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [ite_eq_right hp,one_mul]
      exact (localMass_le_three P (hS P hP) h4).trans (hB _ hb)
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S,localMass P) ≤ ∏ P ∈ S,((if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε) :=
      Finset.prod_le_prod₀ (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7:ℝ)^(S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
      rw [Finset.prod_mul_distrib,← Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (Real.rpow_nonneg (by positivity) _)

def coefficient (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P):ℝ) * norm H.val) : ℂ)

lemma coefficient_norm_le (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (hD : ∀ P ∈ D,Prime P) (H : SmoothIdeal S) :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖idealCoeff η (∏ P ∈ D,P)‖ * ‖idealCoeff ηi H.val.val‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η _) (idealCoeff_norm_le_one ηi _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

lemma coefficient_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP)) H

lemma coefficient_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (coefficient η ηi S D) := (coefficient_summable_norm η ηi S hS D hD).of_norm

lemma coefficient_mass_le_euler (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := by
  exact summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : Character),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

def unitSmooth (S : Finset (Ideal O)) : SmoothIdeal S :=
  ⟨⟨1,one_ne_zero⟩,by
    change (normalizedFactors (1 : Ideal O)).toFinset ⊆ S
    rw [normalizedFactors_one]
    exact Finset.empty_subset _⟩
lemma coefficient_empty_unit (η ηi : Character) (S : Finset (Ideal O)) :
    coefficient η ηi S ∅ (unitSmooth S) = 1 := by
  have hm : (moebius (1 : Ideal O) : ℂ) = 1 := by
    simpa only [Finset.prod_empty,Finset.card_empty,pow_zero] using
      subset_product_moebius ∅ (by simp)
  change (moebius (1 : Ideal O) : ℂ) * idealCoeff η 1 * idealCoeff ηi 1 /
    (Real.sqrt ((Ideal.absNorm (1 : Ideal O) : ℝ) * (Ideal.absNorm (1 : Ideal O) : ℝ)) : ℂ) = 1
  rw [hm,map_one,map_one,map_one]
  norm_num

lemma reflectedTerm_eq_coefficient (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H = coefficient η ηi S D H *
      HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
        (Q * (Ideal.absNorm (∏ P ∈ D,P):ℝ)/(X*norm H.val)) 0 0 := rfl

end SevenEighths.CenteredMomentReflectionMass
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonMaskExpansion
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def naturalSlot (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹ * ∑ I∈pool,idealCoeff χ I*β I

def profileSlot (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P : ℝ) : ℂ :=
  naturalSlot χ pool (fun I=>ν I*W ((I.absNorm:ℝ)/P)) P

lemma outside_prime (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) : outside R I ↔ I∉R := by
  constructor
  · intro h hi
    exact h I hi dvd_rfl
  · intro h J hj hd
    have he : J=I := (prime_dvd_prime_iff_eq (hR J hj) hI).mp hd
    exact h (he ▸ hj)

lemma deleted_prime (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) :
    idealCoeff (χ.excludePrimes R hR) I = if I∈R then 0 else idealCoeff χ I := by
  have h:=deleted_coefficient χ R hR ⟨I,hI.ne_zero⟩
  simpa only [outside_prime R hR I hI,ite_not] using h

theorem naturalSlot_delete (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (pool : Finset (Ideal O)) (hp : ∀ I∈pool,Prime I) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (χ.excludePrimes R hR) pool β P =
      naturalSlot χ pool β P - naturalSlot χ (pool∩R) β P := by
  unfold naturalSlot
  have hinter : pool∩R=pool.filter (fun I=>I∈R) := by ext I;simp
  rw [←mul_sub,hinter,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hi
  rw [deleted_prime χ R hR I (hp I hi)]
  by_cases h:I∈R <;> simp [h]

lemma prod_sub_expansion {α : Type*} [DecidableEq α] (F : Finset α) (a b : α→ℂ) :
    (∏i∈F,(a i-b i))=∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,b i)*(∏i∈F\J,a i) := by
  have he : (∏i∈F,(a i-b i))=∏i∈F,((-b i)+a i) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [he,Finset.prod_add]
  simp only [Finset.prod_neg]

def plainCoefficient (χ : Character) (D : Finset (Ideal O)) : ℂ :=
  (moebius (∏I∈D,I):ℂ)*(idealCoeff χ (∏I∈D,I)/(Real.sqrt (Ideal.absNorm (∏I∈D,I):ℝ):ℂ))

variable {α : Type*} [DecidableEq α]

def signedCoefficient (χ : Character) (R D₁ D₂ : Finset (Ideal O))
    (J : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℂ :=
  plainCoefficient χ D₁*plainCoefficient χ D₂*(-1:ℂ)^J.card*
    ∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i)

theorem simultaneous_deletion (χ : Character) (R : Finset (Ideal O))
    (hR : ∀ I∈R,Prime I) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (F : Finset α)
    (pool : α→Finset (Ideal O)) (hp : ∀i∈F,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₁ X₁ 0 0 *
      HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₂ X₂ 0 0 *
      (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
    ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      signedCoefficient χ R D₁ D₂ J pool β P *
        (HeckeDyadic.polynomial χ false W₁ (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial χ false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
  have hs : (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i))=
      ∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i))*
        (∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
    have hh:=prod_sub_expansion F (fun i=>naturalSlot χ (pool i) (β i) (P i))
      (fun i=>naturalSlot χ (pool i∩R) (β i) (P i))
    exact (Finset.prod_congr rfl (fun i hi=>naturalSlot_delete χ R hR (pool i) (hp i hi) (β i) (P i))).trans hh
  rw [normalized_finite_deletion_moebius χ R hR W₁ (schwartz_decayTwo W₁) X₁ hX₁,
    normalized_finite_deletion_moebius χ R hR W₂ (schwartz_decayTwo W₂) X₂ hX₂,hs]
  rw [Finset.sum_mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [signedCoefficient,plainCoefficient]
  ring

def slotMass (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℝ :=
  (Real.sqrt P)⁻¹ * ∑I∈pool∩R,‖β I‖

lemma slotMass_nonneg (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    0≤ slotMass R pool β P := by unfold slotMass;positivity

lemma naturalSlot_norm (χ : Character) (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ‖naturalSlot χ (pool∩R) β P‖≤ slotMass R pool β P := by
  rw [naturalSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hi
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma plainCoefficient_norm (χ : Character) (D : Finset (Ideal O))
    (hD : ∀I∈D,Prime I) : ‖plainCoefficient χ D‖≤weight (∏I∈D,I) := by
  rw [plainCoefficient,subset_product_moebius D hD]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (idealCoeff_norm_le_one χ _) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [weight,one_div])

lemma slot_point_mass (I : Ideal O) (hI : Prime I) (β : Ideal O→ℂ)
    (P b M : ℝ) (hP : 0<P) (hM : 0≤M) (hβ : ‖β I‖≤M)
    (hs : β I≠0 → (I.absNorm:ℝ)≤b*P) :
    (Real.sqrt P)⁻¹*‖β I‖≤(Real.sqrt (max 1 b)*M)*weight I := by
  by_cases hz : β I=0
  · simp only [hz,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (weight_nonneg _)
  have hN : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)
  have hB : 0≤ max 1 b := le_trans zero_le_one (le_max_left _ _)
  have hsqrt : Real.sqrt (I.absNorm:ℝ)≤Real.sqrt (max 1 b)*Real.sqrt P := by
    rw [←Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt ((hs hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP.le))
  have hi : (Real.sqrt P)⁻¹≤Real.sqrt (max 1 b)*weight I := by
    rw [weight,←div_eq_mul_inv,inv_eq_one_div,
      div_le_div_iff₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr hN)]
    simpa using hsqrt
  calc
    _≤(Real.sqrt (max 1 b)*weight I)*M :=
      mul_le_mul hi hβ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (weight_nonneg _))
    _=_ := by ring

lemma slotMass_bound (R pool : Finset (Ideal O)) (hp : ∀I∈pool,Prime I)
    (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    slotMass R pool β P≤(Real.sqrt (max 1 b)*M)*∑I∈R,weight I := by
  unfold slotMass
  rw [Finset.mul_sum]
  calc
    _≤∑I∈pool∩R,(Real.sqrt (max 1 b)*M)*weight I :=
      Finset.sum_le_sum (fun I hi=>slot_point_mass I (hp I (Finset.mem_inter.mp hi).1)
        β P b M hP hM (hβ I (Finset.mem_inter.mp hi).1) (hs I (Finset.mem_inter.mp hi).1))
    _=(Real.sqrt (max 1 b)*M)*∑I∈pool∩R,weight I := (Finset.mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun I hi hn=>weight_nonneg I))
      (mul_nonneg (Real.sqrt_nonneg _) hM)

lemma one_add_sum_weight (R : Finset (Ideal O)) :
    1+∑I∈R,weight I≤∏I∈R,(1+weight I) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert I R hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hw:=weight_nonneg I
    have hs:0≤∑J∈R,weight J:=Finset.sum_nonneg (fun J _=>weight_nonneg J)
    nlinarith

lemma deletion_le_euler (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    (∏I∈R,(1+weight I))≤∏I∈R,localMass I := by
  apply Finset.prod_le_prod₀ (fun I hi=>by linarith [weight_nonneg I])
  intro I hi
  apply (le_div_iff₀ (sub_pos.mpr (prime_weight_lt_one I (hR I hi)))).mpr
  have h:=weight_nonneg I
  nlinarith

lemma euler_ge_one (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    1≤∏I∈R,localMass I :=
  (show 1≤∏I∈R,(1+weight I) by
    linarith [Finset.sum_nonneg (s:=R) (fun I _=>weight_nonneg I),one_add_sum_weight R]).trans
    (deletion_le_euler R hR)

lemma one_add_slotMass (R pool : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (hp : ∀I∈pool,Prime I) (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    1+slotMass R pool β P≤ max 1 (Real.sqrt (max 1 b)*M)*(∏I∈R,localMass I) := by
  have ha:=slotMass_bound R pool hp β P b M hP hM hβ hs
  have hb:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hc:=le_max_left 1 (Real.sqrt (max 1 b)*M)
  have hd:=le_max_right 1 (Real.sqrt (max 1 b)*M)
  have he:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
  nlinarith

def coefficientMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*∏i∈J,slotMass R (pool i) (β i) (P i)

omit [DecidableEq α] in
lemma signedCoefficient_norm (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤ coefficientMajorant R D₁ D₂ J pool β P := by
  simp only [signedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
  apply mul_le_mul
  · exact mul_le_mul (plainCoefficient_norm χ D₁ (fun I hi=>hR I (hD₁ hi)))
      (plainCoefficient_norm χ D₂ (fun I hi=>hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
  · exact Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>naturalSlot_norm χ R (pool i) (β i) (P i))
  · positivity
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

omit [DecidableEq α] in
lemma majorant_mass (R : Finset (Ideal O)) (F : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      coefficientMajorant R D₁ D₂ J pool β P)=
      (∏I∈R,(1+weight I))^2*(∏i∈F,(1+slotMass R (pool i) (β i) (P i))) := by
  simp only [coefficientMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

def uniformMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α) (b M : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*
    ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)

omit [DecidableEq α] in
lemma uniformMajorant_nonneg (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (b M : α→ℝ) (hM : ∀i∈J,0≤M i) :
    0≤uniformMajorant R D₁ D₂ J b M := by
  apply mul_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_nonneg (fun i hi=>mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
    (Finset.sum_nonneg (fun I _=>weight_nonneg I)))

omit [DecidableEq α] in
lemma signedCoefficient_uniform (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P b M : α→ℝ)
    (hp : ∀i∈J,∀I∈pool i,Prime I) (hP : ∀i∈J,0<P i) (hM : ∀i∈J,0≤M i)
    (hβ : ∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i∈J,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤uniformMajorant R D₁ D₂ J b M := by
  apply (signedCoefficient_norm χ R hR D₁ D₂ hD₁ hD₂ J pool β P).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod₀ (fun i _=>slotMass_nonneg _ _ _ _)
    (fun i hi=>slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))

omit [DecidableEq α] in
lemma uniformMajorant_mass (R : Finset (Ideal O)) (F : Finset α) (b M : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)=
      (∏I∈R,(1+weight I))^2*
        ∏i∈F,(1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)) := by
  simp only [uniformMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

omit [DecidableEq α] in
lemma uniformMajorant_mass_le (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)) * (∏I∈R,localMass I)^(2+F.card) := by
  rw [uniformMajorant_mass]
  have hE:=euler_ge_one R hR
  have hp (i : α) (hi : i∈F) :
      1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
        max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
    have ha:1+∑I∈R,weight I≤∏I∈R,localMass I:=(one_add_sum_weight R).trans (deletion_le_euler R hR)
    have hb:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have hc:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
    nlinarith
  calc
    _≤(∏I∈R,localMass I)^2*
        ∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Finset.prod_nonneg (fun I _=>by linarith [weight_nonneg I]))
          (deletion_le_euler R hR) 2
      · exact Finset.prod_le_prod₀ (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I)))) hp
      · exact Finset.prod_nonneg (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I))))
      · exact sq_nonneg _
    _=_ := by rw [Finset.prod_mul_distrib,Finset.prod_const,pow_add];ring

omit [DecidableEq α] in

theorem uniform_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I),
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  let n:ℕ:=2+F.card
  have hn:(0:ℝ)<n:=by dsimp [n];positivity
  let δ:ℝ:=ε/n
  have hδ:0<δ:=div_pos hε hn
  obtain ⟨C₀,hC₀,hbound⟩:=euler_mass_subpower δ hδ
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0<A:=Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨A*C₀^n,mul_pos hA (pow_pos hC₀ n),?_⟩
  intro R hR
  have he:0≤∏I∈R,localMass I:=(euler_ge_one R hR).trans' zero_le_one
  have hr:0≤(Ideal.absNorm (∏I∈R,I):ℝ):=Nat.cast_nonneg _
  have hpow:((Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ _ hn.ne'
  calc
    _≤A*(∏I∈R,localMass I)^n:=uniformMajorant_mass_le R hR F b M hM
    _≤A*(C₀*(Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he (hbound R hR) n) hA.le
    _=_:=by rw [mul_pow,hpow];ring

omit [DecidableEq α] in

theorem signed_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈F,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs
  apply le_trans _ (hbound R hR)
  apply Finset.sum_le_sum
  intro D₁ hD₁
  apply Finset.sum_le_sum
  intro D₂ hD₂
  apply Finset.sum_le_sum
  intro J hJ
  have hj:=Finset.mem_powerset.mp hJ
  exact signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
    (Finset.mem_powerset.mp hD₂) J pool β P b M
    (fun i hi=>hp i (hj hi)) (fun i hi=>hP i (hj hi)) (fun i hi=>hM i (hj hi))
    (fun i hi=>hβ i (hj hi)) (fun i hi=>hs i (hj hi))

lemma profile_bounds (pool : Finset (Ideal O)) (ν : Ideal O→ℂ) (W : ℝ→ℂ)
    (P b M : ℝ) (hP : 0<P) (hν : ∀I∈pool,‖ν I‖≤1)
    (hW : ∀x,‖W x‖≤M) (hs : Function.support W⊆Set.Iic b) :
    (∀I∈pool,‖ν I*W ((I.absNorm:ℝ)/P)‖≤M) ∧
      (∀I∈pool,ν I*W ((I.absNorm:ℝ)/P)≠0 → (I.absNorm:ℝ)≤b*P) := by
  constructor
  · intro I hi
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν I hi)).trans (hW _)
  · intro I hi hn
    exact (div_le_iff₀ hP).mp (hs (right_ne_zero_of_mul hn))

omit [DecidableEq α] in

theorem profile_signed_mass_subpower (F : Finset α) (b M : α→ℝ)
    (hM : ∀i∈F,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (ν : α→Ideal O→ℂ)
      (W : α→ℝ→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖ν i I‖≤1) → (∀i∈F,∀x,‖W i x‖≤M i) →
      (∀i∈F,Function.support (W i)⊆Set.Iic (b i)) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool
          (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P‖)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=signed_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool ν W P hp hP hν hW hs
  exact hbound R hR χ pool (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P hp hP
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).1)
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).2)

end SevenEighths.CenteredMomentCommonMaskExpansion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentCommonMaskEnergy
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

theorem finite_shared_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι→κ→ℂ) (ρ : κ→ℝ) (hρ : ∀j,0≤ρ j)
    (ha : ∀i j,‖a i j‖≤ρ j) (E : ℝ) (hE : 0≤E)
    (hf : ∀j,(∑i,‖f i j‖^2)≤E) :
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j)^2*E := by
  have hb (j : κ) : (∑i,‖a i j*f i j‖^2)≤(ρ j*Real.sqrt E)^2 := by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2 := Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2) := (Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*E := mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_ := by rw [mul_pow,Real.sq_sqrt hE]
  have hh := CompletedGauss.finite_tsum_energy_bound
    (fun j i=>a i j*f i j) (fun j=>ρ j*Real.sqrt E)
    (fun j=>mul_nonneg (hρ j) (Real.sqrt_nonneg _)) (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

lemma triple_sum {τ : Type*} {υ : Type*} {ξ : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset τ) (T : Finset υ) (U : Finset ξ)
    [Fintype ({x // x∈S}×{x // x∈T}×{x // x∈U})]
    (g : τ→υ→ξ→A) :
    (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑x∈S,∑y∈T,∑z∈U,g x y z := by
  have hh : (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑j∈S×ˢ(T×ˢU),g j.1 j.2.1 j.2.2 := by
    apply Finset.sum_bij (fun j _=>(j.1.val,j.2.1.val,j.2.2.val))
    · intro j _
      exact Finset.mem_product.mpr ⟨j.1.property,Finset.mem_product.mpr ⟨j.2.1.property,j.2.2.property⟩⟩
    · intro i _ j _ h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · apply Prod.ext
        · exact Subtype.ext (congrArg (fun x=>x.2.1) h)
        · exact Subtype.ext (congrArg (fun x=>x.2.2) h)
    · intro j hj
      obtain ⟨h1,h23⟩:=Finset.mem_product.mp hj
      obtain ⟨h2,h3⟩:=Finset.mem_product.mp h23
      exact ⟨(⟨j.1,h1⟩,⟨j.2.1,h2⟩,⟨j.2.2,h3⟩),Finset.mem_univ _,rfl⟩
    · intro j _
      rfl
  simpa only [Finset.sum_product] using hh

theorem actual_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hmass⟩:=uniform_mass_subpower F b M hM (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE he
  let κ := {D : Finset (Ideal O) // D∈R.powerset} ×
    {D : Finset (Ideal O) // D∈R.powerset} × {J : Finset α // J∈F.powerset}
  let a (i : ι) (j : κ) := signedCoefficient (χ i) R j.1.val j.2.1.val j.2.2.val (pool i) (β i) (P i)
  let f (i : ι) (j : κ) := HeckeDyadic.polynomial (χ i) false (W₁ i)
    (X₁ i/(Ideal.absNorm (∏I∈j.1.val,I):ℝ)) 0 0 *
    HeckeDyadic.polynomial (χ i) false (W₂ i)
    (X₂ i/(Ideal.absNorm (∏I∈j.2.1.val,I):ℝ)) 0 0 *
    ∏k∈F\j.2.2.val,naturalSlot (χ i) (pool i k) (β i k) (P i k)
  let ρ (j : κ) := uniformMajorant R j.1.val j.2.1.val j.2.2.val b M
  have hρ (j : κ) : 0≤ρ j := uniformMajorant_nonneg _ _ _ _ _ _
    (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
  have ha (i : ι) (j : κ) : ‖a i j‖≤ρ j := by
    exact signedCoefficient_uniform (χ i) R hR _ _
      (Finset.mem_powerset.mp j.1.property) (Finset.mem_powerset.mp j.2.1.property)
      _ (pool i) (β i) (P i) b M
      (fun k hk=>hp i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hP i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hβ i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hs i k (Finset.mem_powerset.mp j.2.2.property hk))
  have hh:=finite_shared_energy a f ρ hρ ha E hE
    (fun j=>he j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property)
  have hid (i : ι) : (∑j,a i j*f i j)=
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
      ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>signedCoefficient (χ i) R D₁ D₂ J (pool i) (β i) (P i)*
        (HeckeDyadic.polynomial (χ i) false (W₁ i) (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial (χ i) false (W₂ i) (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏k∈F\J,naturalSlot (χ i) (pool i k) (β i k) (P i k)))).trans
      (simultaneous_deletion (χ i) R hR (W₁ i) (W₂ i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
        F (pool i) (hp i) (β i) (P i)).symm
  have hm : (∑j,ρ j)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J b M)).trans_le (hmass R hR)
  have hr : ((Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2))^2=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hid] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>hρ j)) hm 2) hE).trans_eq
      (by rw [mul_pow,hr]))

lemma sqrt_inverse_cpow (X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hX.le (1/2:ℝ))

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 0=(Real.sqrt X:ℂ)⁻¹*idealSum χ W X := by
  rw [sqrt_inverse_cpow X hX]
  unfold HeckeDyadic.polynomial idealSum
  congr 1
  have he:=tsum_subtype_eq_of_support_subset
    (s:={I : Ideal O | I≠0}) (f:=fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi;subst I;exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=_ at he
  simpa only [HeckeDyadic.summand,HeckeDyadic.coefficient,Bool.false_eq_true,ite_false,
    HeckeDyadic.norm,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

def heightCoefficient (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β I*(I.absNorm:ℂ)^(Complex.I*t)

lemma heightCoefficient_norm (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoefficient β t I‖=‖β I‖ := by
  have hn : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [heightCoefficient,norm_mul]
  have hp : ‖(I.absNorm:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hn (Complex.I*t)
  rw [hp,mul_one]

lemma normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X=
      (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
        (normPowerProfile W a b ha hs hW t) X 0 0 := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,plain_zero_height _ _ X hX]
  ring

theorem original_positive_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) X₁ 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₂ 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  rw [F.masked_positive R hR,twistedIdealSum_scale _ W₁ a₁ b₁ ha₁ hs₁ hW₁ t X₁ hX₁,
    twistedIdealSum_scale _ W₂ a₂ b₂ ha₂ hs₂ hW₂ t X₂ hX₂,
    plain_zero_height _ _ X₁ hX₁,plain_zero_height _ _ X₂ hX₂]
  have hn : (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i : α) : (∑I∈pool i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t))=
      ∑I∈pool i,idealCoeff (excluded F.character R) I*heightCoefficient (β i) t I := by
    apply Finset.sum_congr rfl
    intro I hI
    unfold heightCoefficient
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  ring

lemma deleted_height_phase (X N t : ℝ) (hX : 0<X) (hN : 0<N) :
    (X:ℂ)^(Complex.I*t)=(N:ℂ)^(Complex.I*t)*((X/N:ℝ):ℂ)^(Complex.I*t) := by
  have hh:=Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg hX.le hN.le) (Complex.I*t)
  rw [←Complex.ofReal_mul,show N*(X/N)=X by field_simp] at hh
  exact hh

lemma positive_height_phase_norm (X t : ℝ) (hX : 0<X) : ‖(X:ℂ)^(Complex.I*t)‖=1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX (Complex.I*t)

lemma deleted_normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
      (normPowerProfile W a b ha hs hW t) (X/N) 0 0=
      (N:ℂ)^(Complex.I*t)*((Real.sqrt (X/N):ℂ)⁻¹*twistedIdealSum χ W t (X/N)) := by
  rw [normalized_twisted_plain χ W a b ha hs hW t (X/N) (div_pos hX hN),
    deleted_height_phase X N t hX hN]
  ring

theorem original_positive_deletion {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
          signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          (HeckeDyadic.polynomial χ false (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
            (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
           HeckeDyadic.polynomial χ false (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
            (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
           ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_normalized (naturalRow η z hz) R hR W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P hP t X₁ X₂ hX₁ hX₂]
  congr 1
  exact simultaneous_deletion (naturalRow η z hz).character (CompletedGauss.primeSupport R)
    (support_prime R) (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
    (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₁ X₂ hX₁ hX₂ Finset.univ pool
    (fun i _=>hp i) (fun i=>heightCoefficient (β i) t) P

theorem original_retained_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr₁ : 1≤X₁*b₁) (hr₂ : 1≤X₂*b₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      (((clippedScale X₁):ℂ)^(Complex.I*t)*((clippedScale X₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ X₁ hX₁ hr₁ t) (clippedScale X₁) 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ X₂ hX₂ hr₂ t) (clippedScale X₂) 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  exact original_positive_normalized F R hR (dilated W₁ (clipDilation X₁))
    (dilated W₂ (clipDilation X₂)) (a₁/max 1 b₁) b₁ (a₂/max 1 b₂) b₂
    (div_pos ha₁ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W₁ a₁ b₁ (max 1 b₁) (clipDilation X₁) ha₁ (le_max_left _ _)
      (clipDilation_ge_one X₁ hX₁) (clipDilation_le b₁ X₁ hX₁ hr₁) hs₁)
    (dilated_support W₂ a₂ b₂ (max 1 b₂) (clipDilation X₂) ha₂ (le_max_left _ _)
      (clipDilation_ge_one X₂ hX₂) (clipDilation_le b₂ X₂ hX₂ hr₂) hs₂)
    (dilated_contDiff W₁ hW₁ _) (dilated_contDiff W₂ hW₂ _) pool β P hP t
    _ _ (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)

theorem original_retained_zero {α : Type*} [Fintype α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hz : X₁*b₁<1 ∨ X₂*b₂<1) :
    retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂=0 := by
  unfold retainedPositiveRow positiveSlotRow
  rw [←clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  rcases hz with h|h
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h]
    simp
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h]
    simp

theorem original_positive_energy {α : Type*} [Fintype α] [DecidableEq α]
    (b M : α→ℝ) (hM : ∀j,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)(R : Ideal O),R≠0 →
      ∀(W₁ W₂ : ι→ℝ→ℂ)(a₁ b₁ a₂ b₂ : ι→ℝ)
        (ha₁ : ∀i,0<a₁ i)(ha₂ : ∀i,0<a₂ i)
        (hs₁ : ∀i,Function.support (W₁ i)⊆Set.Icc (a₁ i) (b₁ i))
        (hs₂ : ∀i,Function.support (W₂ i)⊆Set.Icc (a₂ i) (b₂ i))
        (hW₁ : ∀i,ContDiff ℝ ∞ (W₁ i))(hW₂ : ∀i,ContDiff ℝ ∞ (W₂ i))
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)
        (t X₁ X₂ : ι→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
      (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      let χ:=fun i=>(naturalRow (η i) (z i) (hz i)).character
      let S:=CompletedGauss.primeSupport R
      (∀D₁∈S.powerset,∀D₂∈S.powerset,∀J∈(Finset.univ : Finset α).powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈Finset.univ\J,naturalSlot (χ i) (pool i j) (heightCoefficient (β i j) (t i)) (P i j)‖^2)≤E) →
      (∑i,‖positiveSlotRow (η i)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
        1 (z i) (W₁ i) (W₂ i) (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i)‖^2)≤
        C*(Ideal.absNorm (∏I∈S,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hbound⟩:=actual_shared_energy (Finset.univ : Finset α) b M (fun j _=>hM j) ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P t X₁ X₂
    hX₁ hX₂ hp hP hβ hs E hE
  dsimp only
  intro hchild
  have hh:=hbound (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
    (fun i=>normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
    X₁ X₂ pool (fun i j=>heightCoefficient (β i j) (t i)) P hX₁ hX₂
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι) := original_positive_normalized (naturalRow (η i) (z i) (hz i)) R hR
    (W₁ i) (W₂ i) (a₁ i) (b₁ i) (a₂ i) (b₂ i) (ha₁ i) (ha₂ i) (hs₁ i) (hs₂ i)
    (hW₁ i) (hW₂ i) (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  simp_rw [he,norm_mul,positive_height_phase_norm _ _ (hX₁ _),
    positive_height_phase_norm _ _ (hX₂ _),one_mul]
  simpa only [excluded,norm_mul] using hh

theorem original_positive_deletion_height {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
        (signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          ((Ideal.absNorm (∏I∈D₁,I):ℂ)^(Complex.I*t)*
           (Ideal.absNorm (∏I∈D₂,I):ℂ)^(Complex.I*t))) *
        (((Real.sqrt (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₁ t (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ))) *
         ((Real.sqrt (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₂ t (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ))) *
         ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_deletion η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂
    pool hp β P hP t X₁ X₂ hX₁ hX₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  apply Finset.sum_congr rfl
  intro J hJ
  have hN₁:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₁
    (fun I hi=>support_prime R I (Finset.mem_powerset.mp hD₁ hi))
  have hN₂:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₂
    (fun I hi=>support_prime R I (Finset.mem_powerset.mp hD₂ hi))
  have h1:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₁ a₁ b₁ ha₁ hs₁ hW₁
    t X₁ (Ideal.absNorm (∏I∈D₁,I):ℝ) hX₁ hN₁
  have h2:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₂ a₂ b₂ ha₂ hs₂ hW₂
    t X₂ (Ideal.absNorm (∏I∈D₂,I):ℝ) hX₂ hN₂
  convert congrArg (fun q : ℂ=>
    signedCoefficient (naturalRow η z hz).character (CompletedGauss.primeSupport R) D₁ D₂ J pool
      (fun i=>heightCoefficient (β i) t) P * q *
      ∏i∈Finset.univ\J,naturalSlot (naturalRow η z hz).character (pool i) (heightCoefficient (β i) t) (P i))
    (congrArg₂ (fun x y : ℂ=>x*y) h1 h2) using 1 <;> push_cast <;> ring

end SevenEighths.CenteredMomentCommonMaskEnergy

end

end OAI

end

