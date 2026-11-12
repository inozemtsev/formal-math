module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part021
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part015
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part022

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentRetainedWeightedSource
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectedNormalization
open CenteredMomentReflectedAnnuli CenteredMomentReflectedTruncation
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

abbrev sourcePrimes (χ ψ : Character) := redundantSet χ.modulus ψ.modulus

def dualScale (χ ψ : Character) (X : ℝ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D.val,P):ℝ)/(X*norm H.val)

lemma dualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    0<dualScale χ ψ X D H := by
  have hD : (∏P∈D.val,P : Ideal O)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>
    (redundantSet_prime χ.modulus ψ.modulus P ((Finset.mem_powerset.mp D.property) hP)).ne_zero)
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hd : 0<(Ideal.absNorm (∏P∈D.val,P):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  exact div_pos (mul_pos hQ hd) (mul_pos hX (CenteredMomentReflectionDeletion.norm_pos H.val))

def retainedColumn (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ)) : ℂ :=
  if a.2∈retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2) then
    HeckeDyadic.polynomial χ.inverse false
      (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale a.2) t)
      (dyadicScale a.2*dualScale χ ψ X a.1.1 a.1.2) 0 0 * P
  else 0

lemma retainedColumn_zero (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ))
    (ha : a.2∉retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2)) :
    retainedColumn χ ψ W X R t hX B n P a=0 := by
  simp only [retainedColumn,ite_eq_right ha]

theorem finiteAnnularColumn_normalized (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H)*P =
    (((1+‖t‖)^n:ℝ):ℂ)*∑'k : ℤ,(annularMass B k:ℂ)*
      retainedColumn χ ψ W X R t hX B n P ((D,H),k) := by
  rw [finiteAnnularColumn,dite_eq_left (dualScale_pos χ ψ X hX D H),
    tsum_eq_sum (s:=retainedAnnuli R (dualScale χ ψ X D H) (dualScale_pos χ ψ X hX D H))
      (fun k hk=>by simp only [retainedColumn,ite_eq_right hk,mul_zero]),
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedColumn,ite_eq_left hk,actual_annular_normalization]
  ring

theorem retainedOriginal_eq_weighted (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖)) :
    retainedOriginal χ ψ W X R t*P =
      (((1+‖t‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes χ ψ),
        signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
          retainedColumn χ ψ W X R t hX B n P a := by
  rw [signed_series_reindex ψ ψ.inverse (sourcePrimes χ ψ) B _ hs]
  change (∑D∈(sourcePrimes χ ψ).powerset,∑'H : SmoothIdeal (sourcePrimes χ ψ),
    coefficient ψ ψ.inverse (sourcePrimes χ ψ) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
        R ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)))*P = _
  rw [←Finset.sum_coe_sort (sourcePrimes χ ψ).powerset,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [←tsum_mul_right,←tsum_mul_left]
  apply tsum_congr
  intro H
  change (coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H))*P = _
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [mul_assoc,tsum_mul_left]
  ring

theorem retainedOriginal_fiber_summable (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖))
    (D : (sourcePrimes χ ψ).powerset) :
    Summable (fun H : SmoothIdeal (sourcePrimes χ ψ)=>
      ‖(coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
        finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
          R (dualScale χ ψ X D H))*P‖) := by
  have hh := ((hs.of_norm.prod.prod_factor D).mul_left (((1+‖t‖)^n:ℝ):ℂ)).norm
  apply hh.congr
  intro H
  congr 1
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [signedWeight,mul_assoc,tsum_mul_left]
  ring

theorem actual_retained_weighted_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(χ ψ : ι→Character)(W : ι→ℝ→ℂ)(X R t : ι→ℝ)
        (hX : ∀i,0<X i)(B : ι→ℕ)(n : ℕ)(P : ι→ℂ),
      (∀i,2≤B i) → ∀(T Rcap E : ℝ),0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀a : ∀i,Index (sourcePrimes (χ i) (ψ i)),
        (∑i,‖retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) (a i)‖^2)≤E) →
      (∀i,Summable (fun a : Index (sourcePrimes (χ i) (ψ i))=>
        ‖signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
          retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a‖)) ∧
      (∀i,retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i =
        (((1+‖t i‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes (χ i) (ψ i)),
          signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
            retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a) ∧
      (∀i,∀D : (sourcePrimes (χ i) (ψ i)).powerset,
        Summable (fun H : SmoothIdeal (sourcePrimes (χ i) (ψ i))=>
          ‖(coefficient (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) D.val H*
            finiteAnnularColumn (χ i).inverse
              (paperRadialFourier (CompletedHeight.normTwistedSource (W i) (t i)))
              (R i) (dualScale (χ i) (ψ i) (X i) D H))*P i‖)) ∧
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2) ≤
        C*Rcap^ε*(1+T)^(2*n)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ ψ W X R t hX B n P hB T Rcap E hT ht hRcap hcap hselection
  let f (i : ι) := retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i)
  have he := hbound (fun i=>sourcePrimes (χ i) (ψ i))
    (fun i=>redundantSet_prime (χ i).modulus (ψ i).modulus) ψ (fun i=>(ψ i).inverse)
    B hB Rcap E hRcap hcap f hselection
  have hid (i : ι) := retainedOriginal_eq_weighted (χ i) (ψ i) (W i) (X i) (R i) (t i)
    (hX i) (B i) n (P i) (he.1 i)
  refine ⟨he.1,hid,?_,?_⟩
  · intro i D
    exact retainedOriginal_fiber_summable (χ i) (ψ i) (W i) (X i) (R i) (t i)
      (hX i) (B i) n (P i) (he.1 i) D
  · let z (i : ι) := ∑'a : Index (sourcePrimes (χ i) (ψ i)),
        signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*f i a
    have hn (i : ι) :
        ‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖=(1+‖t i‖)^n*‖z i‖ := by
      rw [hid i,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    have hp (i : ι) : (1+‖t i‖)^n≤(1+T)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith [ht i]) n
    calc
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2)
          = ∑i,((1+‖t i‖)^n*‖z i‖)^2 := by simp_rw [hn]
      _ ≤ ∑i,((1+T)^n*‖z i‖)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) 2
      _ = ((1+T)^n)^2*∑i,‖z i‖^2 := by simp only [mul_pow,Finset.mul_sum]
      _ ≤ ((1+T)^n)^2*(C*Rcap^ε*E) := mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
      _ = C*Rcap^ε*(1+T)^(2*n)*E := by rw [←pow_mul,Nat.mul_comm n 2];ring

end SevenEighths.CenteredMomentRetainedWeightedSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.RetainedComparisonEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentRetainedComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedChoiceEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_retained_fixed_profile_energy (a b epsilon : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(χ ψ : ι→Character)(P : ι→ℂ)(X R t ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high E T Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (X i) (R i) (t i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := actual_independent_profile_choices a b ha B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Cp,hCp,hp⟩ := hn Wlong hs hW
  refine ⟨Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ χ ψ P X R t ly omega Wshort c d lo hi low high E T Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hE hT ht hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp χ P s Y keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hE henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) Wlong (X i) (R i) (t i) (hX i) B n (P' i) (u i)‖^2)≤
        Cp*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun _=>Wlong) X R t hX (fun _=>B) n P' (fun _=>hB)
    T Rcap _ hT ht hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [P',←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentRetainedComparisonEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalRetainedEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentNaturalRetainedEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentRetainedComparisonEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (a b epsilon Cscale xi : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (Z^along) (Z^(xi/4)) (t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨n,hn⟩ := actual_retained_fixed_profile_energy a b epsilon ha hepsilon B J hB
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ ψ P t omega Wshort c d M along bshort E T Rcap hd hshort hshortsmooth
    hnatural hmod hE hT ht hRcap hcap henergy
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
  have hh := hb χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) t (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    E T Rcap (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hE hT ht hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end SevenEighths.CenteredMomentNaturalRetainedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OriginalComparisonEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentNaturalRetainedEnergy CenteredMomentOriginalReflectionEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false Wlong (Z^along) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_natural_retained_energy a b epsilon Cscale xi ha hepsilon hscale hxi B J hB
  obtain ⟨ne,hne⟩ := actual_original_energy_to_retained a b (xi/2) saving L Cscale epsilon
    ha (by positivity) hscale hepsilon
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hr⟩ := hn Wlong hs hW
  obtain ⟨D,hD,ho⟩ := hne Wlong hs hW
  refine ⟨2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ P t omega Wshort c d M along bshort E T Rcap hχ hd hshort hshortsmooth
    hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal (fun _=>Z^along) t Q T Z Rcap hT hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) ht hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 χ ψ P t omega Wshort c d M along bshort E T Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hE hT ht hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOriginalComparisonEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalComparisonEnergy CenteredMomentRadialPolynomialEnergy
local notation "O" => HeckeFamily.O

def radialEnergy (F : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma sqrt_weight (a p : ℂ) (u : ℝ) (hu : 0≤u) :
    ‖a*(p*(Real.sqrt u:ℂ))‖^2=‖a*p‖^2*u := by
  rw [←mul_assoc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hu]

lemma finite_weighted (rows : Finset O) (keep : O→Prop) (F : O→ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑z : ↥(rows.filter keep),‖F z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)‖^2)=
    ∑z∈rows,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  simp_rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
  rw [Finset.sum_coe_sort (rows.filter keep) (fun z:O=>‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re),Finset.sum_filter]

theorem actual_original_radial_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (_hb : 0≤b) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(χ : O→Character)(P : O→ℂ)(t omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → (∀z,‖P z‖≤Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀z,keep z → ‖t z‖≤T) → 1≤Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  obtain ⟨n,ne,h⟩:=actual_original_comparison a b epsilon Cscale xi saving L ha hepsilon hscale hxi B J hB
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,D,hC,hD,h⟩:=h Wlong hs hW
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ P t omega keep Φ K Pbound Wshort c d M along bshort E T Rcap hK hΦ hP hχ
    hd hshort hshortsmooth hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z:=by linarith [hZ.1]
  have hshortsum:=single_radial_summable χ P omega Wshort c d (Z^bshort) Pbound hd
    (Real.rpow_pos_of_pos hz _) hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let weightedP (z : ↥S) : ℂ:=P z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hmem (z : ↥S) : keep (z:O):=(Finset.mem_filter.mp z.property).2
  have hh:=hZ.2 (fun z:↥S=>χ z) weightedP (fun z=>t z) (fun z=>omega z)
    Wshort c d M along bshort E T Rcap (fun z=>hχ z (hmem z)) hd hshort hshortsmooth
    hML (fun z=>hmod z (hmem z)) hE hT (fun z=>ht z (hmem z)) hRcap
    (fun z=>hcap z (hmem z)) ?_
  · simp only [weightedP,←mul_assoc] at hh
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ,
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

end SevenEighths.CenteredMomentOriginalRadialComparison

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.OriginalRadialTail -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentOriginalRadialTail
open HeckeFamily ConcreteTraceCRT CenteredMomentAbsoluteEnergy
open CenteredMomentPositiveSummability CenteredMomentOriginalRadialComparison
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def tailControl (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  (2:ℝ)^(A+2)*(Finset.Iic (A+2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ

lemma cauchy_all (K : ℝ) (hK : 0<K) :
    (∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤4*(1+Real.pi)^2*max 1 K := by
  by_cases hk : 1≤K
  · have hh:=scaled_eisenstein_cauchy_small K⁻¹ (inv_pos.mpr hK) (inv_le_one_of_one_le₀ hk)
    rw [max_eq_right hk]
    have he : K*(K⁻¹*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹))=
        ∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by rw [←mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
    have hb:=mul_le_mul_of_nonneg_left hh hK.le
    rw [he] at hb
    simpa only [mul_comm K] using hb
  · have hk' : K≤1:=(not_le.mp hk).le
    have hi : 1≤K⁻¹:=(one_le_inv₀ hK).mpr hk'
    have hs:=scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)
    have hh:=hs.tsum_le_tsum (g:=fun z:O=>((1+1*‖eisEmbedding z‖^2)^2)⁻¹) (fun z=>by
      apply inv_anti₀ (by positivity)
      gcongr)
      (scaled_eisenstein_cauchy_summable 1 (by norm_num))
    have hb:=scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
    rw [max_eq_left hk',mul_one]
    exact hh.trans (by simpa only [one_mul] using hb)

lemma tail_pointwise (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) (x r : ℝ) (hr : 0≤ r) (hx : r≤x) :
    ‖Φ x‖≤tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹ := by
  have hxp : 0≤x:=hr.trans hx
  have hh:=SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ)
    (m:=(A+2,0)) (k:=A+2) (n:=0) le_rfl le_rfl Φ x
  simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hxp] at hh
  change (1+x)^(A+2)*‖Φ x‖≤tailControl A Φ at hh
  have hp : (1+r)^A≤(1+x)^A:=pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (1+r)^A*((1+x)^2*‖Φ x‖)≤tailControl A Φ := by
    apply (mul_le_mul_of_nonneg_right hp (by positivity)).trans
    simpa only [pow_add,mul_assoc] using hh
  have hd : 0<(1+r)^A*(1+x)^2:=by positivity
  rw [show tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹=
    tailControl A Φ/((1+r)^A*(1+x)^2) by field_simp]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hb)

theorem actual_radial_tail (A : ℕ) (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) (hR : 0≤R) :
    radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
  let C:=tailControl A Φ*B^2*((1+R/K)^A)⁻¹
  have hC : 0≤C:=by dsimp [C,tailControl];positivity
  have hs:=bounded_radial_summable F B hF (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K hK
  have hp (z:O) :
      (if keep z ∧ R<‖eisEmbedding z‖^2 then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)
      ≤C*((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by
    split_ifs with hz
    · have ht:=tail_pointwise A Φ (‖eisEmbedding z‖^2/K) (R/K)
        (div_nonneg hR hK.le) (div_le_div_of_nonneg_right hz.2.le hK.le)
      have hf:=pow_le_pow_left₀ (norm_nonneg _) (hF z) 2
      have hh:=(mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul hf ht (norm_nonneg _) (sq_nonneg B))
      convert hh using 1 ; dsimp [C] ; simp only [div_eq_mul_inv] ; ring
    · exact mul_nonneg hC (by positivity)
  have hb:=Summable.tsum_le_tsum hp (hs.congr (fun z=>by by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz])) ((scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)).mul_left C)
  rw [tsum_mul_left] at hb
  have hh:=mul_le_mul_of_nonneg_left (cauchy_all K hK) hC
  have hh' : C*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
    convert hh using 1 ; dsimp [C] ; ring
  convert hb.trans hh' using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz]

lemma actual_radial_split (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    radialEnergy F keep Φ K=
      radialEnergy F (fun z=>keep z ∧ ‖eisEmbedding z‖^2≤R) Φ K+
      radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K := by
  unfold radialEnergy
  rw [←Summable.tsum_add (bounded_radial_summable F B hF _ Φ K hK)
    (bounded_radial_summable F B hF _ Φ K hK)]
  apply tsum_congr
  intro z
  by_cases hk:keep z
  · by_cases hr:‖eisEmbedding z‖^2≤R
    · simp [hk,hr,not_lt.mpr hr]
    · simp [hk,hr,not_le.mp hr]
  · simp [hk]

theorem actual_positive_row_tail {ι:Type*} [Fintype ι] [DecidableEq ι]
    (order:ℕ) (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K R:ℝ) (hK:0<K) (hR:0≤R) :
    radialEnergy (fun z=>CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
      (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl order Φ*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i))*
        max 1 K*((1+R/K)^order)⁻¹ := by
  let E:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    CenteredMomentInductionEnergy.positive_squared_absolute η m A z t W₁ W₂
      b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
      S β P b B hP hb hB hβ hN
  have hh:=actual_radial_tail order _ (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K R hK hR
  simpa only [Real.sq_sqrt hE] using hh

end SevenEighths.CenteredMomentOriginalRadialTail

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.NaturalRadialCutoff -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalRadialCutoff
open HeckeFamily ConcreteTraceCRT CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialTail CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

lemma retained_conductor (η:Character) (Z m q xi Ck K:ℝ) (hZ:0<Z) (hCk:0≤Ck)
    (hη:(η.modulus.absNorm:ℝ)≤Z^m) (hK:K≤Ck*Z^q)
    (z:O) (hz:z≠0) (hrow:‖eisEmbedding z‖^2≤K*Z^xi) :
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*Ck*Z^(m+q+xi) := by
  have hn:((Ideal.span {z}).absNorm:ℝ)≤Ck*Z^(q+xi) := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    apply hrow.trans
    have hh:=mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hZ.le xi)
    simpa only [Real.rpow_add hZ,mul_assoc] using hh
  have hh:=(naturalRow η z hz).modulus_power_bound Z m (q+xi) Ck hZ hCk hη hn
  simpa only [add_assoc] using hh

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0<Z) :
    ((1+Z^xi)^order)⁻¹≤Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) (by linarith) order
  have hh:=inv_anti₀ (pow_pos (Real.rpow_pos_of_pos hZ _) _) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  congr 1
  ring

theorem actual_tail_arbitrary_saving (xi saving mass : ℝ) (hxi:0<xi) :
    ∃order:ℕ,∀(F:O→ℂ)(B:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Z:ℝ),
      (∀z,‖F z‖≤B) → 0<K → 1≤Z → B^2*max 1 K≤Z^mass →
      radialEnergy F (fun z=>keep z ∧ K*Z^xi<‖eisEmbedding z‖^2) Φ K≤
        (4*(1+Real.pi)^2*tailControl order Φ)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=exists_nat_ge ((mass+saving)/xi)
  have ho:mass-xi*(order:ℝ)≤-saving := by
    have hh:mass+saving≤(order:ℝ)*xi:=(div_le_iff₀ hxi).mp horder
    linarith
  refine ⟨order,?_⟩
  intro F B keep Φ K Z hF hK hZ hmass
  have hz:0<Z:=by linarith
  have hh:=actual_radial_tail order F B hF keep Φ K (K*Z^xi) hK (by positivity)
  have hdiv:K*Z^xi/K=Z^xi:=by field_simp
  rw [hdiv] at hh
  have hc:0≤4*(1+Real.pi)^2*tailControl order Φ:=by unfold tailControl;positivity
  have hb:(B^2*max 1 K)*((1+Z^xi)^order)⁻¹≤Z^(-saving) := by
    calc
      _≤Z^mass*Z^(-xi*(order:ℝ)) :=
        mul_le_mul hmass (reciprocal_cutoff_bound Z xi order hz) (by positivity) (Real.rpow_nonneg hz.le _)
      _=Z^(mass-xi*(order:ℝ)) := by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^(-saving):=Real.rpow_le_rpow_of_exponent_le hZ ho
  apply hh.trans
  convert mul_le_mul_of_nonneg_left hb hc using 1 ; ring

end SevenEighths.CenteredMomentNaturalRadialCutoff

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentWholeSlotDeletion
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
local notation "O" => ActualEisensteinCubic.O

theorem whole_removal {α:Type*} (S:Finset α) (w:α→ℝ) (F κ mesh:ℝ)
    (hF:0≤F) (hκ:0<κ) (hm:0≤ mesh)
    (hw:∀i∈S,0≤w i) (hwm:∀i∈S,w i≤ mesh) :
    ∃R:Finset α,R⊆S ∧
      (∑i∈R,w i)≤ min (∑i∈S,w i) (F/(6*κ)+mesh) ∧
      (R=S ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay⟩:=CenteredMomentSlotRemoval.whole_slot_removal S w mesh κ F hm hκ hF hw hwm
  refine ⟨R,hR,hbound,hpay,?_⟩
  have hh:=mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hκ.le
  have he:κ*(F/(6*κ)+mesh)=F/6+κ*mesh:=by field_simp
  rwa [he] at hh

def normalizedSlot (η:Character) (m A z:O) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (t P:ℝ) : ℂ := (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

def selectedProduct {α:Type*} (J:Finset α) (η:Character) (m A z:O)
    (W₁ W₂:ℝ→ℂ) (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ)
    (t X₁ X₂:ℝ) : ℂ :=
  ((Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂))*
    ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i)

theorem selectedProduct_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂:ℝ) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      (∏i∈R,normalizedSlot η m A z (S i) (β i) t (P i))*
        selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct
  rw [←Finset.prod_sdiff hR]
  ring

theorem selectedProduct_energy_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂ Z κ:ℝ)
    (hZ:0<Z) (w B:α→ℝ) (_hB:∀i∈R,0≤B i)
    (hslot:∀i∈R,‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2≤B i*Z^(κ*w i)) :
    ‖selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((∏i∈R,B i)*Z^(κ*∑i∈R,w i))*
        ‖selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  rw [selectedProduct_remove J R hR,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _≤∏i∈R,B i*Z^(κ*w i):=Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot
    _=_:=by rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,Finset.mul_sum]

end SevenEighths.CenteredMomentWholeSlotDeletion

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SlotNormalization -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=>hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.UnitSexticWitness -/

section

namespace OAI

namespace SevenEighths.UnitSexticWitness

open ActualEisensteinCubic CanonicalRowCompletion CanonicalUnitEuler
open ConcreteTraceCRT
open scoped Classical
noncomputable section
local notation "lambda" => ConcretePrimeRowBridge.goodLambda

lemma idealRowHom_unit_eq_of_norm_mod_seven (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hodd : ringChar (O ⧸ P) ≠ 2)
    (hmod : Ideal.absNorm P % 36 = 7) (u : Oˣ) :
    idealRowHom u.val P = eisEmbedding u.val := by
  rw [idealRowHom_prime _ P hg, actualSextic_unit_euler P hg hodd]
  have hcard : Nat.card (O ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard]
  have hm : (Ideal.absNorm P - 1) / 6 ≡ 1 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  have he := pow_eq_pow_of_modEq hm (unit_pow_six u)
  simpa only [pow_one] using congrArg eisEmbedding he

lemma prime_norm_good {p : ℕ} (_hp : p.Prime) (hp3 : 3 < p)
    (P : Ideal O) (hP : Ideal.absNorm P = p) : lambda ∉ P := by
  intro hl
  have hd := Ideal.absNorm_dvd_absNorm_of_le
    ((Ideal.span_singleton_le_iff_mem P).mpr hl)
  have hlambda : Ideal.absNorm (Ideal.span {lambda}) = 3 := CubicEisenstein.absNorm_span_lambda
  rw [hP, hlambda] at hd
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

lemma prime_norm_ringChar {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] (hP : Ideal.absNorm P = p) :
    ringChar (O ⧸ P) = p := by
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (O ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hP
  let : CharP (O ⧸ P) p := charP_of_card_eq_prime hcard
  exact ringChar.eq (O ⧸ P) p

lemma exists_primeIdeal_norm {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ P : Ideal O, P.IsMaximal ∧ Ideal.absNorm P = p := by
  have hc := ShortDraftHeckeBridge.split_count_of_mod_one hp hmod
  have hne : ((Ideal.span {(p : ℤ)}).primesOver O).Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  obtain ⟨P, hP⟩ := hne
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hn := ShortDraftHeckeBridge.absNorm_split hp hmod P
  have hP0 : P ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hn
    exact hp.ne_zero hn.symm
  exact ⟨P, hP.1.isMaximal hP0, hn⟩

theorem exists_prime_unit_embedding (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      Ideal.absNorm P % 36 = 7 ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      ∀ u : Oˣ, idealRowHom u.val P = eisEmbedding u.val := by
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max (max B 3) (S.sup Ideal.absNorm)) (q := 36) (a := 7) (by decide) (by decide)
  have hp36 : p % 36 = 7 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  have hp3 : 3 < p := lt_of_le_of_lt ((le_max_right B 3).trans (le_max_left _ _)) hpB
  have hpmod : p % 3 = 1 := by omega
  obtain ⟨P, hmax, hn⟩ := exists_primeIdeal_norm hp hpmod
  let : P.IsMaximal := hmax
  have hg : lambda ∉ P := prime_norm_good hp hp3 P hn
  have hodd : ringChar (O ⧸ P) ≠ 2 := by
    rw [prime_norm_ringChar hp P hn]
    omega
  refine ⟨P, hmax, ?_, ?_, hn ▸ hp36, hg, hodd, ?_⟩
  · intro hPS
    have hle := Finset.le_sup (f := Ideal.absNorm) hPS
    rw [hn] at hle
    have := le_max_right (max B 3) (S.sup Ideal.absNorm)
    omega
  · rw [hn]
    exact lt_of_le_of_lt ((le_max_left B 3).trans (le_max_left _ _)) hpB
  · exact idealRowHom_unit_eq_of_norm_mod_seven P hg hodd (hn ▸ hp36)

theorem exists_unit_witness (u : Oˣ) (hu : u ≠ 1)
    (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      idealRowHom u.val P ≠ 0 ∧ idealRowHom u.val P ≠ 1 := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ := exists_prime_unit_embedding S B
  refine ⟨P, hp, hs, hb, hg, ho, ?_, ?_⟩
  · rw [he u]
    intro hz
    exact Units.ne_zero u (eisEmbedding_injective (by simpa using hz))
  · rw [he u]
    intro hh
    apply hu
    apply Units.ext
    exact eisEmbedding_injective (by simpa using hh)

theorem exists_prime_embedding_after_deletion
    (S : Finset SmoothMobiusCorrection.PrimeIdeal) (B : ℕ) :
    ∃ P : SmoothMobiusCorrection.PrimeIdeal, P ∉ S ∧ B < Ideal.absNorm P.val ∧
      lambda ∉ P.val ∧ ringChar (O ⧸ P.val) ≠ 2 ∧
      ∀ u : Oˣ, IdealEuler.deletePrimes S (idealRowHom u.val) P.val = eisEmbedding u.val := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ :=
    exists_prime_unit_embedding (S.image Subtype.val) B
  let : P.IsMaximal := hp
  let Q : SmoothMobiusCorrection.PrimeIdeal :=
    ⟨P, Ideal.prime_of_isPrime (NeZero.ne P) inferInstance⟩
  have hQ : Q ∉ S := fun h => hs (Finset.mem_image.mpr ⟨Q, h, rfl⟩)
  refine ⟨Q, hQ, hb, hg, ho, ?_⟩
  intro u
  rw [IdealEuler.deletePrimes_prime, ite_eq_right hQ]
  exact he u

theorem deleted_unit_row_ne_principal (u : Oˣ) (hu : u ≠ 1)
    (S : Finset SmoothMobiusCorrection.PrimeIdeal) :
    IdealEuler.deletePrimes S (idealRowHom u.val) ≠
      IdealEuler.deletePrimes S (idealRowHom (1 : O)) := by
  obtain ⟨P, hs, hb, hg, ho, he⟩ := exists_prime_embedding_after_deletion S 0
  intro h
  have hp := DFunLike.congr_fun h P.val
  rw [he u, show (1 : O) = (1 : Oˣ).val from rfl, he 1, Units.val_one, map_one] at hp
  apply hu
  apply Units.ext
  exact eisEmbedding_injective (by simpa using hp)

end
end SevenEighths.UnitSexticWitness

end OAI

end

/-! ## PrimeNumberTheoremAnd.Auxiliary -/

section

/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

/-!
### Auxiliary lemmas
-/

namespace Complex
-- see https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Differentiability.20of.20the.20natural.20map.20.E2.84.9D.20.E2.86.92.20.E2.84.82/near/418095234

lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x

lemma deriv_ofReal (x : ℝ) : deriv ofReal x = 1 :=
  (hasDerivAt_ofReal x).deriv

lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt

end Complex

lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt

lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv

lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal

lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt

lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp

open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  have hreal : HasDerivAt f u.re z := by
    simpa only [Function.comp_def, reCLM_apply, ofReal_re] using
      (reCLM.hasFDerivAt.comp_hasDerivAt z hf)
  exact ⟨u.re, hf.unique hreal.ofReal_comp, hreal⟩

lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂

lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff

lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]

end

