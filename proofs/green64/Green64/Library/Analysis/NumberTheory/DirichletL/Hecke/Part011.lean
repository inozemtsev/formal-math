module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part006

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Hecke / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorDyadicGeometry
open HeckeDyadic

lemma uniform_power_allowance (C p dmin α : ℝ) (hα : 0≤α) (hgap : p<dmin*α) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → C*Z^p≤(Z^d)^α := by
  have hh := constant_absorbed_eventually C (dmin*α-p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd
  have hZp : 0<Z := by linarith
  calc
    _ ≤ Z^(dmin*α-p)*Z^p := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*α) := by rw [←Real.rpow_add hZp]; congr 1; ring
    _ ≤ Z^(d*α) := Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hα)
    _ = _ := Real.rpow_mul hZp.le _ _

lemma uniform_scale_threshold (dmin A : ℝ) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → A≤Z^d := by
  have hh := constant_absorbed_eventually A dmin hd
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hA hZ d hd'
  exact hA.trans (Real.rpow_le_rpow_of_exponent_le hZ hd')

lemma uniform_zero_height (dmin τ : ℝ) (I : ℕ) (hgap : τ<dmin/2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3*i : ℕ)*Z^τ≤(Z^d)^(1/2 : ℝ) := by
  have hh := uniform_power_allowance (3*I : ℕ) τ dmin (1/2) (by norm_num) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hn : (3*i : ℕ)≤3*I := by omega
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.rpow_nonneg (by linarith) _)).trans (hZ d hd)

lemma uniform_height_budget (dmin τ η : ℝ) (I : ℕ) (hτ : 0≤τ)
    (hη : 0≤η) (hgap : 4*τ<dmin*η) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d →
      ∀ i : ℕ, i≤I → (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^η := by
  have hh := uniform_power_allowance ((3*(I : ℝ)+5)^4*16) (4*τ) dmin η hη hgap
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hZ hZ1 d hd i hi
  have hT : 1≤Z^τ := Real.one_le_rpow hZ1 hτ
  have hp : (1+Z^τ)^4≤16*Z^(4*τ) := by
    calc
      _ ≤ (2*Z^τ)^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        have he : (Z^τ)^4=Z^(4*τ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤Z)]
          congr 1
          norm_num
          ring
        rw [mul_pow,he]
        norm_num
  calc
    _ ≤ (3*(I : ℝ)+5)^4*(1+Z^τ)^4 := indexed_height_bound i I hi (Z^τ) (by linarith)
    _ ≤ (3*(I : ℝ)+5)^4*(16*Z^(4*τ)) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((3*(I : ℝ)+5)^4*16)*Z^(4*τ) := by ring
    _ ≤ _ := hZ d hd

lemma uniform_fourier_allowance (dmax τ : ℝ) (hdmax : 0<dmax) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, 0≤d → d≤dmax →
      2*Real.pi*(Z^d)^(τ/(2*dmax))≤Z^τ/2 := by
  have hh := constant_absorbed_eventually (4*Real.pi) (τ/2) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ d hd hd'
  have hZp : 0<Z := by linarith
  have hp : (Z^d)^(τ/(2*dmax))≤Z^(τ/2) := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hm := mul_le_mul_of_nonneg_right hd' (show 0≤τ/(2*dmax) by positivity)
    have he : dmax*(τ/(2*dmax))=τ/2 := by field_simp
    rwa [he] at hm
  have he : Z^(τ/2)*Z^(τ/2)=Z^τ := by rw [←Real.rpow_add hZp]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le (τ/2))
  rw [he] at hh
  have hpi := mul_le_mul_of_nonneg_left hp (show 0≤2*Real.pi by positivity)
  nlinarith

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicLengths -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDyadicGeometry

lemma log_scale_bounds (U x : ℝ) (hU : 8≤U) (hx : 1≤x) (hxU : x≤8*U^21) :
    0≤Real.logb U x ∧ Real.logb U x≤22 ∧ U^(Real.logb U x)=x := by
  have hUp : 0<U := by linarith
  have hU1 : 1<U := by linarith
  have hxp : 0<x := by linarith
  have he := Real.rpow_logb hUp hU1.ne' hxp
  refine ⟨Real.logb_nonneg hU1 hx,?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hU1).mp
  rw [he,show (22 : ℝ)=((22 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  calc
    x ≤ 8*U^21 := hxU
    _ ≤ U*U^21 := mul_le_mul_of_nonneg_right hU (by positivity)
    _ = U^22 := by ring

lemma dyadic_scale_bounds (U : ℝ) (hU : 8≤U) (j k : ℕ)
    (hprod : (2 : ℝ)^j*(2 : ℝ)^k<8*U^21) :
    0≤Real.logb U ((2 : ℝ)^j) ∧ Real.logb U ((2 : ℝ)^j)≤22 ∧
      0≤Real.logb U ((2 : ℝ)^k) ∧ Real.logb U ((2 : ℝ)^k)≤22 ∧
      U^(Real.logb U ((2 : ℝ)^j))=(2 : ℝ)^j ∧
      U^(Real.logb U ((2 : ℝ)^k))=(2 : ℝ)^k := by
  obtain ⟨hj,hk⟩ := HeckeDetectorDyadicBridge.scales_le_eight_terminal (U^21) j k hprod
  obtain ⟨hr,hr',he⟩ := log_scale_bounds U ((2 : ℝ)^j) hU (one_le_pow₀ (by norm_num)) hj
  obtain ⟨hm,hm',he'⟩ := log_scale_bounds U ((2 : ℝ)^k) hU (one_le_pow₀ (by norm_num)) hk
  exact ⟨hr,hr',hm,hm',he,he'⟩

lemma support_exponents (U t r m ε : ℝ) (hU : 1<U) (hcost : 8≤U^ε)
    (hleft : U^r<4*U^t) (hright : U^t/8<U^r*U^m) :
    r≤t+ε ∧ t-ε≤ r+m := by
  have hUp : 0<U := by linarith
  constructor
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^r ≤ 4*U^t := hleft.le
      _ ≤ U^ε*U^t := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hUp.le _)
      _ = U^(t+ε) := by rw [←Real.rpow_add hUp]; congr 1; ring
  · apply (Real.rpow_le_rpow_left_iff hU).mp
    calc
      U^(t-ε) = U^t/U^ε := Real.rpow_sub hUp _ _
      _ ≤ U^t/8 := div_le_div_of_nonneg_left (Real.rpow_nonneg hUp.le _) (by norm_num) hcost
      _ ≤ U^r*U^m := hright.le
      _ = U^(r+m) := (Real.rpow_add hUp _ _).symm

lemma truncation_scale (U t : ℝ) (hU : 2≤U) (ht : 1≤t) (ht' : t≤3/2) :
    2≤U^t ∧ U^t≤U^(3/2 : ℝ) := by
  have hU1 : 1≤U := by linarith
  constructor
  · apply hU.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1 ht
  · exact Real.rpow_le_rpow_of_exponent_le hU1 ht'

end SevenEighths.HeckeDetectorDyadicGeometry

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneous -/

section

namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneous
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤ r ∧ r≤tstar+ε ∧ 0≤ m ∧ m≤1/2+75*ε ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤ r ∧ r≤tstar+ε ∧ 0≤ m ∧ m≤1/2+75*ε ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneous

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

theorem inverse_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (D : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ r q z εw εp εm C : ℝ) (hU : 0<U)
    (hM : ∀ u∈rows, U^(δ*r-εw)≤‖polynomial (χ u) true W D (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-δ*r-2*q*z+εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*r-εw)+(2*q*z-εp))≤‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,norm_mul,mul_pow]
    exact mul_le_mul (hM u hu) (hP u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _)
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem plain_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (N : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ m q z εw εp εm C : ℝ) (hU : 0<U)
    (hS : ∀ u∈rows, U^(δ*m-εw)≤‖polynomial (χ u) false W N (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) false W N (σ u) (freq u)*
        polynomial (χ u) false W N (σ u) (freq u)*P u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ)≤C*U^(1-2*δ*m-2*q*z+2*εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*m-εw)+(δ*m-εw)+(2*q*z-εp))≤
        ‖polynomial (χ u) false W N (σ u) (freq u)*
          polynomial (χ u) false W N (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,Real.rpow_add hU,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _))
      (hP u hu) (Real.rpow_nonneg hU.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem classified_card_bound {α Label : Type*} [Fintype Label]
    (rows : Finset α) (presentation : α→Label) (left right : α→ℕ)
    (B : ℕ) (hleft : ∀ u∈rows, left u<B) (hright : ∀ u∈rows, right u<B)
    (K : ℝ)
    (hfiber : ∀ p : Label, ∀ j∈Finset.range B, ∀ k∈Finset.range B,
      ((rows.filter (fun u => presentation u=p ∧ left u=j ∧ right u=k)).card : ℝ)≤K) :
    (rows.card : ℝ)≤(Fintype.card Label : ℝ)*(B : ℝ)^2*K := by
  let labels : Finset (Label×ℕ×ℕ) := Finset.univ ×ˢ (Finset.range B ×ˢ Finset.range B)
  let label : α→Label×ℕ×ℕ := fun u => (presentation u,left u,right u)
  have hmaps : (rows : Set α).MapsTo label labels := by
    intro u hu
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hleft u hu),Finset.mem_range.mpr (hright u hu)⟩⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have he' : (rows.card : ℝ)=∑ l∈labels,
      ((rows.filter (fun u => label u=l)).card : ℝ) := by exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ l∈labels, K := by
      apply Finset.sum_le_sum
      intro l hl
      rcases l with ⟨p,j,k⟩
      obtain ⟨hp,hjk⟩ := Finset.mem_product.mp hl
      obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
      have hh := hfiber p j hj k hk
      simpa only [label,Prod.mk.injEq] using hh
    _ = _ := by simp [labels,Finset.card_product,pow_two,mul_assoc]

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

def denominator (x : ℝ) : ℝ := 3-17*x/9

def primeWeight (x : ℝ) : ℝ := (2-8*x/9)*(1-x)

def crossing (x t : ℝ) : ℝ := ((2-8*x/9)*t-5*x/9)/denominator x

def inverseExponent (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)

def plainExponent (δ x t r : ℝ) : ℝ := 1-δ*(4*x/9+(2-8*x/9)*(t-r))

def shortExponent (δ x t : ℝ) : ℝ := 1-δ+δ*primeWeight x/denominator x*(3/2-t)

def longExponent (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)

lemma denominator_lower {x : ℝ} (hx : x≤1/2) : 37/18≤denominator x := by
  unfold denominator
  linarith

theorem crossing_bounds {x t : ℝ} (hx : 0≤x) (hx' : x≤1/2)
    (ht : 1≤t) (ht' : t≤3/2) :
    23/37≤ crossing x t ∧ crossing x t≤1 ∧
      1/3≤t-crossing x t ∧ t-crossing x t≤1/2 := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤2-8*x/9 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0≤1-x := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t-crossing x t=((1-x)*t+5*x/9)/denominator x := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

theorem crossing_average (δ x t r : ℝ) (hd : denominator x≠0) :
    ((2-8*x/9)*inverseExponent δ x r+(1-x)*plainExponent δ x t r)/denominator x =
      shortExponent δ x t := by
  unfold inverseExponent plainExponent shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma inverse_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    inverseExponent δ x (crossing x t)=shortExponent δ x t := by
  unfold inverseExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma plain_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    plainExponent δ x t (crossing x t)=shortExponent δ x t := by
  unfold plainExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {δ x t r : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2) :
    (r≤ crossing x t → plainExponent δ x t r≤ shortExponent δ x t) ∧
      (crossing x t≤ r → inverseExponent δ x r≤ shortExponent δ x t) := by
  have hd : denominator x≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hx'))
  constructor
  · intro hr
    rw [←plain_at_crossing δ x t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤2-8*x/9 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [←inverse_at_crossing δ x t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1-x by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

theorem strict_inverse_capacity {r ν : ℝ} (hr : 23/37≤ r) (hν : 0<ν) :
    r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 ∧
      (1-r)/2≤7/37 ∧ 9/37≤3-2*r-8*((1-r)/2-ν) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma plain_capacity_bound {m κ : ℝ} (hm : 1/3≤ m) (hm' : m≤1/2) (hκ : 3/4≤κ) :
    0≤(1-2*m)/(6*κ) ∧ (1-2*m)/(6*κ)≤2/27 := by
  have hkp : 0<6*κ := by linarith
  constructor
  · exact div_nonneg (by linarith) hkp.le
  · apply (div_le_iff₀ hkp).mpr
    nlinarith

lemma prime_supply_margin : (8/39 : ℝ)-7/37=23/1443 := by norm_num

lemma short_ge_base {δ x t : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2)
    (ht : t≤3/2) : 1-δ≤ shortExponent δ x t := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤primeWeight x := mul_nonneg (by linarith) (by linarith)
  unfold shortExponent
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (mul_nonneg hδ hp) hd.le) (by linarith))

lemma inverse_capacity_exponent (δ x r : ℝ) :
    1-δ*r-2*(δ*x)*((1-r)/2)=inverseExponent δ x r := by unfold inverseExponent; ring

theorem capacity_loss {q m Δ γ : ℝ} (_hq : 0≤q) (hq' : q≤1/2)
    (hm : 1/3-γ≤ m) (hm' : m≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hγ : 0≤γ) :
    2*q*(1-2*m)*(2/9-1/(9/2+12*Δ))≤Δ/4+2*γ := by
  have hd : 0<9/2+12*Δ := by linarith
  have hden : (16 : ℝ)≤(9/2)*(9/2+12*Δ) := by nlinarith
  have hqmul : q*(1-2*m)≤(1/2)*(1/3+2*γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0≤24*Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔ' (show 0≤24*γ by positivity)
  have he : 2*q*(1-2*m)*(2/9-1/(9/2+12*Δ)) =
      24*q*(1-2*m)*Δ/((9/2)*(9/2+12*Δ)) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ (show 0<(9/2)*(9/2+12*Δ) by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_left hden (show 0≤Δ/4+2*γ by positivity)
  nlinarith

theorem plain_capacity_comparison {δ x Δ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤1) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hm : 1/3-γ≤ m) (hm' : m≤1/2)
    (hγ : 0≤γ) (hlength : t-r-γ≤ m) :
    1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)≤plainExponent δ x t r+Δ/4+4*γ := by
  have hq : 0≤δ*x := mul_nonneg hδ hx
  have hq' : δ*x≤1/2 := (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss hq hq' hm hm' hΔ hΔ' hγ
  have hc : 0≤δ*(2-8*x/9) := mul_nonneg hδ (by linarith)
  have hc' : δ*(2-8*x/9)≤2 := by
    have hh := mul_le_mul_of_nonneg_right hδ' (show 0≤2-8*x/9 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  have hid : (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9))-plainExponent δ x t r =
      δ*(2-8*x/9)*(t-r-m) := by unfold plainExponent; ring
  have hid' : 1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ) =
      (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9)) +
      2*(δ*x)*(1-2*m)*(2/9-1/(9/2+12*Δ)) := by ring
  rw [hid']
  linarith

lemma inverse_zero_capacity {δ r ν : ℝ} (hδ : 0≤δ)
    (hcap : (1-r)/2≤ν) : 1-δ*r≤1-δ+2*δ*ν := by
  have hh := mul_le_mul_of_nonneg_left hcap hδ
  nlinarith

lemma plain_zero_capacity {δ m κ ν : ℝ} (hδ : 0≤δ) (hκ : 0<κ)
    (hκ' : κ≤1) (hν : 0≤ν) (hcap : (1-2*m)/(6*κ)≤ν) :
    1-2*δ*m≤1-δ+6*δ*ν := by
  have hh := (div_le_iff₀ (show 0<6*κ by positivity)).mp hcap
  have hk := mul_le_mul_of_nonneg_right hκ' hν
  have hm : 1-2*m≤6*ν := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hm hδ
  nlinarith

lemma long_count_bound {δ r t γ : ℝ} (hδ : δ≤5/6) (_hγ : 0≤γ)
    (hr : r≤t+γ) :
    1-5/6+(5/6-δ)*r≤longExponent δ t+(5/6-δ)*γ := by
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤5/6-δ by linarith)
  unfold longExponent
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountOptimization -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

theorem count_bound_of_source_branches (B C U δ x Δ t r m ε ν γ : ℝ)
    (hC : 0≤C) (hU : 1≤U) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (ht : 1≤t) (ht' : t≤3/2) (hν : 0≤ν) (hγ : 0≤γ)
    (hleft : t-r-γ≤ m) (hright : r≤t+γ)
    (hI0 : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B≤C*U^(1-2*δ*m+ε))
    (hI : 23/37≤ r → r<1 → ν<(1-r)/2 → B≤C*U^(inverseExponent δ x r+ε))
    (hP : r≤ crossing x t → m<1/2 → ν<(1-2*m)/(9/2+12*Δ) →
      B≤C*U^(1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+ε)) :
    B≤C*U^(max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ) := by
  let target := max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ
  have hshort : shortExponent δ x t≤ max (shortExponent δ x t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t≤ max (shortExponent δ x t) (longExponent δ t) := le_max_right _ _
  have hbase := short_ge_base hδ hx hx' ht'
  have hcross := crossing_bounds hx hx' ht ht'
  have hchoose := selected_short_bound (t:=t) (r:=r) hδ hx hx'
  have promote (p : ℝ) (hp : B≤C*U^p) (hpt : p≤target) : B≤C*U^target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1≤ r
  · have hmax : max 1 ((1+5*r)/6)=(1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5/6-δ)*γ≤γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r<1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6)=1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing x t≤ r
  · by_cases hcap : (1-r)/2≤ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r≤ crossing x t := (lt_of_not_ge hrc).le
  by_cases hm : 1/2≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m<1/2 := lt_of_not_ge hm
  by_cases hcap : (1-2*m)/(9/2+12*Δ)≤ν
  · apply promote _ hP0
    have hk0 : 0<3/4+2*Δ := by linarith
    have hk1 : 3/4+2*Δ≤1 := by linarith
    have hz := plain_zero_capacity hδ hk0 hk1 hν
      (show (1-2*m)/(6*(3/4+2*Δ))≤ν by convert hcap using 1; ring)
    have hv : 6*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1/3-γ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ≤1 by linarith) hx hx' hΔ hΔ'
      hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBranchBudget
open HeckeDetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤ mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x Δ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)=
      2*(δ*x)*(1-2*m)/(9/2+12*Δ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤ r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (Δ x t r m ε ν : ℝ)
    (hΔ : 0≤Δ) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤ crossing x t) (hleft : t-r-ε≤ m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(9/2+12*Δ)) :
    0≤(1-2*m)/(9/2+12*Δ)-ν ∧ (1-2*m)/(9/2+12*Δ)-ν≤7/37 ∧
      2*m+6*(3/4+2*Δ)*((1-2*m)/(9/2+12*Δ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 ht ht1
  have hm : 1/4≤ m := by linarith [hcross.2.2.1]
  have hd : 0<9/2+12*Δ := by linarith
  have hc : (1-2*m)/(9/2+12*Δ)≤7/37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  have heq : 6*(3/4+2*Δ)=9/2+12*Δ := by ring
  rw [heq,mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.HeckeDetectorBranchBudget

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint -/

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma denominator_endpoint (x : ℝ) : denominator x=Endpoint.denominator (1/2-x) := by
  unfold denominator Endpoint.denominator
  ring

lemma primeWeight_endpoint (x : ℝ) : primeWeight x=Endpoint.primeWeight (1/2-x) := by
  unfold primeWeight Endpoint.primeWeight
  ring

theorem balanced_cutoff_bounds {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    1≤Endpoint.balancedCutoff δ (1/2-x) ∧ Endpoint.balancedCutoff δ (1/2-x)≤3/2 := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hd := Endpoint.denominator_bounds hy hy'
  have hp := Endpoint.primeWeight_bounds hy hy'
  have hJ := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
  have hJp : 0<Endpoint.balanceDenominator δ (1/2-x) := by linarith [hJ.1]
  unfold Endpoint.balancedCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ (by linarith [hp.1])) (by positivity))
  · have hnum : δ*Endpoint.primeWeight (1/2-x)≤Endpoint.balanceDenominator δ (1/2-x) := by
      unfold Endpoint.balanceDenominator
      have hh := mul_nonneg (sub_nonneg.mpr hδ') (show 0≤Endpoint.denominator (1/2-x) by linarith [hd.1])
      linarith
    have hh : δ*Endpoint.primeWeight (1/2-x)/(2*Endpoint.balanceDenominator δ (1/2-x))≤1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

theorem balanced_count_identity {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
        (longExponent δ (Endpoint.balancedCutoff δ (1/2-x))) =
      Endpoint.balancedRowCount δ (1/2-x) := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hDb : 0<Endpoint.denominator (1/2-x) := by
    have hh := Endpoint.denominator_bounds hy hy'
    linarith [hh.1]
  have hJb : 0<Endpoint.balanceDenominator δ (1/2-x) := by
    have hh := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
    linarith [hh.1]
  have hl : longExponent δ (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold longExponent Endpoint.balancedRowCount
    ring
  have hs : shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold shortExponent
    rw [denominator_endpoint,primeWeight_endpoint]
    unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
    generalize hDd : Endpoint.denominator (1/2-x) = D at *
    generalize hPd : Endpoint.primeWeight (1/2-x) = P at *
    generalize hJd : Endpoint.balanceDenominator δ (1/2-x) = J at *
    have hJdef : J=(5/6-δ)*D+δ*P := by
      rw [←hJd, Endpoint.balanceDenominator, hDd, hPd]
    have hD : D ≠ 0 := hDb.ne'
    have hJ : J ≠ 0 := hJb.ne'
    field_simp [hD,hJ]
    rw [hJdef]
    ring
  rw [hl,hs,max_self]

theorem high_bin_count {B C U δ r ε γ : ℝ}
    (hC : 0≤C) (hU : 1≤U) (hδ : 5/6≤δ) (hδ' : δ≤1)
    (hγ : 0≤γ) (hr : 1-γ≤ r)
    (hI : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε)) :
    B≤C*U^(1-δ+ε+γ) := by
  apply hI.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  by_cases hr1 : 1≤ r
  · rw [max_eq_right (show 1≤(1+5*r)/6 by linarith)]
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ) (sub_nonneg.mpr hr1)
    nlinarith
  · rw [max_eq_left (show (1+5*r)/6≤1 by linarith)]
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤δ by linarith)
    have hh' := mul_le_mul_of_nonneg_right hδ' hγ
    nlinarith

theorem high_bin_endpoint {δ q R loss : ℝ} (_hδ : 5/6≤δ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss) :
    -(1/48 : ℝ)+(2/3)*δ+q/6-(13/16)*(1-R)≤
      -1/48-δ/16+(13/16)*loss := by
  linarith

theorem balanced_endpoint_with_loss {δ x R loss : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hR : R≤ max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
      (longExponent δ (Endpoint.balancedCutoff δ (1/2-x)))+loss) :
    -(1/48 : ℝ)+(2/3)*δ+(δ*x)/6-(13/16)*(1-R)≤
      -49/440640+(13/16)*loss := by
  rw [balanced_count_identity hδ hδ' hx hx'] at hR
  have hh := Endpoint.balanced_endpoint_margin hδ hδ'
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  unfold Endpoint.balancedExponent at hh
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Detector.CentralExponent -/

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  (17/48)*(1/2-17/50)+a+17/50-1-a*(23/48)-d*(17/50)+d*R+
    d*(a-1/2)+(1/6)*(17/50-1/2+q)

def relativeExponent (δ d R q : ℝ) : ℝ :=
  -1/48+(2/3)*δ+q/6-(13/16)*(1-R)+(d-13/16)*(R+δ/2-17/50)

lemma original_exponent_identity (a d R q : ℝ) :
    sourceExponent a d R q=3/16+relativeExponent (2*a-1) d R q := by
  unfold sourceExponent relativeExponent
  ring

lemma frequency_slope_bounds (δ R : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤1)
    (hRlo : 1-δ≤R) (hRhi : R≤139/96) :
    4/25≤R+δ/2-17/50 ∧ R+δ/2-17/50≤2 := by
  constructor <;> linarith

lemma relative_extend (δ d R q ζ : ℝ) (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    relativeExponent δ d R q≤ relativeExponent δ (13/16) R q+2*ζ := by
  have hh := mul_le_mul_of_nonneg_right (show d-13/16≤ζ by linarith) hslo
  have hh' := mul_le_mul_of_nonneg_left hshi hζ
  unfold relativeExponent
  nlinarith

lemma balanced_source_margin (δ x R Δ loss ζ d : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤5/6) (hx : 0≤x) (hx1 : x≤1/2)
    (hR : R≤Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ := by
  have hb := Endpoint.balanced_endpoint_margin hδ hδ1
    (show 0≤1/2-x by linarith) (show 1/2-x≤1/2 by linarith)
  have he := relative_extend δ d R (δ*x) ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold Endpoint.balancedExponent at hb
  unfold relativeExponent at he ⊢
  nlinarith

lemma high_source_margin (δ R q Δ loss ζ d : ℝ)
    (hq : q≤δ/2) (hR : R≤1-δ+loss)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ)
    (hslo : 0≤R+δ/2-17/50) (hshi : R+δ/2-17/50≤2) :
    sourceExponent ((1+δ)/2) d R q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ := by
  have he := relative_extend δ d R q ζ hζ hd hslo hshi
  rw [original_exponent_identity]
  have hid : 2*((1+δ)/2)-1=δ := by ring
  rw [hid]
  unfold relativeExponent at he ⊢
  nlinarith

lemma floor_source_margin (q Δ ζ d : ℝ) (hq : q≤1/100)
    (hζ : 0≤ζ) (hd : d≤13/16+ζ) :
    sourceExponent (51/100) d 1 q-(3/16+Δ)≤-7/1200-Δ+2*ζ := by
  have he := relative_extend (1/50) d 1 q ζ hζ hd (by norm_num) (by norm_num)
  rw [original_exponent_identity]
  norm_num only at *
  unfold relativeExponent at he ⊢
  nlinarith

lemma intermediate_source_margin (δ q Δ d : ℝ) (_hδ : 0≤δ) (hδ1 : δ≤5/6)
    (hq : q≤δ/2) (hd : d≤1/2) :
    sourceExponent ((1+δ)/2) d (76/75-(2/3)*δ) q-(3/16+Δ)≤-49/14400-Δ := by
  have hs : 0≤(76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hs
  unfold sourceExponent
  nlinarith

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (105/8)*e+12*d*e+d*eps*(N+8)+heightLoss+mesh/6

lemma realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N d e eps heightLoss mesh≤26*e+(N+8)*eps+heightLoss+mesh/6 := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0≤eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e)=
      Z^((25/48)*a-181/300+(105/8)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
end SevenEighths.ProbeCentralExponent

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowwise -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Set
namespace SevenEighths.HeckeDetectorRowwise

theorem norm_sq_le_anchor_integral (F F' : ℝ→ℂ)
    (hF : Continuous F) (hF' : Continuous F')
    (hd : ∀ x, HasDerivAt F (F' x) x) {a b x : ℝ} (hx : x∈Icc a b) :
    ‖F x‖^2≤‖F a‖^2+∫ t in a..b, (‖F t‖^2+‖F' t‖^2) := by
  let G : ℝ→ℝ := fun t => ‖F t‖^2+‖F' t‖^2
  have hG : Continuous G := (hF.norm.pow 2).add (hF'.norm.pow 2)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hx.1
    (hF.norm.pow 2).continuousOn
    (fun t ht => (hd t).norm_sq.hasDerivWithinAt)
    (hG.continuousOn.integrableOn_Icc)
    (fun t ht => show 2*inner (𝕜:=ℝ) (F t) (F' t)≤G t by
      dsimp [G]
      have hc := real_inner_le_norm (F t) (F' t)
      change (F' t * (starRingEnd ℂ) (F t)).re ≤ ‖F t‖*‖F' t‖ at hc
      nlinarith [sq_nonneg (‖F t‖-‖F' t‖)])
  simp only [Pi.pow_apply] at hh
  have hm := intervalIntegral.integral_mono_interval (μ:=volume) (le_refl a) hx.1 hx.2
    (Filter.Eventually.of_forall (fun t => show 0≤G t by dsimp [G]; positivity))
    (hG.intervalIntegrable a b)
  change ‖F x‖^2≤‖F a‖^2+∫ t in a..b, G t
  linarith

theorem rowwise_energy {ι : Type*} (rows : Finset ι) (F F' : ι→ℝ→ℂ)
    (hF : ∀ i∈rows, Continuous (F i)) (hF' : ∀ i∈rows, Continuous (F' i))
    (hd : ∀ i∈rows, ∀ x, HasDerivAt (F i) (F' i x) x)
    (a b E : ℝ) (hab : a≤b) (choice : ι→ℝ)
    (hc : ∀ i∈rows, choice i∈Icc a b)
    (henergy : ∀ t∈Icc a b, ∑ i∈rows, ‖F i t‖^2≤E)
    (henergy' : ∀ t∈Icc a b, ∑ i∈rows, ‖F' i t‖^2≤E) :
    ∑ i∈rows, ‖F i (choice i)‖^2≤(1+2*(b-a))*E := by
  have hg (i : ι) (hi : i∈rows) :
      Continuous (fun t => ‖F i t‖^2+‖F' i t‖^2) :=
    ((hF i hi).norm.pow 2).add ((hF' i hi).norm.pow 2)
  have hs := Finset.sum_le_sum (fun i hi =>
    norm_sq_le_anchor_integral (F i) (F' i) (hF i hi) (hF' i hi) (hd i hi) (hc i hi))
  rw [Finset.sum_add_distrib,←intervalIntegral.integral_finsetSum
    (fun i hi => (hg i hi).intervalIntegrable a b)] at hs
  have hm : (∫ t in a..b, ∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤(b-a)*(2*E) := by
    have hh := intervalIntegral.integral_mono_on (μ:=volume) hab
      ((continuous_finsetSum rows (fun i hi => hg i hi)).intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
      (fun t ht => show (∑ i∈rows, (‖F i t‖^2+‖F' i t‖^2))≤2*E by
        rw [Finset.sum_add_distrib]
        linarith [henergy t ht,henergy' t ht])
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  have ha := henergy a ⟨le_refl a,hab⟩
  nlinarith

theorem rowwise_energy_two {ι : Type*} (rows : Finset ι)
    (F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ)
    (hcont : ∀ j k i, i∈rows → Continuous (Function.uncurry (F j k i)))
    (hdx : ∀ k i, i∈rows → ∀ x y,
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x)
    (hdy : ∀ j i, i∈rows → ∀ x y,
      HasDerivAt (F j 0 i x) (F j 1 i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (px py : ι→ℝ)
    (hpx : ∀ i∈rows, px i∈Icc a b) (hpy : ∀ i∈rows, py i∈Icc c d)
    (henergy : ∀ j k x, x∈Icc a b → ∀ y, y∈Icc c d →
      ∑ i∈rows, ‖F j k i x y‖^2≤E) :
    ∑ i∈rows, ‖F 0 0 i (px i) (py i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  have cx (j k : Fin 2) (i : ι) (hi : i∈rows) (y : ℝ) :
      Continuous (fun x => F j k i x y) :=
    (hcont j k i hi).comp (continuous_id.prodMk continuous_const)
  have cy (j k : Fin 2) (i : ι) (hi : i∈rows) (x : ℝ) :
      Continuous (F j k i x) :=
    (hcont j k i hi).comp (continuous_const.prodMk continuous_id)
  have he (j : Fin 2) (x : ℝ) (hx : x∈Icc a b) :
      ∑ i∈rows, ‖F j 0 i x (py i)‖^2≤(1+2*(d-c))*E :=
    rowwise_energy rows (fun i => F j 0 i x) (fun i => F j 1 i x)
      (fun i hi => cy j 0 i hi x) (fun i hi => cy j 1 i hi x)
      (fun i hi y => hdy j i hi x y) c d E hcd py hpy
      (fun y hy => henergy j 0 x hx y hy) (fun y hy => henergy j 1 x hx y hy)
  exact rowwise_energy rows (fun i x => F 0 0 i x (py i))
    (fun i x => F 1 0 i x (py i))
    (fun i hi => cx 0 0 i hi (py i)) (fun i hi => cx 1 0 i hi (py i))
    (fun i hi x => hdx 0 i hi x (py i)) a b ((1+2*(d-c))*E) hab px hpx
    (he 0) (he 1)

theorem source_height_cost {T E : ℝ} (_hT : 0≤T) (hE : 0≤E) :
    (1+2*((1:ℝ)-0))*((1+2*(T-(-T)))*E)≤12*(1+T)*E := by
  nlinarith

end SevenEighths.HeckeDetectorRowwise

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwise

theorem chain_rowwise {ι : Type*} (rows : Finset ι) (M : ℕ→ι→ℝ→ℝ→ℂ)
    (cm : ∀ n i, n≤2 → Continuous (Function.uncurry (M n i)))
    (dx : ∀ n i x y, n≤1 → HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x)
    (dy : ∀ n i x y, n≤1 → HasDerivAt (M n i x) (I*M (n+1) i x y) y)
    (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ n, n≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖M n i x y‖^2≤E) :
    ∑ i∈rows, ‖M 0 i (σ i) (freq i)‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let F : Fin 2→Fin 2→ι→ℝ→ℝ→ℂ := fun j k i x y =>
    if j=0 then (if k=0 then M 0 i x y else I*M 1 i x y)
    else (if k=0 then -M 1 i x y else -(I*M 2 i x y))
  have cF (j k : Fin 2) (i : ι) (hi : i∈rows) : Continuous (Function.uncurry (F j k i)) := by
    have c0 := cm 0 i (by norm_num)
    have c1 := cm 1 i (by norm_num)
    have c2 := cm 2 i (by norm_num)
    fin_cases j <;> fin_cases k
    · simpa [F] using c0
    · convert c1.const_mul I using 1
      ext p
      simp [F]
      rfl
    · convert c1.neg using 1
      ext p
      simp [F]
      rfl
    · convert (c2.const_mul I).neg using 1
      ext p
      simp [F]
      rfl
  have dFx (k : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (fun u => F 0 k i u y) (F 1 k i x y) x := by
    fin_cases k
    · simpa [F] using dx 0 i x y (by norm_num)
    · simpa [F] using (dx 1 i x y (by norm_num)).const_mul I
  have dFy (j : Fin 2) (i : ι) (hi : i∈rows) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    fin_cases j
    · simpa [F] using dy 0 i x y (by norm_num)
    · convert (dy 1 i x y (by norm_num)).neg using 1
      · ext t
        simp [F]
      · simp [F]
  have eF (j k : Fin 2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖F j k i x y‖^2≤E := by
    fin_cases j <;> fin_cases k
    · simpa [F] using henergy 0 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 1 (by norm_num) x hx y hy
    · simpa [F] using henergy 1 (by norm_num) x hx y hy
    · simpa [F,norm_mul] using henergy 2 (by norm_num) x hx y hy
  simpa only [F,ite_true] using
    rowwise_energy_two rows F cF dFx dFy a b c d E hab hcd σ freq hσ hf eF

end SevenEighths.HeckeDetectorRowwise

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePolynomial -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

def logProfile (W : ℝ→ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ)*W x

theorem logProfile_cover (W : ℝ→ℂ) (D : ℝ) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    ∀ J : Ideal O, J≠0 → logProfile W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
  intro J hJ hw
  exact hc J hJ (fun hz => hw (by simp [logProfile,hz]))

theorem logProfile_support (W : ℝ→ℂ) :
    Function.support (logProfile W)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [logProfile,hw])

theorem logProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : logProfile W =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [logProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hW.contDiffAt

lemma power_sigma_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift u freq))
      (-(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
  have hd := (((hasDerivAt_id (σ : ℂ)).neg).add_const ((freq : ℂ)*I)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1
  · ext u
    congr 1
    simp only [HeckeDyadic.shift,neg_sub,Pi.neg_apply,id_eq]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [Pi.neg_apply,id_eq]
    ring

lemma power_freq_deriv (x σ freq : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ => (x : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(Real.log x : ℂ)*(x : ℂ)^(-HeckeDyadic.shift σ freq)) freq := by
  have hd := (((hasDerivAt_id (freq : ℂ)).mul_const I).const_add (-(σ : ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1
  · ext u
    congr 1
    simp [HeckeDyadic.shift]
    ring
  · have he : -HeckeDyadic.shift σ freq= -(σ : ℂ)+(freq : ℂ)*I := by unfold HeckeDyadic.shift; ring
    rw [he]
    simp only [id_eq]
    ring

theorem polynomial_sigma_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D u freq)
      (-polynomial χ inv (logProfile W) D σ freq) σ := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift u freq))
      (-coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq)) σ := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,neg_zero] using hasDerivAt_const σ (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_sigma_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,neg_mul,Finset.sum_neg_distrib,mul_neg]

theorem polynomial_freq_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    HasDerivAt (fun u => polynomial χ inv W D σ u)
      (I*polynomial χ inv (logProfile W) D σ freq) freq := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  rw [polynomial_eq_finite χ inv (logProfile W) D σ freq S (logProfile_cover W D S hc)]
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun u => coefficient χ inv J*W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ u))
      (I*(coefficient χ inv J*logProfile W ((J.absNorm : ℝ)/D)*
        (((J.absNorm : ℝ)/D : ℝ) : ℂ)^(-HeckeDyadic.shift σ freq))) freq := by
    by_cases hz : J=0
    · subst J
      simpa only [coefficient_zero,zero_mul,mul_zero] using hasDerivAt_const freq (0 : ℂ)
    have hn : 0<(J.absNorm : ℝ)/D := div_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
    convert (power_freq_deriv _ σ freq hn).const_mul
      (coefficient χ inv J*W ((J.absNorm : ℝ)/D)) using 1
    unfold logProfile
    ring
  convert (HasDerivAt.sum (u:=S) hd).const_mul ((D : ℂ)^(-(1/2 : ℂ))) using 1
  all_goals simp only [Finset.sum_apply,←Finset.mul_sum]
  ring

theorem polynomial_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S) :
    Continuous (fun p : ℝ×ℝ => polynomial χ inv W D p.1 p.2) := by
  simp_rw [polynomial_eq_finite χ inv W D _ _ S hc]
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro J hJ
  by_cases hz : J=0
  · subst J
    simp only [coefficient_zero,zero_mul]
    exact continuous_const
  have hn : 0<(J.absNorm : ℝ)/D := div_pos
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hz)) hD
  apply Continuous.const_mul
  apply Continuous.const_cpow _ (Or.inl (Complex.ofReal_ne_zero.mpr hn.ne'))
  unfold HeckeDyadic.shift
  fun_prop

end SevenEighths.HeckeDetectorRowwisePolynomial

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseMarked -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwiseMarked
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

theorem marked_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (inv : Bool) (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (h0 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv W D x y*P i‖^2≤E)
    (h1 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile W) D x y*P i‖^2≤E)
    (h2 : ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) inv (logProfile (logProfile W)) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) inv W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*E) := by
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    polynomial (χ i) inv ((logProfile^[n]) W) D x y*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    interval_cases n
    all_goals
      dsimp [M,Function.uncurry]
      apply Continuous.mul_const
    · exact polynomial_continuous (χ i) inv W D hD S hc
    · exact polynomial_continuous (χ i) inv (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) inv (logProfile (logProfile W)) D hD S hc2
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M] using (polynomial_sigma_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv W D x y hD S hc).mul_const (P i)
    · simpa [M,mul_assoc] using (polynomial_freq_deriv (χ i) inv (logProfile W) D x y hD S hc1).mul_const (P i)
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤E := by
    interval_cases n
    · simpa [M] using h0 x hx y hy
    · simpa [M] using h1 x hx y hy
    · simpa [M] using h2 x hx y hy
  exact chain_rowwise rows M cm dx dy a b c d E hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwiseMarked

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePlain -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePlain
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorRowwisePolynomial

lemma norm_sum_sq_le (u v : ℂ) : ‖u+v‖^2≤2*(‖u‖^2+‖v‖^2) := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v,sq_nonneg (‖u‖-‖v‖)]

theorem plain_squared_rowwise {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (D : ℝ) (hD : 0<D) (S : Finset (Ideal O))
    (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S)
    (P : ι→ℂ) (a b c d E : ℝ) (hab : a≤b) (hcd : c≤d) (hE : 0≤E)
    (σ freq : ι→ℝ) (hσ : ∀ i∈rows, σ i∈Icc a b)
    (hf : ∀ i∈rows, freq i∈Icc c d)
    (henergy : ∀ j k : ℕ, j+k≤2 → ∀ x∈Icc a b, ∀ y∈Icc c d,
      ∑ i∈rows, ‖polynomial (χ i) false ((logProfile^[j]) W) D x y*
        polynomial (χ i) false ((logProfile^[k]) W) D x y*P i‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) false W D (σ i) (freq i)*
      polynomial (χ i) false W D (σ i) (freq i)*P i‖^2≤
      (1+2*(b-a))*((1+2*(d-c))*(16*E)) := by
  let Q (n : ℕ) (i : ι) (x y : ℝ) := polynomial (χ i) false ((logProfile^[n]) W) D x y
  let M (n : ℕ) (i : ι) (x y : ℝ) :=
    if n=0 then Q 0 i x y*Q 0 i x y*P i
    else if n=1 then 2*Q 0 i x y*Q 1 i x y*P i
    else 2*(Q 1 i x y*Q 1 i x y+Q 0 i x y*Q 2 i x y)*P i
  have hc1 := logProfile_cover W D S hc
  have hc2 := logProfile_cover (logProfile W) D S hc1
  have cq (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (Q n i)) := by
    interval_cases n
    · exact polynomial_continuous (χ i) false W D hD S hc
    · exact polynomial_continuous (χ i) false (logProfile W) D hD S hc1
    · exact polynomial_continuous (χ i) false (logProfile (logProfile W)) D hD S hc2
  have qx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => Q n i u y) (-Q (n+1) i x y) x := by
    interval_cases n
    · exact polynomial_sigma_deriv (χ i) false W D x y hD S hc
    · exact polynomial_sigma_deriv (χ i) false (logProfile W) D x y hD S hc1
  have qy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (Q n i x) (I*Q (n+1) i x y) y := by
    interval_cases n
    · exact polynomial_freq_deriv (χ i) false W D x y hD S hc
    · exact polynomial_freq_deriv (χ i) false (logProfile W) D x y hD S hc1
  have cm (n : ℕ) (i : ι) (hn : n≤2) : Continuous (Function.uncurry (M n i)) := by
    have c0 := cq 0 i (by norm_num)
    have c1 := cq 1 i (by norm_num)
    have c2 := cq 2 i (by norm_num)
    change Continuous (fun p : ℝ×ℝ => M n i p.1 p.2)
    change Continuous (fun p : ℝ×ℝ => Q 0 i p.1 p.2) at c0
    change Continuous (fun p : ℝ×ℝ => Q 1 i p.1 p.2) at c1
    change Continuous (fun p : ℝ×ℝ => Q 2 i p.1 p.2) at c2
    interval_cases n <;> dsimp [M] <;> fun_prop
  have dx (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    interval_cases n
    · convert ((qx 0 i x y (by norm_num)).mul (qx 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qx 0 i x y (by norm_num)).mul (qx 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have dy (n : ℕ) (i : ι) (x y : ℝ) (hn : n≤1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    interval_cases n
    · convert ((qy 0 i x y (by norm_num)).mul (qy 0 i x y (by norm_num))).mul_const (P i) using 1
      · ext u; simp [M]
      · simp [M]; ring
    · convert (((qy 0 i x y (by norm_num)).mul (qy 1 i x y (by norm_num))).const_mul 2).mul_const (P i) using 1
      · ext u; dsimp [M]; ring
      · simp [M]; ring
  have he (n : ℕ) (hn : n≤2) (x : ℝ) (hx : x∈Icc a b) (y : ℝ) (hy : y∈Icc c d) :
      ∑ i∈rows, ‖M n i x y‖^2≤16*E := by
    have e00 := henergy 0 0 (by norm_num) x hx y hy
    have e01 := henergy 0 1 (by norm_num) x hx y hy
    have e11 := henergy 1 1 (by norm_num) x hx y hy
    have e02 := henergy 0 2 (by norm_num) x hx y hy
    change ∑ i∈rows, ‖Q 0 i x y*Q 0 i x y*P i‖^2≤E at e00
    change ∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2≤E at e01
    change ∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2≤E at e11
    change ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2≤E at e02
    interval_cases n
    · simpa only [M,ite_true] using e00.trans (show E≤16*E by linarith)
    · have heq : (∑ i∈rows, ‖M 1 i x y‖^2)=4*∑ i∈rows, ‖Q 0 i x y*Q 1 i x y*P i‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hm : M 1 i x y=2*(Q 0 i x y*Q 1 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
      rw [heq]
      linarith
    · have hh : (∑ i∈rows, ‖M 2 i x y‖^2)≤
          8*((∑ i∈rows, ‖Q 1 i x y*Q 1 i x y*P i‖^2)+
          ∑ i∈rows, ‖Q 0 i x y*Q 2 i x y*P i‖^2) := by
        rw [←Finset.sum_add_distrib,Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have hm : M 2 i x y=2*(Q 1 i x y*Q 1 i x y*P i+Q 0 i x y*Q 2 i x y*P i) := by simp [M]; ring
        rw [hm,norm_mul,mul_pow]
        norm_num
        have hh := norm_sum_sq_le (Q 1 i x y*Q 1 i x y*P i) (Q 0 i x y*Q 2 i x y*P i)
        simp only [norm_mul] at hh
        nlinarith
      linarith
  simpa only [M,ite_true,Q,Function.iterate_zero,id_eq] using
    chain_rowwise rows M cm dx dy a b c d (16*E) hab hcd σ freq hσ hf he

end SevenEighths.HeckeDetectorRowwisePlain

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorSimultaneousSupport -/

section

namespace OAI

noncomputable section

open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorSimultaneousSupport
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorDyadicGeometry HeckeDetectorSaturation HeckeDetectorNormalized

theorem from_actual_zero (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100≤a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, (χ j).modulus.absNorm≤Z^d → ∀ ρ : ℂ,
        LFunction (χ j) ρ=0 → a≤ρ.re → |ρ.im|≤(3*i : ℕ)*Z^τ →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤ r ∧ r≤tstar+ε ∧ 0≤ m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤ m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  have hdmaxp : 0<dmax := hdmin.trans_le hdmax
  have hτF : 0<τ/(2*dmax) := by positivity
  obtain ⟨C,UN,hC,hN⟩ := exists_normalized_product 1 (1/2) (τ/(2*dmax))
    (by norm_num) (by norm_num) (by norm_num) hτF
  obtain ⟨US,hS⟩ := actual_saturation 22 dmax τ ε e κ η C
    (by norm_num) hdmaxp.le hτ hε he he' hκ hκ' hη hbudget hC.le
  have hscale := uniform_scale_threshold dmin (max 8 (max UN US)) hdmin
  have hzeroH := uniform_zero_height dmin τ I hτzero
  have hbudgetH := uniform_height_budget dmin τ η I hτ.le hη hτheight
  have hFourier := uniform_fourier_allowance dmax τ hdmaxp hτ
  have hcost := uniform_power_allowance 8 0 dmin ε hε.le (mul_pos hdmin hε)
  have hT := (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2 : ℝ))
  have hall := hscale.and (hzeroH.and (hbudgetH.and (hFourier.and (hcost.and
    (hT.and (eventually_ge_atTop (1 : ℝ)))))))
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀,?_⟩
  intro Z hZlarge d hd hd' ι _ χ hχ a i hi ha ha' hmax j hQ ρ hzero hρ him tstar ht ht'
  obtain ⟨hscale,hzeroH,hbudgetH,hFourier,hcost,hT,hZ⟩ := hZ₀ Z hZlarge
  let U := Z^d
  have hd0 : 0≤d := (hdmin.trans_le hd).le
  have hlarge := hscale d hd
  have hU8 : 8≤U := (le_max_left _ _).trans hlarge
  have hUN : UN≤U := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hUS : US≤U := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hU2 : 2≤U := by linarith
  have hU1 : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hρlo : 51/100≤ρ.re := ha.trans hρ
  have hρhi : ρ.re≤1 := le_of_lt (lt_of_not_ge (fun hh =>
    LFunction_ne_zero_of_one_le_re (χ j) hh (Or.inr (hχ j)) hzero))
  have hh := him.trans (hzeroH d hd i hi)
  obtain ⟨hDs,hDs'⟩ := truncation_scale U tstar hU2 ht ht'
  obtain ⟨J,hJ,K,hK,ν,hν,hprod,hD,hDN,hterminal⟩ :=
    hN U hUN (χ j) (hχ j) (U^tstar) hDs hDs' (by simpa using hQ) ρ hρlo hzero hh
  obtain ⟨hr,hr',hm,hm',heJ,heK⟩ := dyadic_scale_bounds U hU8 J K hterminal
  let r := Real.logb U ((2 : ℝ)^J)
  let m := Real.logb U ((2 : ℝ)^K)
  change U^r=(2 : ℝ)^J at heJ
  change U^m=(2 : ℝ)^K at heK
  have hJpow : (Z^d)^r=(2 : ℝ)^J := heJ
  have hKpow : (Z^d)^m=(2 : ℝ)^K := heK
  have hcostU : 8≤U^ε := by simpa using hcost d hd
  have hsupport := support_exponents U tstar r m ε hU1 hcostU
    (by simpa only [heJ] using hD) (by simpa only [heJ,heK] using hDN)
  have hfreq : |2*Real.pi*ν-ρ.im|+(Z^τ)/2≤(3*i+2 : ℕ)*Z^τ := by
    have habs : |ν|≤U^(τ/(2*dmax)) := by simpa only [Real.norm_eq_abs] using hν
    have hnu := (mul_le_mul_of_nonneg_left habs (show 0≤2*Real.pi by positivity)).trans
      (hFourier d hd0 hd')
    have hbase : |2*Real.pi*ν-ρ.im|≤2*Real.pi*|ν|+|ρ.im| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_mul,
        abs_of_pos (show 0<2*Real.pi by positivity)] using
        (abs_sub_le (2*Real.pi*ν) 0 ρ.im)
    push_cast at him ⊢
    nlinarith
  have hs := hS Z d hZ hd0 hd' hT hUS hU1 χ hχ a i ha ha' hmax j (U^tstar)
    r m ρ.re (2*Real.pi*ν-ρ.im) hQ (by positivity) hr hr' hm hm'
    (by simpa only [hJpow] using hD.le) hρ hρhi hfreq (hbudgetH d hd i hi)
    (by simpa only [hJpow,hKpow] using hprod)
  refine ⟨J,hJ,K,hK,ν,r,m,hν,heJ,heK,?_,hsupport.1,hm,hs.1,
    (by linarith [hsupport.2]),hs.2.1,hs.2.2⟩
  linarith [hsupport.2,hs.1]

theorem from_actual_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j, (χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j : ι, (χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
        ∃ j : ι, ∃ ρ : ℂ, LFunction (χ j) ρ=0 ∧ a≤ρ.re ∧ |ρ.im|≤(3*i : ℕ)*Z^τ ∧
        ∃ J∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
          ∃ K∈Finset.range (HeckeDetectorPartition.length (⌈2*(Z^d)^21⌉₊ : ℝ)+1),
            ∃ ν r m : ℝ,
              ‖ν‖≤(Z^d)^(τ/(2*dmax)) ∧ (Z^d)^r=(2 : ℝ)^J ∧ (Z^d)^m=(2 : ℝ)^K ∧
              tstar-1/2-76*ε≤ r ∧ r≤tstar+ε ∧ 0≤ m ∧ m≤1/2+75*ε ∧ tstar-r-ε≤ m ∧
              (Z^d)^((2*a-1)*r-2*ε)≤
                ‖polynomial (χ j) true
                  (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular ((Z^d)^tstar) ((Z^d)^r))
                  ((Z^d)^r) ρ.re (2*Real.pi*ν-ρ.im)‖^2 ∧
              (Z^d)^((2*a-1)*m-2*ε)≤
                ‖polynomial (χ j) false positiveAnnular ((Z^d)^m) ρ.re (2*Real.pi*ν-ρ.im)‖^2 := by
  obtain ⟨Z₀,hZ₀⟩ := from_actual_zero dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,him,heq⟩ := HeckeDetectorZeros.maximum_attained χ hχ
    ((3*i : ℕ)*Z^τ) (ha.trans_le hcurrent)
  have hρ : a≤ρ.re := by rw [heq]; exact hcurrent
  exact ⟨j,ρ,hzero,hρ,him,hZ₀ Z hZ d hd hd' χ hχ a i hi ha.le ha' hnext j
    (hQ j) ρ hzero hρ him tstar ht ht'⟩

end SevenEighths.HeckeDetectorSimultaneousSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorSlotSelection -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorSlotSelection

theorem whole_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤ mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤ mesh)
    (hg : ∀ i∈s, 0≤g i) (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*g i) :
    ∃ T : Finset α, T⊆s ∧ (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  induction s using Finset.strongInductionOn generalizing q z with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a,ha,hmax⟩ := s.exists_max_image g hs
      by_cases hza : z≤w a
      · refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
        have hzmesh : z≤ mesh := hza.trans (hwm a ha)
        have hprod := mul_le_mul hqG hzmesh hz hG
        simpa only [Finset.sum_empty] using (sub_nonpos.mpr hprod)
      have haz : w a<z := lt_of_not_ge hza
      let s' := s.erase a
      have hss : s'⊂s := Finset.erase_ssubset ha
      have hsub : s'⊆s := Finset.erase_subset a s
      have hsum : ∑ i∈s, w i=w a+∑ i∈s', w i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s w ha).symm
      have hgain : ∑ i∈s, w i*g i=w a*g a+∑ i∈s', w i*g i := by
        simpa [s',add_comm] using (Finset.sum_erase_add s (fun i => w i*g i) ha).symm
      let W := ∑ i∈s', w i
      let A := ∑ i∈s', w i*g i
      have hW : 0<W := by rw [hsum] at hzs; dsimp [W]; linarith
      have hA : 0≤A := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i (hsub hi)) (hg i (hsub hi)))
      have hAg : A≤W*g a := by
        calc
          _ ≤ ∑ i∈s', w i*g a := Finset.sum_le_sum (fun i hi =>
            mul_le_mul_of_nonneg_left (hmax i (hsub hi)) (hw i (hsub hi)))
          _ = _ := by dsimp [W]; rw [Finset.sum_mul]
      let q' := A/W
      have hq' : 0≤q' := div_nonneg hA hW.le
      have hq'a : q'≤g a := (div_le_iff₀ hW).mpr (by simpa [mul_comm] using hAg)
      have hq'G : q'≤G := hq'a.trans (hgG a ha)
      have he : q'*W=A := div_mul_cancel₀ A hW.ne'
      have hz' : 0≤z-w a := sub_nonneg.mpr haz.le
      have hzs' : z-w a≤∑ i∈s', w i := by rw [hsum] at hzs; linarith
      obtain ⟨T,hTs,hTz,hTgain⟩ := ih s' hss
        (fun i hi => hw i (hsub hi)) (fun i hi => hwm i (hsub hi))
        (fun i hi => hg i (hsub hi)) (fun i hi => hgG i (hsub hi))
        q' (z-w a) hq' hq'G hz' hzs' he.le
      have haT : a∉T := fun h => (Finset.mem_erase.mp (hTs h)).1 rfl
      refine ⟨insert a T,Finset.insert_subset_iff.mpr ⟨ha,hTs.trans hsub⟩,?_,?_⟩
      · rw [Finset.sum_insert haT]
        linarith
      · rw [Finset.sum_insert haT]
        have hprefix : q*z≤w a*g a+q'*(z-w a) := by
          rw [hsum,hgain] at hmean
          change q*(w a+W)≤w a*g a+A at hmean
          rw [←he] at hmean
          by_cases hqq : q≤q'
          · have h1 := mul_le_mul_of_nonneg_right hqq hz
            have h2 := mul_le_mul_of_nonneg_left hq'a (hw a ha)
            nlinarith
          · have hqq' : 0≤q-q' := by linarith
            have h1 := mul_le_mul_of_nonneg_left hzs hqq'
            rw [hsum] at h1
            change (q-q')*z≤(q-q')*(w a+W) at h1
            nlinarith
        linarith
    · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      have hz0 : z=0 := by simpa using le_antisymm hzs hz
      refine ⟨∅,Finset.empty_subset _,by simpa using hz,?_⟩
      simp only [Finset.sum_empty,hz0,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg hG hmesh)

theorem whole_positive_slots {α : Type*} (s : Finset α) (w g : α→ℝ) (G mesh : ℝ)
    (hG : 0≤G) (hmesh : 0≤ mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤ mesh)
    (hgG : ∀ i∈s, g i≤G)
    (q z : ℝ) (hq : 0≤q) (hqG : q≤G) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤z ∧ q*z-G*mesh≤∑ i∈T, w i*g i := by
  classical
  obtain ⟨T,hTs,hTz,hTgain⟩ := whole_slots s w (fun i => max (g i) 0) G mesh hG hmesh
    hw hwm (fun i hi => le_max_right _ _) (fun i hi => max_le (hgG i hi) hG)
    q z hq hqG hz hzs hmean
  let P := T.filter (fun i => 0<g i)
  have hPT : P⊆T := Finset.filter_subset _ _
  refine ⟨P,hPT.trans hTs,fun i hi => (Finset.mem_filter.mp hi).2,?_,?_⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg hPT (fun i hi _ => hw i (hTs hi))).trans hTz
  · have he : (∑ i∈T, w i*max (g i) 0)=∑ i∈P, w i*g i := by
      calc
        _ = ∑ i∈P, w i*max (g i) 0 := by
          symm
          apply Finset.sum_subset hPT
          intro i hi hn
          have hg : g i≤0 := le_of_not_gt (fun h => hn (Finset.mem_filter.mpr ⟨hi,h⟩))
          rw [max_eq_right hg,mul_zero]
        _ = _ := Finset.sum_congr rfl (fun i hi => by
          rw [max_eq_left (Finset.mem_filter.mp hi).2.le])
    rwa [he] at hTgain

theorem selected_product_spike {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤ mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤ mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0)
    : ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧ (∑ i∈T, w i)≤z ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  obtain ⟨T,hTs,hTpos,hTz,hgain⟩ := whole_positive_slots s w g (δ/2) mesh
    (by positivity) hmesh hw hwm hg q z hq hqδ hz hzs hmean
  refine ⟨T,hTs,hTpos,hTz,?_⟩
  intro Q hQ
  have hUp : 0<U := by linarith
  calc
    _ ≤ U^(∑ i∈T, 2*w i*g i) := Real.rpow_le_rpow_of_exponent_le hU (by
      have he : (∑ i∈T, 2*w i*g i)=2*(∑ i∈T, w i*g i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linarith)
    _ = ∏ i∈T, U^(2*w i*g i) := Real.rpow_sum_of_pos hUp _ _
    _ ≤ ∏ i∈T, ‖Q i‖^2 := Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg hUp.le _)
      (fun i hi => hQ i (hTs hi) (hTpos i hi))
    _ = _ := by rw [norm_prod,Finset.prod_pow]

theorem selected_product_with_decrement {α : Type*} (s : Finset α) (w g : α→ℝ)
    (U δ mesh q z ν : ℝ) (hU : 1≤U) (hδ : 0≤δ) (hmesh : 0≤ mesh)
    (hw : ∀ i∈s, 0≤w i) (hwm : ∀ i∈s, w i≤ mesh)
    (hg : ∀ i∈s, g i≤δ/2) (hq : 0≤q) (hqδ : q≤δ/2) (hz : 0≤z) (hν : 0≤ν)
    (hzs : z≤∑ i∈s, w i) (hmean : q*(∑ i∈s, w i)≤∑ i∈s, w i*max (g i) 0) :
    ∃ T : Finset α, T⊆s ∧ (∀ i∈T, 0<g i) ∧
      (∑ i∈T, w i)≤ max 0 (z-ν) ∧
      ∀ Q : α→ℂ, (∀ i∈s, 0<g i → U^(2*w i*g i)≤‖Q i‖^2) →
        U^(2*q*z-2*q*ν-δ*mesh)≤‖∏ i∈T, Q i‖^2 := by
  have hcap : max 0 (z-ν)≤z := max_le hz (by linarith)
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := selected_product_spike s w g U δ mesh q (max 0 (z-ν))
    hU hδ hmesh hw hwm hg hq hqδ (le_max_left _ _) (hcap.trans hzs) hmean
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply le_trans _ (hTb Q hQ)
  apply Real.rpow_le_rpow_of_exponent_le hU
  have hh := mul_le_mul_of_nonneg_left (le_max_right 0 (z-ν)) (show 0≤2*q by positivity)
  nlinarith

end SevenEighths.HeckeDetectorSlotSelection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessRows -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def dyadicLength (U : ℝ) : ℕ := HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1

structure Witness {ι : Type*} (χ : ι→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  label : ι
  zero : ℂ
  zero_eq : LFunction (χ label) zero=0
  zero_lower : a≤zero.re
  zero_height : |zero.im|≤(3*i : ℕ)*T
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  nu : ℝ
  r : ℝ
  m : ℝ
  nu_bound : ‖nu‖≤allowance
  left_scale : U^r=(2 : ℝ)^left.val
  right_scale : U^m=(2 : ℝ)^right.val
  inverse_length_lower : tstar-1/2-76*ε≤ r
  inverse_length_upper : r≤tstar+ε
  plain_length_lower : 0≤ m
  plain_length_upper : m≤1/2+75*ε
  inverse_spike : U^((2*a-1)*r-2*ε)≤
    ‖polynomial (χ label) true
      (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
      (U^r) zero.re (2*Real.pi*nu-zero.im)‖^2
  plain_spike : U^((2*a-1)*m-2*ε)≤
    ‖polynomial (χ label) false positiveAnnular (U^m) zero.re (2*Real.pi*nu-zero.im)‖^2

def Witness.frequency {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : ℝ := 2*Real.pi*w.nu-w.zero.im

theorem Witness.frequency_bound {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) :
    |w.frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T := by
  have hnu : |w.nu|≤allowance := by simpa only [Real.norm_eq_abs] using w.nu_bound
  have hh := abs_sub_le (2*Real.pi*w.nu) 0 w.zero.im
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hnu (by positivity)) w.zero_height)

theorem Witness.real_part_upper {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : w.zero.re≤1 := by
  by_contra hn
  exact LFunction_ne_zero_of_one_lt_re (χ w.label) (lt_of_not_ge hn) w.zero_eq

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem exists_from_maximum (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→Character) (hχ : ∀ j,(χ j).residue≠1)
        (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)<a+2*e →
        a≤HeckeDetectorZeros.zeroMaximum χ hχ ((3*i : ℕ)*Z^τ) →
        (∀ j,(χ j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
          Nonempty (Witness χ (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSimultaneous.from_actual_maximum dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' ι _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩ :=
    hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  exact ⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
    nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩⟩

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorDynamicSelection -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorDynamicSelection
open HeckeFamily HeckeDetectorWitnessRows

theorem actual_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀≤Z → ∀ d : ℝ, dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ), i≤I → 51/100<a → a≤1 →
        (∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u, a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ, 1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,Witness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := exists_from_maximum dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  exact ⟨fun u => Classical.choice (hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha'
    (hnext u) (hcurrent u) (hQ u) tstar ht ht')⟩

def fiber {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i) :
    rows.card=∑ label : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (fiber rows χ U a ε tstar T allowance i w label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => ((w u).label,(w u).left,(w u).right))
    (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

end SevenEighths.HeckeDetectorDynamicSelection

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

structure SupportedWitness {Label : Type*} (χ : Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    extends Witness χ U a ε tstar T allowance i where
  product_length_lower : tstar-r-ε≤ m

theorem actual_supported_witness_family (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := HeckeDetectorSimultaneousSupport.from_actual_maximum dmin dmax τ ε e κ η I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ tstar ht ht'
  have hw (u : Row) : Nonempty (SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i) := by
    obtain ⟨j,ρ,hzero,hρ,hheight,J,hJ,K,hK,nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hprod,hM,hS⟩ :=
      hZ₀ Z hZ d hd hd' (χ u) (hχ u) a i hi ha ha' (hnext u) (hcurrent u) (hQ u) tstar ht ht'
    exact ⟨⟨⟨j,ρ,hzero,hρ,hheight,⟨J,Finset.mem_range.mp hJ⟩,⟨K,Finset.mem_range.mp hK⟩,
      nu,r,m,hnu,hleft,hright,hr,hr',hm,hm',hM,hS⟩,hprod⟩⟩
  exact ⟨fun u => Classical.choice (hw u)⟩

theorem fiber_lengths {Row Label : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (χ : Row→Label→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    tstar-r-ε≤ m ∧ r≤tstar+ε ∧ m≤1/2+75*ε ∧ tstar-1/2-76*ε≤ r ∧ 0≤ m := by
  obtain ⟨u,hu⟩ := hne
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by
    rw [(w u).toWitness.left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by
    rw [(w u).toWitness.right_exponent hU,hK u hu]
  exact hr ▸ hm ▸ ⟨(w u).product_length_lower,(w u).inverse_length_upper,
    (w u).plain_length_upper,(w u).inverse_length_lower,(w u).plain_length_lower⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorAdaptiveCutoff -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorRowCount

def cutoff (δ q : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedCutoff δ (1/2-min (1/2) (max 0 (q/δ))) else 3/2

theorem cutoff_bounds (δ q : ℝ) (hδ : 0≤δ) : 1≤ cutoff δ q ∧ cutoff δ q≤3/2 := by
  unfold cutoff
  split_ifs with hd
  · exact balanced_cutoff_bounds hδ hd (le_min (by norm_num) (le_max_left _ _)) (min_le_left _ _)
  · norm_num

theorem cutoff_eq_balanced (δ q : ℝ) (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) :
    cutoff δ q=Endpoint.balancedCutoff δ (1/2-q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,ite_eq_left hd,max_eq_right hx,min_eq_right hx']

theorem cutoff_eq_high (δ q : ℝ) (hδ : 5/6<δ) : cutoff δ q=3/2 := by
  simp only [cutoff,ite_eq_right (not_le_of_gt hδ)]

theorem actual_adaptive_witnesses (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ,∀ Z : ℝ,Z₀≤Z → ∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ {Row Label : Type*} [Fintype Label] (χ : Row→Label→Character)
        (hχ : ∀ u j,(χ u j).residue≠1) (a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀ u,HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ)<a+2*e) →
        (∀ u,a≤HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
        (∀ u j,(χ u j).modulus.absNorm≤Z^d) → ∀ q : Row→ℝ,
          Nonempty (∀ u,SupportedWitness (χ u) (Z^d) a ε (cutoff (2*a-1) (q u))
            (Z^τ) ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z₀,hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀,?_⟩
  intro Z hZ d hd hd' Row Label _ χ hχ a i hi ha ha' hnext hcurrent hQ q
  have hδ : 0≤2*a-1 := by linarith
  exact ⟨fun u => (Classical.choice (hZ₀ Z hZ d hd hd' χ hχ a i hi ha ha'
    hnext hcurrent hQ (cutoff (2*a-1) (q u))
      (cutoff_bounds (2*a-1) (q u) hδ).1 (cutoff_bounds (2*a-1) (q u) hδ).2)) u⟩

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScale -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeDetectorRowwise

def scaleProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := -W y/2-(y : ℂ)*deriv W y

def scaleSum (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleProfile_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    Continuous (scaleProfile W) := by
  have hd := hW.continuous_deriv (by simp)
  unfold scaleProfile
  fun_prop

theorem scaleProfile_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) : Function.support (scaleProfile W)⊆Icc a b := by
  intro y hy
  by_contra hn
  have hw : W y=0 := by by_contra hw; exact hn (hs hw)
  have hd : deriv W y=0 := by
    apply deriv_of_notMem_tsupport
    exact fun h => hn ((closure_minimal hs isClosed_Icc) h)
  exact hy (by simp [scaleProfile,hw,hd])

theorem scaleSum_continuous (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ W S) (scaleSum χ (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ true J) using 1
    · rfl
    · change coefficient χ true J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ true J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
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

theorem scale_normalization (l : ℝ) :
    ((Real.exp l : ℝ) : ℂ)^(-(1/2 : ℂ))=Complex.exp (-(l : ℂ)/2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos l).ne'),
    ←Complex.ofReal_log (Real.exp_pos l).le,Real.log_exp]
  congr 1
  ring

theorem scaleSum_eq_polynomial (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ W S l=polynomial χ true W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ true W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (shift σ freq)=shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

theorem conjugate_profile_support (W : ℝ→ℂ) :
    Function.support (fun x => conj (W x))=Function.support W := by
  ext x
  simp

theorem conjugate_profile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => conj (W x)) := by
  exact Complex.conjCLE.contDiff.comp hW

theorem scaleProfile_conjugate (W : ℝ→ℂ) (x : ℝ) :
    scaleProfile (fun y => conj (W y)) x=conj (scaleProfile W x) := by
  have hd : deriv (fun y => conj (W y)) x=conj (deriv W x) := by
    simpa only [star_def] using (deriv.star (f:=W) (x:=x))
  simp only [scaleProfile,hd,map_sub,map_div₀,map_neg,map_mul,conj_ofReal,map_ofNat]

theorem logProfile_conjugate (W : ℝ→ℂ) (x : ℝ) :
    HeckeDetectorRowwisePolynomial.logProfile (fun y => conj (W y)) x=
      conj (HeckeDetectorRowwisePolynomial.logProfile W x) := by
  simp only [HeckeDetectorRowwisePolynomial.logProfile,map_mul,conj_ofReal]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer -/

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

def orientedProfile (reverse : Bool) (W : ℝ→ℂ) : ℝ→ℂ :=
  if reverse then fun x => conj (W x) else W

def orientedFrequency (reverse : Bool) (freq : ℝ) : ℝ := if reverse then -freq else freq

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

theorem orientedFrequency_abs (reverse : Bool) (freq : ℝ) :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorRowwise
open ConcretePrimeRowBridge hiding O

def scaleSupport (upper b : ℝ) : Finset (Ideal O) := idealsUpTo ⌈Real.exp upper*b⌉₊

theorem scaleSupport_cover (W : ℝ→ℂ) (a b upper l : ℝ) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hl : l≤upper) :
    ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈scaleSupport upper b := by
  intro J hJ hw
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ),?_⟩
  have hh := (div_le_iff₀ (Real.exp_pos l)).mp (hWs hw).2
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hl) hb
  have hn : (J.absNorm : ℝ)≤Real.exp upper*b := by nlinarith
  exact_mod_cast hn.trans (Nat.le_ceil _)

theorem rowwise_scales {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi) (l : ι→ℝ)
    (hl : ∀ i∈rows, l i∈Icc lo hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp (l i)) 0 0‖^2≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hsp := scaleProfile_support W a b hWs
  have eq0 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) W S t (scaleSupport_cover W a b hi t hb hWs ht.2)
  have eq1 (i : ι) (t : ℝ) (ht : t∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) (scaleProfile W) S t
      (scaleSupport_cover (scaleProfile W) a b hi t hb hsp ht.2)
  have hh := rowwise_energy rows (fun i => scaleSum (χ i) W S)
    (fun i => scaleSum (χ i) (scaleProfile W) S)
    (fun i hi => scaleSum_continuous (χ i) W S hW.continuous)
    (fun i hi => scaleSum_continuous (χ i) (scaleProfile W) S (scaleProfile_continuous W hW))
    (fun i hi t => scaleSum_deriv (χ i) W S (hW.differentiable (by simp)) t)
    lo hi E hlh l hl
    (fun t ht => by simpa only [eq0 _ t ht] using h0 t ht)
    (fun t ht => by simpa only [eq1 _ t ht] using h1 t ht)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [eq0 i (l i) (hl i hi)]

theorem exists_scale_majorant {ι : Type*} (rows : Finset ι) (χ : ι→Character)
    (W : ℝ→ℂ) (a b : ℝ) (hb : 0≤b) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (lo hi E : ℝ) (hlh : lo≤hi)
    (h0 : ∀ t∈Icc lo hi, ∑ i∈rows, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤E)
    (h1 : ∀ t∈Icc lo hi, ∑ i∈rows,
      ‖polynomial (χ i) true (scaleProfile W) (Real.exp t) 0 0‖^2≤E) :
    ∃ B : ι→ℝ, (∀ i, 0≤B i) ∧
      (∀ i, ∀ t∈Icc lo hi, ‖polynomial (χ i) true W (Real.exp t) 0 0‖^2≤B i) ∧
      (∑ i∈rows, B i)≤(1+2*(hi-lo))*E := by
  let S := scaleSupport hi b
  have hm (i : ι) : ∃ t∈Icc lo hi, ∀ u∈Icc lo hi,
      ‖scaleSum (χ i) W S u‖^2≤‖scaleSum (χ i) W S t‖^2 := by
    exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlh)
      ((scaleSum_continuous (χ i) W S hW.continuous).norm.pow 2).continuousOn
  choose t ht hmax using hm
  refine ⟨fun i => ‖polynomial (χ i) true W (Real.exp (t i)) 0 0‖^2,
    fun i => sq_nonneg _,?_,?_⟩
  · intro i u hu
    have hh := hmax i u hu
    rw [scaleSum_eq_polynomial (χ i) W S u (scaleSupport_cover W a b hi u hb hWs hu.2),
      scaleSum_eq_polynomial (χ i) W S (t i) (scaleSupport_cover W a b hi (t i) hb hWs (ht i).2)] at hh
    exact hh
  · exact rowwise_scales rows χ W a b hb hWs hW lo hi E hlh t (fun i hi => ht i) h0 h1

theorem polynomial_zero_small_scale (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (a b D σ freq : ℝ) (hD : 0<D) (hs : Function.support W⊆Icc a b)
    (hsmall : D*b<1) : polynomial χ inv W D σ freq=0 := by
  unfold polynomial
  suffices hh : (∑' J : HeckeDyadic.NonzeroIdeal, summand χ inv W D σ freq J)=0 by
    rw [hh,mul_zero]
  have hz : ∀ J : HeckeDyadic.NonzeroIdeal, summand χ inv W D σ freq J=0 := by
    intro J
    have hw : W (norm J/D)=0 := by
      by_contra hn
      have hb := (div_le_iff₀ hD).mp (hs hn).2
      have hN : 1≤norm J := by
        change (1 : ℝ) ≤ (J.val.absNorm : ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr J.property)
      nlinarith
    simp only [summand,hw,mul_zero,zero_mul]
  simp only [hz,tsum_zero]

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationAggregate -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic
abbrev PrimeIdeal := SmoothMobiusCorrection.PrimeIdeal

def primeRowMap (p : FreeRow×PrimeIdeal) : NonzeroElement :=
  amplifiedElement ⟨p.1.val,p.1.property.1⟩ ⟨p.2.val,p.2.property.ne_zero⟩

theorem primeRowMap_injective : Function.Injective primeRowMap := by
  intro p q hpq
  have he : rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)=
      rowMap (q.1,⟨q.2.val,q.2.property.ne_zero⟩) := congrArg Subtype.val hpq
  have hh := rowMap_injective he
  apply Prod.ext
  · exact congrArg (fun r : FreeRow×NonzeroIdeal => r.1) hh
  · apply Subtype.ext
    exact congrArg (fun r : FreeRow×NonzeroIdeal => r.2.val) hh

theorem primeRowMap_norm_bound (p : FreeRow×PrimeIdeal) (U V : ℝ)
    (hU : (Ideal.span {p.1.val}).absNorm≤U) (hV : (p.2.val.absNorm : ℝ)≤V) :
    ((Ideal.span {((primeRowMap p).val)}).absNorm : ℝ)≤U*V^6 := by
  have hn := rowMap_norm (p.1,⟨p.2.val,p.2.property.ne_zero⟩)
  change ((Ideal.span {rowMap (p.1,⟨p.2.val,p.2.property.ne_zero⟩)}).absNorm : ℝ)≤_
  rw [hn,Nat.cast_mul,Nat.cast_pow]
  exact mul_le_mul hU (pow_le_pow_left₀ (Nat.cast_nonneg _) hV 6)
    (by positivity) ((Nat.cast_nonneg _).trans hU)

theorem averaged_energy (data : RowData) (rows : Finset FreeRow) (primes : Finset PrimeIdeal)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D U V E : ℝ) (hD : 0<D) (hV : 1≤V)
    (hrows : ∀ u∈rows, ((Ideal.span {u.val}).absNorm : ℝ)≤U)
    (hprimes : ∀ P∈primes, (P.val.absNorm : ℝ)≤V)
    (hraw0 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true W (Real.exp l) 0 0‖^2≤E)
    (hraw1 : ∀ R : Finset NonzeroElement,
      (∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6) →
      ∀ l∈Icc (Real.log D-Real.log V) (Real.log D),
      ∑ v∈R, ‖polynomial (data.character v) true (scaleProfile W) (Real.exp l) 0 0‖^2≤E) :
    (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      4*(1+2*Real.log V)*E := by
  let R := (rows×ˢprimes).image primeRowMap
  have hR : ∀ v∈R, ((Ideal.span {v.val}).absNorm : ℝ)≤U*V^6 := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
    exact primeRowMap_norm_bound p U V (hrows p.1 hu) (hprimes p.2 hP)
  have hl : Real.log D-Real.log V≤Real.log D := by linarith [Real.log_nonneg hV]
  obtain ⟨B,hB,hmajor,henergy⟩ := exists_scale_majorant R data.character W a b hb hWs hW
    (Real.log D-Real.log V) (Real.log D) E hl (hraw0 R hR) (hraw1 R hR)
  have hamp (u : FreeRow) (hu : u∈rows) (P : PrimeIdeal) (hP : P∈primes) :
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*B (primeRowMap (u,P)) := by
    have hN : (1 : ℝ)≤P.val.absNorm := by
      exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
    have hNp : (0 : ℝ)<P.val.absNorm := by linarith
    have hlog : Real.log (P.val.absNorm : ℝ)≤Real.log V :=
      Real.log_le_log hNp (hprimes P hP)
    have hDV : Real.log (D/(P.val.absNorm : ℝ))∈Icc (Real.log D-Real.log V) (Real.log D) := by
      rw [Real.log_div hD.ne' hNp.ne']
      constructor <;> linarith [Real.log_nonneg hN]
    have hbase := hmajor (primeRowMap (u,P)) (Real.log D) ⟨hl,le_refl _⟩
    have hlow := hmajor (primeRowMap (u,P)) (Real.log (D/(P.val.absNorm : ℝ))) hDV
    rw [Real.exp_log hD] at hbase
    rw [Real.exp_log (div_pos hD hNp)] at hlow
    have hh := data.prime_energy ⟨u.val,u.property.1⟩ P W a b ha hWs hW D 0 0 hD
    change ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤
      2*(‖polynomial (data.character (primeRowMap (u,P))) true W D 0 0‖^2+
        ‖polynomial (data.character (primeRowMap (u,P))) true W (D/(P.val.absNorm : ℝ)) 0 0‖^2) at hh
    linarith
  have hs : (primes.card : ℝ)*∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2≤4*∑ v∈R, B v := by
    calc
      _ = ∑ p∈rows×ˢprimes,
          ‖polynomial (data.character ⟨p.1.val,p.1.property.1⟩) true W D 0 0‖^2 := by
        rw [Finset.sum_product]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        change (primes.card : ℝ) *
          ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2 =
          ∑ _P∈primes, ‖polynomial (data.character ⟨u.val,u.property.1⟩) true W D 0 0‖^2
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p∈rows×ˢprimes, 4*B (primeRowMap p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hP⟩ := Finset.mem_product.mp hp
        exact hamp p.1 hu p.2 hP
      _ = _ := by
        dsimp [R]
        rw [Finset.mul_sum,Finset.sum_image]
        exact fun p hp q hq h => primeRowMap_injective h
  have hh := mul_le_mul_of_nonneg_left henergy (by norm_num : (0 : ℝ)≤4)
  nlinarith

end SevenEighths.HeckeInverseAmplification

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicControl -/

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace SevenEighths.HeckePrimeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem logDeriv_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I =
      if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (hψs : LFunction ψ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (LFunction ψ) s +
      logDeriv (factors χ.modulus ψ) s := by
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have heq : LFunction χ =ᶠ[nhds s] (fun z => LFunction ψ z * factors χ.modulus ψ z) := by
    filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with z hz
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hz
  rw [(logDeriv_congr_nhds heq).self_of_nhds]
  exact logDeriv_fun_mul s hψs (factors_ne_zero _ _ hs)
    (LFunction_entire_nonprincipal ψ hψ s) (factors_differentiable _ _ s)

theorem original_disk_control (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction χ) z‖ ≤ B*Real.log (complexity χ t) +
          localBound (1/2)*Real.log ((radical χ.modulus).absNorm : ℝ) := by
  obtain ⟨Dp,B,_,hB,hprimitive⟩ := HeckeLogarithmicActual.disk_control e 1 he he' (by norm_num)
  refine ⟨B,hB,?_⟩
  intro χ hχ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).2 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := HeckeDeletionDerivative.factors_logDeriv_norm (1/2) (by norm_num)
    χ.modulus ψ hzre
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 < complexity ψ t := (Real.exp_pos 1).trans_le (complexity_ge_exp ψ t)
  rw [logDeriv_eq_of_mask χ ψ hmask hχ hzpos (by simpa [hregular] using hzeroψ z hz2)]
  apply (norm_add_le _ _).trans
  exact add_le_add (hbound.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hc0 hQ) hB)) hdel

theorem buffered_original_control (e : ℝ) (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-8*e),
        ‖logDeriv (LFunction (χ j)) z‖ ≤ B*Real.log (complexity (χ j) t) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := original_disk_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

theorem buffered_rectangle_control (e : ℝ)
    (he : 0<e) (he' : e<1/1000) :
    ∃ B : ℝ, 0≤B ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+8*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖logDeriv (LFunction (χ j)) z‖≤
        B*Real.log (complexity (χ j) ((3*i+2 : ℕ)*T)) +
          localBound (1/2)*Real.log ((radical (χ j).modulus).absNorm : ℝ) := by
  obtain ⟨B,hB,hbound⟩ := buffered_original_control e he he'
  refine ⟨B,hB,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-8*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2 : ℂ)+z.im*I)=((z.re-2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-2≤0)]
    linarith
  have hz2 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-2*e) :=
    closedBall_subset_closedBall (by linarith) hz6
  refine ⟨HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
    hmax j z.im hzi hz2, ?_⟩
  apply (hbound χ hχ T a i hT ha ha' hmax j z.im hzi z hz6).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.log_le_log ((Real.exp_pos 1).trans_le (complexity_ge_exp _ _))
  unfold complexity
  have hH : 0 ≤ (3*i+2 : ℕ)*T := (abs_nonneg z.im).trans hzi
  rw [abs_of_nonneg hH]
  gcongr

end SevenEighths.HeckePrimeDyadicControl

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Hecke.SignalBounds -/

section

namespace OAI

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
namespace SevenEighths.HeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) {x : ℝ} (hx : 1≤x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact HeckeSignalShift.contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8<s.re})
    (hb : ∀ s : ℂ, 7/8<s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (7/8 : ℝ)<a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta<a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact HeckeSignalShift.signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end SevenEighths.HeckeSignalBounds

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def twistedProfile (W : ℝ → ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-shift σ freq)

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

theorem normalization_eq (Z r : ℝ) (hZ : 0<Z) :
    ((Z^r:ℝ):ℂ)^(-(1/2:ℂ))=((Z^(-r/2):ℝ):ℂ) := by
  have he : (-(1/2:ℂ))=((-(1/2:ℝ)):ℂ) := by norm_num
  calc
    _ = (((Z^r)^(-(1/2:ℝ)):ℝ):ℂ) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_cpow
          (Real.rpow_nonneg hZ.le r) (-(1/2:ℝ))).symm
    _ = _ := ?_
  rw [←Real.rpow_mul hZ.le]
  congr 2
  ring

theorem inverse_eq_initial_source (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial S 1 η (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u := by
  rw [polynomial_eq_finite χ true W (Z^r) σ freq S hcover,normalization_eq Z r hZ]
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  apply congrArg (fun x:ℂ=>((Z^(-r/2):ℝ):ℂ)*x)
  apply Finset.sum_congr rfl
  intro I hI
  simp only [coefficient,ite_true,hrow,heckeIdealCharacter_apply,
    twistedProfile]
  ring

theorem canonical_inverse_eq_initial_source (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial (idealsUpTo ⌈Z^r*b⌉₊) 1
        (idealCoeff η).toMonoidHom (fun _=>1)
        (twistedProfile W σ freq) Z r 0 (m^6*f^4*z) := by
  apply inverse_eq_initial_source (idealCoeff η).toMonoidHom χ (m^6*f^4*z)
    (HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow) W Z r σ freq hZ
  exact finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW

theorem inverse_times_mark_eq_initial (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*idealCoeff χ p)=
      ∑p∈P,A p*originalTotalPolynomial S p η
        (fun _=>1) (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hcover]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=
      ((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow p]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A p*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η p*CanonicalRowCompletion.idealRowHom u p)*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem originalTotal_supported_source (S : Finset (Ideal O)) (P : Ideal O)
    (η : Ideal O →* ℂ) (hη : ∀I,¬CanonicalQuadraticSieve.Supported I → η I=0)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u=
      originalTotalPolynomial (S.filter CanonicalQuadraticSieve.Supported) P η a W Z r z u := by
  unfold originalTotalPolynomial
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with hi
  · rfl
  · simp only [heckeIdealCharacter_apply,hη I hi,zero_mul,mul_zero]

def fixedBase (η : Character) (m f : O) : Ideal O →* ℂ :=
  heckeIdealCharacter (idealCoeff η).toMonoidHom (m^6*f^4)

theorem fixedBase_row (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I=fixedBase η m f I*CanonicalRowCompletion.idealRowHom z I := by
  rw [HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow,
    CanonicalRowCompletion.idealRowHom_argument_mul]
  change idealCoeff η I*(CanonicalRowCompletion.idealRowHom (m^6*f^4) I*
    CanonicalRowCompletion.idealRowHom z I)=
    (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*f^4) I)*
    CanonicalRowCompletion.idealRowHom z I
  ring

theorem fixedBase_zero_unsupported (η : Character) (m f : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (I : Ideal O) (hI : ¬CanonicalQuadraticSieve.Supported I) : fixedBase η m f I=0 := by
  by_cases hi : I=0
  · subst I
    change idealCoeff η 0*_=0
    rw [map_zero,zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hi
  have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
  have he := CanonicalRowCompletion.rowTwist_zero_of_not_supported
    (elementHom η) m f 1 n hmLam hm2 (by rwa [hs])
  change elementCoeff η n*CanonicalRowCompletion.idealRowHom (m^6*f^4*1)
    (Ideal.span {n})=0 at he
  rw [mul_one,hs,←idealCoeff_span η hn,hs] at he
  exact he

theorem canonical_inverse_eq_supported_initial (η χ : Character) (m f z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial ((idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase η m f) (fun _=>1) (twistedProfile W σ freq) Z r 0 z := by
  rw [inverse_eq_initial_source (fixedBase η m f) χ z (fixedBase_row η χ m f z hrow)
    W Z r σ freq hZ (idealsUpTo ⌈Z^r*b⌉₊)
    (finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW)]
  exact originalTotal_supported_source _ _ _ (fixedBase_zero_unsupported η m f hmLam hm2)
    _ _ _ _ _ _

theorem inverse_times_conjugate_row_mark_norm (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hη : ∀p∈P,A p≠0 → η p≠0)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p))‖=
    ‖∑p∈P,(star (A p)/η p)*originalTotalPolynomial S p η
      (fun _=>1) (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑p∈P,(star (A p)/η p)*idealCoeff χ p)=
      star (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p)) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases ha : A p=0
    · simp [ha]
    · rw [hrow p]
      field_simp [hη p hp ha]
  rw [←inverse_times_mark_eq_initial η χ u hrow W Z r z σ freq hZ S P
    (fun p=>star (A p)/η p) hcover,hm]
  simp only [norm_mul,norm_star]

end SevenEighths.InverseInitialRawDictionary

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge SevenEighths.InverseInitialEnergyCallerPool
namespace SevenEighths.InverseInitialEnergyCallerWindow
local notation "Eis" => ActualEisensteinCubic.O

def originalSource (Z r b : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported (Z r b : ℝ) :
    ∀n∈originalSource Z r b,Squarefree n→Supported n := by
  intro n hn _
  exact (Finset.mem_filter.mp hn).2

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j c : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hc : Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (admissible_of_dvd hP hj),
        admissible_supported (admissible_of_dvd hc (idealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive

theorem original_selector_window
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns (originalSource Z r b) P j).Nonempty)
    (a : Ideal Eis→ℂ) (A : Finset (primePool (columns (originalSource Z r b) P j))) :
    reconstructedSelector (originalSource Z r b) P j a A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      InverseMoment.primeMark (forcedSlots (originalSource Z r b) P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) := by
  have hF : ∀I∈columns (originalSource Z r b) P j,Admissible I :=
    fun I hI=>columns_admissible _ hP hj (originalSource_supported Z r b) hI
  have hA := InitialMeanSquare.poolProduct_admissible _ hF A
  apply original_selector_forced_slots _ hP hj hne a
    (fun c=>residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))) A hA.2.1
  intro hPc hlive _
  exact reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hPc hlive

end SevenEighths.InverseInitialEnergyCallerWindow

end

end OAI

end

