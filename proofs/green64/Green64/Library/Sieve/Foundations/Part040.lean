module

public import Green64.Library.Sieve.Foundations.Part039
public import Green64.Library.Sieve.Foundations.Part038
public import Green64.Library.Sieve.Foundations.Part031
public import Green64.Library.Sieve.Foundations.Part021
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part023
public import Green64.Library.Sieve.Foundations.Part037
public import Green64.Library.Sieve.Foundations.Part033
public import Green64.Library.Weights.Part113

@[expose] public section

/-!
# Sieve / Foundations / Part040

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## TrueMellinTailExponentAbsorption -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 700000

/-- Explicit power accounting for the TRUE Parity Ψ-Mellin cutoff
R=L^C0/(2π): R^-H × L^Cmass <= (2π)^H L^-A if the original
Schwartz moment order H is fixed BEFORE L with
A+Cmass <= C0*H. This pays the real 2π convention and the exact
source high-frequency shifted-divisor mass; no hidden spectral
loss or choice of H depending on L. -/
theorem parity_original_true_mellin_tail_power_absorption434
    (L C0 A Cmass : ℝ) (H : ℕ)
    (hL : 1≤L) (hPrecision : Cmass+A≤C0*(H:ℝ)) :
    ((L^C0/(2*Real.pi))^H)⁻¹ * L^Cmass ≤
      (2*Real.pi)^H * L^(-A) := by
  have hLp : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hL
  have hExp : Cmass-C0*(H:ℝ) ≤ -A := by linarith
  have hPower : (L^C0)^H=L^(C0*(H:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hLp.le]
  have hEq : ((L^C0/(2*Real.pi))^H)⁻¹*L^Cmass =
      (2*Real.pi)^H*L^(Cmass-C0*(H:ℝ)) := by
    rw [div_pow, hPower, inv_div, Real.rpow_sub hLp]
    field_simp
  calc
    _ = (2*Real.pi)^H*L^(Cmass-C0*(H:ℝ)) := hEq
    _ ≤ (2*Real.pi)^H*L^(-A) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL hExp)
        (pow_nonneg (by positivity) _)

/-- The source moment H can be selected once for each requested
power saving A and polynomial mass exponent Cmass whenever C0>0.
This is a legal PRE-L choice; no asserted uniform bound on the actual
Schwartz moment M_H is needed (M_H is independent of L). -/
theorem parity_original_true_mellin_moment_order_exists434
    (A Cmass C0 : ℝ) (hC0 : 0<C0) :
    ∃ H : ℕ, A+Cmass ≤ C0*(H:ℝ) := by
  obtain ⟨H,hH⟩ := exists_nat_gt ((A+Cmass)/C0)
  refine ⟨H,?_⟩
  have hLe : (A+Cmass)/C0≤(H:ℝ) := le_of_lt hH
  have hh : A+Cmass≤(H:ℝ)*C0 :=
    (div_le_iff₀ hC0).mp hLe
  simpa only [mul_comm] using hh

/-- The complete numeric Ψ-Mellin Schwartz H-moment and TRUE
all-20-slot W1(P,u) τ(u+2) Q Fourier polynomial are absorbed as
ONE fixed constant 20*(2π)^H*M_H times exp(L)L^-A. Valid for
any nonnegative moment, independently of the original L and Q
labels; analytic proof of the actual integral bound is separate. -/
theorem parity_original_true_mellin_tail_source_mass_absorption434
    (L C0 A Cmass M : ℝ) (H : ℕ)
    (hL : 1≤L) (hM : 0≤M)
    (hPrec : Cmass+A≤C0*(H:ℝ)) :
    (((L^C0/(2*Real.pi))^H)⁻¹ * M) *
      (20*Real.exp L*L^Cmass) ≤
    (20*(2*Real.pi)^H*M) * Real.exp L * L^(-A) := by
  have hBase := parity_original_true_mellin_tail_power_absorption434
    L C0 A Cmass H hL hPrec
  have hFactor : 0≤20*Real.exp L*M := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hBase hFactor
  calc
    _ = (20*Real.exp L*M)*(((L^C0/(2*Real.pi))^H)⁻¹*L^Cmass) := by ring
    _ ≤ (20*Real.exp L*M)*((2*Real.pi)^H*L^(-A)) := hScaled
    _ = (20*(2*Real.pi)^H*M)*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalPsiFilteredFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- Exact ORIGINAL physical B' post-Cauchy finite signed sum is
unchanged by inserting the actual C∞ dyadic ψ partition and
restricting its j-outer to the true globally attained physical
Z heights and immediately preceding half-scales. This is an
IDENTITY, not a norm inequality or hard ψ mask. Original actual
physical n,m' are retained once, and all odd e including P-group
factors remain permitted. The only weight-support premise says
nonzero W entails the SOURCE η_eη_n support; source z-range is
separate and must be discharged from corrected cap-free geometry.
Both are explicit, so no conditional TypeII claim is smuggled. -/
theorem parity_original_true_physical_full_smooth_dyadic_source_neighbor_reindex434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (N : ℕ)
    (W : (ℕ×ℕ) → ℂ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K)
    (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    (hJ : J ⊆ parityOriginalHistoricalFullNEnvelope434 V)
    (hW : ∀q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k, W q≠0 →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0)
    (hZrange : ∀q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k, W q≠0 →
      (2:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤(2:ℝ)^(N+1)) :
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hL band slot δ Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    (∑q∈S,W q) =
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*W q := by
  classical
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hL band slot δ Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let F : ℕ → ℂ := fun j =>
    ∑q∈S,parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*W q
  have hF : (∑q∈S,W q) = ∑j∈Finset.range (N+1),F j := by
    exact parity_original_true_physical_full_smooth_dyadic_reindex434
      d L band slot δ Y e m K J k N W hZrange
  have hNo (j : ℕ) (hj : j∈Finset.range (N+1))
      (hnot : (2:ℕ)^j∉ZSmooth) : F j=0 := by
    dsimp [F]
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hw0 : W q=0
    · simp only [hw0,mul_zero]
    have hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0 :=
      hW q hq hw0
    have hz : 0<parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 := by
      have hr := (hZrange q hq hw0).1
      have hh : (0:ℝ)<(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) := by linarith
      exact_mod_cast hh
    let Z : ℕ := parityOriginalHistoricalActualZDyadicScale434
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2)
    have hq0 := Finset.mem_filter.mp hq
    have hprod := Finset.mem_product.mp hq0.1
    have hJfull : q.2∈parityOriginalHistoricalFullNEnvelope434 V :=
      hJ hprod.2
    have hprodFull : q∈(parityOriginalHistoricalKPrimeFibre434 e m K k).product
        (parityOriginalHistoricalFullNEnvelope434 V) :=
      Finset.mem_product.mpr ⟨hprod.1,hJfull⟩
    have hqZ : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k Z := by
      apply Finset.mem_filter.mpr
      refine ⟨hprodFull,⟨hq0.2,hz,rfl⟩⟩
    have hpsi0 : parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)=0 := by
      by_contra hnon
      have hmem := parity_original_full_odd_physical_smooth_psi_full_neighbor_support434
        d L E V hL band slot δ Y K e m k Z j q he hm hk hqZ hw hnon
      exact hnot hmem
    rw [hpsi0,zero_mul]
  let T : Finset ℕ := (Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth)
  have hSubset : T⊆Finset.range (N+1) := Finset.filter_subset _ _
  have hFilter : (∑j∈Finset.range (N+1),F j) = ∑j∈T,F j := by
    apply (Finset.sum_subset hSubset ?_).symm
    intro j hj hnot
    have hNoZ : (2:ℕ)^j∉ZSmooth := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨hj,hh⟩)
    exact hNo j hj hNoZ
  dsimp only
  exact hF.trans hFilter
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalPsiActualWeight -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6300000

/-- The original η_e,L(e/E)η_n(n/V) weighted full-odd B509 physical
Cauchy pair at fixed e,m,k has an exact smooth-ψ source partition
with NO external weight-support or physical z-range assumptions.
The original full n envelope, cap-free Ybox=ceil(6UV), actual H0,
α,epsilon and natural u/e remain literal. The sole dyadic capacity
hypothesis is the elementary 2^(N+1) upper bound for the REAL
corrected source z-height; its explicit N is constructed next. -/
theorem parity_original_full_odd_actual_weight_smooth_psi_neighbor_reindex434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V) (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (e m : ℕ) (k : ℤ) (N : ℕ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    (hCapacity : 48*Cbox*Real.exp L*L^(K0+88)≤(2:ℝ)^(N+1)) :
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot δ Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let W : ℕ×ℕ → ℂ := fun q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V (by linarith : 8≤L) e q.2:ℝ):ℂ)*
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1
    (∑q∈S,W q) =
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*W q := by
  classical
  have hLw : 8≤L := by linarith
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let W : ℕ×ℕ → ℂ := fun q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y e q.2 m q.1
  have hW (q : ℕ×ℕ) (hq : q∈S) (hNZ : W q≠0) :
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 := by
    intro hzero
    apply hNZ
    dsimp [W]
    simp [hzero]
  have hLone : 1≤L := by linarith
  have hKone : 1≤L^K0 := Real.one_le_rpow hLone hK0
  have hExpLarge : (32:ℝ)≤Real.exp L := by
    have hh := Real.add_one_le_exp L
    linarith
  have hZrange (q : ℕ×ℕ) (hq : q∈S) (hNZ : W q≠0) :
      (2:ℝ)≤(parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ) ∧
      (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)≤(2:ℝ)^(N+1) := by
    have hw := hW q hq hNZ
    have hdata := Finset.mem_filter.mp hq
    have hprod := Finset.mem_product.mp hdata.1
    have hmpK := (Finset.mem_erase.mp (Finset.mem_filter.mp hprod.1).1).2
    have hneq : m≠q.1 :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp hprod.1).1).1.symm
    have hOdd : Odd e := (Finset.mem_filter.mp he).2
    have hPhys := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m q.1 q.2 hOdd hneq hdata.2
    dsimp only at hPhys
    let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
    let Z : ℕ := parityOriginalHistoricalActualZDyadicScale434 z
    have hzpos : 0<z := hPhys.2.1
    have hqZ : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z := by
      apply Finset.mem_filter.mpr
      exact ⟨hdata.1,⟨hdata.2,hzpos,rfl⟩⟩
    have hzBound := parity_original_historical_ungated_full_box_smoothed_actual_Z_window434
      d L U V E K0 Cbox hLw band slot δ K J e m k Z
      hOdd hU hV (by linarith : 0<Cbox) hUV hUVhi hE hm hDyad q hqZ hw
    have hdy := parity_original_historical_actual_z_in_own_dyad434 z hzpos
    have hzRealLow : (Z:ℝ)≤(z:ℝ) := by exact_mod_cast hdy.2.1
    have hzRealHigh : (z:ℝ)<2*(Z:ℝ) := by exact_mod_cast hdy.2.2
    have hLBound : (2:ℝ)≤(Real.exp L/16)*L^K0 := by
      have hExp16 : (2:ℝ)≤Real.exp L/16 := by linarith
      have hePos : 0≤Real.exp L/16 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hKone hePos]
    have hTop : (z:ℝ)≤(2:ℝ)^(N+1) := by
      calc
        _ ≤ 2*(Z:ℝ) := hzRealHigh.le
        _ ≤ 48*Cbox*Real.exp L*L^(K0+88) := by
          nlinarith [hzBound.2]
        _ ≤ (2:ℝ)^(N+1) := hCapacity
    exact ⟨by linarith [hLBound,hzBound.1,hzRealLow],hTop⟩
  have hF := parity_original_true_physical_full_smooth_dyadic_source_neighbor_reindex434
    d L E V hLw band slot δ Y e m K J k N W he hm hk
    (Finset.Subset.rfl) hW hZrange
  dsimp only at hF ⊢
  exact hF
end Green64Analytic.Parity

end

end

/-! ## TruePsiBufferWitness -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The true ORIGINAL C∞ buffer already furnished by the fixed
Parity rank cutoff is in fact ONE throughout [0,log 4], the actual
support required for the smooth dyadic ψ(z/Z) with 1<z/Z<4.
The legacy [0,log 2] witness is insufficient for the neighboring
half-dyad. This proof uses the SAME source η buffer and derivative
budgets, not an artificially modified cutoff or a new assumption. -/
theorem parity_original_true_smooth_psi_log4_buffer_exists434 :
    ∃ A : ℝ, 64≤A ∧ ∃ buf : ℝ → ℂ,
      ContDiff ℝ ∞ buf ∧
      (∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A) ∧
      (∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1) ∧
      (∀t:ℝ,‖buf t‖≤1) ∧
      ∃ K : ℕ → ℝ, (∀ j,0≤K j) ∧
        ∀ L : ℝ, sourceLogDerivativeBudget 0 K L buf := by
  obtain ⟨A,hA,eta,hSmooth,hSupp,hOne,hNorm,hInv,hSuppInv,K,hK,hBudgets⟩ :=
    parity_fixed_rank_cutoff_pair_budget434
  let buf : ℝ → ℂ := fun t => eta (Real.exp t)
  have hApos : 0<A := by linarith
  have hLogInv : Real.log (1/A) = -Real.log A := by
    rw [one_div,Real.log_inv]
  have hSmoothBuf : ContDiff ℝ ∞ buf := hSmooth.comp Real.contDiff_exp
  have hSupportBuf : ∀t:ℝ, buf t≠0 → -Real.log A≤t ∧ t≤Real.log A := by
    intro t ht
    have hh := hSupp (Real.exp t) ht
    have hl : Real.log (1/A)≤Real.log (Real.exp t) :=
      Real.log_le_log (one_div_pos.mpr hApos) hh.1
    have hu : Real.log (Real.exp t)≤Real.log A :=
      Real.log_le_log (Real.exp_pos t) hh.2
    simpa only [hLogInv,Real.log_exp] using And.intro hl hu
  have hOneBuf : ∀ t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1 := by
    intro t ht
    have hExpLo : (1:ℝ)≤Real.exp t := by
      calc
        _ = Real.exp 0 := by simp
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ht.1
    have hExpHi : Real.exp t≤(4:ℝ) := by
      have hh := Real.exp_le_exp.mpr ht.2
      simpa only [Real.exp_log (by norm_num : (0:ℝ)<4)] using hh
    have hFour : (4:ℝ)≤64*Real.exp 2+1 := by
      have hh : (1:ℝ)≤Real.exp 2 := by
        have hh' := Real.exp_le_exp.mpr (show (0:ℝ)≤2 by norm_num)
        simpa using hh'
      nlinarith
    exact hOne (Real.exp t) ⟨by linarith [hExpLo],hExpHi.trans hFour⟩
  have hNormBuf : ∀t:ℝ,‖buf t‖≤1 := fun t => hNorm (Real.exp t)
  refine ⟨A,hA,buf,hSmoothBuf,hSupportBuf,hOneBuf,hNormBuf,K,hK,?_⟩
  intro L
  exact (hBudgets L).1

/-- Same physical 3D Euclidean cube as the old original buffer,
now with the complete smooth ψ support z/Z<4. All fixed objects
are chosen independently of source precision, true B509 n,e,
k, Z, character χ and original Q frequencies. -/
theorem parity_original_true_smooth_psi_uniform_fourier_buffer_exists434 :
    ∃ A : ℝ,64≤A ∧ ∃ R : ℝ,1≤R ∧
      ∃ buf : ℝ → ℂ,
        ∃ (hSmooth : ContDiff ℝ ∞ buf)
          (hSupport : ∀t:ℝ,buf t≠0 →
            -Real.log A≤t ∧ t≤Real.log A),
          (∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1) ∧
          (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,
            ‖t‖≤R) := by
  obtain ⟨A,hA,buf,hSmooth,hSupp,hOne,hNorm,K,hK,hBudget⟩ :=
    parity_original_true_smooth_psi_log4_buffer_exists434
  obtain ⟨R,hR,hCube⟩ :=
    parity_original_historical_euclidean_fixed_log_cube_radius_exists434 A
  exact ⟨A,hA,R,hR,buf,hSmooth,hSupp,hOne,hCube⟩
end Green64Analytic.Parity

end

end

/-! ## TruePsiSourcePullback -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- A TRUE original Parity smooth ψ(z/Z) supported in (1,4) requires
log(z/Z) in [0,log4], not the narrower historical [0,log2] for
sharp binary Z. The real 3D source buffer can be chosen equal to
one on all of these coordinates. -/
theorem parity_original_true_psi_log_triple_in_buffer434
    (U Z : ℝ) (m mp z : ℕ) (hU : 0<U) (hZ : 0<Z)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hPsi : parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/Z) ≠ 0) :
    (Real.log ((m:ℝ)/U) ∈ Set.Icc (0:ℝ) (Real.log 4)) ∧
    (Real.log ((mp:ℝ)/U) ∈ Set.Icc (0:ℝ) (Real.log 4)) ∧
    (Real.log ((z:ℝ)/Z) ∈ Set.Icc (0:ℝ) (Real.log 4)) := by
  have hm := parity_original_historical_log_dyadic_coordinate_Icc434
    U (m:ℝ) hU hmLo hmHi
  have hmp := parity_original_historical_log_dyadic_coordinate_Icc434
    U (mp:ℝ) hU hmpLo hmpHi
  have hLog24 : Real.log 2≤Real.log 4 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hz := parity_original_historical_dyadic_psi_compact_positive_support434
    ((z:ℝ)/Z) hPsi
  have hzLog : 0≤Real.log ((z:ℝ)/Z) ∧
      Real.log ((z:ℝ)/Z)≤Real.log 4 := by
    refine ⟨Real.log_nonneg hz.1.le,?_⟩
    exact Real.log_le_log (lt_trans zero_lt_one hz.1) hz.2.le
  exact ⟨⟨hm.1,hm.2.trans hLog24⟩,
    ⟨hmp.1,hmp.2.trans hLog24⟩,⟨hzLog.1,hzLog.2⟩⟩

/-- **TRUE ORIGINAL SOURCE 3D ψ-SUPPORT EQUALITY**. For every
physical Q/P/B509 ungated odd-e, n, m,m',z event and every
smooth dyadic Z with ψ(z/Z)≠0, the source-constructed 3D
Schwartz kernel f at the exact physical log triple equals the
original actual η_e(e/E)η_n(n/V). The original h=-2 inverse
(4.14) and the true source k=(m'-m)/e are retained. This closes
the fatal missing half-dyad buffer: the old statement requiring
z∈[Z,2Z] alone cannot justify ψ support (1,4). -/
theorem parity_original_ungated_true_psi_dyadic_eta_physical_point_3d434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m mp n : ℕ) (he : Odd e) (hneq : m≠mp)
    (hValid : parityOriginalHistoricalUngatedPhysicalValidN434
      d L band slot δ Y e m mp n)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hk : parityOriginalHistoricalOffdiagK434 e m mp=k)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hmpLo : U≤(mp:ℝ)) (hmpHi : (mp:ℝ)≤2*U)
    (hPsi : parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℝ)/Z)≠0)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1) :
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e n:ℝ):ℂ) =
    parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport
      (parityOriginalHistoricalRealLogTriple434 U Z m mp
        (parityOriginalHistoricalCanonicalZ434 e m mp n)) := by
  let etaE := parityOriginalHistoricalDyadicEtaEAtLComplex434 L hL
  let etaN := parityOriginalHistoricalActualEtaN434
  have hSource := parity_original_historical_ungated_source_eta_equals_euclidean_3d434
    d L band slot δ Y e m mp n he hneq hValid
    U E V Z hU hE hV hZ buf etaE etaN a b hSmooth
    (parity_original_historical_dyadic_eta_e_L_complex_smooth434 L hL)
    parity_original_historical_actual_eta_n_smooth434 hSupport
  rw [hk] at hSource
  have hLogs := parity_original_true_psi_log_triple_in_buffer434
    U Z m mp (parityOriginalHistoricalCanonicalZ434 e m mp n)
    hU hZ hmLo hmHi hmpLo hmpHi hPsi
  have hb0 := hOne4 (Real.log ((m:ℝ)/U)) hLogs.1
  have hb1 := hOne4 (Real.log ((mp:ℝ)/U)) hLogs.2.1
  have hb2 := hOne4
    (Real.log ((parityOriginalHistoricalCanonicalZ434 e m mp n:ℕ)/Z)) hLogs.2.2
  rw [hb0,hb1,hb2] at hSource
  have hWeight := parity_original_historical_dyadic_eta_weight_is_complex_product434
    L E V hL e n
  simp only [one_mul] at hSource
  exact hWeight.trans hSource.symm
end Green64Analytic.Parity

end

end

/-! ## TruePsiFinite3DFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- TRUE original SOURCE smooth-ψ Parity(4.14) full R³ Fourier
identity for an arbitrary finite family of physical h=-2 B509
prime-slot/rough-cofactor signed weights. No artificial dyadic
indicator z∈[Z,2Z] is imposed: the original ψ(z/Z) lives in (1,4),
and the actual C∞ log buffer equals one through log4. The identity
keeps repeated natural e,m',n,z source multiplicities; terms with
zero ψ vanish on BOTH sides without an impossible range hypothesis.
The external original Q-allocation Fourier frequencies do not enter
this identity and can be summed subsequently. -/
theorem parity_original_ungated_true_psi_physical_finite_3d_fourier434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) (mp n : ι → ℕ)
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (he : Odd e)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hPhysical : ∀i∈S,
      m≠mp i ∧
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m (mp i) (n i) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp i)=k ∧
      U≤(mp i:ℝ) ∧ (mp i:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hOne4 : ∀x∈Set.Icc (0:ℝ) (Real.log 4),buf x=1) :
    let t : ι → EuclideanSpace ℝ (Fin 3) :=
      parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport
    let Wpsi : ι → ℂ := fun i =>
      W i * parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)/Z)
    (∑i∈S,Wpsi i *
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) =
      ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginal3DPhysicalFiniteTwistedSource434 S Wpsi t f ζ := by
  classical
  dsimp only
  let t : ι → EuclideanSpace ℝ (Fin 3) :=
    parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hSmooth hSupport
  let Wpsi : ι → ℂ := fun i => W i *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)/Z)
  have hTerm (i : ι) (hi : i∈S) :
      Wpsi i * ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ) =
      Wpsi i * f (t i) := by
    by_cases hψ : parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)/Z)=0
    · simp [Wpsi,hψ]
    · obtain ⟨hne,hvalid,hk,hmpLo,hmpHi⟩ := hPhysical i hi
      have hh := parity_original_ungated_true_psi_dyadic_eta_physical_point_3d434
        d L hL band slot δ Y e m (mp i) (n i) he hne hvalid
        U E V Z hU hE hV hZ k hk hmLo hmHi hmpLo hmpHi hψ
        buf a b hSmooth hSupport hOne4
      change ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ) =
        f (t i) at hh
      rw [hh]
  calc
    _ = parityOriginal3DPhysicalFiniteSignal434 S Wpsi t f := by
      unfold parityOriginal3DPhysicalFiniteSignal434
      apply Finset.sum_congr rfl
      intro i hi
      exact hTerm i hi
    _ = ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginal3DPhysicalFiniteTwistedSource434 S Wpsi t f ζ :=
      parity_original_3d_physical_finite_source_fourier_fubini434 S Wpsi t f

/-- The literal ORIGINAL smooth ψ(z/Z) signed physical source and
its common 3D Fourier BALL differ by the paid true H-th Schwartz
moment times the exact sum of ABSOLUTE physical signed coefficients.
This is an application to the ACTUAL η_eη_n source, not merely an
abstract truncation of an arbitrary artificially truncated cell.
The original ψ-neighbor half-dyad is fully included; no norm
monotonicity of signed subsets or extra count of source events. -/
theorem parity_original_ungated_true_psi_physical_finite_3d_ball_error434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) (mp n : ι → ℕ)
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (he : Odd e)
    (U E V Z : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (k : ℤ) (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hPhysical : ∀i∈S,
      m≠mp i ∧
      parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m (mp i) (n i) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp i)=k ∧
      U≤(mp i:ℝ) ∧ (mp i:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hOne4 : ∀x∈Set.Icc (0:ℝ) (Real.log 4),buf x=1)
    (H : ℕ) (T : ℝ) (hT : 0<T) :
    let t : ι → EuclideanSpace ℝ (Fin 3) :=
      parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport
    let Wpsi : ι → ℂ := fun i =>
      W i * parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)/Z)
    ‖(∑i∈S,Wpsi i *
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) -
      (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
        parityOriginal3DPhysicalFiniteTwistedSource434 S Wpsi t f ζ)‖ ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434 S Wpsi *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  classical
  dsimp only
  let t : ι → EuclideanSpace ℝ (Fin 3) :=
    parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hSmooth hSupport
  let Wpsi : ι → ℂ := fun i => W i *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m (mp i) (n i):ℝ)/Z)
  have hSource := parity_original_ungated_true_psi_physical_finite_3d_fourier434
    S W mp n d L hL band slot δ Y e m he
    U E V Z hU hE hV hZ k hmLo hmHi hPhysical
    buf a b hSmooth hSupport hOne4
  dsimp only at hSource
  have hSourceFinite :
      (∑i∈S,Wpsi i *
        ((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e (n i):ℝ):ℂ)) =
      parityOriginal3DPhysicalFiniteSignal434 S Wpsi t f := by
    calc
      _ = ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginal3DPhysicalFiniteTwistedSource434 S Wpsi t f ζ := hSource
      _ = _ := (parity_original_3d_physical_finite_source_fourier_fubini434 S Wpsi t f).symm
  rw [hSourceFinite]
  exact parity_original_historical_actual_dyadic_finite_3d_truncation434
    S Wpsi t H L hL U E V Z k buf a b hSmooth hSupport T hT
end Green64Analytic.Parity

end

end

/-! ## TruePsiPhysicalCellFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Full actual original h=-2, r20 B509 PHYSICAL smooth ψ
contribution at one e,m,k,Z, with all genuine natural m',n
source events, Q/P prime-slot/rough fine alpha, W1, ε=1/E,
signed group and true moving η_e(e/E)η_n(n/V). The true ψ is
smooth and has support (1,4), not the sharp Z-binary indicator. -/
def parityOriginalActualTruePsiPhysicalCell434
    (d : ℕ) (L E V Z : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : ℂ :=
  ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z) *
    (((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ))

/-- The literal same physical source coefficient moved inside ONE
common 3D Fourier BALL, with a source-fixed log4 buffer. This is
the exact Fourier truncation candidate needed by full original
post-Cauchy SOURCE reconstruction, not the canonical binary Z
Fourier cell from the old incomplete half-neighbor interface. -/
def parityOriginalActualTruePsiPhysicalCellFourierBall434
    (d : ℕ) (L U E V Z : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (buf : ℝ → ℂ) (a b T : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let W : (ℕ×ℕ) → ℂ := fun q =>
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
  let t := parityOriginalHistoricalPhysicalFourierEventTriple434
    U Z e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hSmooth hSupport
  ∫ ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ζ

/-- The true original full-odd e,n,m,m' B509 physical smooth ψ
source contribution is approximated by the correctly buffered
3D Fourier BALL, with EXACT error bounded by actual positive
absolute physical source mass times finite source Schwartz moment.
No subset norm monotonicity and no incorrect z≤2Z hypothesis;
full neighboring smooth dyad z/Z up to 4 is LEGAL. -/
theorem parity_original_true_psi_ungated_physical_cell_ball_error434
    (d : ℕ) (L U E V Z : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (hm : m∈K) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x≠0 → a≤x ∧ x≤b)
    (hOne4 : ∀x∈Set.Icc (0:ℝ) (Real.log 4),buf x=1)
    (H : ℕ) (T : ℝ) (hT : 0<T) :
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let W : (ℕ×ℕ) → ℂ := fun q =>
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport
    ‖parityOriginalActualTruePsiPhysicalCell434
        d L E V Z hL band slot δ ξ rho alpha signed Y e m K J k -
      parityOriginalActualTruePsiPhysicalCellFourierBall434
        d L U E V Z hL band slot δ ξ rho alpha signed Y e m K J k
        buf a b T hSmooth hSupport‖ ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  classical
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let W : (ℕ×ℕ) → ℂ := fun q =>
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
  let mp : (ℕ×ℕ)→ℕ := fun q=>q.1
  let n : (ℕ×ℕ)→ℕ := fun q=>q.2
  have hPhysical : ∀q∈S,
      m≠mp q ∧ parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m (mp q) (n q) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp q)=k ∧
      U≤(mp q:ℝ) ∧ (mp q:ℝ)≤2*U := by
    intro q hq
    obtain ⟨hprod,hvalid⟩ := Finset.mem_filter.mp hq
    obtain ⟨hmp,hJ⟩ := Finset.mem_product.mp hprod
    obtain ⟨hmpK,hk⟩ := Finset.mem_filter.mp hmp
    obtain ⟨hne,hmK⟩ := Finset.mem_erase.mp hmpK
    obtain ⟨hl,hu⟩ := hDyad q.1 hmK
    exact ⟨hne.symm,hvalid,hk,hl,hu⟩
  let t := parityOriginalHistoricalPhysicalFourierEventTriple434
    U Z e m mp n
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hSmooth hSupport
  have hMain := parity_original_ungated_true_psi_physical_finite_3d_ball_error434
    S (fun q => parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1)
    mp n d L hL band slot δ Y e m he U E V Z
    hU hE hV hZ k (hDyad m hm).1 (hDyad m hm).2 hPhysical
    buf a b hSmooth hSupport hOne4 H T hT
  dsimp only at hMain ⊢
  simpa only [parityOriginalActualTruePsiPhysicalCell434,
    parityOriginalActualTruePsiPhysicalCellFourierBall434,W,S,
    mp,n,t,f,mul_assoc] using hMain
end Green64Analytic.Parity

end

end

/-! ## TruePsiTwoScaleOverlap -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A single original natural physical z>0 contributes to AT MOST
TWO smooth ψ(z/Z) Fourier dyad powers Z=2^j: the canonical
2^floor(log2 z) scale and its immediate half-dyad. This is a
cardinality fact about truly nonzero source smooth weights, not a
sharp-dyad replacement or an unwarranted signed-norm inequality. -/
theorem parity_original_true_psi_nonzero_height_card_at_most_two434
    (z : ℕ) (ZS : Finset ℕ)
    (hPower : ∀Z∈ZS, ∃j:ℕ,Z=(2:ℕ)^j) :
    (ZS.filter (fun (Z : ℕ) =>
      parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))≠0)).card≤2 := by
  classical
  let C : ℕ := parityOriginalHistoricalActualZDyadicScale434 z
  let S : Finset ℕ := ZS.filter (fun Z =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))≠0)
  have hsub : S⊆({C}:Finset ℕ) ∪ ({C/2}:Finset ℕ) := by
    intro Z hZ
    have hZin := (Finset.mem_filter.mp hZ).1
    have hψ := (Finset.mem_filter.mp hZ).2
    obtain ⟨j,hEq⟩ := hPower Z hZin
    subst Z
    have hh := parity_original_actual_smooth_psi_dyadic_nonzero_neighbor434
      ({z}:Finset ℕ) z j (by simp) (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hψ)
    simpa only [C,parityOriginalActualSmoothPsiNeighborZEnvelope434,
      Finset.image_singleton] using hh
  change S.card≤2
  calc
    _ ≤ (({C}:Finset ℕ) ∪ ({C/2}:Finset ℕ)).card := Finset.card_le_card hsub
    _ ≤ ({C}:Finset ℕ).card+({C/2}:Finset ℕ).card := Finset.card_union_le _ _
    _ = 2 := by simp

/-- Exact positive Fourier-dyad overlap budget:
Σ_(attained smooth Z) ‖ψ(z/Z)‖ ≤ 2 for ANY original positive
physical z and power-of-two smooth height set. The finite mass of
all original z,e,m,n events is not multiplied by the total number
of Z dyads; each physical event costs at most TWO. -/
theorem parity_original_true_psi_height_norm_mass_le_two434
    (z : ℕ) (ZS : Finset ℕ)
    (hPower : ∀Z∈ZS, ∃j:ℕ,Z=(2:ℕ)^j) :
    (∑Z∈ZS,
      ‖parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))‖) ≤ 2 := by
  classical
  let S : Finset ℕ := ZS.filter (fun Z =>
    parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))≠0)
  have hCard : S.card≤2 := by
    exact parity_original_true_psi_nonzero_height_card_at_most_two434 z ZS hPower
  have hSum :
      (∑Z∈ZS,‖parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))‖) =
      ∑Z∈S,‖parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))‖ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Z hZ
    by_cases hψ : parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))≠0
    · simp [hψ]
    · have hh : parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))=0 := by
        exact not_ne_iff.mp hψ
      simp [hψ,hh]
  calc
    _ = ∑Z∈S,‖parityOriginalHistoricalDyadicSmoothPsi434 ((z:ℝ)/(Z:ℝ))‖ := hSum
    _ ≤ ∑Z∈S,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro Z hZ
      exact parity_original_historical_explicit_smooth_dyadic_psi_norm_le_one434 _
    _ = (S.card:ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast hCard
end Green64Analytic.Parity

end

end

/-! ## TruePsiAbsoluteFibreMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- The TRUE original fixed smooth ψ amplitude, not an abstract
partition, charges at most two unit weights to each original natural
physical z when summing over any power-of-two source Z carrier.
No complex-subsums monotonicity is claimed: BOTH sides are positive
absolute coefficient mass. -/
theorem parity_original_true_psi_finite_physical_weighted_mass_le_two434
    {ι : Type*} (S : Finset ι) (W : ι → ℂ) (z : ι → ℕ)
    (ZS : Finset ℕ) (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j) :
    (∑Z∈ZS,∑i∈S,
      ‖W i*parityOriginalHistoricalDyadicSmoothPsi434
        ((z i:ℝ)/(Z:ℝ))‖) ≤ 2*(∑i∈S,‖W i‖) := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑i∈S,∑Z∈ZS,
      ‖W i*parityOriginalHistoricalDyadicSmoothPsi434 ((z i:ℝ)/(Z:ℝ))‖) =
      ∑i∈S, ‖W i‖*(∑Z∈ZS,
        ‖parityOriginalHistoricalDyadicSmoothPsi434 ((z i:ℝ)/(Z:ℝ))‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [norm_mul]
    _ ≤ ∑i∈S,‖W i‖*(2:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (parity_original_true_psi_height_norm_mass_le_two434 (z i) ZS hPower)
        (norm_nonneg _)
    _ = 2*(∑i∈S,‖W i‖) := by rw [Finset.mul_sum]; ring

/-- The real ORIGINAL source B509/Parity(4.10) ungated H0,
W1, ε=1/E, and fine-alpha offdiagonal coefficients at one
physical (e,m,k) have at most TWICE their unweighted absolute
source coefficient mass across every genuine smooth ψ neighbor
Z. The physical m',n carrier is exactly the corrected all-odd one.
This is a direct source-specialized application and not a bound
on the unrestricted signed Parity(4.17) correlation. -/
theorem parity_original_true_psi_actual_full_odd_emk_mass_le_two434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (ZS : Finset ℕ)
    (hPower : ∀Z∈ZS,∃j : ℕ,Z=(2:ℕ)^j) :
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
    let W : (ℕ×ℕ) → ℂ := fun q =>
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑Z∈ZS,
      parityOriginal3DPhysicalFiniteCoefficientMass434 S
        (fun q => W q*parityOriginalHistoricalDyadicSmoothPsi434
          ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ)))) ≤
      2*parityOriginal3DPhysicalFiniteCoefficientMass434 S W := by
  classical
  dsimp only
  unfold parityOriginal3DPhysicalFiniteCoefficientMass434
  exact parity_original_true_psi_finite_physical_weighted_mass_le_two434
    (parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k)
    (fun q => parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1)
    (fun q => parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) ZS hPower
end Green64Analytic.Parity

end

end

/-! ## TruePsiEtaFilteredCell -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Actual full-odd h=-2 B509 physical carrier, restricted ONLY
where the original NONNEGATIVE smooth η_e(e/E)η_n(n/V) weight is
nonzero. This is the correct filter BEFORE truncating 3D Fourier:
zero-η events vanish in the complete source but can leave a
nonzero truncated Fourier ghost, so deleting them AFTER Fourier
is invalid. -/
def parityOriginalActualTruePsiEtaActivePhysicalEvents434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : Finset (ℕ×ℕ) :=
  (parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k).filter
      (fun q => parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2  ≠  0)

/-- Exact original source identity that removes ONLY zero actual
ηeηn terms BEFORE applying 3D Fourier inversion. All original
signed h=-2 Q/P/B509/H0 weights and the actual smooth ψ(z/Z)
remain unchanged. This filter is legal because source η=0 kills
the corresponding full physical contribution algebraically. -/
theorem parity_original_actual_true_psi_eta_active_source_exact434
    (d : ℕ) (L E V Z : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) :
    parityOriginalActualTruePsiPhysicalCell434
      d L E V Z hL band slot δ ξ rho alpha signed Y e m K J k =
    ∑q∈parityOriginalActualTruePsiEtaActivePhysicalEvents434
        d L E V hL band slot δ Y e m K J k,
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z) *
      (((parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2:ℝ):ℂ)) := by
  classical
  unfold parityOriginalActualTruePsiPhysicalCell434
    parityOriginalActualTruePsiEtaActivePhysicalEvents434
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hη : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2  ≠  0
  · rw [if_pos hη]
  · have hz : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 = 0 :=
      not_ne_iff.mp hη
    rw [if_neg hη]
    simp [hz]

/-- The TRUE SOURCE restricted-eta C∞ smooth ψ 3D Fourier BALL
at one physical e,m,k,Z. In contrast to the unrestricted historical
B633 Fourier ball, this object contains NO zero-eta ghost events;
its full source integral is EXACTLY original source by previous
native identity. It is a mathematically separate Fourier object,
not yet identified with the unrestricted Parity(4.17) correlation. -/
def parityOriginalActualTruePsiEtaActiveFourierBall434
    (d : ℕ) (L U E V Z : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (buf : ℝ → ℂ) (a b T : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t ≠ 0 → a≤t ∧ t≤b) : ℂ :=
  let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
    d L E V hL band slot δ Y e m K J k
  let W : (ℕ×ℕ) → ℂ := fun q =>
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
  let t := parityOriginalHistoricalPhysicalFourierEventTriple434
    U Z e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2)
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hSmooth hSupport
  ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    parityOriginal3DPhysicalFiniteTwistedSource434 S W t f ζ

/-- Direct original source smoothed ψ physical cell minus its
**eta-active-only** low-frequency 3D Fourier BALL has paid error
bounded by EXACT eta-active positive coefficient mass M_H/T^H.
This avoids uncontrolled Fourier ghosts from e,n where original
η=0, preserves both real neighbor dyads z/Z<4, and retains full
natural source multiplicities and literal H0/W1/epsilon weights.
An honest separate bridge is required before using the Parity(4.17)
UNRESTRICTED Fourier-ball estimate on this restricted ball. -/
theorem parity_original_actual_true_psi_eta_active_cell_ball_error434
    (d : ℕ) (L U E V Z : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (alpha : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (hU : 0<U) (hE : 0<E) (hV : 0<V) (hZ : 0<Z)
    (hm : m∈K) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀x:ℝ,buf x ≠ 0 → a≤x ∧ x≤b)
    (hOne4 : ∀x∈Set.Icc (0:ℝ) (Real.log 4),buf x=1)
    (H : ℕ) (T : ℝ) (hT : 0<T) :
    let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
      d L E V hL band slot δ Y e m K J k
    let W : (ℕ×ℕ) → ℂ := fun q =>
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
    let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
      L hL U E V Z k buf a b hSmooth hSupport
    ‖parityOriginalActualTruePsiPhysicalCell434
        d L E V Z hL band slot δ ξ rho alpha signed Y e m K J k -
      parityOriginalActualTruePsiEtaActiveFourierBall434
        d L U E V Z hL band slot δ ξ rho alpha signed Y e m K J k
        buf a b T hSmooth hSupport‖ ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434 S W *
        (parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) := by
  classical
  let S := parityOriginalActualTruePsiEtaActivePhysicalEvents434
    d L E V hL band slot δ Y e m K J k
  let W : (ℕ×ℕ) → ℂ := fun q =>
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1 *
    parityOriginalHistoricalDyadicSmoothPsi434
      ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/Z)
  let mp : (ℕ×ℕ)→ℕ := fun q=>q.1
  let n : (ℕ×ℕ)→ℕ := fun q=>q.2
  have hPhysical : ∀q∈S,
      m≠mp q ∧ parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m (mp q) (n q) ∧
      parityOriginalHistoricalOffdiagK434 e m (mp q)=k ∧
      U≤(mp q:ℝ) ∧ (mp q:ℝ)≤2*U := by
    intro q hq
    obtain ⟨hBase,hη⟩ := Finset.mem_filter.mp hq
    obtain ⟨hprod,hvalid⟩ := Finset.mem_filter.mp hBase
    obtain ⟨hmp,hJ⟩ := Finset.mem_product.mp hprod
    obtain ⟨hmpK,hk⟩ := Finset.mem_filter.mp hmp
    obtain ⟨hne,hmK⟩ := Finset.mem_erase.mp hmpK
    obtain ⟨hl,hu⟩ := hDyad q.1 hmK
    exact ⟨hne.symm,hvalid,hk,hl,hu⟩
  let t := parityOriginalHistoricalPhysicalFourierEventTriple434 U Z e m mp n
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V Z k buf a b hSmooth hSupport
  have hBase := parity_original_ungated_true_psi_physical_finite_3d_ball_error434
    S (fun q => parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho alpha signed Y e q.2 m q.1)
    mp n d L hL band slot δ Y e m he U E V Z
    hU hE hV hZ k (hDyad m hm).1 (hDyad m hm).2 hPhysical
    buf a b hSmooth hSupport hOne4 H T hT
  have hSrc := parity_original_actual_true_psi_eta_active_source_exact434
    d L E V Z hL band slot δ ξ rho alpha signed Y e m K J k
  dsimp only at hBase ⊢
  rw [hSrc]
  simpa only [parityOriginalActualTruePsiEtaActiveFourierBall434,
    S,W,mp,n,t,f,mul_assoc] using hBase
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothDyadicCapacity -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5500000

/-- A completely explicit (not existential, not chosen after J/B/S)
source 2-adic height cut-off covering ALL corrected cap-free true B'
physical z. The factor 48 is the conservative bound obtained after
the original canonical binary dyad has been doubled. -/
def parityOriginalActualTrueSmoothDyadicCapacity434 (L K0 Cbox : ℝ) : ℕ :=
  Nat.log 2 (Nat.ceil (48*Cbox*Real.exp L*L^(K0+88)))

/-- The full source z-height fits the explicit dyadic capacity
N(L), with NO assumptions on the Fourier parameters, coefficient
family, positive e prime factors, or character projector. -/
theorem parity_original_true_smooth_dyadic_capacity434
    (L K0 Cbox : ℝ) :
    48*Cbox*Real.exp L*L^(K0+88) ≤
      (2:ℝ)^(parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox+1) := by
  let H : ℝ := 48*Cbox*Real.exp L*L^(K0+88)
  let Y : ℕ := Nat.ceil H
  have hY : H ≤ (Y:ℝ) := Nat.le_ceil H
  have hp : Y < 2^(Nat.log 2 Y+1) :=
    Nat.lt_pow_succ_log_self (by omega : 1<2) Y
  have hpr : (Y:ℝ) < (2:ℝ)^(Nat.log 2 Y+1) := by
    exact_mod_cast hp
  have hN : parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox=
      Nat.log 2 Y := rfl
  rw [hN]
  exact hY.trans hpr.le
end Green64Analytic.Parity

end

end

/-! ## TruePhysicalPsiExplicitCapacity -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The entire original C-infinity ψ decomposition of one physical
post-Cauchy (e,m,k) fibre, with the real original eta_e(e/E)eta_n(n/V)
and full-odd e carrier, using a canonical N(L) fixed from source
geometry alone. No assumed dyadic capacity or artificial sharp ψ mask.
The filtered j are precisely the physically attained true smooth
neighbor scales; no character-wise or complex-subsummand inequality. -/
theorem parity_original_full_odd_actual_weight_smooth_psi_explicit_capacity434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V) (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (e m : ℕ) (k : ℤ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    :
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot δ Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k
    let W : ℕ×ℕ → ℂ := fun q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V (by linarith : 8≤L) e q.2:ℝ):ℂ)*
        parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho alpha signed Y e q.2 m q.1
    (∑q∈S,W q) =
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*W q := by
  exact parity_original_full_odd_actual_weight_smooth_psi_neighbor_reindex434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot δ ξ rho K alpha signed hDyad
    e m k (parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox)
    he hm hk (parity_original_true_smooth_dyadic_capacity434 L K0 Cbox)
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothNeighborZWindow -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6800000

/-- Every smooth psi scale that can actually occur in the original
cap-free, all-odd, physical Parity B' source, INCLUDING the preceding
half-dyad, satisfies a genuine two-sided original post-Cauchy
height window. No hard ψ mask or false singleton canonical Z is used.
The lower constant changes 1/16 to 1/64, costing only a fixed factor
4; upper 24*Cbox is unchanged. -/
theorem parity_original_full_odd_true_smooth_neighbor_Z_box_window434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ)
    (hDyad : ∀mp∈K, U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    (Real.exp L/64)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
  classical
  have hLw : 8≤L := by linarith
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  have hExact := parity_original_full_odd_actual_Z_union_smooth_neighbor_exact434
    d L E V hLw band slot delta Y K
  dsimp only at hExact
  have hMem : Z∈ZG ∪ ZG.image (fun Z => Z/2) := by
    change Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG at hZ
    rw [hExact] at hZ
    exact hZ
  have hCanon (z0 : ℕ) (hz0 : z0∈ZG) :
      (Real.exp L/16)*L^K0 < (z0:ℝ) ∧
      (z0:ℝ) < 24*Cbox*Real.exp L*L^(K0+88) := by
    exact parity_original_full_odd_actual_nonzero_Z_union_box_window434
      d L U V E K0 Cbox hLw band slot delta K hU hV
      (by linarith : 0<Cbox) hUV hUVhi hE hDyad z0 hz0
  have hPow : 0<Real.exp L*L^K0 := by positivity
  rcases Finset.mem_union.mp hMem with hBase | hHalf
  · have hW := hCanon Z hBase
    constructor
    · nlinarith [hW.1,hPow.le]
    · exact hW.2
  · obtain ⟨z0,hz0,hEq⟩ := Finset.mem_image.mp hHalf
    subst Z
    have hW := hCanon z0 hz0
    have hExp : (32:ℝ) ≤ Real.exp L := by
      have h := Real.add_one_le_exp L
      linarith
    have hPowOne : (1:ℝ)≤L^K0 := Real.one_le_rpow (by linarith) hK0
    have hTwo : (2:ℝ)≤(Real.exp L/16)*L^K0 := by
      have hDiv : (2:ℝ)≤Real.exp L/16 := by linarith
      have hLe := mul_le_mul_of_nonneg_left hPowOne (by positivity : 0≤Real.exp L/16)
      nlinarith
    have hZ0ge : 2≤z0 := by
      have hZ0R : (2:ℝ)≤(z0:ℝ) := (hTwo.trans_lt hW.1).le
      exact_mod_cast hZ0R
    have hDivBound : z0≤4*(z0/2) := by omega
    have hDivReal : (z0:ℝ)≤4*((z0/2:ℕ):ℝ) := by exact_mod_cast hDivBound
    constructor
    · nlinarith [hW.1,hDivReal]
    · have hDivLe : (z0/2:ℕ)≤z0 := by omega
      have hDR : ((z0/2:ℕ):ℝ)≤(z0:ℝ) := by exact_mod_cast hDivLe
      exact hDR.trans_lt hW.2
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothNeighborParity417Height -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6800000

/-- Numeric original Parity(4.17) height remains valid for true smooth
ψ preceding-half scale. The slightly wider low endpoint 1/64 is
absorbed by the existing reserved two logarithmic powers of height
(CZ=K0+90), uniformly in all physical k, fine α and source labels. -/
theorem parity_original_true_smooth_neighbor_417_height_numeric434
    (L K0 Cbox Z : ℝ) (hL : 32≤L) (hK0 : 0≤K0)
    (hCbox : 1≤Cbox) (hLarge : 24*Cbox≤L)
    (hZlo : (Real.exp L/64)*L^K0 < Z)
    (hZhi : Z < 24*Cbox*Real.exp L*L^(K0+88)) :
    Real.exp L*L^(-(K0+90))≤Z ∧
      Z≤Real.exp L*L^(K0+90) := by
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hLsq64 : (64:ℝ)≤L^2 := by nlinarith [hL]
  have hp2 : 0<L^(K0-2) := Real.rpow_pos_of_pos hLp _
  have hExp : -(K0+90)≤K0-2 := by linarith
  have hsmall : L^(-(K0+90))≤L^(K0-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 hExp
  have h64 : 64*L^(-(K0+90))≤L^K0 := by
    calc
      _ ≤ 64*L^(K0-2) := mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ ≤ L^2*L^(K0-2) := mul_le_mul_of_nonneg_right hLsq64 hp2.le
      _ = L^K0 := by
        rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
        congr 1
        ring
  have hLow : Real.exp L*L^(-(K0+90)) ≤ (Real.exp L/64)*L^K0 := by
    have hh := mul_le_mul_of_nonneg_left h64 (by positivity : 0≤Real.exp L/64)
    calc
      _ = (Real.exp L/64)*(64*L^(-(K0+90))) := by ring
      _ ≤ (Real.exp L/64)*L^K0 := hh
  have hLsq : 24*Cbox≤L^2 := by
    nlinarith [hLarge,hL1]
  have hP : 0≤L^(K0+88) := Real.rpow_nonneg hLp.le _
  have hUp : 24*Cbox*Real.exp L*L^(K0+88) ≤
      Real.exp L*L^(K0+90) := by
    have hM := mul_le_mul_of_nonneg_right hLsq hP
    have hH : L^2*L^(K0+88) = L^(K0+90) := by
      rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
      congr 1
      ring
    have hM2 := mul_le_mul_of_nonneg_left (hM.trans_eq hH)
      (Real.exp_pos L).le
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hM2
  exact ⟨(hLow.trans_lt hZlo).le,(hZhi.trans_le hUp).le⟩

/-- EVERY actual physically populated full-odd source smooth ψ scale,
including exactly the neighboring half-scale needed by support 1<t<4,
meets the native unrestricted signed Parity(4.17) original height
hypothesis at CZ=K0+90. The true cap-free physical Ybox=ceil6UV is
kept, with no Pfree-e condition or dependence on a chosen frequency. -/
theorem parity_original_full_odd_true_smooth_neighbor_Z_Parity417_legal434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox) (hLarge : 24*Cbox≤L)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    Real.exp L*L^(-(K0+90)) ≤ (Z:ℝ) ∧
      (Z:ℝ) ≤ Real.exp L*L^(K0+90) := by
  have hZrange := parity_original_full_odd_true_smooth_neighbor_Z_box_window434
    d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta K hDyad Z hZ
  exact parity_original_true_smooth_neighbor_417_height_numeric434
    L K0 Cbox (Z:ℝ) hL hK0 hCbox hLarge hZrange.1 hZrange.2
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothZCapAsymptotic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7200000

/-- The original smooth-weight physical B' source has z < 24 Cbox
exp(L) L^(K0+88). Its genuine all-source positive containing cap,
chosen before any dyadic grouping, is this exact natural ceiling. -/
def parityOriginalActualTrueSmoothPhysicalZCap434 (L K0 Cbox : ℝ) : ℕ :=
  Nat.ceil (24*Cbox*Real.exp L*L^(K0+88))

/-- The real source containing z cap is positive and loses at most
ONE factor in its leading constant: 25 Cbox rather than an invented
2 exp L (known to be false for the corrected cap-free original B'). -/
theorem parity_original_actual_true_smooth_source_z_cap434
    (L K0 Cbox : ℝ) (hL : 32≤L) (hK0 : 0≤K0)
    (hCbox : 1≤Cbox) :
    1≤parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox ∧
    ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ) ≤
      25*Cbox*Real.exp L*L^(K0+88) := by
  let H : ℝ := 24*Cbox*Real.exp L*L^(K0+88)
  let Y : ℕ := Nat.ceil H
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hExp1 : (1:ℝ)≤Real.exp L := Real.one_le_exp (by linarith)
  have hPow1 : (1:ℝ)≤L^(K0+88) :=
    Real.one_le_rpow hL1 (by linarith)
  have hCExp : (1:ℝ)≤Cbox*Real.exp L := by nlinarith
  have hFactor : (1:ℝ)≤Cbox*Real.exp L*L^(K0+88) := by nlinarith
  have hHpos : 0≤H := by dsimp [H]; positivity
  have hH1 : (1:ℝ)≤H := by dsimp [H]; nlinarith
  have hYfloor : H≤(Y:ℝ) := Nat.le_ceil H
  have hYhi : (Y:ℝ) < H+1 := Nat.ceil_lt_add_one hHpos
  have hYone : 1≤Y := by
    have hh : (1:ℝ)≤(Y:ℝ) := hH1.trans hYfloor
    exact_mod_cast hh
  refine ⟨hYone,?_⟩
  change (Y:ℝ)≤25*Cbox*Real.exp L*L^(K0+88)
  dsimp [H] at hYhi
  nlinarith

/-- The exact original positive z cap has the required logarithmic
budget. The only large-L threshold depends on the fixed geometry
K0,Cbox; it is fixed BEFORE source fine cells, Fourier frequencies,
character masks, or source dyadic Z are chosen. -/
theorem parity_eventually_original_actual_true_smooth_source_z_cap_log434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 24*Cbox≤L ∧
      1≤parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox ∧
      ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ) ≤
        25*Cbox*Real.exp L*L^(K0+88) ∧
      Real.log ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ)≤2*L := by
  have hPoly := eventually_native_source_poly_lt_exp_scaled434
    (K0+88) 1 (1/2) (by linarith) (by norm_num) (by norm_num)
  filter_upwards [hPoly,eventually_ge_atTop (32:ℝ),
    eventually_ge_atTop (24*Cbox),
    eventually_ge_atTop (2*Real.log (25*Cbox))]
    with L hP hL hLarge hConst
  have hCap := parity_original_actual_true_smooth_source_z_cap434
    L K0 Cbox hL hK0 hCbox
  refine ⟨hL,hLarge,hCap.1,hCap.2,?_⟩
  have hLp : 0<L := by linarith
  have hPexp : L^(K0+88) ≤ Real.exp (L/2) := by
    simpa only [Real.rpow_one,one_div_mul_eq_div] using hP.2.le
  have hCpositive : (0:ℝ)<25*Cbox := by positivity
  have hCexp : 25*Cbox ≤ Real.exp (L/2) := by
    have hlog : Real.log (25*Cbox)≤L/2 := by linarith
    calc
      (25*Cbox:ℝ) = Real.exp (Real.log (25*Cbox)) :=
        (Real.exp_log hCpositive).symm
      _ ≤ Real.exp (L/2) := Real.exp_le_exp.mpr hlog
  have hproduct : (25*Cbox)*L^(K0+88) ≤
      Real.exp (L/2)*Real.exp (L/2) :=
    mul_le_mul hCexp hPexp (Real.rpow_nonneg hLp.le _) (Real.exp_nonneg _)
  have hYexp : ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ)≤
      Real.exp (2*L) := by
    calc
      _ ≤ 25*Cbox*Real.exp L*L^(K0+88) := hCap.2
      _ = Real.exp L*((25*Cbox)*L^(K0+88)) := by ring
      _ ≤ Real.exp L*(Real.exp (L/2)*Real.exp (L/2)) :=
        mul_le_mul_of_nonneg_left hproduct (Real.exp_pos L).le
      _ = Real.exp (2*L) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
  have hYpos : (0:ℝ)<
      ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCap.1)
  have hlog := Real.log_le_log hYpos hYexp
  simpa only [Real.log_exp] using hlog
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothOriginalEMKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- EXACT full original h=-2 B' post-Cauchy weighted physical source
outer e,m,k with ALL original odd e, all Q/P/B509 two-endpoint source
support, original H0/W1/epsilon and fine alpha. The true eta_e eta_n
weights on natural e,n are not changed. An explicit dyadic capacity
N(L) is chosen from source data before the sum. Inserting the complete
fixed C∞ ψ(z/2^j) dyadic partition and restricting j to exactly the
attained physical binary heights or immediately preceding half-heights
is an IDENTITY of complex sums, not an upper bound of signed subsums.
This is the genuine GLOBAL e/m/k source smoothization; it does not
by itself identify the Fourier integral of the full physical outer. -/
theorem parity_original_full_odd_actual_weight_complete_emk_smooth_psi_outer434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
          W e m k q) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  dsimp only
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  have hCell := parity_original_full_odd_actual_weight_smooth_psi_explicit_capacity434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
    e m k he hm hk
  dsimp only at hCell ⊢
  exact hCell
end Green64Analytic.Parity

end

end

/-! ## SmoothOriginalGlobalKFubini -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5900000

/-- Exact dependent signed k × actual smooth dyadic j Fubini of the
ORIGINAL, nonuniform e,m,k physical carriers. The containing signed
k finite set is supplied by an exact source union, not a newly chosen
larger spectral cutoff. The zero-extension indicator is an equality
of complex coefficients and all (m',n) source multiplicities survive.
No character-wise subset norm inequality is used. -/
theorem parity_original_finite_smooth_dyadic_k_outer_fubini434
    (EF K : Finset ℕ) (ks : ℕ → ℕ → Finset ℤ)
    (KG : Finset ℤ) (T : Finset ℕ)
    (F : ℕ → ℕ → ℤ → ℕ → ℂ)
    (hk : ∀ e∈EF, ∀ m∈K, ks e m⊆KG) :
    (∑ e∈EF,∑ m∈K,∑ k∈ks e m,∑ j∈T,F e m k j) =
      ∑ k∈KG,∑ j∈T,∑ e∈EF,∑ m∈K,
        if k∈ks e m then F e m k j else 0 := by
  classical
  have hCell (e m : ℕ) (he : e∈EF) (hm : m∈K) :
      (∑k∈ks e m,∑j∈T,F e m k j) =
      ∑k∈KG,∑j∈T,if k∈ks e m then F e m k j else 0 := by
    let H : ℤ → ℂ := fun k => ∑j∈T,F e m k j
    have hExt := parity_original_finite_source_sum_zero_extend434
      (ks e m) KG (hk e he m hm) H
    change (∑k∈ks e m,H k) = _
    calc
      _ = ∑k∈KG,if k∈ks e m then H k else 0 := hExt
      _ = ∑k∈KG,∑j∈T,if k∈ks e m then F e m k j else 0 := by
        apply Finset.sum_congr rfl
        intro k hkG
        by_cases hmem : k∈ks e m
        · simp [hmem,H]
        · simp [hmem,H]
  let H : ℕ → ℕ → ℤ → ℕ → ℂ := fun e m k j =>
    if k∈ks e m then F e m k j else 0
  calc
    _ = ∑e∈EF,∑m∈K,∑k∈KG,∑j∈T,H e m k j := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro m hm
      exact hCell e m he hm
    _ = ∑e∈EF,∑k∈KG,∑m∈K,∑j∈T,H e m k j := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_comm]
    _ = ∑k∈KG,∑e∈EF,∑m∈K,∑j∈T,H e m k j := Finset.sum_comm
    _ = ∑k∈KG,∑e∈EF,∑j∈T,∑m∈K,H e m k j := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_comm]
    _ = ∑k∈KG,∑j∈T,∑e∈EF,∑m∈K,H e m k j := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = _ := rfl
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothOriginalGlobalKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- The complete original full-odd physical source e,m,k,m',n
complex B' offdiagonal, with its genuine eta_e eta_n and C∞ ψ,
is EXACTLY grouped by global original physically-derived SIGNED k
with all e,m,q multiplicities retained in the new inner sum. The
outer k union is the literal source union (not an analytic window
or the smaller smoothed nonzero k carrier). This is a true algebraic
bridge toward identifying the globally smoothed Fourier source;
it neither applies a signed-subsum inequality nor claims TypeII. -/
theorem parity_original_full_odd_actual_weight_global_raw_k_smooth_psi_outer434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑k∈KG,∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
            W e m k q
        else 0) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  let T : Finset ℕ := (Finset.range (N+1)).filter
    (fun j => (2:ℕ)^j∈ZSmooth)
  let F : ℕ → ℕ → ℤ → ℕ → ℂ := fun e m k j =>
    ∑q∈S e m k,
      parityOriginalHistoricalDyadicSmoothPsi434
        ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
      W e m k q
  have hk : ∀ e∈EF, ∀ m∈K,
      parityOriginalHistoricalNonzeroKSupport434 e m K ⊆ KG := by
    intro e he m hm k hk
    change k∈(EF.biUnion fun e => K.biUnion fun m =>
      parityOriginalHistoricalNonzeroKSupport434 e m K)
    exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_biUnion.mpr ⟨m,hm,hk⟩⟩
  have hSmooth := parity_original_full_odd_actual_weight_complete_emk_smooth_psi_outer434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  have hKFubini := parity_original_finite_smooth_dyadic_k_outer_fubini434
    EF K (fun e m => parityOriginalHistoricalNonzeroKSupport434 e m K)
    KG T F hk
  dsimp only at hSmooth hKFubini ⊢
  exact hSmooth.trans hKFubini
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothKSupportExact -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7000000

/-- Every genuine ORIGINAL h=-2 full-odd physical e,m,k,m',n atom
with nonzero actual eta_e(e/E)eta_n(n/V) belongs to the TRUE
nonzero-source-weight global signed k support KSm. The proof
constructs its physical canonical z and its actual binary Z cell
and retains all source Q/P/H0 factors; no P-free-e selection. -/
theorem parity_original_full_odd_nonzero_weight_event_implies_smoothed_k434
    (d : ℕ) (L E V : ℝ) (hLw : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K : Finset ℕ) (k : ℤ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k)
    (hWeight : parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0) :
    k∈parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K := by
  classical
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
  let Z := parityOriginalHistoricalActualZDyadicScale434 z
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  have hqData := Finset.mem_filter.mp hq
  have hp := Finset.mem_product.mp hqData.1
  have hmp := Finset.mem_filter.mp hp.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hmp.1).1.symm
  have hz : 0<z := (parity_original_historical_ungated_physical_valid_k_z434
    d L band slot delta Y e m q.1 q.2 heOdd hNe hqData.2).2.1
  have hqZ : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot delta Y e m K J k Z := by
    exact Finset.mem_filter.mpr ⟨hqData.1,⟨hqData.2,hz,rfl⟩⟩
  have hZ : Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hLw band slot delta Y e m K J k := by
    unfold parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩, ⟨q,hqZ,hWeight⟩⟩
  unfold parityOriginalHistoricalFullOddSmoothedKUnion434
  apply Finset.mem_biUnion.mpr
  refine ⟨e,he,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨m,hm,?_⟩
  exact Finset.mem_filter.mpr ⟨hk,⟨Z,hZ⟩⟩

/-- A missing k from the source ACTUAL smoothed KSm carrier means
literally every natural η_eη_n physical event coefficient is zero.
The conclusion is pointwise only for the nonnegative real eta-weight,
NOT for an individual character or a Fourier-truncated ghost. -/
theorem parity_original_full_odd_outside_smoothed_k_eta_zero434
    (d : ℕ) (L E V : ℝ) (hLw : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K : Finset ℕ) (k : ℤ)
    (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
    (hm : m∈K) (hk : k∈parityOriginalHistoricalNonzeroKSupport434 e m K)
    (hNoK : k∉parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k) :
    parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2=0 := by
  by_contra hh
  exact hNoK (parity_original_full_odd_nonzero_weight_event_implies_smoothed_k434
    d L E V hLw band slot delta Y e m K k he hm hk q hq hh)
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothOriginalSmoothedKOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 7400000

/-- The original entire weighted all-odd physical Cauchy
(e,m,k,m',n) complex source with genuine eta_e/n and smooth ψ is
EXACTLY reindexed by its ACTUAL NONZERO-ETA signed KSm carrier,
not the much larger unweighted odd-e quotient set. All zero-
weight raw k fibres vanish literally before Fourier truncation,
not by a false norm comparison of signed subsums. Physical source
k and ψ carry their full original multiplicities and no #character
or Pfree-e assumptions. The full Parity TypeII and source frequency
allocation family integration are not asserted here. -/
theorem parity_original_full_odd_actual_weight_global_smoothed_k_psi_outer434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑k∈KSm,∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈ZSmooth),
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
            W e m k q
        else 0) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  let T : Finset ℕ := (Finset.range (N+1)).filter
    (fun j => (2:ℕ)^j∈ZSmooth)
  let F : ℤ → ℂ := fun k =>
    ∑j∈T, ∑e∈EF, ∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
          W e m k q
      else 0
  have hRaw := parity_original_full_odd_actual_weight_global_raw_k_smooth_psi_outer434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  have hSub : KSm⊆KG := parity_original_full_odd_smoothed_k_sub_raw434
    d L E V hLw band slot delta Y K
  have hZero (k : ℤ) (hk : k∈KG) (hNo : k∉KSm) : F k=0 := by
    dsimp [F]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hK : k∈parityOriginalHistoricalNonzeroKSupport434 e m K
    · simp only [hK,ite_true]
      apply Finset.sum_eq_zero
      intro q hq
      have hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2=0 :=
        parity_original_full_odd_outside_smoothed_k_eta_zero434
          d L E V hLw band slot delta Y e m K k he hm hK hNo q hq
      dsimp only [W]
      rw [hw]
      simp
    · simp [hK]
  have hOmit : (∑k∈KG,F k)=(∑k∈KSm,F k) := by
    exact (Finset.sum_subset hSub hZero).symm
  dsimp only at hRaw ⊢
  exact hRaw.trans hOmit
end Green64Analytic.Parity

end

end

/-! ## ActualSmoothZPowerImage -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- Each ORIGINAL physically attained nonzero eta-weight canonical
binary z-dyad is truly a power of TWO, since the source definition
uses 2^(Nat.log 2 z). This is not an arbitrary source Z label. -/
theorem parity_original_full_odd_nonzero_Z_union_is_binary_power434
    (d : ℕ) (L E V : ℝ) (hLw : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y : ℕ) (K : Finset ℕ) (Z : ℕ)
    (hZ : Z∈parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K) :
    ∃j : ℕ, Z=(2:ℕ)^j := by
  classical
  unfold parityOriginalHistoricalFullOddOriginalZUnion434 at hZ
  obtain ⟨e,he,hR⟩ := Finset.mem_biUnion.mp hZ
  obtain ⟨m,hm,hR⟩ := Finset.mem_biUnion.mp hR
  obtain ⟨k,hk,hcell⟩ := Finset.mem_biUnion.mp hR
  have hImage := (Finset.mem_filter.mp hcell).1
  obtain ⟨q,hq,hEq⟩ := Finset.mem_image.mp hImage
  refine ⟨Nat.log 2 (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2),?_⟩
  simpa only [parityOriginalHistoricalPhysicalZScaleOfEvent434,
    parityOriginalHistoricalActualZDyadicScale434] using hEq.symm

/-- On the corrected true cap-free Parity physical window, every
canonical original binary Z is >=2, hence its preceding half Z/2
is another TRUE integer power of two, never a fictitious 0 or a
fractional Z. No smooth ψ contribution can require an unlegal Z. -/
theorem parity_original_full_odd_nonzero_Z_union_two_or_more434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K) :
    2≤Z := by
  have hZR := parity_original_full_odd_actual_nonzero_Z_union_box_window434
    d L U V E K0 Cbox (by linarith : 8≤L) band slot delta K
    hU hV (by linarith : 0<Cbox) hUV hUVhi hE hDyad Z hZ
  have hexp : (32:ℝ)≤Real.exp L := by
    have h := Real.add_one_le_exp L
    linarith
  have hbase : (1:ℝ)≤L^K0 := Real.one_le_rpow (by linarith : 1≤L) hK0
  have hTwo : (2:ℝ)≤(Real.exp L/16)*L^K0 := by
    have hh : (2:ℝ)≤Real.exp L/16 := by linarith
    nlinarith
  have hcast : (2:ℝ)≤(Z:ℝ) := (hTwo.trans_lt hZR.1).le
  exact_mod_cast hcast

/-- Physical source smooth ψ-neighbor Z scales are likewise genuine
positive powers of two. The preceding half case uses the source
canonical Z>=2, not an artificial sharp mask or unproved divisibility. -/
theorem parity_original_full_odd_smooth_neighbor_Z_is_binary_power434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    ∃j : ℕ, Z=(2:ℕ)^j := by
  classical
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K
  have hExact := parity_original_full_odd_actual_Z_union_smooth_neighbor_exact434
    d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K
  change Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG at hZ
  rw [hExact] at hZ
  rcases Finset.mem_union.mp hZ with hBase | hHalf
  · exact parity_original_full_odd_nonzero_Z_union_is_binary_power434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K Z hBase
  · obtain ⟨z0,hz0,hEq⟩ := Finset.mem_image.mp hHalf
    obtain ⟨j,hPow⟩ := parity_original_full_odd_nonzero_Z_union_is_binary_power434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K z0 hz0
    have h2 : 2≤z0 := parity_original_full_odd_nonzero_Z_union_two_or_more434
      d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
      band slot delta K hDyad z0 hz0
    have hj : 1≤j := by
      by_contra hh
      have j0 : j=0 := by omega
      simp [hPow,j0] at h2
    refine ⟨j-1,?_⟩
    rw [←hEq,hPow]
    have hSucc : (j-1)+1=j := by omega
    have hDivPow : (2:ℕ)^j/2=(2:ℕ)^(j-1) := by
      conv_lhs => rw [←hSucc,pow_succ]
      omega
    exact hDivPow
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothSignedShift -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The original signed Parity h=-2 shift is Δ=2k (not k, not -2k
with a spurious modulus), and its whole true smooth dyadic source
is small enough for unrestricted Eq(4.17) after the SOURCE-derived
height lower bound. The stronger existing rank-cell estimate
|2k/Z| ≤ (128*exp 2)^(-1) implies the literal required |2k|≤Z/128.
The k sign and the character modulus 2|k| are left unchanged. -/
theorem parity_eventually_original_true_smooth_signed_shift_417434
    (CZ Ck : ℝ) (hCZ : 0≤CZ) (hCk : 0≤Ck) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (Z : ℝ) (k : ℤ),
      Real.exp L*L^(-CZ)≤Z → (k.natAbs:ℝ)≤L^Ck →
      |((2*k:ℤ):ℝ)|≤Z/128 := by
  filter_upwards [parity_eventually_rank_cell_signed_shift434
    CZ Ck hCZ hCk] with L hSource
  refine ⟨hSource.1,?_⟩
  intro Z k hZ hk
  have hkReal : |(k:ℝ)|≤L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hk
  obtain ⟨hZpos,hSmall⟩ := hSource.2 Z k hZ hkReal
  have hExpOne : (1:ℝ)≤Real.exp 2 := Real.one_le_exp (by norm_num)
  have hInv : (128*Real.exp 2)⁻¹ ≤ (128:ℝ)⁻¹ := by
    apply (inv_le_inv₀ (by positivity : 0<128*Real.exp 2)
      (by norm_num : (0:ℝ)<128)).mpr
    nlinarith
  have hQuot : |2*(k:ℝ)|/Z≤(128:ℝ)⁻¹ := by
    calc
      _ = |2*(k:ℝ)/Z| := by rw [abs_div,abs_of_pos hZpos]
      _ ≤ (128*Real.exp 2)⁻¹ := hSmall
      _ ≤ (128:ℝ)⁻¹ := hInv
  have hShift := (div_le_iff₀ hZpos).mp hQuot
  have hEq : (((2*k:ℤ):ℝ))=2*(k:ℝ) := by push_cast; ring
  rw [hEq]
  calc
    _ ≤ (128:ℝ)⁻¹*Z := hShift
    _ = Z/128 := by ring
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothSourceKZInputs -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- The source-TRUE nonzero-weight Parity(4.13) k union, the actual
canonical post-Cauchy z dyadic Z union and BOTH smooth ψ neighboring
Z scales simultaneously satisfy EVERY numerical precondition of the
quantified B' global k/Z saving theorem. This is not an arbitrary
finite-set hypothesis: KSm and ZG are literally the full-odd B509
physical Q/P/H0 supports at Ybox=ceil(6UV), with all odd e.

The fixed exponents are Ck=K0+89 and CZ=K0+90. Signed Δ=2k is
small uniformly over the entire actual smooth Z carrier, the true
source z cap has logY<=2L, and there is NO #χ or #source event loss.
The requirement UV<=Cbox expL is original fixed-scale geometry. -/
theorem parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs434
    (K0 Cbox : ℝ) (hK0 : 0≤K0) (hCbox : 1≤Cbox) :
    ∀ᶠ L : ℝ in atTop, 32≤L ∧ 24*Cbox≤L ∧
    1≤parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox ∧
    ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ)≤
      25*Cbox*Real.exp L*L^(K0+88) ∧
    Real.log ((parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox:ℕ):ℝ)≤2*L ∧
      ∀ (d : ℕ) (band : Fin (d+1)) (slot : Fin 20)
        (delta : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length → Bool)
        (hLw : 8≤L)
        (U V E : ℝ) (hU : 0<U) (hV : 0<V)
        (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
        (hE : E=U*L^(-K0)) (K : Finset ℕ)
        (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U),
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
        let N := Nat.ceil (L^(K0+89))
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        (∀k∈KS, k≠0 ∧ k.natAbs≤N ∧ (k.natAbs:ℝ)≤L^(K0+89)) ∧
        (∀z∈ZG, 0<z ∧ z≤Y) ∧
        (∀Z∈ZSmooth,
          Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
          (Z:ℝ)≤Real.exp L*L^(K0+90) ∧
          (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88)) ∧
        (∀k∈KS,∀Z∈ZSmooth, |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128) := by
  have hS := parity_eventually_original_true_smooth_signed_shift_417434
    (K0+90) (K0+89) (by linarith) (by linarith)
  have hY := parity_eventually_original_actual_true_smooth_source_z_cap_log434
    K0 Cbox hK0 hCbox
  filter_upwards [hS,hY] with L hSmall hCap
  refine ⟨hCap.1,hCap.2.1,hCap.2.2.1,hCap.2.2.2.1,hCap.2.2.2.2,?_⟩
  intro d band slot delta hLw U V E hU hV hUV hUVhi hE K hDyad
  classical
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := Nat.ceil (L^(K0+89))
  let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
  have hK : ∀k∈KS,k≠0 ∧ k.natAbs≤N ∧
      (k.natAbs:ℝ)≤L^(K0+89) := by
    intro k hk
    have hh := parity_original_full_odd_smoothed_k_genuine_polylog434
      d L U E V K0 hLw hU hE band slot delta Ybox K hDyad k hk
    exact ⟨hh.1,hh.2.2,hh.2.1.le⟩
  have hZs : ∀z∈ZG,0<z ∧ z≤Y := by
    intro z hz
    have hBound := parity_original_full_odd_actual_nonzero_Z_union_box_window434
      d L U V E K0 Cbox hLw band slot delta K hU hV
      (by linarith : 0<Cbox) hUV hUVhi hE hDyad z hz
    have hPos : (0:ℝ)<(z:ℝ) := by
      have hx : (0:ℝ)<(Real.exp L/16)*L^K0 := by positivity
      linarith
    have hZpos : 0<z := by exact_mod_cast hPos
    have hCeil : 24*Cbox*Real.exp L*L^(K0+88)≤(Y:ℝ) := Nat.le_ceil _
    have hZle : (z:ℝ)≤(Y:ℝ) := (hBound.2.trans_le hCeil).le
    exact ⟨hZpos,by exact_mod_cast hZle⟩
  have hH : ∀Z∈ZSmooth,
      Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
      (Z:ℝ)≤Real.exp L*L^(K0+90) ∧
      (Z:ℝ)≤24*Cbox*Real.exp L*L^(K0+88) := by
    intro Z hZ
    have hh := parity_original_full_odd_true_smooth_neighbor_Z_Parity417_legal434
      d L U V E K0 Cbox hCap.1 hK0 hU hV hCbox hCap.2.1
      hUV hUVhi hE band slot delta K hDyad Z hZ
    have hb := parity_original_full_odd_true_smooth_neighbor_Z_box_window434
      d L U V E K0 Cbox hCap.1 hK0 hU hV hCbox
      hUV hUVhi hE band slot delta K hDyad Z hZ
    exact ⟨hh.1,hh.2,hb.2.le⟩
  have hShift : ∀k∈KS,∀Z∈ZSmooth,
      |((2*k:ℤ):ℝ)|≤(Z:ℝ)/128 := by
    intro k hk Z hz
    exact hSmall.2 (Z:ℝ) k (hH Z hz).1 (hK k hk).2.2
  dsimp only
  exact ⟨hK,hZs,hH,hShift⟩
end Green64Analytic.Parity

end

end

/-! ## BPrimeTruePhysicalKZAnyLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- True global signed k × original C∞ ψ_Z source post-Cauchy B' Fourier
saving, with neither k nor Z nor the natural source height Y supplied
as arbitrary finite sets. Those carriers are the ACTUAL full-odd B509
physical nonzero η_eη_n source support with corrected cap-free Ybox.
The one fixed reserved-Q band/slot and one fine b629 interval remain
quantified; entire original TypeII and all external source families
are not claimed by this theorem. The fixed strict m<2U input is the
original source half-open cofactor dyad and requires source audit. -/
theorem parity_eventually_original_actual_Bprime_true_physical_kZ_any_log434
    (jQ : ℕ) (Agoal D C0 Cf beta gamma K0 Cbox A R : ℝ)
    (hD : 0<D) (hPrecision : Agoal+(K0+89)+K0+90≤D)
    (hCf : Cf = (5*(K0+90))*
      ((((1+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1)) +
      (D+2*parityOriginalW1PolylogExponent434+30))
    (hbeta : 0<beta) (hgamma : 0<gamma)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) :
    ∃ J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ᶠ L : ℝ in atTop, 32≤L ∧ 6*Cbox≤L ∧
        (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
        jQ ≤ sourceOriginalLiteralDepth 20 L ∧
        ∀ (hLw : 8≤L)
          (hFamily : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
        ∀ (slot : Fin 20)
          (delta : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → Bool)
          (freq : Fin (sourceOrderedLabels 20
            (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L) band slot).length → ℝ)
          (rho xi1 xi2 xi3 U E V T : ℝ) (signed : Bool),
          0<U → 0<E → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
          T=L^Cf →
          |rho|≤L^C0 → |xi1|≤L^C0 → |xi2|≤L^C0 → |xi3|≤L^C0 →
        ∀ (prime : Bool) (lFine uFine a b : ℕ),
          Real.exp (beta*L)≤(lFine:ℝ) →
          2≤lFine → uFine≤2*lFine → (uFine:ℝ)≤Real.exp (2*L) →
          (∀m∈Finset.Icc a b,U≤(m:ℝ) ∧ (m:ℝ)<2*U) →
        U*V≤Cbox*Real.exp L →
        let d := sourceOriginalLiteralDepth 20 L
        let K := Finset.Icc a b
        let Ybox := Nat.ceil (6*U*V)
        let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
          d L E V hLw band slot delta Ybox K
        let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
          d L E V hLw band slot delta Ybox K
        let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
        let alpha := restrictSequence K
          (b629ActualFineAlpha434 prime L S gamma lFine uFine)
        let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 0
        let Cmoment1 := parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport 1
        ‖∑k∈KS,∑Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434 ZS,
          parityOriginalActualBprimeFineLowfreqSignal434
            d L U E V hLw (Z:ℝ) k band slot delta freq K alpha
            rho xi1 xi2 xi3 T signed buf A hSmooth hSupport‖ ≤
          (250*Cbox*(1+2/Real.log 2)*(Cmoment+132*Cmoment1))*
            Real.exp L*L^(-Agoal) := by
  obtain ⟨J,B,S,hBS,hMain⟩ :=
    parity_eventually_original_actual_Bprime_fine_smooth_psi_neighbor_kZ_any_log434
      jQ Agoal D C0 Cf (K0+90) (K0+89) beta gamma K0 Cbox A R
      hD hPrecision hCf (by linarith) (by linarith)
      hbeta hgamma hK0 hCbox hA hR buf hSmooth hSupport hCube
  have hSource := parity_eventually_original_actual_full_odd_smooth_source_kZ_inputs434
    K0 Cbox hK0 hCbox
  refine ⟨J,B,S,hBS,?_⟩
  filter_upwards [hMain,hSource] with L hMainL hSourceL
  rcases hMainL with ⟨hL8,hL6,hFamily,hReserved,hMainRest⟩
  rcases hSourceL with ⟨hL32,hLarge,hYpos,hYhi,hYlog,hSourceRest⟩
  refine ⟨hL32,hL6,hFamily,hReserved,?_⟩
  intro hLw hFamily0 band hBand slot delta freq rho xi1 xi2 xi3
    U E V T signed hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyadStrict hUVhi
  classical
  let d := sourceOriginalLiteralDepth 20 L
  let K := Finset.Icc a b
  let Ybox := Nat.ceil (6*U*V)
  let KS := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Ybox K
  let ZS := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Ybox K
  let Y := parityOriginalActualTrueSmoothPhysicalZCap434 L K0 Cbox
  let N := Nat.ceil (L^(K0+89))
  have hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)≤2*U := by
    intro m hm
    obtain ⟨hl,hr⟩ := hDyadStrict m hm
    exact ⟨hl,hr.le⟩
  have hGeo := hSourceRest d band slot delta hLw U V E
    hU hV hUV hUVhi hEscale K hDyadStrict
  dsimp only at hGeo
  rcases hGeo with ⟨hKS,hZS,hZwindow,hShift⟩
  have hMainBound := hMainRest hLw hFamily0 band hBand slot delta freq
    rho xi1 xi2 xi3 U E V T signed
    hU hEpos hV hUV hEscale hT hrho hxi1 hxi2 hxi3
    prime lFine uFine a b hFineLow hl hu huExp hDyad
    KS N Y ZS hKS hZS hZwindow hShift (le_refl N)
    hYhi hYpos hYlog
  dsimp only at hMainBound ⊢
  exact hMainBound
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothZRangeImage -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Real source smooth ψ-neighbor Z is a power of 2^j with a REAL
bounded exponent j≤the *explicit* source dyadic capacity N(L).
The original Z carries its true physical cap-free B509 source
support, so this uses neither an arbitrary Fourier truncation nor
a sharp dyadic substitute for smooth ψ. -/
theorem parity_original_full_odd_true_smooth_neighbor_Z_index_capacity434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (Z : ℕ)
    (hZ : Z∈parityOriginalActualSmoothPsiNeighborZEnvelope434
      (parityOriginalHistoricalFullOddOriginalZUnion434
        d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K)) :
    ∃j : ℕ, j≤parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox ∧
      Z=(2:ℕ)^j := by
  obtain ⟨j,hPow⟩ := parity_original_full_odd_smooth_neighbor_Z_is_binary_power434
    d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
    band slot delta K hDyad Z hZ
  have hBox := parity_original_full_odd_true_smooth_neighbor_Z_box_window434
    d L U V E K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta K hDyad Z hZ
  let Y : ℕ := Nat.ceil (48*Cbox*Real.exp L*L^(K0+88))
  have hCeil : 48*Cbox*Real.exp L*L^(K0+88)≤(Y:ℝ) := Nat.le_ceil _
  have hZsmall : (Z:ℝ)≤(Y:ℝ) := by
    have hCapPos : 0≤Cbox*Real.exp L*L^(K0+88) := by positivity
    linarith [hBox.2,hCeil,hCapPos]
  have hNat : Z≤Y := by exact_mod_cast hZsmall
  have hLog : Nat.log 2 Z ≤ Nat.log 2 Y := Nat.log_mono_right hNat
  have hjLog : Nat.log 2 Z=j := by
    rw [hPow,Nat.log_pow (by norm_num : 1<2)]
  have hjCap : j≤parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox := by
    rw [hjLog] at hLog
    exact hLog
  exact ⟨j,hjCap,hPow⟩

/-- A binary dyadic source set S is EXACTLY the image of the unique
j-values in [0,N] whose powers 2^j belong to S, provided all S
values have genuine source height (j<=N). Full original smooth ψ
partition is therefore neither enlarged nor restricted as a SIGNED
complex subsum when switching from j to its true physical scale Z. -/
theorem parity_original_finite_smooth_Z_power_image_exact434
    (S : Finset ℕ) (N : ℕ)
    (hS : ∀Z∈S,∃j : ℕ,j≤N ∧ Z=(2:ℕ)^j) :
    ((Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈S)).image
      (fun j => (2:ℕ)^j) = S := by
  classical
  ext Z
  constructor
  · intro hz
    obtain ⟨j,hj,hjZ⟩ := Finset.mem_image.mp hz
    rw [←hjZ]
    exact (Finset.mem_filter.mp hj).2
  · intro hZ
    obtain ⟨j,hjLe,hPow⟩ := hS Z hZ
    exact Finset.mem_image.mpr
      ⟨j,Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hjLe),
          by rw [←hPow]; exact hZ⟩, hPow.symm⟩

/-- The REAL original smooth ψ source family, including both
original binary and preceding half-dyads, is exactly the image of
its already kernel-checked full dyadic range filter at the explicit
source capacity N(L); no unsupported j or Z and no missing
neighboring contribution to the physical B' Fourier outer. -/
theorem parity_original_full_odd_true_smooth_Z_image_exact434
    (d : ℕ) (L U V E K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hCbox : 1≤Cbox)
    (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K : Finset ℕ) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V (by linarith : 8≤L) band slot delta (Nat.ceil (6*U*V)) K
    let S := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    ((Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈S)).image
      (fun j => (2:ℕ)^j) = S := by
  dsimp only
  apply parity_original_finite_smooth_Z_power_image_exact434
  intro Z hZ
  exact parity_original_full_odd_true_smooth_neighbor_Z_index_capacity434
    d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
    band slot delta K hDyad Z hZ
end Green64Analytic.Parity

end

end

/-! ## SmoothZSumImage -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 4100000

/-- 2^j is injective at the exact natural dyadic indices used by the
TRUE original ψ family. This avoids any duplicate binary height or
extra multiplicity when passing the original j sum to the physical Z. -/
theorem parity_original_true_dyadic_pow_two_injective434 :
    Function.Injective (fun j : ℕ => (2:ℕ)^j) := by
  intro a b hab
  have h := congrArg (Nat.log 2) hab
  simpa only [Nat.log_pow (by norm_num : 1<2)] using h

/-- If the original smooth dyadic ψ family exactly covers source
physical Z, finite complex reindex j↦2^j is a genuine equality,
not the mathematically false norm monotonicity of a complex subsum.
The same proof works for any complex original H0/Q/P/α source atom. -/
theorem parity_original_finite_true_smooth_dyadic_sum_image_exact434
    (S : Finset ℕ) (N : ℕ)
    (hS : ((Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈S)).image
      (fun j => (2:ℕ)^j) = S)
    (G : ℕ → ℂ) :
    (∑j∈(Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈S),G (2^j)) =
      ∑Z∈S,G Z := by
  classical
  let T := (Finset.range (N+1)).filter (fun j => (2:ℕ)^j∈S)
  change (∑j∈T,G (2^j))=∑Z∈S,G Z
  calc
    _ = ∑Z∈T.image (fun j : ℕ => (2:ℕ)^j),G Z :=
      (Finset.sum_image (s:=T) (g:=fun j : ℕ => (2:ℕ)^j)
        (f:=G) (fun a _ b _ hab =>
          parity_original_true_dyadic_pow_two_injective434 hab)).symm
    _ = ∑Z∈S,G Z := by rw [hS]
end Green64Analytic.Parity

end

end

/-! ## TrueSmoothOriginalKZOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The entire original all-odd B' physical source Cauchy off-diagonal,
with TRUE nonzero η-weight signed KSm and true C∞ ψ-neighbor dyads,
reindexed EXACTLY as a signed k×ZSmooth complex outer. This is a
literal identity of all natural e,m',n,q factors and original H0/W1,
b629 alpha, ε branches, with the same original no-u-cap Ybox. It
uses exact j↦2^j power-of-two image and injectivity, not the false
inequality for norms of complex subsets. Still no Fourier truncation,
all-fine-family summation or full TypeII 4.2 is claimed. -/
theorem parity_original_full_odd_actual_weight_global_smoothed_k_Z_outer434
    (d : ℕ) (L U E V K0 Cbox : ℝ) (hL : 32≤L)
    (hK0 : 0≤K0) (hU : 0<U) (hV : 0<V)
    (hCbox : 1≤Cbox)
    (hUV : Real.exp L≤U*V) (hUVhi : U*V≤Cbox*Real.exp L)
    (hE : E=U*L^(-K0))
    (band : Fin (d+1)) (slot : Fin 20)
    (delta : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (freq : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (alpha : ℕ → ℂ) (signed : Bool)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    let hLw : 8≤L := by linarith
    let EF := parityOriginalHistoricalFullOddEEnvelope434 E
    let J := parityOriginalHistoricalFullNEnvelope434 V
    let Y := Nat.ceil (6*U*V)
    let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
      d L E V hLw band slot delta Y K
    let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
    let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
    let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
    let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
      d L E V hLw band slot delta Y K
    let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
      parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot delta Y e m K J k
    let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
      ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot delta freq rho alpha signed Y e q.2 m q.1
    (∑e∈EF,∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      ∑q∈S e m k, W e m k q) =
    (∑k∈KSm,∑Z∈ZSmooth,
      ∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))*
            W e m k q
        else 0) := by
  classical
  have hLw : 8≤L := by linarith
  let EF := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := Nat.ceil (6*U*V)
  let ZG := parityOriginalHistoricalFullOddOriginalZUnion434
    d L E V hLw band slot delta Y K
  let ZSmooth := parityOriginalActualSmoothPsiNeighborZEnvelope434 ZG
  let N := parityOriginalActualTrueSmoothDyadicCapacity434 L K0 Cbox
  let KG := parityOriginalHistoricalFullOddOriginalKUnion434 E K
  let KSm := parityOriginalHistoricalFullOddSmoothedKUnion434
    d L E V hLw band slot delta Y K
  let S : ℕ → ℕ → ℤ → Finset (ℕ×ℕ) := fun e m k =>
    parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot delta Y e m K J k
  let W : ℕ → ℕ → ℤ → (ℕ×ℕ) → ℂ := fun e m _k q =>
    ((parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2:ℝ):ℂ)*
    parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot delta freq rho alpha signed Y e q.2 m q.1
  let T : Finset ℕ := (Finset.range (N+1)).filter
    (fun j => (2:ℕ)^j∈ZSmooth)
  let G : ℤ → ℕ → ℂ := fun k Z =>
    ∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(Z:ℝ))*
          W e m k q
      else 0
  have hOriginal := parity_original_full_odd_actual_weight_global_smoothed_k_psi_outer434
    d L U E V K0 Cbox hL hK0 hU hV hCbox hUV hUVhi hE
    band slot delta freq rho K alpha signed hDyad
  have hImage := parity_original_full_odd_true_smooth_Z_image_exact434
    d L U V E K0 Cbox hL hK0 hCbox hU hV hUV hUVhi hE
    band slot delta K hDyad
  change T.image (fun j : ℕ => (2:ℕ)^j)=ZSmooth at hImage
  have hKZ (k : ℤ) :
      (∑j∈T,∑e∈EF,∑m∈K,
        if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
          ∑q∈S e m k,
            parityOriginalHistoricalDyadicSmoothPsi434
              ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
            W e m k q else 0) =
      ∑Z∈ZSmooth,G k Z := by
    calc
      _ = ∑j∈T,G k (2^j) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [G]
        simp only [Nat.cast_pow, Nat.cast_ofNat]
      _ = ∑Z∈ZSmooth,G k Z :=
        parity_original_finite_true_smooth_dyadic_sum_image_exact434
          ZSmooth N (by simpa only [T] using hImage) (G k)
  dsimp only at hOriginal ⊢
  calc
    _ = ∑k∈KSm,∑j∈T,∑e∈EF,∑m∈K,
      if k∈parityOriginalHistoricalNonzeroKSupport434 e m K then
        ∑q∈S e m k,
          parityOriginalHistoricalDyadicSmoothPsi434
            ((parityOriginalHistoricalCanonicalZ434 e m q.1 q.2:ℝ)/(2:ℝ)^j)*
          W e m k q else 0 := hOriginal
    _ = ∑k∈KSm,∑Z∈ZSmooth,G k Z := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hKZ k
    _ = _ := rfl
end Green64Analytic.Parity

end

end

