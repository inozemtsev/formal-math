module

public import Green64.Library.Sieve.Foundations.Part052
public import Green64.Library.Sieve.Foundations.Part050
public import Green64.Library.Sieve.Foundations.Part049
public import Green64.Library.Sieve.Foundations.Part045
public import Green64.Library.Weights.Part108
public import Green64.Library.Sieve.Foundations.PresieveBlocks
public import Green64.Library.Sieve.Foundations.Part006

@[expose] public section

/-!
# Sieve / Foundations / Part053

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalWeightedCompositeSource -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The original section 8.3 bin source, specified before any dyadic regrouping:
positive ordered factors, the literal real bin, A_rho Psi, and the actual
rough/prime full-cell tests. No least-prime equality is built into this source. -/
def parityOriginalSieveUnbalancedBinSource434
    (proxyM proxyN : Bool) (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (S gamma gamma' : ℝ) (Y : ℕ) : ℂ :=
  parityOriginalParityBilinearSource434 d L rho Psi
    (Finset.Icc 1 (Y+2))
    ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma gamma'))
    (parityOriginalFullCellCoefficient434 proxyM false L S gamma 1 (Y+2))
    (parityOriginalFullCellCoefficient434 proxyN true L S gamma 1 (Y+2)) Y

/-- The original positive ORDERED balanced factor source; the diagonal is retained. -/
def balancedFactorSum
    (proxyM proxyN : Bool) (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (S gamma kappa : ℝ) (Y : ℕ) : ℂ :=
  parityOriginalParityBilinearSource434 d L rho Psi
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    (parityOriginalFullCellCoefficient434 proxyM true L S gamma 1 (Y+2))
    (parityOriginalFullCellCoefficient434 proxyN true L S gamma 1 (Y+2)) Y

/-- Literal weighted least-prime composite mass for one original bin. -/
def parityOriginalUnbalancedLeastPrimeMass434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (gamma gamma' : ℝ) (Y : ℕ) : ℝ :=
  ∑ u ∈ (Finset.range (Y+1)).filter
    (fun u => ¬(u+2).Prime ∧ parityOriginalExponentBin434 L gamma gamma' (u+2).minFac),
      parityWeight d L rho u * Psi ((u:ℝ)/Real.exp L)

/-- Literal residual composite mass after the unbalanced least-prime region. -/
def balancedCompositeMass
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (kappa : ℝ) (Y : ℕ) : ℝ :=
  ∑ u ∈ (Finset.range (Y+1)).filter
    (fun u => ¬(u+2).Prime ∧
      Real.exp (((1/2:ℝ)-kappa)*L)<((u+2).minFac:ℝ)),
      parityWeight d L rho u * Psi ((u:ℝ)/Real.exp L)

/-- Taking the real part is exact for genuine real source coefficients. -/
theorem parity_original_parity_source_real_coeff_re434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (alpha beta : ℕ → ℝ) (Y : ℕ) :
    (parityOriginalParityBilinearSource434 d L rho Psi K J
      (fun m => (alpha m:ℂ)) (fun n => (beta n:ℂ)) Y).re =
      ∑ u ∈ Finset.range (Y+1),
        (parityWeight d L rho u * Psi ((u:ℝ)/Real.exp L)) *
          ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, alpha z.1*beta z.2 := by
  have h : parityOriginalParityBilinearSource434 d L rho Psi K J
      (fun m => (alpha m:ℂ)) (fun n => (beta n:ℂ)) Y =
      ((∑ u ∈ Finset.range (Y+1),
        (parityWeight d L rho u * Psi ((u:ℝ)/Real.exp L)) *
          ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, alpha z.1*beta z.2 : ℝ):ℂ) := by
    unfold parityOriginalParityBilinearSource434
    push_cast
    rfl
  rw [h]
  rfl

/-- Source-exact real form of the original unbalanced sharp test sum. -/
theorem parity_original_unbalanced_sharp_source_re434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (S gamma gamma' : ℝ) (Y : ℕ) :
    (parityOriginalSieveUnbalancedBinSource434 false false d L rho Psi S gamma gamma' Y).re =
      ∑ u ∈ Finset.range (Y+1),
        (parityWeight d L rho u * Psi ((u:ℝ)/Real.exp L)) *
          ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434
            (Finset.Icc 1 (Y+2))
            ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma gamma')) u,
              sourceD19RoughTest ((Real.exp L)^gamma) z.1 *
                (if z.2.Prime then (1:ℝ) else 0) := by
  unfold parityOriginalSieveUnbalancedBinSource434
  have h := parity_original_parity_source_coeff_congr434 d L rho Psi
    (Finset.Icc 1 (Y+2))
    ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma gamma'))
    (parityOriginalFullCellCoefficient434 false false L S gamma 1 (Y+2))
    (parityOriginalFullCellCoefficient434 false true L S gamma 1 (Y+2))
    (fun m => (sourceD19RoughTest ((Real.exp L)^gamma) m:ℂ))
    (fun n => Complex.ofReal (if n.Prime then (1:ℝ) else 0)) Y
    (by intro m hm; simp [parityOriginalFullCellCoefficient434,
      parityOriginalActualFullCellSharpTest434,hm])
    (by intro n hn; have hn' := (Finset.mem_filter.mp hn).1
        by_cases hp : n.Prime <;> simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellSharpTest434,hn',hp])
  rw [h,parity_original_parity_source_real_coeff_re434]

/-- Source-exact real form of the original balanced ordered prime-pair sum. -/
theorem parity_original_balanced_sharp_source_re434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ) (S gamma kappa : ℝ) (Y : ℕ) :
    (balancedFactorSum false false d L rho Psi S gamma kappa Y).re =
      ∑ u ∈ Finset.range (Y+1),
        (parityWeight d L rho u * Psi ((u:ℝ)/Real.exp L)) *
          ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434
            ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
            ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa)) u,
              (if z.1.Prime then (1:ℝ) else 0) *
                (if z.2.Prime then (1:ℝ) else 0) := by
  unfold balancedFactorSum
  have h := parity_original_parity_source_coeff_congr434 d L rho Psi
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    (parityOriginalFullCellCoefficient434 false true L S gamma 1 (Y+2))
    (parityOriginalFullCellCoefficient434 false true L S gamma 1 (Y+2))
    (fun m => Complex.ofReal (if m.Prime then (1:ℝ) else 0))
    (fun n => Complex.ofReal (if n.Prime then (1:ℝ) else 0)) Y
    (by intro m hm; have hm' := (Finset.mem_filter.mp hm).1
        by_cases hp : m.Prime <;> simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellSharpTest434,hm',hp])
    (by intro n hn; have hn' := (Finset.mem_filter.mp hn).1
        by_cases hp : n.Prime <;> simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellSharpTest434,hn',hp])
  rw [h,parity_original_parity_source_real_coeff_re434]

/-- The actual section 8.3 composite mass is DOMINATED by the literal rough/prime
source. The proof constructs the least-prime pair; other divisors remain positive
overcounting. Repeated prime factors require no exception. -/
theorem parity_original_unbalanced_composite_mass_le_source434
    (d : ℕ) (L rho : ℝ) (hRho : |rho|≤1)
    (Psi : ℝ → ℝ) (hPsiPos : ∀t,0≤Psi t)
    (S gamma gamma' : ℝ) (Y : ℕ) :
    parityOriginalUnbalancedLeastPrimeMass434 d L rho Psi gamma gamma' Y ≤
      (parityOriginalSieveUnbalancedBinSource434 false false
        d L rho Psi S gamma gamma' Y).re := by
  classical
  rw [parity_original_unbalanced_sharp_source_re434]
  unfold parityOriginalUnbalancedLeastPrimeMass434
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro u hu
  have huY : u≤Y := by have h := Finset.mem_range.mp hu; omega
  have hWeight : 0≤parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L) :=
    mul_nonneg (parity_original_parity_A_nonneg434 d L rho hRho u) (hPsiPos _)
  let T := parityOriginalShiftTwoPositivePairFibre434
    (Finset.Icc 1 (Y+2))
    ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma gamma')) u
  let f : ℕ×ℕ → ℝ := fun z =>
    sourceD19RoughTest ((Real.exp L)^gamma) z.1 *
      (if z.2.Prime then 1 else 0)
  have hPos : ∀z∈T,0≤f z := by
    intro z hz
    dsimp [f]
    unfold sourceD19RoughTest
    split_ifs <;> norm_num
  by_cases hSelected : ¬(u+2).Prime ∧
      parityOriginalExponentBin434 L gamma gamma' (u+2).minFac
  · rw [if_pos hSelected]
    obtain ⟨hp,hm,hprod,hmin,hmUpper,hpUpper⟩ :=
      parity_original_composite_least_prime_factorization434 (u+2) (by omega) hSelected.1
    have hz : ((u+2)/(u+2).minFac,(u+2).minFac)∈T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,hp.pos,hprod⟩
      · exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos,by omega⟩,hSelected.2⟩
      · omega
    have hOne : f ((u+2)/(u+2).minFac,(u+2).minFac)=1 := by
      dsimp [f]
      rw [parity_original_unbalanced_minfac_rough_test_one434
        (u+2) (by omega) hSelected.1 L gamma hSelected.2.1]
      simp [hp]
    have hSum : 1≤∑z∈T,f z := by
      rw [←hOne]
      exact Finset.single_le_sum hPos hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSum hWeight
  · rw [if_neg hSelected]
    exact mul_nonneg hWeight (Finset.sum_nonneg hPos)

/-- The actual section 8.4 residual composite mass is dominated by the positive
ordered prime-pair source on B_kappa, including its diagonal. -/
theorem parity_eventually_original_balanced_composite_mass_le_source434
    (kappa : ℝ) (hkappa : 0<kappa) (hkappaSmall : kappa<(1/50:ℝ))
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t,0≤Psi t) :
    ∀ᶠ L : ℝ in atTop, ∀ (d Y : ℕ) (rho S gamma : ℝ), |rho|≤1 →
      balancedCompositeMass d L rho Psi kappa Y ≤
        (balancedFactorSum false false d L rho Psi S gamma kappa Y).re := by
  classical
  filter_upwards [parity_eventually_original_balanced_composite_prime_pair434
    kappa hkappa hkappaSmall Psi hPsi] with L hPairs
  intro d Y rho S gamma hRho
  rw [parity_original_balanced_sharp_source_re434]
  unfold balancedCompositeMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro u hu
  have huY : u≤Y := by have h := Finset.mem_range.mp hu; omega
  have hWeight : 0≤parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L) :=
    mul_nonneg (parity_original_parity_A_nonneg434 d L rho hRho u) (hPsiPos _)
  let T := parityOriginalShiftTwoPositivePairFibre434
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa))
    ((Finset.Icc 1 (Y+2)).filter (balancedFactor L kappa)) u
  let f : ℕ×ℕ → ℝ := fun z =>
    (if z.1.Prime then 1 else 0)*(if z.2.Prime then 1 else 0)
  have hPos : ∀z∈T,0≤f z := by
    intro z hz
    dsimp [f]
    split_ifs <;> norm_num
  by_cases hSelected : ¬(u+2).Prime ∧
      Real.exp (((1/2:ℝ)-kappa)*L)<((u+2).minFac:ℝ)
  · rw [if_pos hSelected]
    by_cases hZero : Psi ((u:ℝ)/Real.exp L)=0
    · simp [hZero]
    · obtain ⟨m,n,hm,hn,hprod,hBalM,hBalN⟩ := hPairs u hZero hSelected.1 hSelected.2
      have hmN : m≤u+2 := by
        have hh := Nat.mul_le_mul_left m hn.pos
        simpa [hprod] using hh
      have hnN : n≤u+2 := by
        have hh := Nat.mul_le_mul_right n hm.pos
        simpa [hprod] using hh
      have hz : (m,n)∈T := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hm.pos,hn.pos,hprod⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm.pos,by omega⟩,hBalM⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn.pos,by omega⟩,hBalN⟩
      have hOne : f (m,n)=1 := by simp [f,hm,hn]
      have hSum : 1≤∑z∈T,f z := by
        rw [←hOne]
        exact Finset.single_le_sum hPos hz
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hSum hWeight
  · rw [if_neg hSelected]
    exact mul_nonneg hWeight (Finset.sum_nonneg hPos)
end Green64Analytic.Parity

end

end

/-! ## OriginalSieveRectangleCarriers -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Restricting the large factor to its lower source range is exact for ANY
coefficients, including both nonsmooth proxies. It follows from mn=u+2 and
the same nonzero compact Psi, not from the support of a sharp test. -/
theorem parity_original_unbalanced_bin_source_trim_large_factor434
    (d : ℕ) (L rho b1 kappa gamma gamma' : ℝ) (hL : 0≤L)
    (hkappa : 0≤kappa) (hb1 : b1≤(1/2:ℝ)-kappa)
    (hGamma : b1≤gamma) (hGamma' : gamma'≤(1/2:ℝ)-kappa)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L rho Psi
      (Finset.Icc 1 (Y+2))
      ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma gamma'))
      alpha beta Y =
    parityOriginalParityBilinearSource434 d L rho Psi
      (Finset.Icc (max 1 ⌈Real.exp (b1*L)⌉₊) (Y+2))
      ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma gamma'))
      alpha beta Y := by
  classical
  unfold parityOriginalParityBilinearSource434
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hZero : Psi ((u:ℝ)/Real.exp L)=0
  · simp [hZero]
  · congr 1
    apply Finset.sum_congr
    · ext ⟨m,n⟩
      constructor
      · intro hz
        obtain ⟨hprod,hmpos,hnpos,hEq⟩ := Finset.mem_filter.mp hz
        obtain ⟨hm,hn⟩ := Finset.mem_product.mp hprod
        have hBin := (Finset.mem_filter.mp hn).2
        have hLower : Real.exp (b1*L)≤(n:ℝ) :=
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hGamma hL)).trans hBin.1.le
        have hUpper : (n:ℝ)≤Real.exp (((1/2:ℝ)-kappa)*L) :=
          hBin.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hGamma' hL))
        have hM := (parity_original_unbalanced_true_physical_factor_range434
          L b1 kappa Psi hL hPsi m n u hEq hZero hLower hUpper).1
        have hMlow : Real.exp (b1*L)≤(m:ℝ) :=
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hL)).trans hM
        have hm' : m∈Finset.Icc (max 1 ⌈Real.exp (b1*L)⌉₊) (Y+2) :=
          Finset.mem_Icc.mpr ⟨max_le hmpos (Nat.ceil_le.mpr hMlow),(Finset.mem_Icc.mp hm).2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm',hn⟩,hmpos,hnpos,hEq⟩
      · intro hz
        obtain ⟨hprod,hmpos,hnpos,hEq⟩ := Finset.mem_filter.mp hz
        obtain ⟨hm,hn⟩ := Finset.mem_product.mp hprod
        have hm' : m∈Finset.Icc 1 (Y+2) :=
          Finset.mem_Icc.mpr ⟨hmpos,(Finset.mem_Icc.mp hm).2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm',hn⟩,hmpos,hnpos,hEq⟩
    · intro z hz
      rfl

/-- The literal unbalanced bin source equals the exact integer rectangle stage
with its original full-cell values. All three replacement stages use this identity. -/
theorem parity_original_sieve_unbalanced_bin_eq_rectangle434
    (proxyM proxyN : Bool) (d : ℕ) (L rho b1 kappa gamma gamma' : ℝ) (hL : 0≤L)
    (hkappa : 0≤kappa) (hb1 : b1≤(1/2:ℝ)-kappa)
    (hGamma : b1≤gamma) (hGamma' : gamma'≤(1/2:ℝ)-kappa)
    (Psi : ℝ → ℝ) (hPsi : Function.support Psi ⊆ Set.Icc 1 2)
    (S : ℝ) (Y : ℕ) :
    parityOriginalSieveUnbalancedBinSource434 proxyM proxyN d L rho Psi S gamma gamma' Y =
      parityOriginalFullCellPairStage434 proxyM proxyN false true
        d L rho Psi S gamma gamma
        (max 1 ⌈Real.exp (b1*L)⌉₊) (Y+2)
        (max 1 (⌊Real.exp (gamma*L)⌋₊+1))
        (min (Y+2) ⌊Real.exp (gamma'*L)⌋₊) Y := by
  unfold parityOriginalSieveUnbalancedBinSource434 parityOriginalFullCellPairStage434
  rw [parity_original_unbalanced_bin_source_trim_large_factor434
    d L rho b1 kappa gamma gamma' hL hkappa hb1 hGamma hGamma' Psi hPsi]
  rw [parity_original_exponent_bin_filter_Icc_exact434]
  apply parity_original_parity_source_coeff_congr434
  · intro m hm
    exact parity_original_fullcell_coefficient_nested_eq434 proxyM false L S gamma
      1 (Y+2) _ _ m (le_max_left _ _) le_rfl hm
  · intro n hn
    exact parity_original_fullcell_coefficient_nested_eq434 proxyN true L S gamma
      1 (Y+2) _ _ n (le_max_left _ _) (min_le_left _ _) hn

/-- Exact closed balanced rectangle for every original sharp/proxy stage. -/
theorem parity_original_sieve_balanced_eq_rectangle434
    (proxyM proxyN : Bool) (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (S gamma kappa : ℝ) (Y : ℕ) :
    balancedFactorSum proxyM proxyN d L rho Psi S gamma kappa Y =
      parityOriginalFullCellPairStage434 proxyM proxyN true true
        d L rho Psi S gamma gamma
        (max 1 ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊)
        (min (Y+2) ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊)
        (max 1 ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊)
        (min (Y+2) ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊) Y := by
  unfold balancedFactorSum parityOriginalFullCellPairStage434
  rw [parity_original_balanced_filter_Icc_exact434]
  apply parity_original_parity_source_coeff_congr434
  · intro m hm
    exact parity_original_fullcell_coefficient_nested_eq434 proxyM true L S gamma
      1 (Y+2) _ _ m (le_max_left _ _) (min_le_left _ _) hm
  · intro n hn
    exact parity_original_fullcell_coefficient_nested_eq434 proxyN true L S gamma
      1 (Y+2) _ _ n (le_max_left _ _) (min_le_left _ _) hn

/-- Actual u-cap makes every possible positive shifted factor fit the analytic upper gate. -/
theorem parity_original_shifted_factor_cap_le_exp_two_L434
    (L : ℝ) (hL : 8≤L) :
    ((⌊2*Real.exp L⌋₊+2:ℕ):ℝ)≤Real.exp (2*L) := by
  have hFloor := Nat.floor_le (by positivity : 0≤2*Real.exp L)
  have hx : 4≤Real.exp L := by nlinarith [Real.add_one_le_exp L]
  have hExp : Real.exp (2*L)=Real.exp L*Real.exp L := by
    rw [show 2*L=L+L by ring,Real.exp_add]
  rw [hExp]
  push_cast
  nlinarith

/-- Literal bin endpoints satisfy the required full-cell lower and upper gates.
There is no free dyadic admissibility assumption here. -/
theorem parity_original_unbalanced_bin_rectangle_endpoints434
    (L b1 gamma gamma' : ℝ) (hL : 8≤L) (hb1 : 0<b1) (hGamma : b1≤gamma) :
    let Y := ⌊2*Real.exp L⌋₊
    Real.exp (2*(b1/3)*L)≤((max 1 ⌈Real.exp (b1*L)⌉₊:ℕ):ℝ) ∧
    Real.exp (2*(b1/3)*L)≤((max 1 (⌊Real.exp (gamma*L)⌋₊+1):ℕ):ℝ) ∧
    ((Y+2:ℕ):ℝ)≤Real.exp (2*L) ∧
    ((min (Y+2) ⌊Real.exp (gamma'*L)⌋₊:ℕ):ℝ)≤Real.exp (2*L) := by
  dsimp only
  have hL0 : 0≤L := by linarith
  have hExp : Real.exp (2*(b1/3)*L)≤Real.exp (b1*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hL0)
  have ha : Real.exp (b1*L)≤((max 1 ⌈Real.exp (b1*L)⌉₊:ℕ):ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈Real.exp (b1*L)⌉₊)
  have hFloor : Real.exp (gamma*L)≤((⌊Real.exp (gamma*L)⌋₊+1:ℕ):ℝ) := by
    have h := (Nat.lt_floor_add_one (Real.exp (gamma*L))).le
    simpa using h
  have hc : Real.exp (b1*L)≤((max 1 (⌊Real.exp (gamma*L)⌋₊+1):ℕ):ℝ) :=
    ((Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hGamma hL0)).trans hFloor).trans
      (by exact_mod_cast le_max_right 1 (⌊Real.exp (gamma*L)⌋₊+1))
  have hCap := parity_original_shifted_factor_cap_le_exp_two_L434 L hL
  refine ⟨hExp.trans ha,hExp.trans hc,hCap,?_⟩
  have hh : ((min (⌊2*Real.exp L⌋₊+2) ⌊Real.exp (gamma'*L)⌋₊:ℕ):ℝ) ≤
      ((⌊2*Real.exp L⌋₊+2:ℕ):ℝ) := by
    exact_mod_cast (min_le_left (⌊2*Real.exp L⌋₊+2) (⌊Real.exp (gamma'*L)⌋₊))
  exact hh.trans hCap

/-- The source choices b1<1/100 and kappa<1/50 imply every balanced endpoint gate. -/
theorem parity_original_balanced_rectangle_endpoints434
    (L b1 kappa : ℝ) (hL : 8≤L)
    (hb1 : 0<b1) (hb1Small : b1<(1/100:ℝ)) (hkappaSmall : kappa<(1/50:ℝ)) :
    let Y := ⌊2*Real.exp L⌋₊
    Real.exp (2*(b1/3)*L)≤
      ((max 1 ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊:ℕ):ℝ) ∧
    ((min (Y+2) ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊:ℕ):ℝ)≤Real.exp (2*L) := by
  dsimp only
  have hL0 : 0≤L := by linarith
  have hGap : 2*(b1/3)≤(1/2:ℝ)-2*kappa := by linarith
  have ha : Real.exp (2*(b1/3)*L)≤
      Real.exp (((1/2:ℝ)-2*kappa)*L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hGap hL0)
  refine ⟨ha.trans ((Nat.le_ceil _).trans
    (by exact_mod_cast le_max_right 1 ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊)),?_⟩
  have hh : ((min (⌊2*Real.exp L⌋₊+2) ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊:ℕ):ℝ) ≤
      ((⌊2*Real.exp L⌋₊+2:ℕ):ℝ) := by
    exact_mod_cast (min_le_left (⌊2*Real.exp L⌋₊+2) (⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊))
  exact hh.trans (parity_original_shifted_factor_cap_le_exp_two_L434 L hL)
end Green64Analytic.Parity

end

end

/-! ## OriginalSieveExternalLedger -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32000

/-- Exact source factor exchange; there is no half factor in an ordered pair sum. -/
theorem parity_original_parity_source_swap_factors434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (alpha beta : ℕ → ℂ) (Y : ℕ) :
    parityOriginalParityBilinearSource434 d L rho Psi K J alpha beta Y =
      parityOriginalParityBilinearSource434 d L rho Psi J K beta alpha Y := by
  unfold parityOriginalParityBilinearSource434
  apply Finset.sum_congr rfl
  intro u hu
  rw [parity_original_positive_shifted_fibre_swap_factors434]

theorem parity_original_fullcell_pair_stage_swap434
    (pm pn primeM primeN : Bool) (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (S gm gn : ℝ) (a b c e Y : ℕ) :
    parityOriginalFullCellPairStage434 pm pn primeM primeN d L rho Psi S gm gn a b c e Y =
      parityOriginalFullCellPairStage434 pn pm primeN primeM d L rho Psi S gn gm c e a b Y := by
  unfold parityOriginalFullCellPairStage434
  exact parity_original_parity_source_swap_factors434 d L rho Psi _ _ _ _ Y

/-- Both sequential replacement orders on one source, all four norms explicitly paid. -/
def parityOriginalTwoOrdersProxyError434 (s : Bool → Bool → ℂ) : ℝ :=
  ‖s false false-s true false‖ + ‖s true false-s true true‖ +
    ‖s false false-s false true‖ + ‖s false true-s true true‖

/-- The exact finite extraction regions: one actual source for every fixed bin,
and the one balanced ordered-pair source. -/
def parityOriginalSieveRegionStage434
    (pm pn : Bool) (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (S b1 kappa : ℝ) (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) (region : Option (Fin N)) : ℂ :=
  match region with
  | none => balancedFactorSum pm pn d L rho Psi S b1 kappa Y
  | some i => parityOriginalSieveUnbalancedBinSource434 pm pn d L rho Psi S (t i) (t (i+1)) Y

/-- The errors actually used by sections 8.3 and 8.4, for BOTH parity signs:
one rough-on-m replacement per bin, and two balanced replacements. -/
def requiredProxyError
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (S b1 kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ sign : Bool, (
    (∑ i : Fin N,
      ‖parityOriginalSieveUnbalancedBinSource434 false false d L (if sign then 1 else -1)
          Psi S (t i) (t (i+1)) Y -
        parityOriginalSieveUnbalancedBinSource434 true false d L (if sign then 1 else -1)
          Psi S (t i) (t (i+1)) Y‖) +
    ‖balancedFactorSum false false d L (if sign then 1 else -1) Psi S b1 kappa Y -
      balancedFactorSum true false d L (if sign then 1 else -1) Psi S b1 kappa Y‖ +
    ‖balancedFactorSum true false d L (if sign then 1 else -1) Psi S b1 kappa Y -
      balancedFactorSum true true d L (if sign then 1 else -1) Psi S b1 kappa Y‖)

/-- Stronger ledger: both steps in BOTH factor orders for every actual source region
and BOTH parity signs. This deliberately counts more than the extraction needs. -/
def allOrdersProxyError
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (S b1 kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ sign : Bool, ∑ region : Option (Fin N),
    parityOriginalTwoOrdersProxyError434 (fun pm pn =>
      parityOriginalSieveRegionStage434 pm pn d L (if sign then 1 else -1)
        Psi S b1 kappa N t Y region)

/-- Actual source quarter-dyadic family of each original region, independent of all tests. -/
def parityOriginalSieveRegionDyads434
    (L b1 kappa : ℝ) (N : ℕ) (t : ℕ → ℝ) (Y : ℕ)
    (region : Option (Fin N)) : Finset (ℕ×ℕ) :=
  match region with
  | none => parityOriginalSourceRectangleDyads434 L
      (max 1 ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊)
      (min (Y+2) ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊)
      (max 1 ⌈Real.exp (((1/2:ℝ)-2*kappa)*L)⌉₊)
      (min (Y+2) ⌊Real.exp (((1/2:ℝ)+2*kappa)*L)⌋₊) Y
  | some i => parityOriginalSourceRectangleDyads434 L
      (max 1 ⌈Real.exp (b1*L)⌉₊) (Y+2)
      (max 1 (⌊Real.exp (t i*L)⌋₊+1))
      (min (Y+2) ⌊Real.exp (t (i+1)*L)⌋₊) Y

/-- Explicit external labels: parity sign, factor order, actual bin/balanced region,
and one of its actually attained physical quarter dyads. -/
def parityOriginalSieveExternalDyads434
    (L b1 kappa : ℝ) (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    Finset (Σ _q : Bool × Bool × Option (Fin N), ℕ×ℕ) :=
  Finset.univ.sigma (fun q =>
    parityOriginalSieveRegionDyads434 L b1 kappa N t Y q.2.2)

/-- The external family count is derived for the literal source labels; no arbitrary
beta/fine-interval family is hidden in this number. Full cells are inside coefficients. -/
theorem parity_original_sieve_external_dyads_card434
    (L b1 kappa : ℝ) (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    (parityOriginalSieveExternalDyads434 L b1 kappa N t Y).card ≤
      4*(N+1)*((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1)) := by
  classical
  unfold parityOriginalSieveExternalDyads434
  rw [Finset.card_sigma]
  calc
    _ ≤ ∑ _q : Bool × Bool × Option (Fin N),
        (Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1) := by
      apply Finset.sum_le_sum
      intro q hq
      rcases q with ⟨sign,orientation,region⟩
      cases region <;> exact parity_original_source_rectangle_dyads_card434 L _ _ _ _ Y
    _ = _ := by simp; ring

/-- Complete error ledger for the actual h=-2 Parity bin and balanced sources.
All first and nonsmooth-second replacements in both orders and parity branches are
proved from the actual analytic source, with fixed finite external bins and exact
physical quarter-dyadic counts. No source mass lower bound is presumed. -/
theorem parity_eventually_original_sieve_all_proxy_errors434
    (N : ℕ) (b1 kappa : ℝ) (hb1 : 0<b1) (hb1Small : b1<(1/100:ℝ))
    (hkappa : 0<kappa) (hkappaSmall : kappa<(1/50:ℝ))
    (jQ : ℕ) (goal target C0 beta betaP K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤(b1/3))
    (hBeta : beta≤2*(b1/3))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : (goal+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S C : ℝ, 2*((B:ℝ)+1)+3<S ∧ 0<C ∧
      ∀ (t : ℕ → ℝ), Monotone t → t 0=b1 → t N=(1/2:ℝ)-kappa →
      ∀ᶠ L : ℝ in atTop,
        let d := sourceOriginalLiteralDepth 20 L
        let Y := ⌊2*Real.exp L⌋₊
        let Q := C*
          (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)*Real.exp L*L^(-goal)
        requiredProxyError d L Psi S b1 kappa N t Y ≤
          2*((N:ℝ)+3)*Q ∧
        allOrdersProxyError d L Psi S b1 kappa N t Y ≤
          12*((N:ℝ)+1)*Q := by
  obtain ⟨H,J,B,S,hBS,hSource⟩ :=
    parity_eventually_original_both_parity_full_rectangles_proxy_steps434
      (ι := Option (Fin N)) jQ goal target C0 beta betaP (b1/3) K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  let C1 := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 1
  let Cmoment := parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport 0
  let Cphys := 1000*(1+2/Real.log 2)*(Cmoment+132*C1)
  let Csource := 1+24*(2+Cphys+24*C1)
  let M_H := ∫s : ℝ, ‖s‖^H *
    ‖(𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖
  let Kfix := (1+2/Real.log 2)^2*
    (4+Csource*(∫s : ℝ,
      ‖(𝓕 (parityOriginalLogCutoff434
        (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
        20*(2*Real.pi)^H*M_H)
  let C := |Kfix|+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨H,J,B,S,C,hBS,hC,?_⟩
  intro t ht hFirst hLast
  let gamma : Option (Fin N) → ℝ := fun r =>
    match r with | none => b1 | some i => t i
  have hgamma : ∀r,0<gamma r := by
    intro r
    cases r with
    | none => exact hb1
    | some i =>
        have hh : b1≤t i := by simpa only [hFirst] using ht (Nat.zero_le i.val)
        exact hb1.trans_le hh
  filter_upwards [hSource gamma gamma hgamma hgamma] with L hAll
  have h8 : 8≤L := by have hh := (hAll none).2.1; linarith
  have hL : 0≤L := by linarith
  let Y := ⌊2*Real.exp L⌋₊
  let d := sourceOriginalLiteralDepth 20 L
  let D : ℝ := (((Nat.log 2 (Y+2)+1)*(Nat.log 2 (Y+2)+1):ℕ):ℝ)
  let Q := C*D*Real.exp L*L^(-goal)
  have hCoef : Kfix≤C := by
    dsimp only [C]
    linarith [le_abs_self Kfix]
  have hBound : D*((1+2/Real.log 2)^2*
      ((4+Csource*(∫s : ℝ,
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
          20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal))) ≤ Q := by
    have hh := mul_le_mul_of_nonneg_right hCoef
      (show 0≤D*Real.exp L*L^(-goal) by dsimp [D]; positivity)
    calc
      _ = Kfix*D*Real.exp L*L^(-goal) := by dsimp only [Kfix]; ring
      _ ≤ C*D*Real.exp L*L^(-goal) := by nlinarith [hh]
      _ = Q := rfl
  have hRect : ∀ (r : Option (Fin N)) (a b c e : ℕ),
      Real.exp (2*(b1/3)*L)≤(a:ℝ) →
      Real.exp (2*(b1/3)*L)≤(c:ℝ) →
      (b:ℝ)≤Real.exp (2*L) → (e:ℝ)≤Real.exp (2*L) →
      ∀ (p q : Bool) (rho : ℝ), rho=1 ∨ rho=(-1) →
      let src := fun pm pn => parityOriginalFullCellPairStage434 pm pn p q
        d L rho Psi S (gamma r) (gamma r) a b c e Y
      ‖src false false-src true false‖≤Q ∧
      ‖src true false-src true true‖≤2*Q ∧
      ‖src false false-src false true‖≤Q ∧
      ‖src false true-src true true‖≤2*Q := by
    intro r a b c e ha hc hb he p q rho hSigns
    have hRest := (hAll r).2.2.2.2.2
    have hf := hRest a b c e Y ha hc hb he rfl p q rho hSigns
    have hr := hRest c e a b Y hc ha he hb rfl q p rho hSigns
    let src := fun pm pn => parityOriginalFullCellPairStage434 pm pn p q
      d L rho Psi S (gamma r) (gamma r) a b c e Y
    let raw := D*((1+2/Real.log 2)^2*
      ((4+Csource*(∫s : ℝ,
        ‖(𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hPsiSmooth hPsiSupport) : 𝓢(ℝ,ℂ)) s‖) +
          20*(2*Real.pi)^H*M_H)*Real.exp L*L^(-goal)))
    have hf' : ‖src false false-src true false‖≤ raw ∧
        ‖src true false-src true true‖≤2*raw := by
      simpa only [src,raw,D,Y,d,C1,Cmoment,Cphys,Csource,M_H,
        parityOriginalFullCellPairStage434,parityOriginalFullCellCoefficient434,
        Bool.false_eq_true,ite_false,ite_true] using And.intro hf.1 hf.2.1
    have hr' :
        ‖parityOriginalFullCellPairStage434 false false q p d L rho Psi S
            (gamma r) (gamma r) c e a b Y -
          parityOriginalFullCellPairStage434 true false q p d L rho Psi S
            (gamma r) (gamma r) c e a b Y‖≤ raw ∧
        ‖parityOriginalFullCellPairStage434 true false q p d L rho Psi S
            (gamma r) (gamma r) c e a b Y -
          parityOriginalFullCellPairStage434 true true q p d L rho Psi S
            (gamma r) (gamma r) c e a b Y‖≤2*raw := by
      simpa only [raw,D,Y,d,C1,Cmoment,Cphys,Csource,M_H,
        parityOriginalFullCellPairStage434,parityOriginalFullCellCoefficient434,
        Bool.false_eq_true,ite_false,ite_true] using And.intro hr.1 hr.2.1
    rw [parity_original_fullcell_pair_stage_swap434 false false q p,
      parity_original_fullcell_pair_stage_swap434 true false q p,
      parity_original_fullcell_pair_stage_swap434 true true q p] at hr'
    change ‖src false false-src true false‖≤Q ∧
      ‖src true false-src true true‖≤2*Q ∧
      ‖src false false-src false true‖≤Q ∧
      ‖src false true-src true true‖≤2*Q
    exact ⟨hf'.1.trans hBound,hf'.2.trans (by linarith),
      hr'.1.trans hBound,hr'.2.trans (by linarith)⟩
  have hRegions : ∀ (r : Option (Fin N)) (rho : ℝ), rho=1 ∨ rho=(-1) →
      let src := fun pm pn =>
        parityOriginalSieveRegionStage434 pm pn d L rho Psi S b1 kappa N t Y r
      ‖src false false-src true false‖≤Q ∧
      ‖src true false-src true true‖≤2*Q ∧
      ‖src false false-src false true‖≤Q ∧
      ‖src false true-src true true‖≤2*Q := by
    intro r rho hSigns
    cases r with
    | none =>
        have hEnd := parity_original_balanced_rectangle_endpoints434
          L b1 kappa h8 hb1 hb1Small hkappaSmall
        have hh := hRect none _ _ _ _ hEnd.1 hEnd.1 hEnd.2 hEnd.2 true true rho hSigns
        dsimp only [parityOriginalSieveRegionStage434,gamma] at hh ⊢
        simpa only [parity_original_sieve_balanced_eq_rectangle434] using hh
    | some i =>
        have hG : b1≤t i := by simpa only [hFirst] using ht (Nat.zero_le i.val)
        have hG' : t (i+1)≤(1/2:ℝ)-kappa := by
          simpa only [hLast] using ht (show i.val+1≤N by omega)
        have hBandb : b1≤(1/2:ℝ)-kappa := by linarith
        have hEnd := parity_original_unbalanced_bin_rectangle_endpoints434
          L b1 (t i) (t (i+1)) h8 hb1 hG
        have hh := hRect (some i) _ _ _ _ hEnd.1 hEnd.2.1 hEnd.2.2.1 hEnd.2.2.2
          false true rho hSigns
        dsimp only [parityOriginalSieveRegionStage434,gamma] at hh ⊢
        simpa only [parity_original_sieve_unbalanced_bin_eq_rectangle434
          _ _ d L rho b1 kappa (t i) (t (i+1)) hL hkappa.le hBandb hG hG' Psi hPsiSet]
          using hh
  have hSigns : ∀sign : Bool,(if sign then (1:ℝ) else -1)=1 ∨
      (if sign then (1:ℝ) else -1)=(-1) := by intro sign; cases sign <;> simp
  have hRequired : requiredProxyError d L Psi S b1 kappa N t Y ≤
      2*((N:ℝ)+3)*Q := by
    unfold requiredProxyError
    calc
      _ ≤ ∑ sign : Bool, ((N:ℝ)+3)*Q := by
        apply Finset.sum_le_sum
        intro sign hs
        have hSum :
            (∑ i : Fin N,
              ‖parityOriginalSieveUnbalancedBinSource434 false false d L (if sign then 1 else -1)
                  Psi S (t i) (t (i+1)) Y -
                parityOriginalSieveUnbalancedBinSource434 true false d L (if sign then 1 else -1)
                  Psi S (t i) (t (i+1)) Y‖) ≤ (N:ℝ)*Q := by
          calc
            _ ≤ ∑ _i : Fin N,Q := Finset.sum_le_sum (fun i _ =>
              (hRegions (some i) _ (hSigns sign)).1)
            _ = _ := by simp
        have hBal := hRegions none _ (hSigns sign)
        dsimp only [parityOriginalSieveRegionStage434] at hBal
        nlinarith [hSum,hBal.1,hBal.2.1]
      _ = _ := by simp; ring
  have hAllOrders : allOrdersProxyError d L Psi S b1 kappa N t Y ≤
      12*((N:ℝ)+1)*Q := by
    unfold allOrdersProxyError
    calc
      _ ≤ ∑ _sign : Bool, ∑ _r : Option (Fin N),6*Q := by
        apply Finset.sum_le_sum
        intro sign hs
        apply Finset.sum_le_sum
        intro r hr
        have hh := hRegions r _ (hSigns sign)
        unfold parityOriginalTwoOrdersProxyError434
        linarith [hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
      _ = _ := by simp; ring
  dsimp only
  exact ⟨hRequired,hAllOrders⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalSieveD230LittleO -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32000

theorem parity_original_sieve_required_proxy_error_nonneg434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (S b1 kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    0≤ requiredProxyError d L Psi S b1 kappa N t Y := by
  unfold requiredProxyError
  positivity

theorem parity_original_sieve_all_orders_proxy_error_nonneg434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (S b1 kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    0≤allOrdersProxyError d L Psi S b1 kappa N t Y := by
  unfold allOrdersProxyError parityOriginalTwoOrdersProxyError434
  positivity

/-- Fixed ORIGINAL D*=230 now controls the ACTUAL original bin/balanced total error,
with both steps, both factor orders, all physical external dyads and both signs.
The conclusion is little-o of the absolute exp(L)*L^(-222) scale. Conversion to
little-o(Xrho/L) still requires the true localized positive Xrho lower bound. -/
theorem parity_original_sieve_D230_total_proxy_error_littleO_exp222434
    (N : ℕ) (b1 kappa : ℝ) (hb1 : 0<b1) (hb1Small : b1<(1/100:ℝ))
    (hkappa : 0<kappa) (hkappaSmall : kappa<(1/50:ℝ))
    (jQ : ℕ) (target C0 beta betaP K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤(b1/3))
    (hBeta : beta≤2*(b1/3))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : ((230:ℝ)+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (t : ℕ → ℝ), Monotone t → t 0=b1 → t N=(1/2:ℝ)-kappa →
      Asymptotics.IsLittleO atTop
        (fun L : ℝ => requiredProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊)
        (fun L : ℝ => Real.exp L*L^(-(222:ℝ))) ∧
      Asymptotics.IsLittleO atTop
        (fun L : ℝ => allOrdersProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊)
        (fun L : ℝ => Real.exp L*L^(-(222:ℝ))) := by
  obtain ⟨H,J,B,S,C,hBS,hC,hSource⟩ :=
    parity_eventually_original_sieve_all_proxy_errors434
      N b1 kappa hb1 hb1Small hkappa hkappaSmall
      jQ 230 target C0 beta betaP K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  refine ⟨H,J,B,S,hBS,?_⟩
  intro t ht hFirst hLast
  have hSourceT := hSource t ht hFirst hLast
  have hSmall : ∀ eps : ℝ,0<eps →
      ∀ᶠ L : ℝ in atTop,
        requiredProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊ ≤
          eps*(Real.exp L*L^(-(222:ℝ))) ∧
        allOrdersProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊ ≤
          eps*(Real.exp L*L^(-(222:ℝ))) := by
    intro eps hEps
    have hNum := parity_eventually_original_source_D230_160_quarter_vs_Xrho221434
      (12*((N:ℝ)+1)*C/160) eps (by positivity) hEps
    filter_upwards [hSourceT,hNum,eventually_ge_atTop (0:ℝ)] with L hS hN hL
    let D : ℝ := (((Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1)*
      (Nat.log 2 (⌊2*Real.exp L⌋₊+2)+1):ℕ):ℝ)
    let Q := C*D*Real.exp L*L^(-(230:ℝ))
    have hQ : 0≤Q := by dsimp [Q,D]; positivity
    have hNum' : 12*((N:ℝ)+1)*Q≤eps*(Real.exp L*L^(-(222:ℝ))) := by
      have hId : 160*(12*((N:ℝ)+1)*C/160)*D*Real.exp L*L^(-(230:ℝ)) =
          12*((N:ℝ)+1)*Q := by dsimp only [Q]; ring
      change 160*(12*((N:ℝ)+1)*C/160)*D*Real.exp L*L^(-(230:ℝ)) ≤
        eps*Real.exp L*L^(-(222:ℝ)) at hN
      rw [hId] at hN
      nlinarith
    have hRequired : 2*((N:ℝ)+3)*Q≤12*((N:ℝ)+1)*Q := by
      have hCoef : 2*((N:ℝ)+3)≤12*((N:ℝ)+1) := by nlinarith [show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N]
      exact mul_le_mul_of_nonneg_right hCoef hQ
    exact ⟨hS.1.trans (hRequired.trans hNum'),hS.2.trans hNum'⟩
  constructor
  · rw [Asymptotics.isLittleO_iff]
    intro eps hEps
    filter_upwards [hSmall eps hEps,eventually_ge_atTop (0:ℝ)] with L hSmallL hL
    have hErr := parity_original_sieve_required_proxy_error_nonneg434
      (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊
    have hScale : 0≤Real.exp L*L^(-(222:ℝ)) := by positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg hErr,abs_of_nonneg hScale] using hSmallL.1
  · rw [Asymptotics.isLittleO_iff]
    intro eps hEps
    filter_upwards [hSmall eps hEps,eventually_ge_atTop (0:ℝ)] with L hSmallL hL
    have hErr := parity_original_sieve_all_orders_proxy_error_nonneg434
      (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊
    have hScale : 0≤Real.exp L*L^(-(222:ℝ)) := by positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg hErr,abs_of_nonneg hScale] using hSmallL.2
end Green64Analytic.Parity

end

end

/-! ## SourceFamiliesIntegratedAudit -/

section



end

/-! ## OriginalProxyErrorXrho -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The absolute source error scale is small relative to actual localized
X_rho/L. The required positive mass is proved here from the original cutoff,
rather than assumed as a lower-bound hypothesis. -/
theorem parity_original_littleO_exp222_to_Xrho434
    (Psi : ℝ → ℝ) (hCont : Continuous Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t, 0 ≤ Psi t)
    (hInterior : ∃ t : ℝ, 1<t ∧ t<2 ∧ 0<Psi t)
    (f : ℝ → ℝ)
    (hf : Asymptotics.IsLittleO atTop f
      (fun L : ℝ => Real.exp L*L^(-222:ℝ)))
    (rho : ℝ) (hRho : rho=1 ∨ rho=-1) :
    Asymptotics.IsLittleO atTop f
      (fun L : ℝ => localizedMass Psi rho L/L) := by
  obtain ⟨c0,hc0,hMass⟩ :=
    localizedMass_lower_bound
      Psi hCont hSupport hNonneg hInterior
  rw [Asymptotics.isLittleO_iff]
  intro eps hEps
  have hErr := Asymptotics.isLittleO_iff.mp hf (mul_pos hEps hc0)
  filter_upwards [hErr,hMass,eventually_gt_atTop (0:ℝ)] with L hE hM hL
  have hPow : L^(-222:ℝ)*L = L^(-221:ℝ) := by
    calc
      _ = L^(-222:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^((-222:ℝ)+1) := (Real.rpow_add hL _ _).symm
      _ = L^(-221:ℝ) := by norm_num
  have hLower : c0*(Real.exp L*L^(-222:ℝ)) ≤
      localizedMass Psi rho L/L := by
    apply (le_div_iff₀ hL).mpr
    have hId : c0*(Real.exp L*L^(-222:ℝ))*L =
        c0*Real.exp L*L^(-221:ℝ) := by
      calc
        _ = (c0*Real.exp L)*(L^(-222:ℝ)*L) := by ring
        _ = _ := by rw [hPow]
    rw [hId]
    exact hM rho hRho
  have hScale : 0≤Real.exp L*L^(-222:ℝ) := by positivity
  have hMassNonneg : 0≤localizedMass Psi rho L/L :=
    (mul_nonneg hc0.le hScale).trans hLower
  have hE' : ‖f L‖≤(eps*c0)*(Real.exp L*L^(-222:ℝ)) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hScale] using hE
  calc
    ‖f L‖ ≤ (eps*c0)*(Real.exp L*L^(-222:ℝ)) := hE'
    _ = eps*(c0*(Real.exp L*L^(-222:ℝ))) := by ring
    _ ≤ eps*(localizedMass Psi rho L/L) :=
      mul_le_mul_of_nonneg_left hLower hEps.le
    _ = eps*‖localizedMass Psi rho L/L‖ := by
      rw [Real.norm_eq_abs,abs_of_nonneg hMassNonneg]

/-- Parity section7.3 for the true source: both successive replacements,
both factor orientations, all admitted original bins and balanced region,
both parity signs, with one original D*=230 choice and shared H,J,B,S
chosen before the bin endpoints. The denominator is the actual finite
localized X_rho, whose positive mass has been proved above. -/
theorem parity_original_sieve_D230_total_proxy_error_littleO_Xrho434
    (N : ℕ) (b1 kappa : ℝ) (hb1 : 0<b1) (hb1Small : b1<(1/100:ℝ))
    (hkappa : 0<kappa) (hkappaSmall : kappa<(1/50:ℝ))
    (jQ : ℕ) (target C0 beta betaP K0 A R : ℝ)
    (hbetaP : 0<betaP) (hbstar : 2*betaP≤(b1/3))
    (hBeta : beta≤2*(b1/3))
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ≤betaP/4)
    (hC0 : 0<C0) (hTarget : 0≤target)
    (hK0Target : 2*target+2*parityOriginalW1PolylogExponent434+344≤K0)
    (hPrecision : ((230:ℝ)+2)+parityOriginalSelectedECoefficientPolylogExponent434+
      parityOriginalB590FixedFourierPolynomialExponent434≤target)
    (hbeta : 0<beta)
    (hK0 : 0≤K0) (hA : 0<A) (hR : 1≤R)
    (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t:ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A)
    (hOne4 : ∀t∈Set.Icc (0:ℝ) (Real.log 4),buf t=1)
    (hCube : ∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R)
    (Psi : ℝ → ℝ)
    (hPsiSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hPsiSupport : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t)
    (hPsiLe : ∀t:ℝ,Psi t≤1)
    (hPsiInterior : ∃ t : ℝ, 1<t ∧ t<2 ∧ 0<Psi t) :
    ∃ H J B : ℕ, ∃ S : ℝ, 2*((B:ℝ)+1)+3<S ∧
      ∀ (t : ℕ → ℝ), Monotone t → t 0=b1 → t N=(1/2:ℝ)-kappa →
      ∀ rho : ℝ, (rho=1 ∨ rho=-1) →
      Asymptotics.IsLittleO atTop
        (fun L : ℝ => requiredProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊)
        (fun L : ℝ => localizedMass Psi rho L/L) ∧
      Asymptotics.IsLittleO atTop
        (fun L : ℝ => allOrdersProxyError
          (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N t ⌊2*Real.exp L⌋₊)
        (fun L : ℝ => localizedMass Psi rho L/L) := by
  obtain ⟨H,J,B,S,hBS,hErrors⟩ :=
    parity_original_sieve_D230_total_proxy_error_littleO_exp222434
      N b1 kappa hb1 hb1Small hkappa hkappaSmall
      jQ target C0 beta betaP K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision
      hbeta hK0 hA hR buf hSmooth hSupport hOne4 hCube
      Psi hPsiSmooth hPsiSupport hPsiSet hPsiPos hPsiLe
  have hPsiCont : Continuous Psi := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.comp hPsiSmooth.continuous
  refine ⟨H,J,B,S,hBS,?_⟩
  intro t ht hFirst hLast rho hRho
  have hE := hErrors t ht hFirst hLast
  constructor
  · exact parity_original_littleO_exp222_to_Xrho434
      Psi hPsiCont hPsiSet hPsiPos hPsiInterior _ hE.1 rho hRho
  · exact parity_original_littleO_exp222_to_Xrho434
      Psi hPsiCont hPsiSet hPsiPos hPsiInterior _ hE.2 rho hRho
end Green64Analytic.Parity

end

end

/-! ## OriginalNegativeCongruence -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000

/-- Actual source congruence error for the shifted equation p=u+2.
The main term is the very same finite X_rho divided by phi(d). -/
def parityOriginalCongruenceRemainder434
    (Psi : ℝ → ℝ) (rho L : ℝ) (d : ℕ) : ℝ :=
  (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
    if d ∣ u+2 then
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u *
        Psi ((u:ℝ)/Real.exp L) else 0) -
    localizedMass Psi rho L/(d.totient:ℝ)

def parityOriginalCongruenceTotalError434
    (Psi : ℝ → ℝ) (rho theta L : ℝ) : ℝ :=
  ∑ d ∈ (Finset.range (⌊(Real.exp L)^theta⌋₊+1)).filter
    (fun d => Odd d ∧ Squarefree d),
    |parityOriginalCongruenceRemainder434 Psi rho L d|

/-- Exact finite-source equality with the independently checked native
Parity5.2 remainder. In particular the residue is -2, not a retuned mask. -/
theorem parity_original_negative_congruence_remainder_eq434
    (Psi : ℝ → ℝ) (L : ℝ) (d : ℕ) :
    parityOriginalCongruenceRemainder434 Psi (-1) L d =
      sourceShiftTwoRemainder 20 Psi L d := by
  unfold parityOriginalCongruenceRemainder434 sourceShiftTwoRemainder
    sourceShiftTwoDivisorMass sourceOriginalMovingWeight
  rw [parity_original_minus_Xrho_eq_original_XA434]
  simp only [parity_original_minus_parity_A_eq_original_A434]

/-- Genuine native odd-source congruence distribution specialized at D=230.
No character, distribution, or desired mass assumption is introduced. -/
theorem parity_original_negative_congruence_D230_bound434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (theta : ℝ) (hTheta : 0<theta) (hThetaUpper : theta<1/2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ L : ℝ in atTop,
      parityOriginalCongruenceTotalError434 Psi (-1) theta L ≤
      C*(Real.exp L*L^(-230:ℝ) +
        localizedMass Psi (-1) L*L^(-18:ℝ)) := by
  obtain ⟨C,hC,hBound⟩ := source_shift_two_congruence_input_unconditional
    20 (by norm_num) Psi hSmooth hSupport hNonneg
    theta 230 hTheta hThetaUpper (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hBound] with L hL
  simpa only [parityOriginalCongruenceTotalError434,
    parity_original_negative_congruence_remainder_eq434,
    parity_original_minus_Xrho_eq_original_XA434] using hL

/-- Immediate downstream consequence: the total genuine Parity5.2 remainder
over all odd squarefree d<=x^theta is o(Xminus/L), for every fixed theta<1/2.
Only the negative parity source is asserted; the positive parity
character/congruence extension remains a separate obligation. -/
theorem parity_original_negative_congruence_littleO_Xrho434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (theta : ℝ) (hTheta : 0<theta) (hThetaUpper : theta<1/2) :
    Asymptotics.IsLittleO atTop
      (fun L : ℝ => parityOriginalCongruenceTotalError434 Psi (-1) theta L)
      (fun L : ℝ => localizedMass Psi (-1) L/L) := by
  obtain ⟨C,hC,hBound⟩ :=
    parity_original_negative_congruence_D230_bound434
      Psi hSmooth hSupport hNonneg theta hTheta hThetaUpper
  obtain ⟨c0,hc0,hMass⟩ := localizedMass_lower_bound
    Psi hSmooth.continuous hSupport hNonneg hInterior
  have h8 : Tendsto (fun L : ℝ => L^(-8:ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<8)
  have h17 : Tendsto (fun L : ℝ => L^(-17:ℝ)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<17)
  have hCoef : Tendsto
      (fun L : ℝ => (C/c0)*L^(-8:ℝ)+C*L^(-17:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds.mul h8).add (tendsto_const_nhds.mul h17) :
        Tendsto (fun L : ℝ => (C/c0)*L^(-8:ℝ)+C*L^(-17:ℝ))
          atTop (𝓝 ((C/c0)*0+C*0)))
  rw [Asymptotics.isLittleO_iff]
  intro eps hEps
  have hSmall := (tendsto_order.mp hCoef).2 eps hEps
  filter_upwards [hBound,hMass,hSmall,eventually_gt_atTop (0:ℝ)]
    with L hB hM hSmallL hL
  let X := localizedMass Psi (-1) L
  have hMassL : c0*Real.exp L*L^(-221:ℝ)≤X := hM (-1) (Or.inr rfl)
  have hX : 0≤X :=
    (by positivity : 0≤ c0*Real.exp L*L^(-221:ℝ)).trans hMassL
  have hXL : 0≤X/L := div_nonneg hX hL.le
  have hPow (a b : ℝ) : L^a*L^b=L^(a+b) := (Real.rpow_add hL a b).symm
  have hProd : L^(-221:ℝ)*L^(-9:ℝ)=L^(-230:ℝ) := by
    rw [hPow];norm_num
  have hDiv9 : L^(-9:ℝ)=L^(-8:ℝ)/L := by
    apply (eq_div_iff (ne_of_gt hL)).mpr
    calc
      _ = L^(-9:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [hPow];norm_num
  have hDiv18 : L^(-18:ℝ)=L^(-17:ℝ)/L := by
    apply (eq_div_iff (ne_of_gt hL)).mpr
    calc
      _ = L^(-18:ℝ)*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [hPow];norm_num
  have hFirst : Real.exp L*L^(-230:ℝ)≤ c0⁻¹*L^(-8:ℝ)*(X/L) := by
    have hm := mul_le_mul_of_nonneg_right hMassL
      (by positivity : 0≤ c0⁻¹*L^(-9:ℝ))
    have hLeft : (c0*Real.exp L*L^(-221:ℝ))*(c0⁻¹*L^(-9:ℝ)) =
        Real.exp L*L^(-230:ℝ) := by
      calc
        _ = (c0*c0⁻¹)*Real.exp L*(L^(-221:ℝ)*L^(-9:ℝ)) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hc0),hProd];ring
    have hRight : X*(c0⁻¹*L^(-9:ℝ))=c0⁻¹*L^(-8:ℝ)*(X/L) := by
      rw [hDiv9]
      ring
    rwa [hLeft,hRight] at hm
  have hScaled : C*(Real.exp L*L^(-230:ℝ)+X*L^(-18:ℝ))≤
      ((C/c0)*L^(-8:ℝ)+C*L^(-17:ℝ))*(X/L) := by
    calc
      _ ≤ C*(c0⁻¹*L^(-8:ℝ)*(X/L)+X*L^(-18:ℝ)) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add hFirst (le_refl _)) hC
      _ = _ := by rw [hDiv18];simp only [div_eq_mul_inv];ring
  have hErrNonneg : 0≤parityOriginalCongruenceTotalError434 Psi (-1) theta L := by
    unfold parityOriginalCongruenceTotalError434
    positivity
  have hFinal : parityOriginalCongruenceTotalError434 Psi (-1) theta L≤eps*(X/L) :=
    hB.trans (hScaled.trans (mul_le_mul_of_nonneg_right hSmallL.le hXL))
  change ‖parityOriginalCongruenceTotalError434 Psi (-1) theta L‖ ≤ eps*‖X/L‖
  simpa only [Real.norm_eq_abs,abs_of_nonneg hErrNonneg,abs_of_nonneg hXL] using hFinal
end Green64Analytic.Parity

end

end

/-! ## OriginalMassIntegratedAudit -/

section

set_option pp.universes false

end

/-! ## OriginalSharpPresieve -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.Parity
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

/-- The explicit block-sieve loss at the genuine density cap C=8 and eta=1/2. -/
def parityOriginalPresieveRho434 (h : ℕ) : ℝ :=
  ((Real.exp (Real.exp 1*8)/(1-Real.exp (-1)))/Real.exp (-8/(1/2))) *
    Real.exp (-(h:ℝ))

/-- The genuine original negative-parity congruence theorem in the exact
unweighted epsilon form consumed by the initial block sieve. -/
theorem parity_original_negative_congruence_error_small434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (theta eps : ℝ) (hTheta : 0<theta) (hThetaUpper : theta<1/2)
    (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      (∑ d ∈ (Finset.range (⌊(Real.exp L)^theta⌋₊+1)).filter
        (fun d => Odd d ∧ Squarefree d), |sourceShiftTwoRemainder 20 Psi L d|) ≤
        eps * sourceOriginalXA 20
          (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
          (sourceOriginalPAllActualBands 20 L) (Real.exp L) Psi / L := by
  have hSmall := (Asymptotics.isLittleO_iff.mp
    (parity_original_negative_congruence_littleO_Xrho434
      Psi hSmooth hSupport hNonneg hInterior theta hTheta hThetaUpper)) hEps
  filter_upwards [hSmall,eventually_gt_atTop (0:ℝ)] with L hErr hL
  have hX : 0≤localizedMass Psi (-1) L := by
    rw [parity_original_minus_Xrho_eq_original_XA434]
    exact source_original_XA_nonneg _ _ _ _ _ hNonneg
  have hE : 0≤parityOriginalCongruenceTotalError434 Psi (-1) theta L := by
    unfold parityOriginalCongruenceTotalError434
    positivity
  have hXL : 0≤localizedMass Psi (-1) L/L := div_nonneg hX hL.le
  change ‖parityOriginalCongruenceTotalError434 Psi (-1) theta L‖ ≤
    eps*‖localizedMass Psi (-1) L/L‖ at hErr
  rw [Real.norm_eq_abs,abs_of_nonneg hE,Real.norm_eq_abs,abs_of_nonneg hXL] at hErr
  simpa only [parityOriginalCongruenceTotalError434,
    parity_original_negative_congruence_remainder_eq434,
    parity_original_minus_Xrho_eq_original_XA434,mul_div_assoc] using hErr

/-- Parity's actual h=-2 initial presieve, with both bounds, the full finite
Euler product, and its explicit truncation loss. Distribution and positive
mass are proved imports; no abstract sieve or remainder premise occurs.
The finite block depth is chosen after L and produces no extra error loss. -/
theorem parity_original_negative_sharp_initial_presieve434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta theta eps : ℝ) (h : ℕ)
    (hBeta : 0<beta) (hTheta : 0<theta) (hThetaUpper : theta<1/2)
    (hh : 2≤h) (hEven : Even h)
    (hLevel : beta*(4*(h:ℝ)+2)≤theta) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      let P := sourceAllOddPrimeSet ((Real.exp L)^beta)
      let X := sourceOriginalXA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) (Real.exp L) Psi
      let V := ∏ q ∈ P,(1-sourceShiftTwoLocalDensity q)
      X*V*(1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h))-
        eps*X/L ≤ sourceShiftTwoSiftedMass 20 Psi L P ∧
      sourceShiftTwoSiftedMass 20 Psi L P ≤
        X*V*Real.exp (parityOriginalPresieveRho434 h)+eps*X/L := by
  filter_upwards [parity_original_negative_congruence_error_small434
    Psi hSmooth hSupport hNonneg hInterior theta eps hTheta hThetaUpper hEps,
    eventually_gt_atTop (0:ℝ)] with L hErr hL
  let z := (Real.exp L)^beta
  have hz : 1<z := Real.one_lt_rpow (Real.one_lt_exp_iff.mpr hL) hBeta
  obtain ⟨J,hJ⟩ := source_exists_natural_halfpower_depth z hz
  let blocks := fun j : Fin J => sourceNaturalOddPrimeBlock 1 z j.val
  have hBlocks : ∀ j q,q∈blocks j → q.Prime ∧ 3≤q ∧
      z^((1/2:ℝ)^(j.val+1))<(q:ℝ) ∧ (q:ℝ)≤z^((1/2:ℝ)^j.val) := by
    intro j q hq
    have ht := source_natural_block_prime 1 z j.val q hq
    exact ⟨ht.1,source_natural_block_odd 1 z j.val q hq,ht.2⟩
  have hP : Finset.univ.biUnion blocks=sourceAllOddPrimeSet z :=
    source_natural_unit_blocks_cover_all_odd_primes J z hz hJ
  have hBound := source_shift_two_block_sieve 20 Psi L z 8 J h blocks hz hh hEven
    (by norm_num) hNonneg hBlocks
    (source_shift_two_block_local_density_le_eight z hz J blocks hBlocks)
  dsimp only at hBound
  rw [hP] at hBound
  have hZLevel : z^(4*(h:ℝ)+2)≤(Real.exp L)^theta := by
    rw [←Real.rpow_mul (Real.exp_pos L).le]
    exact Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hL.le) hLevel
  have hPrime : ∀ p∈sourceAllOddPrimeSet z,p.Prime ∧ 3≤p := by
    intro p hp
    exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
  have hSub := source_shift_two_block_divisors_in_range
    (sourceAllOddPrimeSet z) L z theta h hPrime hZLevel
  have hRaw := Finset.sum_le_sum_of_subset_of_nonneg hSub
    (fun d _ _ => abs_nonneg (sourceShiftTwoRemainder 20 Psi L d))
  have hSmall := hRaw.trans hErr
  constructor
  · exact (_root_.sub_le_sub_left hSmall _).trans hBound.1
  · exact hBound.2.trans (_root_.add_le_add (le_refl _) hSmall)
end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalConditionedBlock -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

noncomputable def parityOriginalConditionedWeight434
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (p u : ℕ) : ℝ :=
  if p ∣ u+2 then sourceOriginalMovingWeight r₀ Ψ L u else 0

noncomputable def parityOriginalConditionedMass434
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (p : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
    if p ∣ u+2 ∧ ∀ q ∈ P, ¬q ∣ u+2 then sourceOriginalMovingWeight r₀ Ψ L u else 0

/-- Exact prime-conditioned original source moments, with the true p*d remainder. -/
theorem parity_original_conditioned_moment434
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ) (p : ℕ) (P s : Finset ℕ)
    (hp : p.Prime) (hP : ∀ q ∈ P, q.Prime) (hps : p ∉ P) (hs : s ⊆ P) :
    (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      parityOriginalConditionedWeight434 r₀ Ψ L p u *
        ∏ q ∈ s, if q ∈ sourceShiftTwoBad P u then (1:ℝ) else 0) =
    (sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ * sourceShiftTwoLocalDensity p) *
        (∏ q ∈ s, sourceShiftTwoLocalDensity q) +
          sourceShiftTwoRemainder r₀ Ψ L (p * ∏ q ∈ s, q) := by
  have hpnot : p ∉ s := fun h => hps (hs h)
  have hPi : ∀ q ∈ insert p P, q.Prime := by
    intro q hq; rcases Finset.mem_insert.mp hq with rfl | hq; exact hp; exact hP q hq
  have hsi : insert p s ⊆ insert p P := Finset.insert_subset_insert p hs
  have h := source_shift_two_exact_block_moment r₀ Ψ L (insert p P) (insert p s) hPi hsi
  rw [Finset.prod_insert hpnot, Finset.prod_insert hpnot] at h
  have heq : (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      sourceOriginalMovingWeight r₀ Ψ L u *
        ∏ q ∈ insert p s, if q ∈ sourceShiftTwoBad (insert p P) u then (1:ℝ) else 0) =
      ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        parityOriginalConditionedWeight434 r₀ Ψ L p u *
          ∏ q ∈ s, if q ∈ sourceShiftTwoBad P u then (1:ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.prod_insert hpnot]
    have he : (∏ q ∈ s, if q ∈ sourceShiftTwoBad (insert p P) u then (1:ℝ) else 0) =
        ∏ q ∈ s, if q ∈ sourceShiftTwoBad P u then (1:ℝ) else 0 := by
      apply Finset.prod_congr rfl
      intro q hq
      simp only [sourceShiftTwoBad, Finset.mem_filter, hs hq,
        Finset.mem_insert_of_mem (hs hq), true_and]
    rw [he]
    by_cases hd : p ∣ u+2 <;> simp [parityOriginalConditionedWeight434,sourceShiftTwoBad,hd]
  rw [heq] at h
  exact h.trans (by ring)

/-- Exact conditional sifted mass, not a test for 2u+1. -/
theorem parity_original_conditioned_sifted434 (r₀ : ℕ) (Ψ : ℝ → ℝ) (L : ℝ)
    (p J : ℕ) (blocks : Fin J → Finset ℕ) :
    (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
      parityOriginalConditionedWeight434 r₀ Ψ L p u *
        (if ∀ j, blocks j ∩ sourceShiftTwoBad (Finset.univ.biUnion blocks) u = ∅
         then (1:ℝ) else 0)) =
      parityOriginalConditionedMass434 r₀ Ψ L p (Finset.univ.biUnion blocks) := by
  unfold parityOriginalConditionedMass434
  apply Finset.sum_congr rfl
  intro u hu
  have he : (∀ j, blocks j ∩ sourceShiftTwoBad (Finset.univ.biUnion blocks) u = ∅) ↔
      ∀ q ∈ Finset.univ.biUnion blocks, ¬q ∣ u+2 := by
    constructor
    · intro h q hq hd
      obtain ⟨j,_,hqj⟩ := Finset.mem_biUnion.mp hq
      have hm : q ∈ blocks j ∩ sourceShiftTwoBad (Finset.univ.biUnion blocks) u :=
        Finset.mem_inter.mpr ⟨hqj,Finset.mem_filter.mpr ⟨hq,hd⟩⟩
      rw [h j] at hm
      exact Finset.notMem_empty q hm
    · intro h j
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hh := Finset.mem_filter.mp (Finset.mem_inter.mp hq).2
      exact h q hh.1 hh.2
  rw [if_congr he rfl rfl]
  by_cases hd : p ∣ u+2 <;>
    by_cases hq : ∀ q ∈ Finset.univ.biUnion blocks, ¬q ∣ u+2 <;>
    simp [parityOriginalConditionedWeight434,hd,hq]

/-- Two-sided source block sieve after conditioning on the large prime p. -/
theorem parity_original_conditioned_block_sieve434
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L z : ℝ) (p J h : ℕ)
    (blocks : Fin J → Finset ℕ) (hz : 1 < z) (hh : 2 ≤ h) (hev : Even h)
    (hnon : ∀ t, 0 ≤ Ψ t) (hp : p.Prime)
    (hps : p ∉ Finset.univ.biUnion blocks)
    (hblocks : ∀ j q, q ∈ blocks j → q.Prime ∧ 3 ≤ q ∧
      z^((1/2:ℝ)^(j.val+1)) < (q:ℝ) ∧ (q:ℝ) ≤ z^((1/2:ℝ)^j.val)) :
    let P := Finset.univ.biUnion blocks
    let X := sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ
    let V := ∏ q ∈ P, (1-sourceShiftTwoLocalDensity q)
    let E := ∑ d ∈ (∏ q ∈ P,q).divisors.filter
      (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ z^(4*(h:ℝ)+2)),
        |sourceShiftTwoRemainder r₀ Ψ L (p*d)|
    X*sourceShiftTwoLocalDensity p*V*(1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h))-E ≤
      parityOriginalConditionedMass434 r₀ Ψ L p P ∧
    parityOriginalConditionedMass434 r₀ Ψ L p P ≤
      X*sourceShiftTwoLocalDensity p*V*Real.exp (parityOriginalPresieveRho434 h)+E := by
  let P := Finset.univ.biUnion blocks
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq; obtain ⟨j,_,hq⟩ := Finset.mem_biUnion.mp hq; exact (hblocks j q hq).1
  have hden : ∀ j q, q ∈ blocks j →
      0 ≤ sourceShiftTwoLocalDensity q ∧ sourceShiftTwoLocalDensity q ≤ 1-(1/2:ℝ) := by
    intro j q hq
    have hpq := (hblocks j q hq).1
    have h3 : (3:ℝ) ≤ q := by exact_mod_cast (hblocks j q hq).2.1
    rw [sourceShiftTwoLocalDensity, Nat.totient_prime hpq, Nat.cast_sub hpq.one_le, Nat.cast_one]
    constructor
    · exact inv_nonneg.mpr (by linarith)
    · rw [inv_eq_one_div]
      apply (div_le_iff₀ (by linarith : (0:ℝ)<q-1)).mpr
      norm_num; linarith
  have hX := source_original_XA_nonneg r₀
    (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
    (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ hnon
  have h := Green64Analytic.SieveContinuation.weighted_block_sieve
    h J blocks z 8 (1/2) (Finset.range (⌊2*Real.exp L⌋₊+1))
    (parityOriginalConditionedWeight434 r₀ Ψ L p) (sourceShiftTwoBad P)
    sourceShiftTwoLocalDensity (fun d => sourceShiftTwoRemainder r₀ Ψ L (p*d))
    (sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ * sourceShiftTwoLocalDensity p)
    hz hh hev (by norm_num) (by norm_num)
    (mul_nonneg hX (by unfold sourceShiftTwoLocalDensity; positivity))
    (by intro u hu; unfold parityOriginalConditionedWeight434; split_ifs
        · exact mul_nonneg (source_original_parity_pointwise _ _ _ _).1 (hnon _)
        · exact le_rfl)
    (fun j q hq => ⟨(hblocks j q hq).1,(hblocks j q hq).2.2⟩) hden
    (source_shift_two_block_local_density_le_eight z hz J blocks hblocks)
    (fun s hs => parity_original_conditioned_moment434 r₀ Ψ L p P s hp hP hps hs)
  dsimp only at h ⊢
  rw [parity_original_conditioned_sifted434] at h
  exact h

end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalConditionedError -/

section

open Filter Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- An unconditional finite arithmetic theorem: a modulus p*d whose
first prime p is strictly LARGER than every prime factor permitted in
d has a unique representation (p,d). This is independent of source
analytic weights and thus directly reusable for original Echi indices. -/
theorem parity_original_large_prime_divisor_pair_unique434
    (p p' d d' : ℕ) (hp : p.Prime) (hp' : p'.Prime)
    (P P' : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime ∧ q < p)
    (hP' : ∀ q ∈ P', q.Prime ∧ q < p')
    (hd : d ∣ ∏ q ∈ P, q)
    (hd' : d' ∣ ∏ q ∈ P', q)
    (heq : p*d = p'*d') :
    p=p' ∧ d=d' := by
  have hple : p ≤ p' := by
    have hdiv : p ∣ p'*d' := by
      rw [← heq]
      exact dvd_mul_right p d
    rcases (hp.dvd_mul).mp hdiv with hpp | hpd
    · have he : p=p' := (Nat.prime_dvd_prime_iff_eq hp hp').mp hpp
      omega
    · have hprod : p ∣ ∏ q ∈ P', q := hpd.trans hd'
      obtain ⟨q,hq,hpq⟩ :=
        (Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ => q)).mp hprod
      have hqPrime : q.Prime := (hP' q hq).1
      have hqLt : q < p' := (hP' q hq).2
      have hqLe : p ≤ q := Nat.le_of_dvd hqPrime.pos hpq
      omega
  have hple' : p' ≤ p := by
    have hdiv : p' ∣ p*d := by
      rw [heq]
      exact dvd_mul_right p' d'
    rcases (hp'.dvd_mul).mp hdiv with hpp | hpd
    · have he : p'=p := (Nat.prime_dvd_prime_iff_eq hp' hp).mp hpp
      omega
    · have hprod : p' ∣ ∏ q ∈ P, q := hpd.trans hd
      obtain ⟨q,hq,hpq⟩ :=
        (Prime.dvd_finsetProd_iff hp'.prime (fun q : ℕ => q)).mp hprod
      have hqPrime : q.Prime := (hP q hq).1
      have hqLt : q < p := (hP q hq).2
      have hqLe : p' ≤ q := Nat.le_of_dvd hqPrime.pos hpq
      omega
  have heqP : p=p' := Nat.le_antisymm hple hple'
  subst p'
  exact ⟨rfl, Nat.mul_left_cancel hp.pos heq⟩

/-- A finite, multiplicity-FREE ℓ¹ pushforward under any injective
index-to-modulus map. This is the exact combinatorial ingredient
needed to transfer the source original unweighted Echi sum to (p,d).
No distribution or prime hypotheses occur in this lemma. -/
theorem parity_original_injective_indexed_L1_434
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (M : Finset ℕ)
    (f : ι → ℕ) (hInj : Set.InjOn f (↑S))
    (hImage : ∀ a ∈ S, f a ∈ M) (R : ℕ → ℝ) :
    (∑ a ∈ S, |R (f a)|) ≤ ∑ d ∈ M, |R d| := by
  have hSub : S.image f ⊆ M := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    exact hImage a ha
  have heq : (∑ d ∈ S.image f, |R d|) =
      ∑ a ∈ S, |R (f a)| := Finset.sum_image hInj
  have hle : (∑ d ∈ S.image f, |R d|) ≤
      ∑ d ∈ M, |R d| :=
    Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun d hd hn => abs_nonneg _)
  exact heq.symm.trans_le hle

/-- The actual unweighted congruence range, with each modulus counted once. -/
def parityOriginalShiftedRemainderRange434
    (r₀ : ℕ) (Psi : ℝ → ℝ) (L theta : ℝ) : ℝ :=
  ∑ d∈(Finset.range (⌊(Real.exp L)^theta⌋₊+1)).filter
    (fun d => Odd d ∧ Squarefree d),|sourceShiftTwoRemainder r₀ Psi L d|

/-- Genuine conditioned errors inject into the single actual modulus range.
The large prime is unique above z; no divisor multiplicity or family count
is introduced, and no coprimality of that prime with the cofactor of u+2
is imposed. Only the sieve modulus d is squarefree. -/
theorem parity_original_conditioned_error_bound434
    (r₀ : ℕ) (Psi : ℝ → ℝ) (L theta z U H : ℝ)
    (P S : Finset ℕ) (hP : ∀ q∈P,q.Prime ∧ 3≤q ∧ (q:ℝ)≤z)
    (hS : ∀ p∈S,p.Prime ∧ 3≤p ∧ z<(p:ℝ) ∧ (p:ℝ)≤U)
    (hH : 0≤H) (hLevel : U*H≤(Real.exp L)^theta) :
    (∑ p∈S,∑ d∈(∏ q∈P,q).divisors.filter
      (fun d : ℕ => Squarefree d ∧ (d:ℝ)≤H),
      |sourceShiftTwoRemainder r₀ Psi L (p*d)|) ≤
        parityOriginalShiftedRemainderRange434 r₀ Psi L theta := by
  let D := (∏ q∈P,q).divisors.filter (fun d : ℕ => Squarefree d ∧ (d:ℝ)≤H)
  let T := S.product D
  let M := (Finset.range (⌊(Real.exp L)^theta⌋₊+1)).filter
    (fun d => Odd d ∧ Squarefree d)
  have hDiv (d : ℕ) (hd : d∈D) : d∣∏ q∈P,q :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hSmall (p : ℕ) (hp : p∈S) : ∀ q∈P,q.Prime ∧ q<p := by
    intro q hq
    exact ⟨(hP q hq).1,by exact_mod_cast (hP q hq).2.2.trans_lt (hS p hp).2.2.1⟩
  have hInj : Set.InjOn (fun a : ℕ×ℕ => a.1*a.2) (↑T) := by
    rintro ⟨p,d⟩ hpd ⟨p',d'⟩ hp'd' hEq
    have hpD := Finset.mem_product.mp hpd
    have hpD' := Finset.mem_product.mp hp'd'
    have h := parity_original_large_prime_divisor_pair_unique434 p p' d d'
      (hS p hpD.1).1 (hS p' hpD'.1).1 P P
      (hSmall p hpD.1) (hSmall p' hpD'.1)
      (hDiv d hpD.2) (hDiv d' hpD'.2) hEq
    exact Prod.ext h.1 h.2
  have hOddProduct : Odd (∏ q∈P,q) := by
    apply Nat.coprime_two_right.mp
    apply Nat.Coprime.prod_left
    intro q hq
    apply Nat.coprime_two_right.mpr
    exact (hP q hq).1.odd_of_ne_two (by have := (hP q hq).2.1;omega)
  have hImage : ∀ a∈T,a.1*a.2∈M := by
    rintro ⟨p,d⟩ hpd
    have hpD := Finset.mem_product.mp hpd
    obtain ⟨hp,hThree,hzp,hpU⟩ := hS p hpD.1
    have hd := Finset.mem_filter.mp hpD.2
    have hdDiv := hDiv d hpD.2
    have hNot : ¬p∣d := by
      intro hpd'
      obtain ⟨q,hq,hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ => q)).mp
        (hpd'.trans hdDiv)
      have hEq : p=q := (Nat.prime_dvd_prime_iff_eq hp (hP q hq).1).mp hpq
      have hlt := (hSmall p hpD.1 q hq).2
      omega
    have hCop : p.Coprime d := hp.coprime_iff_not_dvd.mpr hNot
    have hSF : Squarefree (p*d) := (Nat.squarefree_mul hCop).mpr ⟨hp.squarefree,hd.2.1⟩
    have hOddP : Odd p := hp.odd_of_ne_two (by omega)
    have hOddD : Odd d := hOddProduct.of_dvd_nat hdDiv
    have hU : 0≤U := (Nat.cast_nonneg p).trans hpU
    have hSize : ((p*d:ℕ):ℝ)≤(Real.exp L)^theta := by
      push_cast
      exact (mul_le_mul hpU hd.2.2 (Nat.cast_nonneg d) hU).trans hLevel
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hSize)),hOddP.mul hOddD,hSF⟩
  have hPush := parity_original_injective_indexed_L1_434 T M (fun a : ℕ×ℕ => a.1*a.2)
    hInj hImage (sourceShiftTwoRemainder r₀ Psi L)
  have hPush' : (∑ p∈S,∑ d∈D,|sourceShiftTwoRemainder r₀ Psi L (p*d)|) ≤
      ∑ d∈M,|sourceShiftTwoRemainder r₀ Psi L d| := by
    calc
      _ = ∑ a∈S.product D,|sourceShiftTwoRemainder r₀ Psi L (a.1*a.2)| :=
        (Finset.sum_product S D (fun a : ℕ×ℕ => |sourceShiftTwoRemainder r₀ Psi L (a.1*a.2)|)).symm
      _ ≤ _ := hPush
  exact hPush' 

/-- Source-true two-sided conditional sieve, with ONE global remainder sum. -/
theorem parity_original_conditioned_sum434
    (r₀ : ℕ) (Ψ : ℝ → ℝ) (L θ z U : ℝ) (J h : ℕ)
    (blocks : Fin J → Finset ℕ) (S : Finset ℕ)
    (hz : 1 < z) (hh : 2 ≤ h) (hev : Even h) (hnon : ∀ t, 0 ≤ Ψ t)
    (hblocks : ∀ j q, q ∈ blocks j → q.Prime ∧ 3 ≤ q ∧
      z^((1/2:ℝ)^(j.val+1)) < (q:ℝ) ∧ (q:ℝ) ≤ z^((1/2:ℝ)^j.val))
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ z < (p:ℝ) ∧ (p:ℝ) ≤ U)
    (hlevel : U*z^(4*(h:ℝ)+2) ≤ (Real.exp L)^θ) :
    let P := Finset.univ.biUnion blocks
    let X := sourceOriginalXA r₀
      (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
      (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ
    let main : ℝ := X*(∏ q ∈ P, (1-sourceShiftTwoLocalDensity q))*
      (∑ p ∈ S, sourceShiftTwoLocalDensity p)
    main*(1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h))-parityOriginalShiftedRemainderRange434 r₀ Ψ L θ ≤
      ∑ p ∈ S,parityOriginalConditionedMass434 r₀ Ψ L p P ∧
    (∑ p ∈ S,parityOriginalConditionedMass434 r₀ Ψ L p P) ≤
      main*Real.exp (parityOriginalPresieveRho434 h)+parityOriginalShiftedRemainderRange434 r₀ Ψ L θ := by
  let P := Finset.univ.biUnion blocks
  have hP : ∀ q ∈ P, q.Prime ∧ 3 ≤ q ∧ (q:ℝ) ≤ z := by
    intro q hq
    obtain ⟨j,_,hq⟩ := Finset.mem_biUnion.mp hq
    have he : (1/2:ℝ)^j.val ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine ⟨(hblocks j q hq).1,(hblocks j q hq).2.1,?_⟩
    exact (hblocks j q hq).2.2.2.trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hz.le he)
  let X := sourceOriginalXA r₀
    (sourceOriginalQActualBands r₀ (sourceOriginalLiteralDepth r₀ L) L)
    (sourceOriginalPAllActualBands r₀ L) (Real.exp L) Ψ
  let V : ℝ := ∏ q ∈ P, (1-sourceShiftTwoLocalDensity q)
  let E := fun p => ∑ d ∈ (∏ q ∈ P,q).divisors.filter
    (fun d : ℕ => Squarefree d ∧ (d:ℝ) ≤ z^(4*(h:ℝ)+2)),
      |sourceShiftTwoRemainder r₀ Ψ L (p*d)|
  have hsumE : (∑ p ∈ S,E p) ≤ parityOriginalShiftedRemainderRange434 r₀ Ψ L θ :=
    parity_original_conditioned_error_bound434 r₀ Ψ L θ z U _ P S hP hS (by positivity) hlevel
  have hpoint : ∀ p ∈ S,
      X*sourceShiftTwoLocalDensity p*V*(1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h))-E p ≤
        parityOriginalConditionedMass434 r₀ Ψ L p P ∧
      parityOriginalConditionedMass434 r₀ Ψ L p P ≤
        X*sourceShiftTwoLocalDensity p*V*Real.exp (parityOriginalPresieveRho434 h)+E p := by
    intro p hp
    simpa only [X,V,E,P,mul_assoc] using
      parity_original_conditioned_block_sieve434 r₀ Ψ L z p J h blocks hz hh hev hnon (hS p hp).1
        (by intro hpP; have := (hP p hpP).2.2; linarith [(hS p hp).2.2.1]) hblocks
  have hlo := Finset.sum_le_sum (fun p hp => (hpoint p hp).1)
  have hup := Finset.sum_le_sum (fun p hp => (hpoint p hp).2)
  rw [Finset.sum_sub_distrib] at hlo
  rw [Finset.sum_add_distrib] at hup
  have heq (v : ℝ) : (∑ p ∈ S,X*sourceShiftTwoLocalDensity p*V*v) =
      X*V*(∑ p ∈ S,sourceShiftTwoLocalDensity p)*v := by
    calc
      _ = ∑ p ∈ S,(X*V*v)*sourceShiftTwoLocalDensity p := by
        apply Finset.sum_congr rfl; intro p hp; ring
      _ = (X*V*v)*(∑ p ∈ S,sourceShiftTwoLocalDensity p) := by rw [Finset.mul_sum]
      _ = _ := by ring
  rw [heq] at hlo hup
  exact ⟨(sub_le_sub_left hsumE _).trans hlo,
    hup.trans (_root_.add_le_add le_rfl hsumE)⟩

end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalFullRoughPresieve -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

/-- The literal original finite source restricted by the least prime factor
of u+2. Its parity weight retains all multiplicities of primes in u. -/
def parityOriginalRoughMass434 (Psi : ℝ → ℝ) (rho beta L : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
    if (Real.exp L)^beta < ((u+2).minFac:ℝ) then
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u *
        Psi ((u:ℝ)/Real.exp L) else 0

/-- Prime two is absent from u+2 on every nonzero actual negative source
weight, by the proved L^20-roughness of the literal Q/P alphabet of u. -/
theorem parity_original_negative_weight_prime_two_exclusion434
    (Psi : ℝ → ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℕ,
      sourceOriginalMovingWeight 20 Psi L u ≠ 0 → ¬2∣u+2 := by
  filter_upwards [source_shift_two_actual_weight_roughness 20 (by norm_num) Psi,
    eventually_ge_atTop (2:ℝ)] with L hRough hL u hw
  intro hTwo
  have hTwoU : 2∣u := by omega
  have hLower := hRough u 2 hw Nat.prime_two hTwoU
  have hPow : (2:ℝ)^20≤L^20 := pow_le_pow_left₀ (by norm_num) hL 20
  norm_num at hPow
  norm_num at hLower
  linarith

/-- Exact strict least-prime-factor cutoff. The shifted integer u+2 is
always at least two, so no convention for the least prime factor of one
enters. The closed upper prime cutoff excludes a prime exactly at z. -/
theorem parity_original_odd_prime_avoidance_iff_minFac434
    (u : ℕ) (z : ℝ) (hz : 0≤z) (hTwo : ¬2∣u+2) :
    (∀ p∈sourceAllOddPrimeSet z,¬p∣u+2) ↔ z<((u+2).minFac:ℝ) := by
  constructor
  · intro hAvoid
    by_contra hNot
    have hLe : ((u+2).minFac:ℝ)≤z := le_of_not_gt hNot
    have hPrime : (u+2).minFac.Prime := Nat.minFac_prime (by omega)
    have hDvd := Nat.minFac_dvd (u+2)
    have hThree : 3≤(u+2).minFac := by
      have hAtLeastTwo := hPrime.two_le
      by_contra h
      have he : (u+2).minFac=2 := by omega
      exact hTwo (by simpa only [he] using hDvd)
    have hMem : (u+2).minFac∈sourceAllOddPrimeSet z :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hThree,Nat.le_floor hLe⟩,hPrime⟩
    exact hAvoid _ hMem hDvd
  · intro hMin p hp hDiv
    have hPrime := (Finset.mem_filter.mp hp).2
    have hNatLe := Nat.minFac_le_of_dvd hPrime.two_le hDiv
    have hRealLe : ((u+2).minFac:ℝ)≤(p:ℝ) := by exact_mod_cast hNatLe
    have hpLe : (p:ℝ)≤z := by
      have hFloor : (p:ℝ)≤⌊z⌋₊ := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      exact hFloor.trans (Nat.floor_le hz)
    exact (not_lt_of_ge (hRealLe.trans hpLe)) hMin

/-- Whole finite source equality, uniformly in the cutoff exponent. On
zero-weight terms no equivalence of masks is asserted or required. -/
theorem parity_original_negative_rough_mass_eq_odd_sifted434
    (Psi : ℝ → ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ beta : ℝ,
      parityOriginalRoughMass434 Psi (-1) beta L =
        sourceShiftTwoSiftedMass 20 Psi L
          (sourceAllOddPrimeSet ((Real.exp L)^beta)) := by
  filter_upwards [parity_original_negative_weight_prime_two_exclusion434 Psi]
    with L hTwo beta
  unfold parityOriginalRoughMass434 sourceShiftTwoSiftedMass
  apply Finset.sum_congr rfl
  intro u hu
  have hWeight :
      parityWeight (sourceOriginalLiteralDepth 20 L) L (-1) u *
        Psi ((u:ℝ)/Real.exp L)=sourceOriginalMovingWeight 20 Psi L u := by
    simp only [sourceOriginalMovingWeight,parity_original_minus_parity_A_eq_original_A434]
  rw [hWeight]
  by_cases hw : sourceOriginalMovingWeight 20 Psi L u=0
  · simp only [hw,ite_self]
  · have hMask := parity_original_odd_prime_avoidance_iff_minFac434 u
      ((Real.exp L)^beta) (Real.rpow_pos_of_pos (Real.exp_pos L) beta).le (hTwo u hw)
    simp only [hMask]

/-- The genuine original Parity initial presieve in full roughness notation:
all primes, the same Xminus, the same finite Euler product, and both bounds.
Its negative parity conclusion requires no unproved source sieve input. -/
theorem parity_original_negative_full_rough_presieve434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta theta eps : ℝ) (h : ℕ)
    (hBeta : 0<beta) (hTheta : 0<theta) (hThetaUpper : theta<1/2)
    (hh : 2≤h) (hEven : Even h)
    (hLevel : beta*(4*(h:ℝ)+2)≤theta) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      let P := sourceAllOddPrimeSet ((Real.exp L)^beta)
      let X := localizedMass Psi (-1) L
      let V := ∏ q∈P,(1-sourceShiftTwoLocalDensity q)
      X*V*(1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h))-
        eps*X/L ≤ parityOriginalRoughMass434 Psi (-1) beta L ∧
      parityOriginalRoughMass434 Psi (-1) beta L ≤
        X*V*Real.exp (parityOriginalPresieveRho434 h)+eps*X/L := by
  filter_upwards [parity_original_negative_sharp_initial_presieve434
    Psi hSmooth hSupport hNonneg hInterior beta theta eps h
    hBeta hTheta hThetaUpper hh hEven hLevel hEps,
    parity_original_negative_rough_mass_eq_odd_sifted434 Psi] with L hSieve hEq
  rw [hEq beta]
  simpa only [parity_original_minus_Xrho_eq_original_XA434] using hSieve
end Green64Analytic.Parity

end

end

/-! ## OriginalConditionalDistribution -/

section

open Filter Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- The full conditional-sieve level is admissible for every fixed depth h.
The source W=exp(sqrt L) and all p<=exp(eta L) are kept literally. -/
theorem parity_original_conditioned_subpower_level434 (γ η θ : ℝ) (h : ℕ)
    (hγ : 0 < γ) (hηθ : η < θ) :
    ∀ᶠ L : ℝ in atTop,
      let z := Real.exp (Real.sqrt L)
      2 ≤ z ∧ z < (Real.exp L)^γ ∧
      (Real.exp L)^η * z^(4*(h:ℝ)+2) ≤ (Real.exp L)^θ := by
  have hδ : 0 < θ-η := sub_pos.mpr hηθ
  filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop
    (max (Real.log 2) (max (2/γ) ((4*(h:ℝ)+2)/(θ-η)))),
    eventually_gt_atTop (0:ℝ)] with L hL hLp
  have hr0 := Real.sqrt_nonneg L
  have hrp := Real.sqrt_pos.mpr hLp
  have hrsq := Real.sq_sqrt hLp.le
  have hlog : Real.log 2 ≤ Real.sqrt L := (le_max_left _ _).trans hL
  have hg : 2/γ ≤ Real.sqrt L := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hL
  have ha : (4*(h:ℝ)+2)/(θ-η) ≤ Real.sqrt L :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hL
  have hgm : 2 ≤ γ*Real.sqrt L := by
    simpa [mul_comm] using (div_le_iff₀ hγ).mp hg
  have hsm : Real.sqrt L < L*γ := by
    have hm := mul_le_mul_of_nonneg_right hgm hr0
    nlinarith
  have hac : 4*(h:ℝ)+2 ≤ (θ-η)*Real.sqrt L := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp ha
  have hal : Real.sqrt L*(4*(h:ℝ)+2) ≤ L*(θ-η) := by
    have hm := mul_le_mul_of_nonneg_right hac hr0
    nlinarith
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact (Real.exp_log (by norm_num : (0:ℝ)<2)).symm.trans_le (Real.exp_le_exp.mpr hlog)
  · rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    exact Real.exp_lt_exp.mpr hsm
  · rw [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,
      Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith

/-- Arbitrary relative sieve precision can be chosen at fixed even depth. -/
theorem parity_original_conditioned_exists_precise_depth434 (ε : ℝ) (hε : 0 < ε) :
    ∃ h : ℕ, 2 ≤ h ∧ Even h ∧
      parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h) ≤ ε ∧
      Real.exp (parityOriginalPresieveRho434 h) ≤ 1+ε := by
  have hρ : Tendsto parityOriginalPresieveRho434 atTop (𝓝 0) := by
    unfold parityOriginalPresieveRho434
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    simpa only [mul_zero,Function.comp_def] using he.const_mul
      ((Real.exp (Real.exp 1*8)/(1-Real.exp (-1)))/Real.exp (-8/(1/2)))
  have he : Tendsto (fun h : ℕ => Real.exp (parityOriginalPresieveRho434 h)) atTop (𝓝 1) := by
    simpa only [Real.exp_zero,Function.comp_def] using
      (Real.continuous_exp.tendsto (0:ℝ)).comp hρ
  have hp := hρ.mul he
  simp only [zero_mul] at hp
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1
    ((hp.eventually_lt_const hε).and (he.eventually_lt_const (by linarith : (1:ℝ)<1+ε)))
  exact ⟨2*(N+1),by omega,⟨N+1,by omega⟩,
    (hN (2*(N+1)) (by omega)).1.le,(hN (2*(N+1)) (by omega)).2.le⟩

/-- Arbitrarily accurate original u+2 conditional sieve at W=exp(sqrt L).
All source weights are fixed; S may be ANY moving subset of the prime range.
There is no proxy, TypeII, or distribution hypothesis in this theorem. -/
theorem parity_original_negative_conditional_distribution434
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : Function.support Ψ ⊆ Set.Icc (1:ℝ) 2) (hnon : ∀ t,0 ≤ Ψ t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Ψ t)
    (γ η θ ε : ℝ) (hγ : 0 < γ) (hγη : γ < η) (hηθ : η < θ)
    (hθu : θ < 1/2) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S,p.Prime ∧ (Real.exp L)^γ < (p:ℝ) ∧ (p:ℝ) ≤ (Real.exp L)^η) →
      let P := sourceAllOddPrimeSet (Real.exp (Real.sqrt L))
      let X := sourceOriginalXA 20
        (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
        (sourceOriginalPAllActualBands 20 L) (Real.exp L) Ψ
      let main : ℝ := X*(∏ q ∈ P, (1-sourceShiftTwoLocalDensity q))*
        (∑ p ∈ S,sourceShiftTwoLocalDensity p)
      main*(1-ε)-ε*X/L ≤ (∑ p ∈ S,parityOriginalConditionedMass434 20 Ψ L p P) ∧
      (∑ p ∈ S,parityOriginalConditionedMass434 20 Ψ L p P) ≤ main*(1+ε)+ε*X/L := by
  obtain ⟨h,hh,hev,hrlo,hrhi⟩ := parity_original_conditioned_exists_precise_depth434 ε hε
  have hθ : 0 < θ := hγ.trans (hγη.trans hηθ)
  filter_upwards [parity_original_conditioned_subpower_level434 γ η θ h hγ hηθ,
    parity_original_negative_congruence_error_small434 Ψ hΨ hs hnon hInterior
      θ ε hθ hθu hε] with L hlevel hErr
  intro S hS
  let z := Real.exp (Real.sqrt L)
  let P := sourceAllOddPrimeSet z
  have hz : 1 < z := lt_of_lt_of_le (by norm_num) hlevel.1
  obtain ⟨J,hJ⟩ := source_exists_natural_halfpower_depth z hz
  let blocks := fun j : Fin J => sourceNaturalOddPrimeBlock 1 z j.val
  have hblocks : ∀ j q,q ∈ blocks j → q.Prime ∧ 3 ≤ q ∧
      z^((1/2:ℝ)^(j.val+1)) < (q:ℝ) ∧ (q:ℝ) ≤ z^((1/2:ℝ)^j.val) := by
    intro j q hq
    have hq' := source_natural_block_prime 1 z j.val q hq
    exact ⟨hq'.1,source_natural_block_odd 1 z j.val q hq,hq'.2⟩
  have hP : Finset.univ.biUnion blocks = P :=
    source_natural_unit_blocks_cover_all_odd_primes J z hz hJ
  have hSp : ∀ p ∈ S,p.Prime ∧ 3 ≤ p ∧ z < (p:ℝ) ∧ (p:ℝ) ≤ (Real.exp L)^η := by
    intro p hp
    have hh := hS p hp
    have hzp : z < (p:ℝ) := hlevel.2.1.trans hh.2.1
    have h2 : (2:ℝ)<p := hlevel.1.trans_lt hzp
    have h3 : 3 ≤ p := by
      have hp2 : 2 < p := by exact_mod_cast h2
      omega
    exact ⟨hh.1,h3,hzp,hh.2.2⟩
  have hout := parity_original_conditioned_sum434 20 Ψ L θ z ((Real.exp L)^η) J h blocks S
    hz hh hev hnon hblocks hSp hlevel.2.2
  dsimp only at hout
  rw [hP] at hout
  let X := sourceOriginalXA 20
    (sourceOriginalQActualBands 20 (sourceOriginalLiteralDepth 20 L) L)
    (sourceOriginalPAllActualBands 20 L) (Real.exp L) Ψ
  let main : ℝ := X*(∏ q ∈ P, (1-sourceShiftTwoLocalDensity q))*
    (∑ p ∈ S,sourceShiftTwoLocalDensity p)
  have hm : 0 ≤ main := by
    apply mul_nonneg
    · apply mul_nonneg (source_original_XA_nonneg _ _ _ _ _ hnon)
      apply Finset.prod_nonneg
      intro q hq
      have hpr := (Finset.mem_filter.mp hq).2
      have h3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      have hq2 : (2:ℝ) ≤ q.totient := by
        rw [Nat.totient_prime hpr]; exact_mod_cast (show 2 ≤ q-1 by omega)
      apply sub_nonneg.mpr
      unfold sourceShiftTwoLocalDensity
      apply (inv_le_one₀ (by linarith : (0:ℝ)<q.totient)).mpr
      linarith
    · exact Finset.sum_nonneg (fun p hp => by unfold sourceShiftTwoLocalDensity; positivity)
  have hE : parityOriginalShiftedRemainderRange434 20 Ψ L θ ≤ ε*X/L :=
    hErr
  have hl : main*(1-ε) ≤ main*(1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h)) :=
    mul_le_mul_of_nonneg_left (by linarith) hm
  have hu : main*Real.exp (parityOriginalPresieveRho434 h) ≤ main*(1+ε) :=
    mul_le_mul_of_nonneg_left hrhi hm
  exact ⟨(_root_.sub_le_sub hl hE).trans hout.1,
    hout.2.trans (_root_.add_le_add hu hE)⟩

end Green64Analytic.SourceBlockSieve

namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve

/-- Literal prime-conditioned source sum with the full least-prime-factor
mask. No restriction on multiplicities or on the cofactor is present. -/
def parityOriginalConditionedRoughMass434
    (Psi : ℝ → ℝ) (rho L z : ℝ) (p : ℕ) : ℝ :=
  ∑ u∈Finset.range (⌊2*Real.exp L⌋₊+1),
    if p∣u+2 ∧ z<((u+2).minFac:ℝ) then
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
        Psi ((u:ℝ)/Real.exp L) else 0

theorem parity_original_negative_conditioned_rough_eq434 (Psi : ℝ → ℝ) :
    ∀ᶠ L : ℝ in atTop,∀ z : ℝ,0≤z → ∀ p : ℕ,
      parityOriginalConditionedRoughMass434 Psi (-1) L z p=
        parityOriginalConditionedMass434 20 Psi L p (sourceAllOddPrimeSet z) := by
  filter_upwards [parity_original_negative_weight_prime_two_exclusion434 Psi]
    with L hTwo z hz p
  unfold parityOriginalConditionedRoughMass434 parityOriginalConditionedMass434
  apply Finset.sum_congr rfl
  intro u hu
  have hWeight :
      parityWeight (sourceOriginalLiteralDepth 20 L) L (-1) u*
        Psi ((u:ℝ)/Real.exp L)=sourceOriginalMovingWeight 20 Psi L u := by
    simp only [sourceOriginalMovingWeight,parity_original_minus_parity_A_eq_original_A434]
  rw [hWeight]
  by_cases hw : sourceOriginalMovingWeight 20 Psi L u=0
  · simp only [hw,ite_self]
  · have hMask := parity_original_odd_prime_avoidance_iff_minFac434 u z hz (hTwo u hw)
    simp only [hMask]

/-- Real original conditional sieve uniformly over every moving finite
prime subset in the fixed exponent range. The same Xminus and full roughness
appear in both bounds, with one global error and no family-count loss. -/
theorem parity_original_negative_conditional_full_rough434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (gamma eta theta eps : ℝ) (hGamma : 0<gamma) (hGammaEta : gamma<eta)
    (hEtaTheta : eta<theta) (hThetaUpper : theta<1/2) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,∀ S : Finset ℕ,
      (∀ p∈S,p.Prime ∧ (Real.exp L)^gamma<(p:ℝ) ∧ (p:ℝ)≤(Real.exp L)^eta) →
      let W := Real.exp (Real.sqrt L)
      let X := localizedMass Psi (-1) L
      let main := X*(∏ q∈sourceAllOddPrimeSet W,(1-sourceShiftTwoLocalDensity q))*
        (∑ p∈S,sourceShiftTwoLocalDensity p)
      main*(1-eps)-eps*X/L ≤ (∑ p∈S,parityOriginalConditionedRoughMass434 Psi (-1) L W p) ∧
      (∑ p∈S,parityOriginalConditionedRoughMass434 Psi (-1) L W p) ≤
        main*(1+eps)+eps*X/L := by
  filter_upwards [parity_original_negative_conditional_distribution434
    Psi hSmooth hSupport hNonneg hInterior gamma eta theta eps
    hGamma hGammaEta hEtaTheta hThetaUpper hEps,
    parity_original_negative_conditioned_rough_eq434 Psi] with L hDist hEq S hS
  have h := hDist S hS
  simpa only [parity_original_minus_Xrho_eq_original_XA434,
    hEq (Real.exp (Real.sqrt L)) (Real.exp_pos _).le] using h

end Green64Analytic.Parity

end

end

/-! ## OriginalPositivePresieve -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
open Green64Analytic.SmallB
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Exact form of the actual shifted C=8 block loss. The ordinary-rough
C=4 SmallB constant is not substituted for this source constant. -/
theorem parity_original_presieve_rho_exact434 (h : ℕ) :
    parityOriginalPresieveRho434 h =
      Real.exp (8*Real.exp 1+16-(h:ℝ))/(1-Real.exp (-1)) := by
  have hArg : (-8/(1/2):ℝ)=-16 := by norm_num
  rw [parityOriginalPresieveRho434,hArg,Real.exp_neg (16:ℝ)]
  simp only [div_eq_mul_inv,inv_inv]
  calc
    _ = (Real.exp (Real.exp 1*8)*Real.exp 16*Real.exp (-(h:ℝ)))*
        (1-Real.exp (-1))⁻¹ := by ring
    _ = _ := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 2
      ring

/-- The original floor choice, including the sharper original level
1/5+2 beta and the available theta=1/2-kappa range. -/
theorem parity_original_presieve_source_depth_budget434
    (beta kappa : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/100)
    (hKappaUpper : kappa<1/50) :
    2≤ sourceDepth beta ∧ Even (sourceDepth beta) ∧
      beta*(4*(sourceDepth beta:ℝ)+2)≤1/5+2*beta ∧
      beta*(4*(sourceDepth beta:ℝ)+2)≤1/2-kappa := by
  have hBudget := sourceDepth_budget beta hBeta hSmall
  have hH : (sourceDepth beta:ℝ)≤2*(1/(40*beta)) := by
    simp only [sourceDepth,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num)
  have hIdentity : beta*(4*(2*(1/(40*beta)))+2)=1/5+2*beta := by
    field_simp
    ring
  have hSharp : beta*(4*(sourceDepth beta:ℝ)+2)≤1/5+2*beta := by
    calc
      _ ≤ beta*(4*(2*(1/(40*beta)))+2) :=
        mul_le_mul_of_nonneg_left (by linarith) hBeta.le
      _ = _ := hIdentity
  exact ⟨by omega,hBudget.2.1,hSharp,by linarith⟩

/-- Explicit depth size for a fixed admissible small source parameter. -/
theorem parity_original_presieve_source_depth_ge_fifty434
    (beta : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/1000) :
    50≤ sourceDepth beta := by
  have hDen : 0<40*beta := by positivity
  have hQ : (25:ℝ)≤1/(40*beta) :=
    (le_div_iff₀ hDen).mpr (by nlinarith)
  have hFloor : 25≤⌊1/(40*beta)⌋₊ := Nat.le_floor hQ
  change 50≤2*⌊1/(40*beta)⌋₊
  omega

/-- A fully explicit positive truncation coefficient for the actual shifted
rho, independent of L and using only exact exponential inequalities. -/
theorem parity_original_presieve_rho_small434 (h : ℕ) (hh : 50≤h) :
    0<parityOriginalPresieveRho434 h ∧ parityOriginalPresieveRho434 h≤1/512 ∧
      3/4≤1-parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h) := by
  have hInv : Real.exp (-1)≤(1/2:ℝ) := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)).mpr
    linarith [Real.exp_one_gt_two]
  have hDen : 0<1-Real.exp (-1) := by linarith
  have hExpTen : (1024:ℝ)≤Real.exp 10 := by
    calc
      (1024:ℝ)=(2:ℝ)^10 := by norm_num
      _ ≤ (Real.exp 1)^10 :=
        pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 10
      _ = Real.exp 10 := by simpa using (Real.exp_nat_mul (1:ℝ) 10).symm
  have hExpNegTen : Real.exp (-10)≤(1/1024:ℝ) := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos 10) (by norm_num)).mpr
    nlinarith
  have hH : (50:ℝ)≤h := by exact_mod_cast hh
  have hNum : Real.exp (8*Real.exp 1+16-(h:ℝ))≤(1/1024:ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [Real.exp_one_lt_three])).trans hExpNegTen
  have hPos : 0<parityOriginalPresieveRho434 h := by
    rw [parity_original_presieve_rho_exact434]
    exact div_pos (Real.exp_pos _) hDen
  have hUpper : parityOriginalPresieveRho434 h≤(1/512:ℝ) := by
    rw [parity_original_presieve_rho_exact434]
    apply (div_le_iff₀ hDen).mpr
    nlinarith
  have hExp : Real.exp (parityOriginalPresieveRho434 h)≤3 :=
    (Real.exp_le_exp.mpr (hUpper.trans (by norm_num))).trans Real.exp_one_lt_three.le
  have hLoss : parityOriginalPresieveRho434 h*Real.exp (parityOriginalPresieveRho434 h)≤
      (1/512:ℝ)*3 :=
    mul_le_mul hUpper hExp (Real.exp_pos _).le (by norm_num)
  exact ⟨hPos,hUpper,by nlinarith⟩

/-- The actual full-roughness initial presieve with Parity's original floor
depth and theta=1/2-kappa, all chosen before L. -/
theorem parity_original_negative_full_rough_source_depth434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta kappa eps : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/100)
    (hKappa : 0<kappa) (hKappaUpper : kappa<1/50) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      let P := sourceAllOddPrimeSet ((Real.exp L)^beta)
      let X := localizedMass Psi (-1) L
      let V := ∏ q∈P,(1-sourceShiftTwoLocalDensity q)
      let rho := parityOriginalPresieveRho434 (sourceDepth beta)
      X*V*(1-rho*Real.exp rho)-eps*X/L ≤ parityOriginalRoughMass434 Psi (-1) beta L ∧
      parityOriginalRoughMass434 Psi (-1) beta L ≤ X*V*Real.exp rho+eps*X/L := by
  have hDepth := parity_original_presieve_source_depth_budget434 beta kappa hBeta hSmall hKappaUpper
  exact parity_original_negative_full_rough_presieve434
    Psi hSmooth hSupport hNonneg hInterior beta (1/2-kappa) eps (sourceDepth beta)
    hBeta (by linarith) (by linarith) hDepth.1 hDepth.2.1 hDepth.2.2.2 hEps

/-- Genuine positive source mass survives the full initial presieve.
The fixed epsilon is chosen from the proved Euler floor before L. This
asserts rough shifted integers, not yet primes. -/
theorem parity_original_negative_positive_presieve_mass434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta kappa : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/1000)
    (hKappa : 0<kappa) (hKappaUpper : kappa<1/50) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp (-Real.eulerMascheroniConstant)/beta/8)*
          localizedMass Psi (-1) L/L ≤
        parityOriginalRoughMass434 Psi (-1) beta L ∧
      0<parityOriginalRoughMass434 Psi (-1) beta L := by
  let c : ℝ := Real.exp (-Real.eulerMascheroniConstant)/beta/4
  have hc : 0<c := by dsimp [c];positivity
  have hRho := parity_original_presieve_rho_small434 (sourceDepth beta)
    (parity_original_presieve_source_depth_ge_fifty434 beta hBeta hSmall)
  have hSieve := parity_original_negative_full_rough_source_depth434
    Psi hSmooth hSupport hNonneg hInterior beta kappa (c/4)
    hBeta (by linarith) hKappa hKappaUpper (by positivity)
  obtain ⟨c0,hc0,hMass⟩ := localizedMass_lower_bound
    Psi hSmooth.continuous hSupport hNonneg hInterior
  filter_upwards [hSieve,parity_original_presieve_euler_lower434 beta hBeta,
    hMass,eventually_gt_atTop (0:ℝ)] with L hS hV hM hL
  let X := localizedMass Psi (-1) L
  let V := ∏ q∈sourceAllOddPrimeSet ((Real.exp L)^beta),(1-sourceShiftTwoLocalDensity q)
  let rho := parityOriginalPresieveRho434 (sourceDepth beta)
  have hX : 0<X :=
    (by positivity : 0<c0*Real.exp L*L^(-221:ℝ)).trans_le (hM (-1) (Or.inr rfl))
  have hVNonneg : 0≤V := (by positivity : 0≤ c/L).trans hV
  have hMain : X*(c/L)*(3/4)≤X*V*(1-rho*Real.exp rho) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hV hX.le) hRho.2.2
      (by norm_num) (mul_nonneg hX.le hVNonneg)
  have hLower : (Real.exp (-Real.eulerMascheroniConstant)/beta/8)*X/L ≤
      parityOriginalRoughMass434 Psi (-1) beta L := by
    calc
      _ = X*(c/L)*(3/4)-(c/4)*X/L := by dsimp [c];ring
      _ ≤ X*V*(1-rho*Real.exp rho)-(c/4)*X/L :=
        _root_.sub_le_sub hMain (le_refl _)
      _ ≤ _ := hS.1
  exact ⟨hLower,(by positivity :
    0<(Real.exp (-Real.eulerMascheroniConstant)/beta/8)*X/L).trans_le hLower⟩

/-- The surviving actual source has a fixed positive exp(L)*L^(-222)
lower bound. The constant is existentially fixed before L. -/
theorem parity_original_negative_presieve_mass_lower_222434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (beta kappa : ℝ) (hBeta : 0<beta) (hSmall : beta≤1/1000)
    (hKappa : 0<kappa) (hKappaUpper : kappa<1/50) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ L : ℝ in atTop,
      c*Real.exp L*L^(-222:ℝ)≤parityOriginalRoughMass434 Psi (-1) beta L := by
  obtain ⟨c0,hc0,hMass⟩ := localizedMass_lower_bound
    Psi hSmooth.continuous hSupport hNonneg hInterior
  let a : ℝ := Real.exp (-Real.eulerMascheroniConstant)/beta/8
  have ha : 0<a := by dsimp [a];positivity
  refine ⟨a*c0,mul_pos ha hc0,?_⟩
  filter_upwards [hMass,parity_original_negative_positive_presieve_mass434
    Psi hSmooth hSupport hNonneg hInterior beta kappa hBeta hSmall hKappa hKappaUpper,
    eventually_gt_atTop (0:ℝ)] with L hM hS hL
  have hPower : L^(-221:ℝ)/L=L^(-222:ℝ) := by
    calc
      _ = L^(-221:ℝ)/L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^((-221:ℝ)-1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  calc
    (a*c0)*Real.exp L*L^(-222:ℝ) =
        (a/L)*(c0*Real.exp L*L^(-221:ℝ)) := by rw [←hPower];ring
    _ ≤ (a/L)*localizedMass Psi (-1) L :=
      mul_le_mul_of_nonneg_left (hM (-1) (Or.inr rfl)) (by positivity)
    _ = a*localizedMass Psi (-1) L/L := by ring
    _ ≤ _ := hS.1
end Green64Analytic.Parity

end

end

