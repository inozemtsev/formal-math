module

public import Green64.Library.Sieve.Foundations.Part054
public import Green64.Library.Sieve.Foundations.FrozenDensityMesh
public import Green64.Library.Weights.Part032
public import Green64.Library.Weights.Part037
public import Green64.Library.Sieve.Foundations.Part053
public import Green64.Library.Sieve.Foundations.Part050
public import Green64.Library.Sieve.Foundations.Part044
public import Green64.Library.Sieve.Foundations.Part040

@[expose] public section

/-!
# Sieve / Foundations / Part055

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalUnbalancedReindex -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- The original complex wrapper has exactly its real full-cell value. -/
theorem parity_original_fullcell_coefficient_real434
    (proxy prime : Bool) (L S gamma : ℝ) (a b n : ℕ) :
    ((parityOriginalFullCellCoefficient434 proxy prime L S gamma a b n).re : ℂ) =
      parityOriginalFullCellCoefficient434 proxy prime L S gamma a b n := by
  classical
  by_cases hn : n∈Finset.Icc a b
  · cases proxy <;> cases prime <;>
      simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,
        parityOriginalActualFullCellSharpTest434,hn]
  · cases proxy <;> cases prime <;>
      simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,
        parityOriginalActualFullCellSharpTest434,hn]

/-- Nonzero original rough-proxy support includes n>=2. No unrestricted
rough-product converse at cofactor one is used. -/
theorem parity_original_fullcell_rough_proxy_support434
    (L S gamma : ℝ) (a b n : ℕ)
    (hne : (parityOriginalFullCellCoefficient434 true false L S gamma a b n).re≠0) :
    sourceD20Rough (Real.exp (Real.sqrt L)) n := by
  classical
  by_contra h
  simp [parityOriginalFullCellCoefficient434,parityOriginalActualFullCellProxyBeta434,
    sourceD20FullProxy,sourceD20CellProxy,h] at hne

/-- Exact agreement of the actual prime-bin floor convention and the
original exponent carrier, with no large-L hypothesis. -/
theorem parity_original_prime_bin_exponent_mem434
    (gamma eta L : ℝ) (p : ℕ) :
    p∈parityOriginalPrimeBin434 gamma eta L ↔
      p.Prime ∧ parityOriginalExponentBin434 L gamma eta p := by
  rw [parity_original_prime_bin_mem434]
  simp only [parityOriginalExponentBin434,
    Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
  rw [mul_comm L gamma,mul_comm L eta]

/-- Exact finite prime-divisor reindex of the original positive pair fibre.
The cofactor may contain repeated copies of p. Every divisibility term
automatically lies in the actual finite factor range. -/
theorem parity_original_positive_pair_prime_reindex434
    (L gamma eta : ℝ) (Y u : ℕ) (hu : u≤Y) (f : ℕ → ℝ) :
    (∑ z∈parityOriginalShiftTwoPositivePairFibre434
      (Finset.Icc 1 (Y+2))
      ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma eta)) u,
      f z.1*(if z.2.Prime then (1:ℝ) else 0)) =
    ∑ p∈parityOriginalPrimeBin434 gamma eta L,
      if p∣u+2 then f ((u+2)/p) else 0 := by
  classical
  let T := parityOriginalShiftTwoPositivePairFibre434
    (Finset.Icc 1 (Y+2))
    ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma eta)) u
  change (∑ z∈T,f z.1*(if z.2.Prime then (1:ℝ) else 0)) = _
  simp only [mul_ite,mul_one,mul_zero]
  rw [←Finset.sum_filter,←Finset.sum_filter]
  apply Finset.sum_bij (fun z _ => z.2)
  · intro z hz
    obtain ⟨hzT,hp⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzProd,hmPos,hpPos,hProd⟩ := Finset.mem_filter.mp hzT
    have hBin := (Finset.mem_filter.mp (Finset.mem_product.mp hzProd).2).2
    apply Finset.mem_filter.mpr
    refine ⟨(parity_original_prime_bin_exponent_mem434 gamma eta L z.2).mpr ⟨hp,hBin⟩,?_⟩
    exact ⟨z.1,by simpa only [Nat.mul_comm] using hProd.symm⟩
  · intro z hz z' hz' hEq
    have hZ := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hZ' := (Finset.mem_filter.mp (Finset.mem_filter.mp hz').1).2
    apply Prod.ext
    · apply Nat.mul_right_cancel hZ.2.1
      calc
        z.1*z.2 = u+2 := hZ.2.2
        _ = z'.1*z'.2 := hZ'.2.2.symm
        _ = z'.1*z.2 := by rw [hEq]
    · exact hEq
  · intro p hp
    obtain ⟨hpBin,hDiv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpPrime,hBin⟩ := (parity_original_prime_bin_exponent_mem434 gamma eta L p).mp hpBin
    have hpLe : p≤u+2 := Nat.le_of_dvd (by omega) hDiv
    have hqPos : 0<(u+2)/p := Nat.div_pos_iff.mpr ⟨hpPrime.pos,hpLe⟩
    have hqLe : (u+2)/p≤Y+2 := (Nat.div_le_self _ _).trans (by omega)
    refine ⟨((u+2)/p,p),?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,hpPrime⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hqPos,hpPrime.pos,Nat.div_mul_cancel hDiv⟩
    · exact Finset.mem_Icc.mpr ⟨by omega,hqLe⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le,by omega⟩,hBin⟩
  · intro z hz
    have hZ := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hDiv : (u+2)/z.2=z.1 := by
      rw [←hZ.2.2,Nat.mul_div_cancel _ hZ.2.1]
    simp only [hDiv]

/-- The genuine original first-replacement source, reindexed exactly by
prime divisors of u+2 and their unique cofactor. The complete-cell proxy
is unchanged; the finite source range and actual parity coefficient remain. -/
theorem parity_original_unbalanced_proxy_source_divisor_reindex434
    (d : ℕ) (L rho : ℝ) (Psi : ℝ → ℝ)
    (S gamma eta : ℝ) (Y : ℕ) :
    (parityOriginalSieveUnbalancedBinSource434 true false
      d L rho Psi S gamma eta Y).re =
    ∑ p∈parityOriginalPrimeBin434 gamma eta L,
      ∑ u∈Finset.range (Y+1),
        if p∣u+2 then
          (parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L)) *
          (parityOriginalFullCellCoefficient434 true false
            L S gamma 1 (Y+2) ((u+2)/p)).re else 0 := by
  classical
  let F := parityOriginalFullCellCoefficient434 true false L S gamma 1 (Y+2)
  have hSource :
      (parityOriginalSieveUnbalancedBinSource434 true false
        d L rho Psi S gamma eta Y).re =
      ∑ u∈Finset.range (Y+1),
        (parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L)) *
        ∑ z∈parityOriginalShiftTwoPositivePairFibre434
          (Finset.Icc 1 (Y+2))
          ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma eta)) u,
          (F z.1).re*(if z.2.Prime then (1:ℝ) else 0) := by
    unfold parityOriginalSieveUnbalancedBinSource434
    have h := parity_original_parity_source_coeff_congr434 d L rho Psi
      (Finset.Icc 1 (Y+2))
      ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma eta))
      F (parityOriginalFullCellCoefficient434 false true L S gamma 1 (Y+2))
      (fun m => ((F m).re : ℂ))
      (fun n => Complex.ofReal (if n.Prime then (1:ℝ) else 0)) Y
      (by intro m hm
          exact (parity_original_fullcell_coefficient_real434 true false L S gamma 1 (Y+2) m).symm)
      (by intro n hn
          have hn' := (Finset.mem_filter.mp hn).1
          by_cases hp : n.Prime <;>
            simp [parityOriginalFullCellCoefficient434,
              parityOriginalActualFullCellSharpTest434,hn',hp])
    rw [h,parity_original_parity_source_real_coeff_re434]
  rw [hSource]
  have hReindex :
      (∑ u∈Finset.range (Y+1),
        (parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L)) *
        ∑ z∈parityOriginalShiftTwoPositivePairFibre434
          (Finset.Icc 1 (Y+2))
          ((Finset.Icc 1 (Y+2)).filter (parityOriginalExponentBin434 L gamma eta)) u,
          (F z.1).re*(if z.2.Prime then (1:ℝ) else 0)) =
      ∑ u∈Finset.range (Y+1),
        (parityWeight d L rho u*Psi ((u:ℝ)/Real.exp L)) *
        ∑ p∈parityOriginalPrimeBin434 gamma eta L,
          if p∣u+2 then (F ((u+2)/p)).re else 0 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [parity_original_positive_pair_prime_reindex434 L gamma eta Y u
      (by have h := Finset.mem_range.mp hu; omega) (fun m => (F m).re)]
  rw [hReindex]
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedDensitySup -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- The literal fixed-bin supremum in Parity (7.8). The first density
parameter is the LEFT endpoint and the second variable is 1-t. -/
def parityOriginalUnbalancedDensitySup434 (gamma eta : ℝ) : ℝ :=
  sSup ((fun t : ℝ => Green64Analytic.SmallB.sourceDensity gamma (1-t)) ''
    Set.Icc gamma eta)

theorem parity_original_unbalanced_density_image_bdd434
    (gamma eta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta)
    (hEta : eta<1/2) :
    BddAbove ((fun t : ℝ => Green64Analytic.SmallB.sourceDensity gamma (1-t)) ''
      Set.Icc gamma eta) := by
  obtain ⟨C,hC,hBound⟩ := sourceD28_density_compact_bounded
    gamma (1-eta) (1-gamma) hGamma (by linarith)
  refine ⟨C,?_⟩
  rintro y ⟨t,ht,rfl⟩
  exact hBound (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩

theorem parity_original_density_le_bin_sup434
    (gamma eta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta)
    (hEta : eta<1/2) (t : ℝ) (ht : t∈Set.Icc gamma eta) :
    Green64Analytic.SmallB.sourceDensity gamma (1-t) ≤
      parityOriginalUnbalancedDensitySup434 gamma eta := by
  exact le_csSup
    (parity_original_unbalanced_density_image_bdd434 gamma eta hGamma hOrder hEta)
    ⟨t,ht,rfl⟩

theorem parity_original_unbalanced_density_sup_pos434
    (gamma eta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta)
    (hEta : eta<1/2) :
    0<parityOriginalUnbalancedDensitySup434 gamma eta := by
  have hLower := Green64Analytic.SmallB.sourceDensity_one_prime_lower
    gamma (1-gamma) hGamma
  have hCap := parity_original_density_le_bin_sup434 gamma eta hGamma hOrder hEta
    gamma ⟨le_rfl,hOrder.le⟩
  exact (one_div_pos.mpr (by linarith : 0<1-gamma)).trans_le (hLower.trans hCap)

/-- The small overshoot in the actual cofactor exponent is absorbed by
continuity at 1-gamma. No source cap is assumed and no endpoint is erased. -/
theorem parity_original_unbalanced_density_sup_overshoot434
    (gamma eta eps : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta)
    (hEta : eta<1/2) (hEps : 0<eps) :
    ∃ delta : ℝ, 0<delta ∧ delta<gamma ∧
      ∀ w∈Set.Icc (1-eta) (1-gamma+delta),
        Green64Analytic.SmallB.sourceDensity gamma w ≤
          parityOriginalUnbalancedDensitySup434 gamma eta+eps := by
  have hCont := sourceD27_original_density_continuousAt_w
    gamma (1-gamma) hGamma (by linarith)
  obtain ⟨r,hr,hMod⟩ := Metric.continuousAt_iff.mp hCont eps hEps
  let delta := min (gamma/2) (r/2)
  have hDelta : 0<delta := lt_min (by positivity) (by positivity)
  have hDeltaGamma : delta<gamma := (min_le_left _ _).trans_lt (by linarith)
  have hDeltaR : delta< r := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨delta,hDelta,hDeltaGamma,?_⟩
  intro w hw
  by_cases hUpper : w≤1-gamma
  · have hMem : 1-w∈Set.Icc gamma eta := ⟨by linarith,by linarith [hw.1]⟩
    have hh := parity_original_density_le_bin_sup434 gamma eta hGamma hOrder hEta
      (1-w) hMem
    have hId : 1-(1-w)=w := by ring
    rw [hId] at hh
    exact hh.trans (le_add_of_nonneg_right hEps.le)
  · have hwLow : 1-gamma<w := lt_of_not_ge hUpper
    have hd : dist w (1-gamma)< r := by
      rw [Real.dist_eq,abs_of_nonneg (by linarith)]
      linarith [hw.2]
    have hh := hMod hd
    rw [Real.dist_eq] at hh
    have hCap := parity_original_density_le_bin_sup434 gamma eta hGamma hOrder hEta
      gamma ⟨le_rfl,hOrder.le⟩
    have hDiff := (le_abs_self
      (Green64Analytic.SmallB.sourceDensity gamma w-
        Green64Analytic.SmallB.sourceDensity gamma (1-gamma))).trans_lt hh
    linarith

/-- Positive ordinary Euler factor at the actual subpower cutoff. This
uses the existing natural-prime product lower bound, including prime 2. -/
theorem parity_original_subpower_natural_euler_pos434 (L : ℝ) :
    0<sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ := by
  have hW : 1≤⌊Real.exp (Real.sqrt L)⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mpr
      (by simpa using Real.one_le_exp (Real.sqrt_nonneg L))
  have hWr : (0:ℝ)<(⌊Real.exp (Real.sqrt L)⌋₊:ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hW)
  exact (inv_pos.mpr hWr).trans_le (source_natural_euler_lower _ hW)

/-- The genuine active ORIGINAL full-cell coefficient is bounded by the
literal bin supremum with arbitrary fixed slack. The physical equation,
compact Psi and the D29 pointwise theorem supply every support premise. -/
theorem parity_original_actual_fullcell_bin_sup434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (S gamma eta eps : ℝ) (hS : 0<S) (hGamma : 0<gamma)
    (hOrder : gamma<eta) (hEta : eta<1/2) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,∀ (rho : ℝ) (u p m : ℕ),
      parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
        Psi ((u:ℝ)/Real.exp L)≠0 →
      m*p=u+2 → (Real.exp L)^gamma<(p:ℝ) → (p:ℝ)≤(Real.exp L)^eta →
      (parityOriginalFullCellCoefficient434 true false L S gamma 1
        (⌊2*Real.exp L⌋₊+2) m).re ≤
        (parityOriginalUnbalancedDensitySup434 gamma eta+eps)/
          (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊) := by
  obtain ⟨delta,hDelta,hDeltaGamma,hCap⟩ :=
    parity_original_unbalanced_density_sup_overshoot434 gamma eta (eps/2)
      hGamma hOrder hEta (by positivity)
  filter_upwards [parity_original_actual_cofactor_precise_window434
      Psi hSupport gamma eta delta hDelta,
    parity_original_actual_fullcell_cofactor_density434 Psi hSupport
      S gamma eta delta (eps/2) hS hGamma hOrder hEta hDelta hDeltaGamma
      (by positivity),eventually_gt_atTop (0:ℝ)]
      with L hWindow hPoint hL rho u p m hWeight hProd hpLow hpHigh
  have hmWindow := hWindow rho u p m hWeight hProd hpLow hpHigh
  have hmPos : (0:ℝ) < m := (Real.exp_pos _).trans_le hmWindow.1
  have hLogLow := Real.log_le_log (Real.exp_pos _) hmWindow.1
  have hLogHigh := Real.log_le_log hmPos hmWindow.2
  rw [Real.log_exp] at hLogLow hLogHigh
  have hLogMem : Real.log (m:ℝ)/L∈Set.Icc (1-eta) (1-gamma+delta) :=
    ⟨(le_div_iff₀ hL).mpr (by nlinarith),
      (div_le_iff₀ hL).mpr (by nlinarith)⟩
  have hD := hCap _ hLogMem
  have hDen : 0<L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊ :=
    mul_pos hL (parity_original_subpower_natural_euler_pos434 L)
  exact (hPoint rho u p m hWeight hProd hpLow hpHigh).trans
    ((div_le_div_iff_of_pos_right hDen).mpr (by linarith))
end Green64Analytic.Parity

end

end

/-! ## OriginalDensityMeshBudget -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
open Green64Analytic.FrozenBins
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

theorem parity_original_density_joint_continuous434 :
    ContinuousOn
      (fun q : ℝ×ℝ => Green64Analytic.SmallB.sourceDensity q.1 q.2)
      {q | 0<q.1 ∧ q.1<q.2} := by
  simpa only [Green64Analytic.SmallB.sourceDensity,
    Green64Analytic.SmallB.sourceSimplexTerm] using
    Green64Analytic.ReciprocalSimplex.density_continuity

theorem parity_original_density_square_continuous434
    (b c : ℝ) (hb : 0<b) (hbc : b<c) (hc : c<1/2) :
    ContinuousOn
      (fun q : ℝ×ℝ => Green64Analytic.SmallB.sourceDensity q.1 (1-q.2))
      (Set.Icc b c ×ˢ Set.Icc b c) := by
  apply parity_original_density_joint_continuous434.comp
    ((continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn)
  intro q hq
  change 0<q.1 ∧ q.1<1-q.2
  constructor
  · exact hb.trans_le hq.1.1
  · linarith [hq.1.2,hq.2.2]

theorem parity_original_density_integrand_nonneg434
    (b t : ℝ) (hb : 0<b) (ht : t∈Set.Icc b (1/2)) :
    0≤Green64Analytic.SmallB.sourceDensity t (1-t)*t⁻¹ := by
  have ht0 : 0<t := hb.trans_le ht.1
  have hw0 : 0<1-t := by linarith [ht.2]
  have hLower := Green64Analytic.SmallB.sourceDensity_one_prime_lower t (1-t) ht0
  exact mul_nonneg
    ((div_nonneg (by norm_num : (0:ℝ)≤1) hw0.le).trans hLower)
    (inv_nonneg.mpr ht0.le)

/-- Actual Parity (7.8), with arbitrary positive fixed slack. The supremal
density bins use the source reciprocal-simplex density. Joint continuity,
the finite adjacent-integral identity and the native minimum-disintegration
theorem supply the entire bound. Integrability and disintegration are not
hypotheses. N is fixed before all later proxy and large-L choices. -/
theorem parity_original_unbalanced_fixed_density_mesh434
    (b c eps : ℝ) (hb : 0<b) (hbc : b<c)
    (hc : c<1/2) (hEps : 0<eps) :
    ∃ N : ℕ,0 < N ∧
      Monotone (affineGrid b c N) ∧
      (∀ i : ℕ,i < N →
        b≤affineGrid b c N i ∧
        affineGrid b c N i<affineGrid b c N (i+1) ∧
        affineGrid b c N (i+1)≤ c) ∧
      (∑ i∈Finset.range N,
        parityOriginalUnbalancedDensitySup434
          (affineGrid b c N i) (affineGrid b c N (i+1))*
        Real.log (affineGrid b c N (i+1)/affineGrid b c N i)) ≤
          Green64Analytic.SmallB.sourceDensity b 1-1+eps := by
  let F := fun q : ℝ×ℝ => Green64Analytic.SmallB.sourceDensity q.1 (1-q.2)
  have hF : ContinuousOn F (Set.Icc b c ×ˢ Set.Icc b c) :=
    parity_original_density_square_continuous434 b c hb hbc hc
  have hLog : 0<Real.log (c/b) := Real.log_pos ((one_lt_div hb).mpr hbc)
  obtain ⟨N,hN,hRange,hLocal⟩ :=
    exists_frozen_density_grid F hbc (div_pos hEps hLog) hF
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hStrict (i : ℕ) : affineGrid b c N i<affineGrid b c N (i+1) := by
    rw [←sub_pos,affineGrid_step b c N i hN]
    exact div_pos (sub_pos.mpr hbc) hNr
  have hMono : Monotone (affineGrid b c N) := by
    intro i j hij
    have hijr : (i:ℝ)≤(j:ℝ) := by exact_mod_cast hij
    have hq := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hijr (sub_nonneg.mpr hbc.le)) hNr.le
    dsimp [affineGrid]
    linarith
  have hSum := frozen_upper_log_sum F hb hbc hF N hN hLocal
  change (∑ i∈Finset.range N,
      parityOriginalUnbalancedDensitySup434
        (affineGrid b c N i) (affineGrid b c N (i+1))*
      Real.log (affineGrid b c N (i+1)/affineGrid b c N i)) ≤
    (∫ t in b..c,Green64Analytic.SmallB.sourceDensity t (1-t)*t⁻¹)+
      (eps/Real.log (c/b))*Real.log (c/b) at hSum
  rw [div_mul_cancel₀ _ (ne_of_gt hLog)] at hSum
  have hInt := Green64Analytic.MinDisintegration.source_density_intervalIntegrable
    b hb (by linarith)
  have hNonneg :
      0≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc b (1/2))]
        (fun t : ℝ => Green64Analytic.SmallB.sourceDensity t (1-t)*t⁻¹) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    exact parity_original_density_integrand_nonneg434 b t hb ⟨ht.1.le,ht.2⟩
  have hIntegral := intervalIntegral.integral_mono_interval
    le_rfl hbc.le hc.le hNonneg hInt
  rw [←Green64Analytic.MinDisintegration.literal_minimum_disintegration
    b hb (by linarith)] at hIntegral
  refine ⟨N,hN,hMono,?_,?_⟩
  · intro i hi
    exact ⟨(hRange i (Nat.le_of_lt hi)).1,hStrict i,
      (hRange (i+1) (Nat.succ_le_of_lt hi)).2⟩
  · linarith [hSum,hIntegral]
end Green64Analytic.Parity

end

end

/-! ## OriginalSmallBChoice -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- An actual fixed sufficiently small b for the original initial-minus-
unbalanced cancellation. The source small-b bound is the closed native
unconditional theorem, and b=1/(40*T) is chosen from T*exp(-T) -> 0.
No density comparison, PNT/Mertens premise or desired coefficient bound
is supplied as a hypothesis. -/
theorem parity_original_exists_small_b_unbalanced_margin434 :
    ∃ b : ℝ,0<b ∧ b≤1/1000 ∧
      (4/5:ℝ) ≤
        Real.exp (-Real.eulerMascheroniConstant)/b*
          (1-parityOriginalPresieveExponentialConstant434*Real.exp (-(1/(40*b))))-
        (Green64Analytic.SmallB.sourceDensity b 1-1+1/10) := by
  let K := 40*Real.exp (-Real.eulerMascheroniConstant)*
    (parityOriginalPresieveExponentialConstant434+Green64Analytic.SmallB.sieveC)
  have hDecay : Tendsto (fun T : ℝ => K*(T*Real.exp (-T))) atTop (𝓝 0) := by
    simpa only [pow_one,mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul K
  have hSmall : ∀ᶠ T : ℝ in atTop,K*(T*Real.exp (-T))≤1/10 :=
    (hDecay.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/10))).mono
      (fun T h => h.le)
  obtain ⟨T,hT25,hSmallT⟩ := ((eventually_ge_atTop (25:ℝ)).and hSmall).exists
  have hT : 0<T := by linarith
  let b := 1/(40*T)
  have hb : 0<b := div_pos (by norm_num) (mul_pos (by norm_num) hT)
  have hbSmall : b≤1/1000 := by
    change 1/(40*T)≤1/1000
    apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<40) hT)).mpr
    linarith
  have hExponent : 1/(40*b)=T := by
    dsimp [b]
    field_simp [ne_of_gt hT]
  have hCorrection :
      Real.exp (-Real.eulerMascheroniConstant)/b*
        (parityOriginalPresieveExponentialConstant434+Green64Analytic.SmallB.sieveC)*
          Real.exp (-(1/(40*b)))≤1/10 := by
    rw [hExponent]
    have hEq :
        Real.exp (-Real.eulerMascheroniConstant)/b*
          (parityOriginalPresieveExponentialConstant434+Green64Analytic.SmallB.sieveC)*
            Real.exp (-T)=K*(T*Real.exp (-T)) := by
      dsimp [b,K]
      field_simp
    rw [hEq]
    exact hSmallT
  have hDensity := Green64Analytic.SourcePNT2.literal_small_b_exp_bound_unconditional
    b hb (by linarith : b≤1/100)
  refine ⟨b,hb,hbSmall,?_⟩
  nlinarith [hDensity,hCorrection]
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedConditionalCap -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

theorem parity_original_conditional_bin_mass_nonneg434
    (Psi : ℝ → ℝ) (hNonneg : ∀ x,0≤Psi x)
    (rho gamma eta L : ℝ) (hRho : |rho|≤1) :
    0≤parityOriginalConditionalBinMass434 Psi rho gamma eta L := by
  unfold parityOriginalConditionalBinMass434 parityOriginalConditionedRoughMass434
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro u hu
  split_ifs
  · exact mul_nonneg
      (parity_original_parity_A_nonneg434 (sourceOriginalLiteralDepth 20 L) L rho hRho u)
      (hNonneg _)
  · exact le_rfl

/-- Actual post-proxy unbalanced source versus actual conditioned sieve
mass. The exact divisor reindex is used, and nonzero full-cell proxy
forces roughness of the cofactor and hence of u+2. Repeated primes are
allowed; neither coprimality nor squarefreeness is assumed. -/
theorem parity_original_unbalanced_proxy_le_conditional_mass434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ x,0≤Psi x)
    (S gamma eta eps : ℝ) (hS : 0<S) (hGamma : 0<gamma)
    (hOrder : gamma<eta) (hEta : eta<1/2) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,∀ rho : ℝ,|rho|≤1 →
      (parityOriginalSieveUnbalancedBinSource434 true false
        (sourceOriginalLiteralDepth 20 L) L rho Psi S gamma eta
        ⌊2*Real.exp L⌋₊).re ≤
      ((parityOriginalUnbalancedDensitySup434 gamma eta+eps)/
        (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊))*
        parityOriginalConditionalBinMass434 Psi rho gamma eta L := by
  filter_upwards [parity_original_actual_fullcell_bin_sup434
      Psi hSupport S gamma eta eps hS hGamma hOrder hEta hEps,
    parity_original_conditioned_subpower_level434 gamma eta (eta+1) 0 hGamma (by linarith),
    eventually_gt_atTop (0:ℝ)] with L hCap hLevel hL rho hRho
  let C := (parityOriginalUnbalancedDensitySup434 gamma eta+eps)/
    (L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)
  have hC : 0≤C := div_nonneg
    (by linarith [parity_original_unbalanced_density_sup_pos434 gamma eta hGamma hOrder hEta])
    (mul_nonneg hL.le (parity_original_subpower_natural_euler_pos434 L).le)
  rw [parity_original_unbalanced_proxy_source_divisor_reindex434]
  unfold parityOriginalConditionalBinMass434 parityOriginalConditionedRoughMass434
  change (∑ p∈parityOriginalPrimeBin434 gamma eta L,∑ u∈Finset.range (⌊2*Real.exp L⌋₊+1),
    if p∣u+2 then
      (parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
        Psi ((u:ℝ)/Real.exp L))*
      (parityOriginalFullCellCoefficient434 true false L S gamma 1
        (⌊2*Real.exp L⌋₊+2) ((u+2)/p)).re else 0) ≤
    C*∑ p∈parityOriginalPrimeBin434 gamma eta L,∑ u∈Finset.range (⌊2*Real.exp L⌋₊+1),
      if p∣u+2 ∧ Real.exp (Real.sqrt L)<((u+2).minFac:ℝ) then
        parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
          Psi ((u:ℝ)/Real.exp L) else 0
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hPrime,hpLow,hpHigh⟩ := (parity_original_prime_bin_mem434 gamma eta L p).mp hp
  have hpW : Real.exp (Real.sqrt L)<(p:ℝ) := hLevel.2.1.trans hpLow
  apply Finset.sum_le_sum
  intro u hu
  have hWeightNonneg :=
    mul_nonneg (parity_original_parity_A_nonneg434
      (sourceOriginalLiteralDepth 20 L) L rho hRho u) (hNonneg ((u:ℝ)/Real.exp L))
  by_cases hDiv : p∣u+2
  · simp only [hDiv,ite_true,true_and]
    by_cases hWeight :
        parityWeight (sourceOriginalLiteralDepth 20 L) L rho u*
          Psi ((u:ℝ)/Real.exp L)=0
    · simp only [hWeight,zero_mul,ite_self,mul_zero,le_refl]
    · by_cases hProxy :
          (parityOriginalFullCellCoefficient434 true false L S gamma 1
            (⌊2*Real.exp L⌋₊+2) ((u+2)/p)).re=0
      · rw [hProxy,mul_zero]
        split_ifs
        · exact mul_nonneg hC hWeightNonneg
        · simp only [mul_zero,le_refl]
      · have hRough := parity_original_fullcell_rough_proxy_support434
          L S gamma 1 (⌊2*Real.exp L⌋₊+2) ((u+2)/p) hProxy
        have hProd : ((u+2)/p)*p=u+2 := Nat.div_mul_cancel hDiv
        have hShiftRough := (parity_original_rough_mul_prime_iff434
          (Real.exp (Real.sqrt L)) ((u+2)/p) p hRough.1 hPrime hpW).mpr hRough
        rw [hProd] at hShiftRough
        rw [if_pos hShiftRough.2]
        have hh := mul_le_mul_of_nonneg_left
          (hCap rho u p ((u+2)/p) hWeight hProd hpLow hpHigh) hWeightNonneg
        simpa only [C,mul_comm] using hh
  · simp only [hDiv,ite_false,false_and,mul_zero,le_refl]
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedBinBudget -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- The ordinary Euler normalization in the actual D29 proxy includes
prime 2 and is definitionally the rough-count Euler product. -/
theorem parity_original_rough_euler_natural434 (z : ℝ) :
    Green64Analytic.SmallB.roughEuler z=sourceNaturalEuler ⌊z⌋₊ := rfl

/-- Genuine conditioned source mass normalized by the ordinary Euler
factor. This joins the actual negative-parity (8.2) to the exact shifted
Euler ratio, retaining the singular-series multiplier. -/
theorem parity_original_negative_conditional_natural_euler_limit434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (gamma eta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta)
    (hEta : eta<1/2) :
    Tendsto (fun L : ℝ => parityOriginalConditionalBinMass434 Psi (-1) gamma eta L/
      (localizedMass Psi (-1) L*
        sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊))
      atTop (𝓝 (singularSeries*Real.log (eta/gamma))) := by
  have hM := parity_original_negative_conditional_sieve_8_2_434
    Psi hSmooth hSupport hNonneg hInterior gamma eta ((eta+1/2)/2)
    hGamma hOrder (by linarith) (by linarith)
  have hE : Tendsto (fun L : ℝ =>
      parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L))/
        sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)
      atTop (𝓝 singularSeries) := by
    simpa only [Function.comp_def,parity_original_rough_euler_natural434] using
      parity_original_shifted_euler_ratio_tendsto434.comp
        (Real.tendsto_exp_atTop.comp Real.tendsto_sqrt_atTop)
  have hProduct := hM.mul hE
  rw [mul_comm (Real.log (eta/gamma)) singularSeries] at hProduct
  apply hProduct.congr'
  filter_upwards [negative_localizedMass_eventually_pos
    Psi hSmooth.continuous hSupport hNonneg hInterior] with L hX
  have hV := parity_original_subpower_natural_euler_pos434 L
  have hV1 := parity_original_shifted_euler_pos434 (Real.exp (Real.sqrt L))
  field_simp [ne_of_gt hX,ne_of_gt hV,ne_of_gt hV1]

/-- Actual ORIGINAL single-bin post-proxy source at scale Xminus/L.
No density cap, source-identity or positive source-mass hypothesis is
assumed: all three are established by the preceding native source proofs. -/
theorem parity_original_negative_unbalanced_proxy_bin_budget434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (S gamma eta eps : ℝ) (hS : 0<S) (hGamma : 0<gamma)
    (hOrder : gamma<eta) (hEta : eta<1/2) (hEps : 0<eps) :
    ∀ᶠ L : ℝ in atTop,
      (parityOriginalSieveUnbalancedBinSource434 true false
        (sourceOriginalLiteralDepth 20 L) L (-1) Psi S gamma eta
        ⌊2*Real.exp L⌋₊).re ≤
      (singularSeries*
        parityOriginalUnbalancedDensitySup434 gamma eta*Real.log (eta/gamma)+eps)*
        (localizedMass Psi (-1) L/L) := by
  let C := parityOriginalUnbalancedDensitySup434 gamma eta
  let T := singularSeries*Real.log (eta/gamma)
  have hSing : 0<singularSeries :=
    lt_of_lt_of_le zero_lt_one singularSeries_converges_and_ge_one.2
  have hLog : 0<Real.log (eta/gamma) := Real.log_pos ((one_lt_div hGamma).mpr hOrder)
  have hT : 0<T := mul_pos hSing hLog
  let delta := eps/(2*T)
  have hDelta : 0<delta := div_pos hEps (mul_pos (by norm_num) hT)
  have hDeltaT : delta*T=eps/2 := by
    dsimp [delta]
    field_simp [ne_of_gt hT]
  let g := fun L : ℝ => parityOriginalConditionalBinMass434 Psi (-1) gamma eta L/
    (localizedMass Psi (-1) L*
      sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)
  have hG : Tendsto g atTop (𝓝 T) :=
    parity_original_negative_conditional_natural_euler_limit434
      Psi hSmooth hSupport hNonneg hInterior gamma eta hGamma hOrder hEta
  have hClose : ∀ᶠ L : ℝ in atTop,(C+delta)*g L≤C*T+eps := by
    have hTarget : (C+delta)*T<C*T+eps := by nlinarith [hDeltaT]
    exact ((hG.const_mul (C+delta)).eventually (gt_mem_nhds hTarget)).mono
      (fun L h => h.le)
  filter_upwards [parity_original_unbalanced_proxy_le_conditional_mass434
      Psi hSupport hNonneg S gamma eta delta hS hGamma hOrder hEta hDelta,
    hClose,negative_localizedMass_eventually_pos
      Psi hSmooth.continuous hSupport hNonneg hInterior,
    eventually_gt_atTop (0:ℝ)] with L hCap hBound hX hL
  have hV := parity_original_subpower_natural_euler_pos434 L
  have hAlg :
      (C+delta)/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)*
        parityOriginalConditionalBinMass434 Psi (-1) gamma eta L =
      ((C+delta)*g L)*(localizedMass Psi (-1) L/L) := by
    dsimp [g]
    field_simp [ne_of_gt hL,ne_of_gt hX,ne_of_gt hV]
  have hSource := hCap (-1) (by norm_num)
  change _≤(C+delta)/(L*sourceNaturalEuler ⌊Real.exp (Real.sqrt L)⌋₊)*
    parityOriginalConditionalBinMass434 Psi (-1) gamma eta L at hSource
  rw [hAlg] at hSource
  have hFinal := hSource.trans
    (mul_le_mul_of_nonneg_right hBound (div_pos hX hL).le)
  have hCoeff : C*T+eps=
      singularSeries*
        parityOriginalUnbalancedDensitySup434 gamma eta*Real.log (eta/gamma)+eps := by
    dsimp [C,T]
    ring
  rw [hCoeff] at hFinal
  exact hFinal
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedMeshBudget -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.FrozenBins
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- A fixed genuine finite family of source bins. The common L threshold
is obtained over Fin N, and the actual N losses are paid by eps/N. -/
theorem parity_original_negative_unbalanced_proxy_finite_budget434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (S eps : ℝ) (hS : 0<S) (hEps : 0<eps)
    (N : ℕ) (hN : 0 < N) (t : ℕ → ℝ)
    (hBins : ∀ i : ℕ,i < N → 0<t i ∧ t i<t (i+1) ∧ t (i+1)<1/2) :
    ∀ᶠ L : ℝ in atTop,
      (∑ i∈Finset.range N,
        (parityOriginalSieveUnbalancedBinSource434 true false
          (sourceOriginalLiteralDepth 20 L) L (-1) Psi S (t i) (t (i+1))
          ⌊2*Real.exp L⌋₊).re) ≤
      (singularSeries*
        (∑ i∈Finset.range N,
          parityOriginalUnbalancedDensitySup434 (t i) (t (i+1))*
            Real.log (t (i+1)/t i))+eps)*
        (localizedMass Psi (-1) L/L) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hEach (i : Fin N) :
      ∀ᶠ L : ℝ in atTop,
        (parityOriginalSieveUnbalancedBinSource434 true false
          (sourceOriginalLiteralDepth 20 L) L (-1) Psi S (t i) (t (i+1))
          ⌊2*Real.exp L⌋₊).re ≤
        (singularSeries*
          parityOriginalUnbalancedDensitySup434 (t i) (t (i+1))*
            Real.log (t (i+1)/t i)+eps/(N:ℝ))*
          (localizedMass Psi (-1) L/L) :=
    parity_original_negative_unbalanced_proxy_bin_budget434
      Psi hSmooth hSupport hNonneg hInterior S (t i) (t (i+1)) (eps/(N:ℝ))
      hS (hBins i i.isLt).1 (hBins i i.isLt).2.1
      (hBins i i.isLt).2.2 (div_pos hEps hNr)
  have hAll := Filter.eventually_all.mpr hEach
  filter_upwards [hAll] with L hBounds
  have hSum := Finset.sum_le_sum (s:=Finset.univ)
    (fun i (_hi : i∈(Finset.univ : Finset (Fin N))) => hBounds i)
  have hRange :
      (∑ i∈Finset.range N,
        (parityOriginalSieveUnbalancedBinSource434 true false
          (sourceOriginalLiteralDepth 20 L) L (-1) Psi S (t i) (t (i+1))
          ⌊2*Real.exp L⌋₊).re) ≤
      ∑ i∈Finset.range N,
        (singularSeries*
          parityOriginalUnbalancedDensitySup434 (t i) (t (i+1))*
            Real.log (t (i+1)/t i)+eps/(N:ℝ))*
          (localizedMass Psi (-1) L/L) := by
    rw [←Fin.sum_univ_eq_sum_range,←Fin.sum_univ_eq_sum_range]
    exact hSum
  have hCoeff :
      (∑ i∈Finset.range N,
        (singularSeries*
          parityOriginalUnbalancedDensitySup434 (t i) (t (i+1))*
            Real.log (t (i+1)/t i)+eps/(N:ℝ))) =
      singularSeries*
        (∑ i∈Finset.range N,
          parityOriginalUnbalancedDensitySup434 (t i) (t (i+1))*
            Real.log (t (i+1)/t i))+eps := by
    simp only [mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum,
      Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    congr 1
    field_simp [ne_of_gt hNr]
  rw [←Finset.sum_mul,hCoeff] at hRange
  exact hRange

/-- The actual ORIGINAL post-proxy unbalanced source, with the literal
Parity (7.8) density budget. The fixed N and endpoints precede every S and L.
The source lower bound and conditional sieve are already native inputs,
not unproved assumptions in this statement. -/
theorem parity_original_negative_unbalanced_proxy_mesh_budget434
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (b c meshSlack : ℝ) (hb : 0<b) (hbc : b<c)
    (hc : c<1/2) (hSlack : 0 < meshSlack) :
    ∃ N : ℕ,0 < N ∧
      Monotone (affineGrid b c N) ∧
      affineGrid b c N 0=b ∧ affineGrid b c N N=c ∧
      ∀ S : ℝ,0<S → ∀ eps : ℝ,0<eps →
        ∀ᶠ L : ℝ in atTop,
          (∑ i∈Finset.range N,
            (parityOriginalSieveUnbalancedBinSource434 true false
              (sourceOriginalLiteralDepth 20 L) L (-1) Psi S
              (affineGrid b c N i) (affineGrid b c N (i+1))
              ⌊2*Real.exp L⌋₊).re) ≤
          (singularSeries*
            (Green64Analytic.SmallB.sourceDensity b 1-1+meshSlack)+eps)*
            (localizedMass Psi (-1) L/L) := by
  obtain ⟨N,hN,hMono,hBins,hMesh⟩ :=
    parity_original_unbalanced_fixed_density_mesh434 b c meshSlack hb hbc hc hSlack
  refine ⟨N,hN,hMono,affineGrid_zero b c N,affineGrid_last b c N hN,?_⟩
  intro S hS eps hEps
  have hActual := parity_original_negative_unbalanced_proxy_finite_budget434
    Psi hSmooth hSupport hNonneg hInterior S eps hS hEps N hN (affineGrid b c N)
    (fun i hi => ⟨hb.trans_le (hBins i hi).1,(hBins i hi).2.1,
      (hBins i hi).2.2.trans_lt hc⟩)
  filter_upwards [hActual,negative_localizedMass_eventually_pos
      Psi hSmooth.continuous hSupport hNonneg hInterior,
    eventually_gt_atTop (0:ℝ)] with L hBound hX hL
  have hSing : 0≤ singularSeries :=
    le_trans zero_le_one singularSeries_converges_and_ge_one.2
  have hCoeff := mul_le_mul_of_nonneg_left hMesh hSing
  exact hBound.trans (mul_le_mul_of_nonneg_right
    (by linarith : singularSeries*
      (∑ i∈Finset.range N,
        parityOriginalUnbalancedDensitySup434 (affineGrid b c N i)
          (affineGrid b c N (i+1))*
        Real.log (affineGrid b c N (i+1)/affineGrid b c N i))+eps ≤
      singularSeries*
        (Green64Analytic.SmallB.sourceDensity b 1-1+meshSlack)+eps)
    (div_pos hX hL).le)
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedSharpBudget -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.FrozenBins
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Exact projection of the first negative-branch source replacements
from the already proved original two-sign required-error ledger. -/
theorem parity_original_negative_unbalanced_error_le_required434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (S b kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    (∑ i∈Finset.range N,
      ‖parityOriginalSieveUnbalancedBinSource434 false false d L (-1)
          Psi S (t i) (t (i+1)) Y-
        parityOriginalSieveUnbalancedBinSource434 true false d L (-1)
          Psi S (t i) (t (i+1)) Y‖) ≤
      requiredProxyError d L Psi S b kappa N t Y := by
  let R := fun sign : Bool =>
    (∑ i : Fin N,
      ‖parityOriginalSieveUnbalancedBinSource434 false false d L
          (if sign then 1 else -1) Psi S (t i) (t (i+1)) Y-
        parityOriginalSieveUnbalancedBinSource434 true false d L
          (if sign then 1 else -1) Psi S (t i) (t (i+1)) Y‖)+
    ‖balancedFactorSum false false d L
        (if sign then 1 else -1) Psi S b kappa Y-
      balancedFactorSum true false d L
        (if sign then 1 else -1) Psi S b kappa Y‖+
    ‖balancedFactorSum true false d L
        (if sign then 1 else -1) Psi S b kappa Y-
      balancedFactorSum true true d L
        (if sign then 1 else -1) Psi S b kappa Y‖
  have hProject : R false≤∑ sign : Bool,R sign :=
    Finset.single_le_sum (fun sign _ => by dsimp [R]; positivity)
      (Finset.mem_univ false)
  have hBranch :
      (∑ i∈Finset.range N,
        ‖parityOriginalSieveUnbalancedBinSource434 false false d L (-1)
            Psi S (t i) (t (i+1)) Y-
          parityOriginalSieveUnbalancedBinSource434 true false d L (-1)
            Psi S (t i) (t (i+1)) Y‖) ≤ R false := by
    rw [←Fin.sum_univ_eq_sum_range]
    dsimp [R]
    have hFirst := norm_nonneg
      (balancedFactorSum false false d L (-1) Psi S b kappa Y-
        balancedFactorSum true false d L (-1) Psi S b kappa Y)
    have hSecond := norm_nonneg
      (balancedFactorSum true false d L (-1) Psi S b kappa Y-
        balancedFactorSum true true d L (-1) Psi S b kappa Y)
    linarith
  exact hBranch.trans hProject

/-- Finite sharp-source comparison with the actual required ledger.
No identification of an aggregate source expression is assumed. -/
theorem parity_original_negative_unbalanced_sharp_le_proxy_error434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ) (S b kappa : ℝ)
    (N : ℕ) (t : ℕ → ℝ) (Y : ℕ) :
    (∑ i∈Finset.range N,
      (parityOriginalSieveUnbalancedBinSource434 false false d L (-1)
        Psi S (t i) (t (i+1)) Y).re) ≤
    (∑ i∈Finset.range N,
      (parityOriginalSieveUnbalancedBinSource434 true false d L (-1)
        Psi S (t i) (t (i+1)) Y).re)+
      requiredProxyError d L Psi S b kappa N t Y := by
  have hEach (i : ℕ) :
      (parityOriginalSieveUnbalancedBinSource434 false false d L (-1)
        Psi S (t i) (t (i+1)) Y).re ≤
      (parityOriginalSieveUnbalancedBinSource434 true false d L (-1)
        Psi S (t i) (t (i+1)) Y).re+
      ‖parityOriginalSieveUnbalancedBinSource434 false false d L (-1)
          Psi S (t i) (t (i+1)) Y-
        parityOriginalSieveUnbalancedBinSource434 true false d L (-1)
          Psi S (t i) (t (i+1)) Y‖ := by
    have h := Complex.re_le_norm
      (parityOriginalSieveUnbalancedBinSource434 false false d L (-1)
          Psi S (t i) (t (i+1)) Y-
        parityOriginalSieveUnbalancedBinSource434 true false d L (-1)
          Psi S (t i) (t (i+1)) Y)
    rw [Complex.sub_re] at h
    linarith
  have hSum := Finset.sum_le_sum (s:=Finset.range N) (fun i _ => hEach i)
  rw [Finset.sum_add_distrib] at hSum
  have hError := parity_original_negative_unbalanced_error_le_required434
    d L Psi S b kappa N t Y
  linarith

/-- Actual ORIGINAL sharp unbalanced budget after its real first proxy
replacement. The original D230/reserved-Q/precision chronology and common
H,J,B,S are retained. The fixed density mesh is chosen before H,J,B,S;
the arbitrary asymptotic slack and L occur last. -/
theorem parity_original_negative_unbalanced_sharp_mesh_budget434
    (b1 kappa : ℝ) (hb1 : 0<b1) (hb1Small : b1<(1/100:ℝ))
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
    (Psi : ℝ → ℝ) (hPsiSmooth : ContDiff ℝ ∞ Psi)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀t:ℝ,0≤Psi t) (hPsiLe : ∀t:ℝ,Psi t≤1)
    (hPsiInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t) :
    ∃ N H J B : ℕ,∃ S : ℝ,0 < N ∧ 2*((B:ℝ)+1)+3<S ∧
      ∀ eps : ℝ,0<eps → ∀ᶠ L : ℝ in atTop,
        (∑ i∈Finset.range N,
          (parityOriginalSieveUnbalancedBinSource434 false false
            (sourceOriginalLiteralDepth 20 L) L (-1) Psi S
            (affineGrid b1 (1/2-kappa) N i)
            (affineGrid b1 (1/2-kappa) N (i+1)) ⌊2*Real.exp L⌋₊).re) ≤
        (singularSeries*
          (Green64Analytic.SmallB.sourceDensity b1 1-1+1/10)+eps)*
          (localizedMass Psi (-1) L/L) := by
  obtain ⟨N,hN,hMono,hZero,hEnd,hProxy⟩ :=
    parity_original_negative_unbalanced_proxy_mesh_budget434
      Psi hPsiSmooth hPsiSet hPsiPos hPsiInterior
      b1 (1/2-kappa) (1/10) hb1 (by linarith) (by linarith) (by norm_num)
  have hPsiComplex : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hPsiSmooth
  have hPsiWide : ∀t:ℝ,(Psi t:ℂ)≠0 → (1/64:ℝ)≤t ∧ t≤64 := by
    intro t ht
    have hne : Psi t≠0 := by simpa only [ne_eq,Complex.ofReal_eq_zero] using ht
    have hs := hPsiSet hne
    constructor <;> linarith [hs.1,hs.2]
  obtain ⟨H,J,B,S,hS,hErrors⟩ :=
    parity_original_sieve_D230_total_proxy_error_littleO_Xrho434
      N b1 kappa hb1 hb1Small hkappa hkappaSmall jQ target C0 beta betaP K0 A R
      hbetaP hbstar hBeta hBand hC0 hTarget hK0Target hPrecision hbeta hK0 hA hR
      buf hSmooth hSupport hOne4 hCube Psi hPsiComplex hPsiWide hPsiSet hPsiPos
      hPsiLe hPsiInterior
  have hSpos : 0<S := by have hB := Nat.cast_nonneg (α:=ℝ) B; linarith
  have hError := (hErrors (affineGrid b1 (1/2-kappa) N) hMono hZero hEnd
    (-1) (Or.inr rfl)).1
  refine ⟨N,H,J,B,S,hN,hS,?_⟩
  intro eps hEps
  filter_upwards [hProxy S hSpos (eps/2) (by positivity),
    hError.bound (by positivity : 0<eps/2),
    negative_localizedMass_eventually_pos
      Psi hPsiSmooth.continuous hPsiSet hPsiPos hPsiInterior,
    eventually_gt_atTop (0:ℝ)] with L hP hE hX hL
  have hEpos := parity_original_sieve_required_proxy_error_nonneg434
    (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N
      (affineGrid b1 (1/2-kappa) N) ⌊2*Real.exp L⌋₊
  have hScale : 0≤localizedMass Psi (-1) L/L := (div_pos hX hL).le
  simp only [Real.norm_eq_abs,abs_of_nonneg hEpos,abs_of_nonneg hScale] at hE
  have hCompare := parity_original_negative_unbalanced_sharp_le_proxy_error434
    (sourceOriginalLiteralDepth 20 L) L Psi S b1 kappa N
      (affineGrid b1 (1/2-kappa) N) ⌊2*Real.exp L⌋₊
  nlinarith
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedParameterClosure -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.FrozenBins
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- All original TypeII and cutoff-buffer parameters are actual existing
native witnesses. Reserved Q and target precision 232 are fixed before
K0,H,J,B,S and L. No analytic or carrier-equality premise is left. -/
theorem parity_original_negative_unbalanced_sharp_budget_exists434
    (Psi : ℝ → ℝ) (hPsiSmooth : ContDiff ℝ ∞ Psi)
    (hPsiSet : Function.support Psi ⊆ Set.Icc 1 2)
    (hPsiPos : ∀ t,0≤Psi t) (hPsiLe : ∀ t,Psi t≤1)
    (hPsiInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (b1 kappa : ℝ) (hb1 : 0<b1) (hb1Small : b1<1/100)
    (hkappa : 0<kappa) (hkappaSmall : kappa<1/50) :
    ∃ N H J B : ℕ,∃ S : ℝ,0 < N ∧ 2*((B:ℝ)+1)+3<S ∧
      ∀ eps : ℝ,0<eps → ∀ᶠ L : ℝ in atTop,
        (∑ i∈Finset.range N,
          (parityOriginalSieveUnbalancedBinSource434 false false
            (sourceOriginalLiteralDepth 20 L) L (-1) Psi S
            (affineGrid b1 (1/2-kappa) N i)
            (affineGrid b1 (1/2-kappa) N (i+1)) ⌊2*Real.exp L⌋₊).re) ≤
        (singularSeries*
          (Green64Analytic.SmallB.sourceDensity b1 1-1+1/10)+eps)*
          (localizedMass Psi (-1) L/L) := by
  let betaP : ℝ := b1/12
  let beta : ℝ := b1/3
  have hbetaP : 0<betaP := by dsimp [betaP]; positivity
  have hbstar : 2*betaP≤b1/3 := by dsimp [betaP]; linarith
  have hBeta : beta≤2*(b1/3) := by dsimp [beta]; linarith
  have hbeta : 0<beta := by dsimp [beta]; positivity
  obtain ⟨jQ,hBand⟩ := parity_original_exists_fixed_reserved_Q_band434 betaP hbetaP
  obtain ⟨target,K0,hTarget,hPrecision,hK0,hK0Target⟩ :=
    parity_original_TypeII_target_K0_precision_compatible434 ((230:ℝ)+2)
  obtain ⟨A,hA64,R,hR,buf,hSmooth,hSupport,hOne4,hCube⟩ :=
    parity_original_true_smooth_psi_uniform_fourier_buffer_exists434
  exact parity_original_negative_unbalanced_sharp_mesh_budget434
    b1 kappa hb1 hb1Small hkappa hkappaSmall
    jQ target 1 beta betaP K0 A R hbetaP hbstar hBeta hBand
    (by norm_num) hTarget hK0Target hPrecision hbeta hK0 (by linarith) hR
    buf hSmooth hSupport hOne4 hCube Psi hPsiSmooth hPsiSet hPsiPos hPsiLe hPsiInterior
end Green64Analytic.Parity

end

end

/-! ## OriginalUnbalancedSieve83 -/

section

open Filter Real Topology
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.FrozenBins
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

/-- Literal remaining source after the unbalanced subtraction is bounded
by the actual prime mass plus the actual balanced-composite mass.
The least-prime partition is exact and counts multiplicities. -/
theorem parity_original_rough_minus_unbalanced_le_prime_balanced434
    (Psi : ℝ → ℝ) (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ x,0≤Psi x)
    (rho beta kappa L S : ℝ) (hRho : |rho|≤1) (hL : 0≤L) (hBeta : beta≤1)
    (N : ℕ) (t : ℕ → ℝ) (ht : Monotone t)
    (hZero : t 0=beta) (hEnd : t N=1/2-kappa) :
    parityOriginalRoughMass434 Psi rho beta L-
      (∑ i∈Finset.range N,
        (parityOriginalSieveUnbalancedBinSource434 false false
          (sourceOriginalLiteralDepth 20 L) L rho Psi S (t i) (t (i+1))
          ⌊2*Real.exp L⌋₊).re) ≤
    primeMass Psi rho L+
      balancedCompositeMass (sourceOriginalLiteralDepth 20 L)
        L rho Psi kappa ⌊2*Real.exp L⌋₊ := by
  have hEq := parity_original_rough_prime_composite_decomposition434
    Psi hSupport rho beta kappa L hL hBeta t ht N hZero hEnd
  have hCompare := Finset.sum_le_sum (s:=Finset.range N) (fun i _ =>
    parity_original_unbalanced_composite_mass_le_source434
      (sourceOriginalLiteralDepth 20 L) L rho hRho Psi hNonneg S
      (t i) (t (i+1)) ⌊2*Real.exp L⌋₊)
  linarith

/-- Original Parity (8.3) for h=-2 and negative parity, with no conditional
sieve, density-budget, parameter-witness or positive-mass assumptions.
The conclusion concerns the genuine prime and balanced-composite masses.
All source parameters, including a sufficiently small b and the common
H,J,B,S, are constructed before the final eventual L. -/
theorem negative_prime_or_composite_mass_lower_bound
    (Psi : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ Psi)
    (hSupport : Function.support Psi ⊆ Set.Icc 1 2)
    (hNonneg : ∀ t,0≤Psi t) (hLe : ∀ t,Psi t≤1)
    (hInterior : ∃ t : ℝ,1<t ∧ t<2 ∧ 0<Psi t)
    (kappa : ℝ) (hKappa : 0<kappa) (hKappaUpper : kappa<1/50) :
    ∀ᶠ L : ℝ in atTop,
      (singularSeries/2)*
        (localizedMass Psi (-1) L/L) ≤
      primeMass Psi (-1) L+
        balancedCompositeMass (sourceOriginalLiteralDepth 20 L)
          L (-1) Psi kappa ⌊2*Real.exp L⌋₊ := by
  obtain ⟨b,hb,hSmall,hMargin⟩ := parity_original_exists_small_b_unbalanced_margin434
  obtain ⟨N,H,J,B,S,hN,hS,hSharp⟩ :=
    parity_original_negative_unbalanced_sharp_budget_exists434
      Psi hSmooth hSupport hNonneg hLe hInterior b kappa hb (by linarith)
      hKappa hKappaUpper
  have hSing : 0<singularSeries :=
    lt_of_lt_of_le zero_lt_one singularSeries_converges_and_ge_one.2
  have hMono : Monotone (affineGrid b (1/2-kappa) N) := by
    intro i j hij
    have hijr : (i:ℝ)≤(j:ℝ) := by exact_mod_cast hij
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hWidth : 0≤(1/2-kappa)-b := by linarith
    have hq := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hijr hWidth) hNr.le
    dsimp [affineGrid]
    linarith
  filter_upwards [parity_original_negative_initial_presieve_8_1_434
      Psi hSmooth hSupport hNonneg hInterior b kappa
        (singularSeries/10) hb hSmall hKappa hKappaUpper (by positivity),
    hSharp (singularSeries/10) (by positivity),
    negative_localizedMass_eventually_pos
      Psi hSmooth.continuous hSupport hNonneg hInterior,
    eventually_gt_atTop (0:ℝ)] with L hInitial hUnbalanced hX hL
  have hInitial' :
      (singularSeries*
          (Real.exp (-Real.eulerMascheroniConstant)/b*
            (1-parityOriginalPresieveExponentialConstant434*Real.exp (-(1/(40*b)))))-
        singularSeries/10)*
        (localizedMass Psi (-1) L/L) ≤
      parityOriginalRoughMass434 Psi (-1) b L := by
    convert hInitial using 1 <;> ring
  have hMarginMul := mul_le_mul_of_nonneg_left hMargin hSing.le
  have hCoefficient :
      singularSeries/2 ≤
        (singularSeries*
          (Real.exp (-Real.eulerMascheroniConstant)/b*
            (1-parityOriginalPresieveExponentialConstant434*Real.exp (-(1/(40*b)))))-
          singularSeries/10)-
        (singularSeries*
          (Green64Analytic.SmallB.sourceDensity b 1-1+1/10)+
            singularSeries/10) := by
    nlinarith [hMarginMul]
  have hScaled := mul_le_mul_of_nonneg_right hCoefficient (div_pos hX hL).le
  have hRemaining :
      (singularSeries/2)*
        (localizedMass Psi (-1) L/L) ≤
      parityOriginalRoughMass434 Psi (-1) b L-
        (∑ i∈Finset.range N,
          (parityOriginalSieveUnbalancedBinSource434 false false
            (sourceOriginalLiteralDepth 20 L) L (-1) Psi S
            (affineGrid b (1/2-kappa) N i)
            (affineGrid b (1/2-kappa) N (i+1)) ⌊2*Real.exp L⌋₊).re) := by
    nlinarith [hInitial',hUnbalanced,hScaled]
  exact hRemaining.trans
    (parity_original_rough_minus_unbalanced_le_prime_balanced434
      Psi hSupport hNonneg (-1) b kappa L S (by norm_num) hL.le (by linarith)
      N (affineGrid b (1/2-kappa) N) hMono (affineGrid_zero _ _ _)
      (affineGrid_last _ _ _ hN))
end Green64Analytic.Parity

end

end

