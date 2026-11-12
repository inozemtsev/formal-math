module

public import Green64.Library.Weights.Part044
public import Green64.Library.Weights.OriginalGroupMasses
public import Green64.Library.Analysis.Estimates.Part011
public import Green64.Library.Correlation.PhysicalPathDamping
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Green64.Library.Weights.Part004

@[expose] public section

/-!
# Correlation / Part035

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceNativeOriginalBIGSharedDefect -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6500000

/-- The actual full native BIG prime family supplies every analytic premise
for the original all-endpoint shared-draw defect with an arbitrary complex
source coupling K and arbitrary position-dependent envelope B>=0. In
particular the upper bound is not made a fixed logarithmic power BEFORE
the endpoint summation. Exact forbidden set includes BOTH endpoint prime
divisors and every explicit auxiliary prime; the sampling law is the
unconditioned full harmonic BIG mass, with no replacement by distinct
draws. This is a single GROUP-SHARED draw and is NOT, alone, a full
J-fold RAW R_J overlap estimate. -/
theorem eventually_native_original_BIG_shared_dirty_envelope434
    (r : ℕ) (hr : 1 ≤ r) (Ca D : ℝ) (hCa : 0 ≤ Ca) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp 1 ≤ L ∧
      ∀ (w wp : ℕ) (aux : Finset ℕ)
        (K : (sourceNativeOriginalBigType434 r L → ℕ) → ℂ)
        (B : ℝ),
      0 ≤ B → 0 < w → 0 < wp →
      (w:ℝ) ≤ Real.exp (2*L) →
      (wp:ℝ) ≤ Real.exp (2*L) →
      (aux.card:ℝ) ≤ Ca*Real.log L →
      (∀ s ∈ Fintype.piFinset (sourceNativeOriginalTb434 r L),
        ‖K s‖ ≤ B) →
      ‖∑ s ∈ Fintype.piFinset (sourceNativeOriginalTb434 r L),
        if sourceSharedClean434
             (fun _ => sourceSharedForbidden434 w wp aux) s
        then (0:ℂ)
        else
          (sourceSharedLaw434
            (fun i => sourcePrimeSharedAtom434
              (sourceNativeOriginalVbig434 r L i)) s : ℂ) * K s‖ ≤
        B*L^(-D) := by
  classical
  let Vfloor : ℝ := Real.log (6/5:ℝ)/2
  let Cgroup : ℝ := 3+(Real.log 2)⁻¹
  have hv : 0 < Vfloor :=
    ShiftTwoTerminal.source_actual_P_uniform_mass_floor_positive
  have hCgroup : 0 ≤ Cgroup := by
    dsimp [Cgroup]
    have hpos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  filter_upwards [
      eventually_source_actual_shared_arbitrary_envelope434
        (3/10:ℝ) Vfloor Cgroup Ca D
        (by norm_num) hv hCgroup hCa,
      eventually_source_native_original_group_masses434 r hr,
      eventually_ge_atTop (Real.exp 1)]
    with L hSaving hMass hL
  refine ⟨hL, ?_⟩
  intro w wp aux K B hB hw hwp hwSize hwpSize hAux hK
  obtain ⟨_, hS, hMasses⟩ := hMass
  have hV : ∀ g : sourceNativeOriginalBigType434 r L,
      sourceNativeOriginalVbig434 r L g =
        ∑ p ∈ sourceNativeOriginalTb434 r L g, 1/(p:ℝ) := by
    intro g
    simp only [sourceNativeOriginalVbig434, one_div]
  have hVmin : ∀ g : sourceNativeOriginalBigType434 r L,
      Vfloor ≤ sourceNativeOriginalVbig434 r L g :=
    fun g => (hMasses hS).2.2 g |>.1
  have hPmin : ∀ g : sourceNativeOriginalBigType434 r L,
      ∀ p ∈ sourceNativeOriginalTb434 r L g,
        Real.exp (L^(3/10:ℝ)) ≤ (p:ℝ) := by
    intro g p hp
    exact (source_native_original_Tb_prime_range434 r L g p hp).2.1
  have hcount : (Fintype.card (sourceNativeOriginalBigType434 r L):ℝ) ≤
      Cgroup * Real.log L := (source_native_original_group_upper_counts434
        r L hS hr hL).2
  exact hSaving (sourceNativeOriginalTb434 r L)
    (sourceNativeOriginalVbig434 r L)
    w wp aux K B hB hw hwp hwSize hwpSize
    hcount hAux hV hVmin hPmin hK
end Green64Analytic.SourceBlockSieve

end

end

/-! ## EulerRelativeCRT -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A quantitative positive lower bound for the ACTUAL local-density
product. The means, and their sum, are unchanged. -/
theorem b638_euler_lower434 (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p ≤ 1/2) :
    Real.exp (-2*(∑ p ∈ P, w p)) ≤ ∏ p ∈ P, (1-w p) := by
  have hlocal (p : ℕ) (hp : p ∈ P) : Real.exp (-2*w p) ≤ 1-w p := by
    have hu := hw p hp
    have ht : 0 < 1-w p := by linarith
    have hi : (1-w p)⁻¹ ≤ 1+2*w p := by
      rw [←one_div]
      apply (div_le_iff₀ ht).mpr
      nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
    have hl := Real.one_sub_inv_le_log_of_pos ht
    have hh : -2*w p ≤ Real.log (1-w p) := by linarith
    simpa only [Real.exp_log ht] using Real.exp_le_exp.mpr hh
  calc
    _ = ∏ p ∈ P, Real.exp (-2*w p) := by rw [←Real.exp_sum,Finset.mul_sum]
    _ ≤ _ := Finset.prod_le_prod₀ (fun p hp => (Real.exp_pos _).le) hlocal

/-- Relative form of the complete finite physical-path CRT error. Both
Bonferroni and finite class-count errors remain visible. No independence
or cancellation estimate is a premise. -/
theorem b638_relative_physical_path_CRT434
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (Q a A B : ℕ) (hQ : 0 < Q) (hAB : A < B)
    (hc : ∀ p ∈ P, Q.Coprime p)
    (visits : Finset ℕ) (eta : ℕ → ℝ) (offset : ℕ → ℤ)
    (heta : ∀ i ∈ visits, 0 ≤ eta i ∧ eta i ≤ 1)
    (hhalf : ∀ p ∈ P,
      b637ResidueMean434 (b637PathResidueLoss434 visits eta offset) p ≤ 1/2)
    (K : ℕ) :
    let f := b637PathResidueLoss434 visits eta offset
    let lam := ∑ p ∈ P, b637ResidueMean434 f p
    let V := ∏ p ∈ P, (1-b637ResidueMean434 f p)
    let U := 1+∑ p ∈ P, b637ResidueTotal434 f p
    let H : ℝ := (B-A:ℕ)
    Real.exp (-2*lam) ≤ V ∧
    |(∑ n ∈ Finset.Ico A B, if Nat.ModEq Q n a then
        ∏ p ∈ P, ∏ i ∈ visits,
          (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1) else 0) - H/(Q:ℝ)*V| ≤
      (H/(Q:ℝ)*V)*
        (Real.exp (4*lam)/(2:ℝ)^(2*K+1) +
          ((Q:ℝ)/H)*2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1)*Real.exp (2*lam)) := by
  dsimp only
  let f := b637PathResidueLoss434 visits eta offset
  let lam := ∑ p ∈ P, b637ResidueMean434 f p
  let V := ∏ p ∈ P, (1-b637ResidueMean434 f p)
  let U := 1+∑ p ∈ P, b637ResidueTotal434 f p
  let H : ℝ := (B-A:ℕ)
  have hHp : 0 < H := by dsimp [H]; exact_mod_cast Nat.sub_pos_of_lt hAB
  have hQp : (0:ℝ) < Q := by exact_mod_cast hQ
  have hw : ∀ p ∈ P, 0 ≤ b637ResidueMean434 f p ∧ b637ResidueMean434 f p ≤ 1/2 := by
    intro p hp
    exact ⟨(b637_physical_path_residue_budget434 visits eta offset heta p (hP p hp).pos).2.2.1,
      hhalf p hp⟩
  have hV := b638_euler_lower434 P (b637ResidueMean434 f) hw
  change Real.exp (-2*lam) ≤ V at hV
  have hfactor : 1 ≤ V*Real.exp (2*lam) := by
    have hm := mul_le_mul_of_nonneg_right hV (Real.exp_nonneg (2*lam))
    have he : Real.exp (-2*lam)*Real.exp (2*lam)=1 := by rw [←Real.exp_add]; ring_nf; simp
    rw [he] at hm
    exact hm
  have hfinite := b637_physical_path_damping_CRT434 P hP Q a A B hQ hAB.le hc
    visits eta offset heta K
  dsimp only at hfinite
  have hU0 : 0 ≤ U := by
    dsimp [U,b637ResidueTotal434]
    apply add_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun p hp => Finset.sum_nonneg (fun r hr =>
      (b637_physical_path_residue_budget434 visits eta offset heta p (hP p hp).pos).1 r |>.1))
  have hR0 : 0 ≤ H/(Q:ℝ)*(Real.exp (2*lam)/(2:ℝ)^(2*K+1)) +
      2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1) := by positivity
  refine ⟨hV,hfinite.trans ?_⟩
  change H/(Q:ℝ)*(Real.exp (2*lam)/(2:ℝ)^(2*K+1)) +
      2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1) ≤ _
  calc
    _ ≤ (H/(Q:ℝ)*(Real.exp (2*lam)/(2:ℝ)^(2*K+1)) +
      2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1))*(V*Real.exp (2*lam)) := by
        nlinarith only [mul_le_mul_of_nonneg_left hfactor hR0]
    _ = _ := by
      have he : Real.exp (4*lam)=Real.exp (2*lam)*Real.exp (2*lam) := by
        rw [←Real.exp_add]; congr 1; ring
      change _ = H/(Q:ℝ)*V*(Real.exp (4*lam)/(2:ℝ)^(2*K+1)+
        (Q:ℝ)/H*2*((2*K+2:ℕ):ℝ)*Real.exp 1*U^(2*K+1)*Real.exp (2*lam))
      rw [he]
      field_simp
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualPArithmetic -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Every prime in the complete ORIGINAL r20 family has the true
exp(L^.1) and exp(L^.4) bounds, including all SMALL and BIG bands. -/
theorem b638_actual_full_P_range434 (L : ℝ) (hL : 1 ≤ L)
    (p : ℕ) (hp : p ∈ sourceNativeOriginalG434 20 L) :
    p.Prime ∧ Real.exp (L^(1/10:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
  obtain ⟨g,_,hpg⟩ := Finset.mem_biUnion.mp hp
  exact source_native_original_ALL_P_prime_range434 20 L hL g p hpg

/-- Cardinality bound for the full original prime union. No cap is
placed on the number of marked prime choices or on the original D mass. -/
theorem b638_actual_full_P_card434 (L : ℝ) (hL : 1 ≤ L) :
    ((sourceNativeOriginalG434 20 L).card:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
  have hsub : sourceNativeOriginalG434 20 L ⊆
      Finset.Icc 1 (Nat.floor (Real.exp (L^(2/5:ℝ)))) := by
    intro p hp
    have hr := b638_actual_full_P_range434 L hL p hp
    exact Finset.mem_Icc.mpr ⟨hr.1.one_le,Nat.le_floor hr.2.2⟩
  have hc := Finset.card_le_card hsub
  have hc' : (sourceNativeOriginalG434 20 L).card ≤
      Nat.floor (Real.exp (L^(2/5:ℝ))) := by simpa using hc
  exact (show ((sourceNativeOriginalG434 20 L).card:ℝ) ≤
    (Nat.floor (Real.exp (L^(2/5:ℝ))):ℝ) by exact_mod_cast hc').trans
      (Nat.floor_le (Real.exp_nonneg _))

/-- Genuine unrenormalized harmonic mass of the complete r20 family.
The fixed constant precedes all paths, active primes and truncations. -/
theorem b638_eventually_actual_full_P_mass434 :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ L : ℝ in atTop,
      1 ≤ L ∧ (∑ p ∈ sourceNativeOriginalG434 20 L, 1/(p:ℝ)) ≤ C*Real.log L := by
  let C : ℝ := 4*(3+(Real.log 2)⁻¹)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_native_original_ALL_P_masses434 20,
    eventually_ge_atTop (Real.exp 1)] with L hMass hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  refine ⟨hL1,?_⟩
  have hgroups := source_original_P_all_group_card_log 20 L (by norm_num) hL
  calc
    _ = ∑ g : SourceNativeOriginalAllP434 20 L, sourceNativeOriginalAllPMass434 20 L g := by
      rw [sourceNativeOriginalG434,Finset.sum_biUnion]
      · rfl
      · intro i hi j hj hij
        apply Finset.disjoint_left.mpr
        intro p hp hq
        exact hij (source_original_P_actual_all_disjoint 20 L (by norm_num)
          (lt_of_lt_of_le (by norm_num) hL1) i j p hp hq)
    _ ≤ ∑ g : SourceNativeOriginalAllP434 20 L, (4:ℝ) := by
      exact Finset.sum_le_sum (fun g hg => (hMass g).2)
    _ = 4*((sourceOriginalPAllGroupIndices 20 L).card:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,
        SourceNativeOriginalAllP434,sourceOriginalPAllGroupType]
      ring
    _ ≤ C*Real.log L := by dsimp [C]; nlinarith

/-- The true active-prime modulus retains every DISTINCT active prime.
Its upper bound is derived from the actual full P range. -/
theorem b638_actual_active_P_modulus434 (L : ℝ) (hL : 1 ≤ L)
    (active : Finset ℕ) (hactive : active ⊆ sourceNativeOriginalG434 20 L) :
    0 < ∏ p ∈ active, p ∧
    ((∏ p ∈ active, p:ℕ):ℝ) ≤
      Real.exp ((active.card:ℝ)*L^(2/5:ℝ)) := by
  have hp := fun p hp => b638_actual_full_P_range434 L hL p (hactive hp)
  refine ⟨Finset.prod_pos (fun p hpa => (hp p hpa).1.pos),?_⟩
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ p ∈ active, Real.exp (L^(2/5:ℝ)) :=
      Finset.prod_le_prod₀ (fun p hpa => Nat.cast_nonneg p) (fun p hpa => (hp p hpa).2.2)
    _ = _ := by rw [Finset.prod_const,←Real.exp_nat_mul]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityRelativeCRT -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Uniform relative CRT saving on the FULL literal Parity r20 prime family,
with the ORIGINAL moment length, all actual signed physical offsets and
all inactive-prime damping factors. The active modulus is its exact
prime product. Only the finite active-slot cardinality budget is an input;
all harmonic masses, local-density lower bounds and finite CRT errors
are proved here. This is a pathwise arithmetic transfer, not yet a
spectral trace or a signed Type-II estimate. -/
theorem b638_eventually_actual_parity_relative_CRT434
    (E gamma : ℝ) (hE : 0≤E) (hgamma : 0<gamma) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    let N := 2*Nat.ceil (L^(13/25:ℝ))
    ∀ active : Finset ℕ,
      active ⊆ sourceNativeOriginalG434 20 L →
      active.card ≤ J*(N+1)*(sourceOriginalPAllGroupIndices 20 L).card →
    ∀ a lo hi : ℕ, Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
    ∀ eta : ℕ → ℝ, ∀ offset : ℕ → ℤ,
      (∀ i ∈ Finset.range (N+1), 0≤eta i ∧ eta i≤1) →
    let Q : ℕ := ∏ p ∈ active, p
    let P := sourceNativeOriginalG434 20 L \ active
    let f := b637PathResidueLoss434 (Finset.range (N+1)) eta offset
    let V := ∏ p ∈ P, (1-b637ResidueMean434 f p)
    0<V ∧
    |(∑ n ∈ Finset.Ico lo hi, if Nat.ModEq Q n a then
        ∏ p ∈ P, ∏ i ∈ Finset.range (N+1),
          (if (p:ℤ) ∣ (n:ℤ)+offset i then eta i else 1) else 0) -
      ((hi-lo:ℕ):ℝ)/(Q:ℝ)*V| ≤
        (((hi-lo:ℕ):ℝ)/(Q:ℝ)*V)*L^(-E*(N:ℝ)) := by
  obtain ⟨C,hC,hMass⟩ := b638_eventually_actual_full_P_mass434
  let Cg : ℝ := 3+(Real.log 2)⁻¹
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCg : 0<Cg := by dsimp [Cg]; positivity
  let Cq : ℝ := (J:ℝ)*Cg
  have hCq : 0≤Cq := by dsimp [Cq]; positivity
  filter_upwards [hMass,b638_eventually_relative_CRT_rate434 C Cq E gamma hC.le hCq hE hgamma,
    eventually_ge_atTop (Real.exp 1)] with L hMass hRates hLarge
  dsimp only at hRates ⊢
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  let K := Nat.ceil (L^(11/20:ℝ))
  have hL := hMass.1
  have hLp : 0<L := zero_lt_one.trans_le hL
  have hl : 0≤Real.log L := Real.log_nonneg hL
  have hN := b638_moment_and_order434 L hL
  change 1≤N ∧ (N:ℝ) ≤ 4*L^(13/25:ℝ) ∧
    ((N+1:ℕ):ℝ) ≤ 5*L^(13/25:ℝ) ∧
    2*L^(11/20:ℝ) ≤ ((2*K+1:ℕ):ℝ) ∧
    ((2*K+1:ℕ):ℝ) ≤ 5*L^(11/20:ℝ) ∧
    ((2*K+2:ℕ):ℝ) ≤ 6*L^(11/20:ℝ) at hN
  intro active hactive hcard a lo hi hH eta offset heta
  let Q : ℕ := ∏ p ∈ active, p
  let P := sourceNativeOriginalG434 20 L \ active
  let visits := Finset.range (N+1)
  let f := b637PathResidueLoss434 visits eta offset
  let lam := ∑ p ∈ P, b637ResidueMean434 f p
  let V := ∏ p ∈ P, (1-b637ResidueMean434 f p)
  let U := 1+∑ p ∈ P, b637ResidueTotal434 f p
  let H : ℝ := (hi-lo:ℕ)
  have hHp : 0<H := (Real.exp_pos _).trans_le hH
  have hInterval : lo<hi := by
    have hh : 0<hi-lo := by
      exact_mod_cast (show (0:ℝ)<((hi-lo:ℕ):ℝ) from hHp)
    omega
  have hmod := b638_actual_active_P_modulus434 L hL active hactive
  have hQp : 0<Q := hmod.1
  have hPsub : P ⊆ sourceNativeOriginalG434 20 L := Finset.sdiff_subset
  have hPrime : ∀ p ∈ P, p.Prime :=
    fun p hp => (b638_actual_full_P_range434 L hL p (hPsub hp)).1
  have hCoprime : ∀ p ∈ P, Q.Coprime p := by
    intro p hp
    apply Nat.Coprime.prod_left
    intro q hq
    apply (Nat.coprime_primes (b638_actual_full_P_range434 L hL q (hactive hq)).1 (hPrime p hp)).mpr
    intro he
    have hn := (Finset.mem_sdiff.mp hp).2
    exact hn (he ▸ hq)
  have hBudget (p : ℕ) (hp : p ∈ P) :=
    b637_physical_path_residue_budget434 visits eta offset heta p (hPrime p hp).pos
  have hhalf : ∀ p ∈ P, b637ResidueMean434 f p ≤ 1/2 := by
    intro p hp
    have hr := b638_actual_full_P_range434 L hL p (hPsub hp)
    have hp0 : (0:ℝ)<p := by exact_mod_cast hr.1.pos
    have hv : (visits.card:ℝ) ≤ (p:ℝ)/2 := by
      dsimp [visits]
      rw [Finset.card_range]
      exact hN.2.2.1.trans (hRates.2.1.trans (div_le_div_of_nonneg_right hr.2.1 (by norm_num)))
    exact (hBudget p hp).2.2.2.trans ((div_le_iff₀ hp0).mpr (by linarith))
  have hlam0 : 0≤lam := Finset.sum_nonneg (fun p hp => (hBudget p hp).2.2.1)
  have hPmass : (∑ p ∈ P, 1/(p:ℝ)) ≤ C*Real.log L := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hPsub
      (fun p hp hnp => by positivity)).trans hMass.2
  have hlam : lam ≤ C*((N+1:ℕ):ℝ)*Real.log L := by
    calc
      _ ≤ ∑ p ∈ P, (visits.card:ℝ)/(p:ℝ) :=
        Finset.sum_le_sum (fun p hp => (hBudget p hp).2.2.2)
      _ = (visits.card:ℝ)*(∑ p ∈ P, 1/(p:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ (visits.card:ℝ)*(C*Real.log L) :=
        mul_le_mul_of_nonneg_left hPmass (Nat.cast_nonneg _)
      _ = _ := by simp only [visits,Finset.card_range]; ring
  have htot0 : 0≤∑ p ∈ P, b637ResidueTotal434 f p := by
    apply Finset.sum_nonneg
    intro p hp
    exact Finset.sum_nonneg (fun r hr => ((hBudget p hp).1 r).1)
  have hU1 : 1≤U := by dsimp [U]; linarith
  have hPcard : (P.card:ℝ) ≤ Real.exp (L^(2/5:ℝ)) := by
    have hh := Finset.card_le_card hPsub
    exact (show (P.card:ℝ) ≤ ((sourceNativeOriginalG434 20 L).card:ℝ) by exact_mod_cast hh).trans
      (b638_actual_full_P_card434 L hL)
  have hU : U ≤ 1+((N+1:ℕ):ℝ)*Real.exp (L^(2/5:ℝ)) := by
    have hh : (∑ p ∈ P,b637ResidueTotal434 f p) ≤ (P.card:ℝ)*(visits.card:ℝ) := by
      calc
        _ ≤ ∑ p ∈ P,(visits.card:ℝ) := Finset.sum_le_sum (fun p hp => (hBudget p hp).2.1)
        _ = _ := by simp
    have hc := mul_le_mul_of_nonneg_right hPcard (Nat.cast_nonneg visits.card)
    dsimp [U]
    simp only [visits,Finset.card_range] at hh hc
    nlinarith only [hh,hc]
  have hGroup := source_original_P_all_group_card_log 20 L (by norm_num) hLarge
  have hcardR : (active.card:ℝ) ≤ (J:ℝ)*((N+1:ℕ):ℝ)*
      ((sourceOriginalPAllGroupIndices 20 L).card:ℝ) := by exact_mod_cast hcard
  have hcardBudget : (active.card:ℝ) ≤ Cq*((N+1:ℕ):ℝ)*Real.log L := by
    have hh := mul_le_mul_of_nonneg_left hGroup (show 0≤(J:ℝ)*((N+1:ℕ):ℝ) by positivity)
    dsimp [Cq,Cg]
    nlinarith only [hh,hcardR]
  have hQbound : (Q:ℝ) ≤ Real.exp (Cq*((N+1:ℕ):ℝ)*Real.log L*L^(2/5:ℝ)) := by
    apply hmod.2.trans
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hcardBudget (Real.rpow_nonneg hLp.le _))
  have hrelative := b638_relative_physical_path_CRT434 P hPrime Q a lo hi hQp hInterval
    hCoprime visits eta offset heta hhalf K
  change Real.exp (-2*lam) ≤ V ∧ _ at hrelative
  have hVpos : 0<V := (Real.exp_pos _).trans_le hrelative.1
  have hRate := hRates.2.2 lam U (Q:ℝ) H hlam0 hlam hU1 hU
    (Nat.cast_nonneg Q) hQbound hH
  have he : Real.exp (-E*(N:ℝ)*Real.log L) = L^(-E*(N:ℝ)) := by
    rw [Real.rpow_def_of_pos hLp]
    congr 1
    ring
  rw [he] at hRate
  refine ⟨hVpos,hrelative.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hRate (by positivity)
end Green64Analytic.SourceBlockSieve

end

end

