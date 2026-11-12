module

public import Green64.Library.Sieve.Foundations.PresieveBlocks
public import Green64.Library.Analysis.Estimates.Part003

@[expose] public section

/-!
# Sieve / Foundations / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalPresieveEulerFloor -/

section

/-! The actual finite shifted Euler product: exact correction factorization,
a finite integer telescope, and the already native real-cutoff Mertens theorem.
This is a positive lower bound, not an assertion of an exact singular limit. -/
open Filter Real Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

noncomputable def sourceV1CorrectionFactor (p : ℕ) : ℝ :=
  1 - (((p : ℝ)-1)^2)⁻¹

/-- Exact telescoping product for every INTEGER between 3 and N.
It is a lower bound for the prime-only correction, not an asymptotic. -/
theorem source_correction_integer_telescope (k : ℕ) :
    (∏ p ∈ Finset.Icc 3 (k+3), sourceV1CorrectionFactor p) =
      ((k+3:ℕ):ℝ)/(2*(k+2:ℕ):ℝ) := by
  induction k with
  | zero =>
      simp [sourceV1CorrectionFactor]
      norm_num
  | succ k ih =>
      have hs : 3 ≤ (k+3)+1 := by omega
      have hsucc : (∏ p ∈ Finset.Icc 3 (k+1+3),
          sourceV1CorrectionFactor p) =
        (∏ p ∈ Finset.Icc 3 (k+3),sourceV1CorrectionFactor p) *
          sourceV1CorrectionFactor (k+3+1) := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          (Finset.prod_Icc_succ_top hs sourceV1CorrectionFactor)
      rw [hsucc, ih]
      unfold sourceV1CorrectionFactor
      push_cast
      have hk2 : (k:ℝ)+2 ≠ 0 := by positivity
      have hk3 : (k:ℝ)+3 ≠ 0 := by positivity
      have hk4 : (k:ℝ)+4 ≠ 0 := by positivity
      field_simp [hk2, hk3, hk4]
      ring

/-- Every correction factor lies in [0,1] for integers p≥3. -/
theorem source_correction_factor_bounds (p : ℕ) (hp : 3 ≤ p) :
    0 ≤ sourceV1CorrectionFactor p ∧
      sourceV1CorrectionFactor p ≤ 1 := by
  have hpr : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hpdiff : 0 < (p:ℝ)-1 := by linarith
  have hden : 0 < ((p:ℝ)-1)^2 := pow_pos hpdiff 2
  have hge : 1 ≤ ((p:ℝ)-1)^2 := by nlinarith
  have hinv : (((p:ℝ)-1)^2)⁻¹ ≤ 1 :=
    (inv_le_one₀ hden).mpr hge
  have hpos : 0 ≤ (((p:ℝ)-1)^2)⁻¹ := inv_nonneg.mpr hden.le
  dsimp [sourceV1CorrectionFactor]
  constructor <;> linarith

/-- All integer correction factors telescope to at least 1/2.
Any sub-alphabet of the integers p≥3 has a LARGER product. -/
theorem source_correction_finite_ge_half
    (P : Finset ℕ) (k : ℕ) (hP : P ⊆ Finset.Icc 3 (k+3)) :
    (1/2:ℝ) ≤ ∏ p ∈ P, sourceV1CorrectionFactor p := by
  have hnonneg : ∀ p ∈ Finset.Icc 3 (k+3),
      0 ≤ sourceV1CorrectionFactor p := by
    intro p hp
    exact (source_correction_factor_bounds p (Finset.mem_Icc.mp hp).1).1
  have hle : ∀ p ∈ Finset.Icc 3 (k+3), p ∉ P →
      sourceV1CorrectionFactor p ≤ 1 := by
    intro p hp _
    exact (source_correction_factor_bounds p (Finset.mem_Icc.mp hp).1).2
  have hprod : (∏ p ∈ Finset.Icc 3 (k+3), sourceV1CorrectionFactor p) ≤
      (∏ p ∈ P, sourceV1CorrectionFactor p) :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hP hnonneg hle
  rw [source_correction_integer_telescope] at hprod
  have hden : (0:ℝ) < 2*((k+2:ℕ):ℝ) := by positivity
  have hhalf : (1/2:ℝ) ≤ ((k+3:ℕ):ℝ)/(2*((k+2:ℕ):ℝ)) := by
    apply (le_div_iff₀ hden).mpr
    push_cast
    nlinarith
  exact hhalf.trans hprod

/-- No external finite cutoff is needed for the universal 1/2 bound. -/
theorem source_correction_any_finite_ge_half
    (P : Finset ℕ) (hp : ∀ p ∈ P, 3 ≤ p) :
    (1/2:ℝ) ≤ ∏ p ∈ P, sourceV1CorrectionFactor p := by
  let k : ℕ := P.sup (fun p : ℕ => p)
  have hsubset : P ⊆ Finset.Icc 3 (k+3) := by
    intro p hpm
    have hle : p ≤ k := by
      exact Finset.le_sup (f := fun p : ℕ => p) hpm
    exact Finset.mem_Icc.mpr ⟨hp p hpm, by omega⟩
  exact source_correction_finite_ge_half P k hsubset

/-- Exact finite shifted-density factorization, without discarded primes. -/
theorem source_shift_two_local_factor_split
    (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    1-sourceShiftTwoLocalDensity p =
      (1-(p:ℝ)⁻¹)*sourceV1CorrectionFactor p := by
  have hpr : (3:ℝ) ≤ p := by exact_mod_cast h3
  have hzero : (p:ℝ) ≠ 0 := by positivity
  have hone : (p:ℝ)-1 ≠ 0 := by linarith
  rw [sourceShiftTwoLocalDensity, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  unfold sourceV1CorrectionFactor
  field_simp [hzero, hone]
  ring

/-- Exact factorization for the genuine finite h-sieve prime alphabet. -/
theorem source_shift_two_euler_factorization
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) :
    (∏ p ∈ P, (1-sourceShiftTwoLocalDensity p)) =
      (∏ p ∈ P, (1-(p:ℝ)⁻¹)) *
      (∏ p ∈ P, sourceV1CorrectionFactor p) := by
  calc
    _ = ∏ p ∈ P, ((1-(p:ℝ)⁻¹)*sourceV1CorrectionFactor p) :=
      Finset.prod_congr rfl (fun p hpm =>
        source_shift_two_local_factor_split p (hp p hpm).1 (hp p hpm).2)
    _ = _ := Finset.prod_mul_distrib

/-- No log-power loss: the true V1 factor is at least ONE HALF of the
ordinary prime Euler product on the identical finite prime alphabet. -/
theorem source_shift_two_V1_ge_half_ordinary
    (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) :
    (1/2:ℝ)*(∏ p ∈ P, (1-(p:ℝ)⁻¹)) ≤
      ∏ p ∈ P, (1-sourceShiftTwoLocalDensity p) := by
  have hnonneg : 0 ≤ (∏ p ∈ P, (1-(p:ℝ)⁻¹)) := by
    apply Finset.prod_nonneg
    intro p hpm
    have hpr : (3:ℝ) ≤ p := by exact_mod_cast (hp p hpm).2
    have hpos : (0:ℝ) < p := by linarith
    have hinv : (p:ℝ)⁻¹ ≤ 1 :=
      (inv_le_one₀ hpos).mpr (by linarith)
    linarith
  have hcorr := source_correction_any_finite_ge_half P
    (fun p hpm => (hp p hpm).2)
  rw [source_shift_two_euler_factorization P hp]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcorr hnonneg

/-- Compare true shift-two V1 for a block alphabet P with the ordinary
Euler product for ANY complete prime alphabet G containing it. The factor
1/2 is universal; no artificial extra logarithmic power is lost. -/
theorem source_shift_two_V1_ge_half_full_euler
    (P G : Finset ℕ) (hPG : P ⊆ G)
    (hp : ∀ p ∈ P, p.Prime ∧ 3 ≤ p)
    (hG : ∀ p ∈ G, p.Prime) :
    (1/2:ℝ)*(∏ p ∈ G, (1-(p:ℝ)⁻¹)) ≤
      ∏ p ∈ P, (1-sourceShiftTwoLocalDensity p) := by
  have hnonneg : ∀ p ∈ G, 0 ≤ 1-(p:ℝ)⁻¹ := by
    intro p hpm
    have hpr : (2:ℝ) ≤ p := by exact_mod_cast (hG p hpm).two_le
    have hpos : (0:ℝ) < p := by linarith
    have hinv : (p:ℝ)⁻¹ ≤ 1 :=
      (inv_le_one₀ hpos).mpr (by linarith)
    linarith
  have hle1 : ∀ p ∈ G, p ∉ P → 1-(p:ℝ)⁻¹ ≤ 1 := by
    intro p hpm _
    have hpos : (0:ℝ) < p := by exact_mod_cast (hG p hpm).pos
    have hn : 0 ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr hpos.le
    linarith
  have hprod : (∏ p ∈ G, (1-(p:ℝ)⁻¹)) ≤
      (∏ p ∈ P, (1-(p:ℝ)⁻¹)) :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hPG hnonneg hle1
  calc
    (1/2:ℝ)*(∏ p ∈ G, (1-(p:ℝ)⁻¹)) ≤
      (1/2:ℝ)*(∏ p ∈ P, (1-(p:ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ (∏ p ∈ P, (1-sourceShiftTwoLocalDensity p)) :=
      source_shift_two_V1_ge_half_ordinary P hp

/-- An actual fixed 1/L lower bound for the entire moving original Euler
product. Its constant is fixed with beta, before L; no Mertens premise remains. -/
theorem parity_original_presieve_euler_lower434 (beta : ℝ) (hBeta : 0<beta) :
    ∀ᶠ L : ℝ in atTop,
      (Real.exp (-Real.eulerMascheroniConstant)/beta/4)/L ≤
        ∏ p∈sourceAllOddPrimeSet ((Real.exp L)^beta),
          (1-sourceShiftTwoLocalDensity p) := by
  let c : ℝ := Real.exp (-Real.eulerMascheroniConstant)/beta
  have hc : 0<c := by dsimp [c];positivity
  have hLim : Tendsto
      (fun L : ℝ => L*Green64Analytic.SmallB.roughEuler ((Real.exp L)^beta))
      atTop (𝓝 c) := by
    simpa only [Function.comp_def,Real.log_exp] using
      (Green64Analytic.SmallB.real_roughEuler_mertens beta hBeta).comp
        Real.tendsto_exp_atTop
  have hM := (tendsto_order.mp hLim).1 (c/2) (by linarith)
  filter_upwards [hM,eventually_gt_atTop (0:ℝ)] with L hM hL
  let z := (Real.exp L)^beta
  let P := sourceAllOddPrimeSet z
  let G := Green64Analytic.SmallB.roughAlphabet z
  have hSubset : P⊆G := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    have hFloor := (Finset.mem_Icc.mp hm.1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hm.2⟩
  have hP : ∀ p∈P,p.Prime ∧ 3≤p := by
    intro p hp
    exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
  have hG : ∀ p∈G,p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hV : (1/2:ℝ)*Green64Analytic.SmallB.roughEuler z ≤
      ∏ p∈P,(1-sourceShiftTwoLocalDensity p) := by
    simpa only [Green64Analytic.SmallB.roughEuler,one_div] using
      source_shift_two_V1_ge_half_full_euler P G hSubset hP hG
  have hScaled : c/4≤L*(∏ p∈P,(1-sourceShiftTwoLocalDensity p)) := by
    calc
      c/4=(1/2:ℝ)*(c/2) := by ring
      _ ≤ (1/2:ℝ)*(L*Green64Analytic.SmallB.roughEuler z) :=
        mul_le_mul_of_nonneg_left hM.le (by norm_num)
      _ = L*((1/2:ℝ)*Green64Analytic.SmallB.roughEuler z) := by ring
      _ ≤ L*(∏ p∈P,(1-sourceShiftTwoLocalDensity p)) :=
        mul_le_mul_of_nonneg_left hV hL.le
  exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hScaled)

end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalSingularProduct -/

section

open Filter Real Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- The genuine correction term, with neutral terms outside the odd primes. -/
def parityOriginalSingularFactor434 (p : ℕ) : ℝ :=
  if p.Prime ∧ 3≤p then sourceV1CorrectionFactor p else 1

/-- Parity (5.7) at h=-2: the actual odd-prime product, including the factor2. -/
def singularSeries : ℝ :=
  2*∏' p : ({p : ℕ | p.Prime ∧ 3≤p} : Set ℕ),sourceV1CorrectionFactor p.val

def parityOriginalFiniteSingular434 (z : ℝ) : ℝ :=
  2*∏ p∈sourceAllOddPrimeSet z,sourceV1CorrectionFactor p

def parityOriginalShiftedEuler434 (z : ℝ) : ℝ :=
  ∏ p∈sourceAllOddPrimeSet z,(1-sourceShiftTwoLocalDensity p)

theorem parity_original_singular_series_eq_masked434 :
    singularSeries=2*∏' p : ℕ,parityOriginalSingularFactor434 p := by
  unfold singularSeries
  simpa only [Set.mulIndicator_apply,Set.mem_setOf_eq,parityOriginalSingularFactor434] using
    congrArg (fun t : ℝ => 2*t)
      (tprod_subtype ({p : ℕ | p.Prime ∧ 3≤p} : Set ℕ) sourceV1CorrectionFactor)

/-- Actual unordered product convergence and positivity. This establishes
HasProd first; no default value of a nonconvergent tprod is used. -/
theorem singularSeries_converges_and_ge_one :
    Multipliable parityOriginalSingularFactor434 ∧ 1≤ singularSeries := by
  let F := fun s : Finset ℕ => ∏ p∈s,parityOriginalSingularFactor434 p
  have hFactor (p : ℕ) :
      0≤parityOriginalSingularFactor434 p ∧ parityOriginalSingularFactor434 p≤1 := by
    unfold parityOriginalSingularFactor434
    split_ifs with hp
    · exact source_correction_factor_bounds p hp.2
    · norm_num
  have hLower (s : Finset ℕ) : (1/2:ℝ)≤F s := by
    have h := source_correction_any_finite_ge_half
      (s.filter (fun p => p.Prime ∧ 3≤p))
      (fun p hp => (Finset.mem_filter.mp hp).2.2)
    simpa only [F,Finset.prod_filter,parityOriginalSingularFactor434] using h
  have hAnti : Antitone F := by
    intro s t hst
    exact Finset.prod_le_prod_of_subset_of_le_one₀ hst
      (fun p _ => (hFactor p).1) (fun p _ _ => (hFactor p).2)
  have hBdd : BddBelow (Set.range F) := by
    refine ⟨(1/2:ℝ),?_⟩
    rintro _ ⟨s,rfl⟩
    exact hLower s
  have hProd : HasProd parityOriginalSingularFactor434 (⨅ s : Finset ℕ,F s) :=
    tendsto_atTop_ciInf hAnti hBdd
  have hMul := hProd.multipliable
  have hHalf : (1/2:ℝ)≤∏' p : ℕ,parityOriginalSingularFactor434 p :=
    le_hasProd_of_le_prod hMul.hasProd hLower
  refine ⟨hMul,?_⟩
  rw [parity_original_singular_series_eq_masked434]
  linarith

/-- Exact finite cutoff identity, retaining the actual floor for every real z. -/
theorem parity_original_singular_cutoff_eq434 (z : ℝ) :
    (∏ p∈Finset.range (⌊z⌋₊+1),parityOriginalSingularFactor434 p)=
      ∏ p∈sourceAllOddPrimeSet z,sourceV1CorrectionFactor p := by
  have hSets : (Finset.range (⌊z⌋₊+1)).filter
      (fun p => p.Prime ∧ 3≤p)=sourceAllOddPrimeSet z := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_range,sourceAllOddPrimeSet,Finset.mem_Icc]
    constructor
    · rintro ⟨hp,hPrime,hThree⟩
      exact ⟨⟨hThree,by omega⟩,hPrime⟩
    · rintro ⟨⟨hThree,hp⟩,hPrime⟩
      exact ⟨by omega,hPrime,hThree⟩
  rw [←hSets,Finset.prod_filter]
  rfl

theorem parity_original_finite_singular_tendsto434 :
    Tendsto parityOriginalFiniteSingular434 atTop (𝓝 singularSeries) := by
  have hMul := singularSeries_converges_and_ge_one.1
  have hRange := hMul.hasProd.tendsto_prod_nat.comp
    ((tendsto_add_atTop_nat 1).comp
      (tendsto_nat_floor_atTop : Tendsto (fun z : ℝ => ⌊z⌋₊) atTop atTop))
  have hCorr : Tendsto (fun z : ℝ =>
      ∏ p∈sourceAllOddPrimeSet z,sourceV1CorrectionFactor p)
      atTop (𝓝 (∏' p : ℕ,parityOriginalSingularFactor434 p)) := by
    simpa only [Function.comp_def,parity_original_singular_cutoff_eq434] using hRange
  rw [parity_original_singular_series_eq_masked434]
  exact hCorr.const_mul 2

/-- Exactly the omitted prime2 supplies the factor2 in the singular product. -/
theorem parity_original_full_prime_alphabet_eq_insert_two434
    (z : ℝ) (hz : 2≤z) :
    Green64Analytic.SmallB.roughAlphabet z=insert 2 (sourceAllOddPrimeSet z) := by
  have hFloor : 2≤⌊z⌋₊ := Nat.le_floor hz
  ext p
  simp only [Green64Analytic.SmallB.roughAlphabet,Finset.mem_filter,Finset.mem_range,
    Finset.mem_insert,sourceAllOddPrimeSet,Finset.mem_Icc]
  constructor
  · rintro ⟨hp,hPrime⟩
    by_cases hTwo : p=2
    · exact Or.inl hTwo
    · have hPrimeTwo := hPrime.two_le
      exact Or.inr ⟨⟨by omega,by omega⟩,hPrime⟩
  · rintro (rfl | ⟨⟨hThree,hp⟩,hPrime⟩)
    · exact ⟨by omega,Nat.prime_two⟩
    · exact ⟨by omega,hPrime⟩

theorem parity_original_shifted_euler_exact434 (z : ℝ) (hz : 2≤z) :
    parityOriginalShiftedEuler434 z=
      Green64Analytic.SmallB.roughEuler z*parityOriginalFiniteSingular434 z := by
  let P := sourceAllOddPrimeSet z
  have hNotTwo : 2∉P := by simp [P,sourceAllOddPrimeSet]
  have hOrdinary : Green64Analytic.SmallB.roughEuler z=
      (1/2:ℝ)*(∏ p∈P,(1-(p:ℝ)⁻¹)) := by
    unfold Green64Analytic.SmallB.roughEuler
    rw [parity_original_full_prime_alphabet_eq_insert_two434 z hz,Finset.prod_insert hNotTwo]
    norm_num
  have hP : ∀ p∈P,p.Prime ∧ 3≤p := by
    intro p hp
    exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
  change (∏ p∈P,(1-sourceShiftTwoLocalDensity p))=_
  rw [source_shift_two_euler_factorization P hP,hOrdinary]
  unfold parityOriginalFiniteSingular434
  dsimp [P]
  ring

theorem parity_original_shifted_euler_ratio_tendsto434 :
    Tendsto (fun z : ℝ => parityOriginalShiftedEuler434 z/
      Green64Analytic.SmallB.roughEuler z) atTop (𝓝 singularSeries) := by
  apply parity_original_finite_singular_tendsto434.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with z hz
  have hPositive : 0<Green64Analytic.SmallB.roughEuler z := by
    apply Finset.prod_pos
    intro p hp
    have hPrime := (Finset.mem_filter.mp hp).2
    have hpPos : (0:ℝ)<p := by exact_mod_cast hPrime.pos
    have hpOne : (1:ℝ)<p := by exact_mod_cast hPrime.one_lt
    exact sub_pos.mpr ((inv_lt_one₀ hpPos).mpr hpOne)
  rw [parity_original_shifted_euler_exact434 z hz]
  field_simp

/-- Exact original singular multiplier at every fixed positive power cutoff. -/
theorem parity_original_shifted_euler_power_mertens434
    (beta : ℝ) (hBeta : 0<beta) :
    Tendsto (fun L : ℝ => L*parityOriginalShiftedEuler434 ((Real.exp L)^beta))
      atTop (𝓝 (singularSeries*Real.exp (-Real.eulerMascheroniConstant)/beta)) := by
  have hZ : Tendsto (fun L : ℝ => (Real.exp L)^beta) atTop atTop :=
    (tendsto_rpow_atTop hBeta).comp Real.tendsto_exp_atTop
  have hM : Tendsto (fun L : ℝ => L*Green64Analytic.SmallB.roughEuler ((Real.exp L)^beta))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/beta)) := by
    simpa only [Function.comp_def,Real.log_exp] using
      (Green64Analytic.SmallB.real_roughEuler_mertens beta hBeta).comp Real.tendsto_exp_atTop
  have hC := parity_original_finite_singular_tendsto434.comp hZ
  have h : Tendsto (fun L : ℝ => L*parityOriginalShiftedEuler434 ((Real.exp L)^beta))
      atTop (𝓝 ((Real.exp (-Real.eulerMascheroniConstant)/beta)*singularSeries)) := by
    apply (hM.mul hC).congr'
    filter_upwards [hZ.eventually (eventually_ge_atTop (2:ℝ))] with L hz
    rw [parity_original_shifted_euler_exact434 _ hz]
    simp only [Function.comp_def]
    ring
  convert h using 1 <;> ring

/-- The same singular multiplier at the literal subpower W=exp(sqrt L). -/
theorem parity_original_shifted_euler_subpower_mertens434 :
    Tendsto (fun L : ℝ => Real.sqrt L*
      parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L)))
      atTop (𝓝 (singularSeries*Real.exp (-Real.eulerMascheroniConstant))) := by
  have hZ : Tendsto (fun L : ℝ => Real.exp (Real.sqrt L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp Real.tendsto_sqrt_atTop
  have hM : Tendsto (fun L : ℝ => Real.sqrt L*
      Green64Analytic.SmallB.roughEuler (Real.exp (Real.sqrt L)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa only [Function.comp_def,Real.log_exp,Real.rpow_one,div_one] using
      (Green64Analytic.SmallB.real_roughEuler_mertens 1 (by norm_num)).comp hZ
  have hC := parity_original_finite_singular_tendsto434.comp hZ
  have h : Tendsto (fun L : ℝ => Real.sqrt L*
      parityOriginalShiftedEuler434 (Real.exp (Real.sqrt L)))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)*singularSeries)) := by
    apply (hM.mul hC).congr'
    filter_upwards [hZ.eventually (eventually_ge_atTop (2:ℝ))] with L hz
    rw [parity_original_shifted_euler_exact434 _ hz]
    simp only [Function.comp_def]
    ring
  simpa only [mul_comm] using h
end Green64Analytic.SourceBlockSieve

end

end

/-! ## OriginalPrimeBins -/

section

open Filter Real Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def parityOriginalPrimeInterval434 (x y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime

def parityOriginalPrimeBin434 (gamma eta L : ℝ) : Finset ℕ :=
  parityOriginalPrimeInterval434 ((Real.exp L)^gamma) ((Real.exp L)^eta)

theorem parity_original_prime_interval_mem434
    (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (p : ℕ) :
    p∈parityOriginalPrimeInterval434 x y ↔ p.Prime ∧ x<(p:ℝ) ∧ (p:ℝ)≤y := by
  simp only [parityOriginalPrimeInterval434,Finset.mem_filter,Finset.mem_Ioc,
    Nat.floor_lt hx,Nat.le_floor_iff hy]
  tauto

theorem parity_original_prime_bin_mem434 (gamma eta L : ℝ) (p : ℕ) :
    p∈parityOriginalPrimeBin434 gamma eta L ↔
      p.Prime ∧ (Real.exp L)^gamma<(p:ℝ) ∧ (p:ℝ)≤(Real.exp L)^eta :=
  parity_original_prime_interval_mem434 _ _
    (Real.rpow_pos_of_pos (Real.exp_pos L) gamma).le
    (Real.rpow_pos_of_pos (Real.exp_pos L) eta).le p

/-- Exact native Mertens prefix cancellation at the actual open/closed bin. -/
theorem parity_original_prime_bin_reciprocal_tendsto434
    (gamma eta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta) :
    Tendsto (fun L : ℝ => ∑ p∈parityOriginalPrimeBin434 gamma eta L,(1:ℝ)/p)
      atTop (𝓝 (Real.log (eta/gamma))) := by
  have hEta : 0<eta := hGamma.trans hOrder
  have hX : Tendsto (fun L : ℝ => (Real.exp L)^gamma) atTop atTop :=
    (tendsto_rpow_atTop hGamma).comp Real.tendsto_exp_atTop
  have hY : Tendsto (fun L : ℝ => (Real.exp L)^eta) atTop atTop :=
    (tendsto_rpow_atTop hEta).comp Real.tendsto_exp_atTop
  have hError : Tendsto Mertens.E₂p atTop (𝓝 0) := by
    simpa only [div_one] using Mertens.E₂p.bound'.tendsto_div_nhds_zero
  have hLimit : Tendsto (fun L : ℝ => Real.log (eta/gamma)+
      (Mertens.E₂p ((Real.exp L)^eta)-Mertens.E₂p ((Real.exp L)^gamma)))
      atTop (𝓝 (Real.log (eta/gamma))) := by
    simpa only [sub_self,add_zero,Function.comp_def] using
      tendsto_const_nhds.add ((hError.comp hY).sub (hError.comp hX))
  apply hLimit.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hXY : (Real.exp L)^gamma≤(Real.exp L)^eta :=
    Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hL.le) hOrder.le
  have hSum := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then (1:ℝ)/p else 0)
    (Nat.zero_le ⌊(Real.exp L)^gamma⌋₊) (Nat.floor_le_floor hXY)
  rw [←Finset.sum_filter,←Finset.sum_filter,←Finset.sum_filter] at hSum
  rw [Mertens.sum_prime_div_eq,Mertens.sum_prime_div_eq] at hSum
  have hLog (a : ℝ) (ha : 0<a) :
      Real.log (Real.log ((Real.exp L)^a))=Real.log L+Real.log a := by
    simp only [Real.rpow_def_of_pos (Real.exp_pos L),Real.log_exp]
    exact Real.log_mul (ne_of_gt hL) (ne_of_gt ha)
  rw [hLog gamma hGamma,hLog eta hEta] at hSum
  rw [Real.log_div (ne_of_gt hEta) (ne_of_gt hGamma)]
  change _ = ∑ p∈(Finset.Ioc ⌊(Real.exp L)^gamma⌋₊ ⌊(Real.exp L)^eta⌋₊).filter Nat.Prime,(1:ℝ)/p
  linarith

/-- The p-1 correction is controlled by the same finite bin reciprocal
mass divided by x-1; no relative restriction eta<2 gamma is imposed. -/
theorem parity_original_prime_interval_shift_correction434
    (x y : ℝ) (hx : 1<x) (hy : 0≤y) :
    0≤(∑ p∈parityOriginalPrimeInterval434 x y,sourceShiftTwoLocalDensity p)-
       (∑ p∈parityOriginalPrimeInterval434 x y,(1:ℝ)/p) ∧
    (∑ p∈parityOriginalPrimeInterval434 x y,sourceShiftTwoLocalDensity p)-
       (∑ p∈parityOriginalPrimeInterval434 x y,(1:ℝ)/p) ≤
       (∑ p∈parityOriginalPrimeInterval434 x y,(1:ℝ)/p)/(x-1) := by
  have hPoint (p : ℕ) (hp : p∈parityOriginalPrimeInterval434 x y) :
      0≤ sourceShiftTwoLocalDensity p-(1:ℝ)/p ∧
      sourceShiftTwoLocalDensity p-(1:ℝ)/p≤((1:ℝ)/p)/(x-1) := by
    obtain ⟨hPrime,hxp,hpy⟩ := (parity_original_prime_interval_mem434 x y (by linarith) hy p).mp hp
    have hpPos : (0:ℝ)<p := by exact_mod_cast hPrime.pos
    have hpOne : 0<(p:ℝ)-1 := by linarith
    have hEq : sourceShiftTwoLocalDensity p-(1:ℝ)/p=((1:ℝ)/p)/((p:ℝ)-1) := by
      rw [sourceShiftTwoLocalDensity,Nat.totient_prime hPrime,Nat.cast_sub hPrime.one_le,Nat.cast_one]
      field_simp [ne_of_gt hpPos,ne_of_gt hpOne]
      ring
    rw [hEq]
    exact ⟨by positivity,div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)⟩
  constructor
  · rw [←Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun p hp => (hPoint p hp).1)
  · simpa only [Finset.sum_sub_distrib,Finset.sum_div] using
      Finset.sum_le_sum (fun p hp => (hPoint p hp).2)

/-- Literal Parity8.2 prime-bin harmonic factor, using the already proved
native Mertens theorem and the finite p-1 correction above. -/
theorem parity_original_prime_bin_local_density_tendsto434
    (gamma eta : ℝ) (hGamma : 0<gamma) (hOrder : gamma<eta) :
    Tendsto (fun L : ℝ => ∑ p∈parityOriginalPrimeBin434 gamma eta L,sourceShiftTwoLocalDensity p)
      atTop (𝓝 (Real.log (eta/gamma))) := by
  have hRecip := parity_original_prime_bin_reciprocal_tendsto434 gamma eta hGamma hOrder
  have hX : Tendsto (fun L : ℝ => (Real.exp L)^gamma) atTop atTop :=
    (tendsto_rpow_atTop hGamma).comp Real.tendsto_exp_atTop
  have hDen : Tendsto (fun L : ℝ => (Real.exp L)^gamma-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hX.eventually_ge_atTop (b+1)] with L hL
    linarith
  have hUpper := hRecip.div_atTop hDen
  have hBounds : ∀ᶠ L : ℝ in atTop,
      0≤(∑ p∈parityOriginalPrimeBin434 gamma eta L,sourceShiftTwoLocalDensity p)-
        (∑ p∈parityOriginalPrimeBin434 gamma eta L,(1:ℝ)/p) ∧
      (∑ p∈parityOriginalPrimeBin434 gamma eta L,sourceShiftTwoLocalDensity p)-
        (∑ p∈parityOriginalPrimeBin434 gamma eta L,(1:ℝ)/p) ≤
        (∑ p∈parityOriginalPrimeBin434 gamma eta L,(1:ℝ)/p)/((Real.exp L)^gamma-1) := by
    filter_upwards [hX.eventually (eventually_gt_atTop (1:ℝ))] with L hx
    exact parity_original_prime_interval_shift_correction434 _ _ hx
      (Real.rpow_pos_of_pos (Real.exp_pos L) eta).le
  have hDiff : Tendsto (fun L : ℝ =>
      (∑ p∈parityOriginalPrimeBin434 gamma eta L,sourceShiftTwoLocalDensity p)-
      (∑ p∈parityOriginalPrimeBin434 gamma eta L,(1:ℝ)/p)) atTop (𝓝 0) :=
    squeeze_zero' (hBounds.mono (fun L h => h.1)) (hBounds.mono (fun L h => h.2)) hUpper
  simpa only [sub_add_cancel,zero_add] using hDiff.add hRecip

/-- Actual adjacent bins are disjoint, including every endpoint equality. -/
theorem parity_original_prime_bins_pairwise_disjoint434
    (t : ℕ → ℝ) (ht : Monotone t) (L : ℝ) (hL : 0≤L) :
    Pairwise (fun i j : ℕ => Disjoint
      (parityOriginalPrimeBin434 (t i) (t (i+1)) L)
      (parityOriginalPrimeBin434 (t j) (t (j+1)) L)) := by
  have hOrdered (i j : ℕ) (hij : i<j) : Disjoint
      (parityOriginalPrimeBin434 (t i) (t (i+1)) L)
      (parityOriginalPrimeBin434 (t j) (t (j+1)) L) := by
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi := (parity_original_prime_bin_mem434 _ _ _ _).mp hpi
    have hj := (parity_original_prime_bin_mem434 _ _ _ _).mp hpj
    have hE := Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hL)
      (ht (Nat.succ_le_of_lt hij))
    exact (not_lt_of_ge (hi.2.2.trans hE)) hj.2.1
  intro i j hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hOrdered i j h
  · exact (hOrdered j i h).symm

/-- Exact external-bin summation identity; disjointness is proved from the
actual monotone endpoints, rather than assumed after erasing family labels. -/
theorem parity_original_prime_bins_sum_union434
    (t : ℕ → ℝ) (ht : Monotone t) (L : ℝ) (hL : 0≤L)
    (I : Finset ℕ) (F : ℕ → ℝ) :
    (∑ i∈I,∑ p∈parityOriginalPrimeBin434 (t i) (t (i+1)) L,F p)=
      ∑ p∈I.biUnion (fun i => parityOriginalPrimeBin434 (t i) (t (i+1)) L),F p := by
  symm
  apply Finset.sum_biUnion
  intro i hi j hj hne
  exact parity_original_prime_bins_pairwise_disjoint434 t ht L hL hne

/-- The union of every actual consecutive bin is the exact outer interval. -/
theorem parity_original_prime_bins_union434
    (t : ℕ → ℝ) (ht : Monotone t) (L : ℝ) (hL : 0≤L) (N : ℕ) :
    (Finset.range N).biUnion (fun i => parityOriginalPrimeBin434 (t i) (t (i+1)) L)=
      parityOriginalPrimeBin434 (t 0) (t N) L := by
  induction N with
  | zero => simp [parityOriginalPrimeBin434,parityOriginalPrimeInterval434]
  | succ N ih =>
    rw [Finset.range_add_one,Finset.biUnion_insert,ih,Finset.union_comm]
    unfold parityOriginalPrimeBin434 parityOriginalPrimeInterval434
    rw [←Finset.filter_union,Finset.Ioc_union_Ioc_eq_Ioc]
    · exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hL) (ht (Nat.zero_le N)))
    · exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp hL) (ht (Nat.le_succ N)))
end Green64Analytic.SourceBlockSieve

end

end

