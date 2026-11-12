module

public import Green64.Library.Weights.ParityFineInputs
public import Green64.Library.Weights.DivisorPowerMajorant
public import Green64.Library.Weights.Part073
public import Green64.Library.Sieve.Foundations.Part005
public import Green64.Library.Weights.Part005
public import Green64.Library.Weights.Part033
public import Green64.Library.Correlation.Part021
public import Green64.Library.Weights.Part105
public import Green64.Library.Weights.Part102
public import Mathlib

@[expose] public section

/-!
# Analysis / Estimates / Part015

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## PrimeSlotCoreNorm -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- The genuine source power phase has modulus one at every occurring
positive divisor. No frequency bound or replacement by a formal phase. -/
theorem b656_imaginary_power_norm434 (n : ℕ) (hn : 0<n) (t : ℝ) :
    ‖imaginaryPower n t‖=1 := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos
    (show (0:ℝ)<n by exact_mod_cast hn) (Complex.I*(t:ℂ))
  simpa only [imaginaryPower,Complex.ofReal_natCast,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,
    Real.rpow_zero] using h

theorem b656_divisors_card_mono434 (a b : ℕ) (hb : b≠0) (h : a∣b) :
    a.divisors.card ≤ b.divisors.card := by
  apply Finset.card_le_card
  intro d hd
  exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.mem_divisors.mp hd).1 h,hb⟩

/-- The original FULL prime-slot core is bounded using the divisor count
of its ORDINARY part, not of n. This distinction keeps the eventual
physical L2 exponent independent of the selected mark count J. -/
theorem b656_prime_core_norm_le_divisor_square434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (ha : ∀ m, ‖F.alpha m‖≤A) (hc : ∀ r, ‖F.residual r‖≤C) (n : ℕ) :
    ‖primeSlotCoreValue P F n‖ ≤ A*C*
      ((sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n).divisors.card:ℝ)^2 := by
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n
  have ht (m : ℕ) (hm : m∈ns.divisors) (p : ℕ) (hp : p∈(ns/m).divisors) :
      ‖(if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
        F.alpha m*F.character m*imaginaryPower m F.sigma₀*
          imaginaryPower p F.sigma₁*F.residual (ns/m/p) else 0 : ℂ)‖ ≤ A*C := by
    by_cases hg : p.Prime ∧ p∈Finset.Icc F.lo F.hi
    · rw [ite_eq_left hg]
      simp only [norm_mul,b656_imaginary_power_norm434 m (Nat.pos_of_mem_divisors hm),
        b656_imaginary_power_norm434 p (Nat.pos_of_mem_divisors hp),mul_one]
      have hchar : ‖F.character m‖≤1 := F.character.norm_le_one (m:ZMod F.q)
      calc
        _ ≤ (A*1)*C := mul_le_mul (mul_le_mul (ha m) hchar (norm_nonneg _) hA)
          (hc _) (norm_nonneg _) (mul_nonneg hA zero_le_one)
        _ = _ := by rw [mul_one]
    · rw [ite_eq_right hg,norm_zero]
      exact mul_nonneg hA hC
  unfold primeSlotCoreValue
  dsimp only
  change ‖∑ m∈ns.divisors, ∑ p∈(ns/m).divisors,
    if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
      F.alpha m*F.character m*imaginaryPower m F.sigma₀*
        imaginaryPower p F.sigma₁*F.residual (ns/m/p) else 0‖ ≤ _
  calc
    _ ≤ ∑ m∈ns.divisors, ∑ p∈(ns/m).divisors, A*C := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro m hm
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p hp => ht m hm p hp))
    _ ≤ ∑ _m∈ns.divisors, (ns.divisors.card:ℝ)*(A*C) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.sum_const,nsmul_eq_mul]
      have hd : ns/m ∣ ns := ⟨m,(Nat.div_mul_cancel (Nat.mem_divisors.mp hm).1).symm⟩
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
        (b656_divisors_card_mono434 (ns/m) ns (Nat.mem_divisors.mp hm).2 hd)) (mul_nonneg hA hC)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul]
      ring

/-- Fixed fourth divisor moment with explicit exponent15 and constant1,
reusing the production d16 majorant and harmonic convolution budget. -/
theorem b656_tau_four_counting434 (Y : ℕ) :
    (∑ n∈Finset.Ioc 0 Y, (n.divisors.card:ℝ)^4) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15 := by
  have hmajor : (∑ n∈Finset.Ioc 0 Y, (n.divisors.card:ℝ)^4) ≤
      ∑ n∈Finset.Ioc 0 Y, ((ArithmeticFunction.zeta^16) n:ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    exact_mod_cast Green64Analytic.SourceDivisorMoment.b593_actual_tau_four_le_d16_434
      n (Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1)
  have hconv : (∑ n∈Finset.Ioc 0 Y, ((ArithmeticFunction.zeta^16) n:ℝ)) ≤
      (Y:ℝ)*(Green64Analytic.SourceDivisorMoment.reciprocalHarmonic Y)^15 := by
    simpa using Green64Analytic.SourceDivisorMoment.b593_zeta_power_unweighted434 Y 14
  exact hmajor.trans (hconv.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_nonneg Y)
      (Green64Analytic.SourceDivisorMoment.reciprocalHarmonic_le_one_add_log Y) 15)
    (Nat.cast_nonneg Y)))
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## HarmonicError -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

/-- Translation of a positive integer interval preserves the actual fourth
moment, with no multiplicity or sign loss in the shift. -/
theorem parity_translated_tau_four_sum434
    (S : Finset ℕ) (Y : ℕ) (s : ℤ)
    (hS : ∀ n ∈ S, 0 < (n:ℤ)+s ∧ (n:ℤ)+s ≤ (Y:ℤ)) :
    (∑ n ∈ S, (((n:ℤ)+s).toNat.divisors.card:ℝ)^4) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15 := by
  classical
  let f : ℕ → ℕ := fun n => ((n:ℤ)+s).toNat
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro a ha b hb hab
    have hpa := (hS a ha).1
    have hpb := (hS b hb).1
    change ((a:ℤ)+s).toNat = ((b:ℤ)+s).toNat at hab
    omega
  have hsub : S.image f ⊆ Finset.Ioc 0 Y := by
    intro n hn
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    have hh := hS a ha
    rw [Finset.mem_Ioc]
    dsimp only [f]
    omega
  calc
    _ = ∑ n ∈ S.image f, (n.divisors.card:ℝ)^4 := by
      symm
      exact Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)
    _ ≤ ∑ n ∈ Finset.Ioc 0 Y, (n.divisors.card:ℝ)^4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot => by positivity)
    _ ≤ _ := b656_tau_four_counting434 Y

/-- The two full divisor-square weights are controlled by the genuine
fourth divisor moment at both endpoints. No cancellation of a selected
subset of core atoms is used. -/
theorem parity_translated_tau_square_product_sum434
    (S : Finset ℕ) (Y : ℕ) (s : ℤ)
    (hS : S ⊆ Finset.Ioc 0 Y)
    (hShift : ∀ n ∈ S, 0 < (n:ℤ)+s ∧ (n:ℤ)+s ≤ (Y:ℤ)) :
    (∑ n ∈ S, (n.divisors.card:ℝ)^2 *
      (((n:ℤ)+s).toNat.divisors.card:ℝ)^2) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15 := by
  have hfirst : (∑ n ∈ S, (n.divisors.card:ℝ)^4) ≤
      (Y:ℝ)*(1+Real.log (Y:ℝ))^15 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun n hn hnot => by positivity)).trans (b656_tau_four_counting434 Y)
  have hsecond := parity_translated_tau_four_sum434 S Y s hShift
  have hpoint : (∑ n ∈ S, (n.divisors.card:ℝ)^2 *
      (((n:ℤ)+s).toNat.divisors.card:ℝ)^2) ≤
      ((∑ n ∈ S, (n.divisors.card:ℝ)^4) +
        (∑ n ∈ S, (((n:ℤ)+s).toNat.divisors.card:ℝ)^4))/2 := by
    calc
      _ ≤ ∑ n ∈ S, ((n.divisors.card:ℝ)^4 +
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^4)/2 := by
        apply Finset.sum_le_sum
        intro n hn
        nlinarith [sq_nonneg ((n.divisors.card:ℝ)^2 -
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^2)]
      _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith


/-- The original cutoff interval gives positivity and one common translated
integer cap, for either sign of the actual shift. -/
theorem parity_harmonic_cutoff_shift_support434
    (X : ℝ) (hX : 0 < X) (s : ℤ)
    (hs : |(s:ℝ)| ≤ X/128) (psi : ℝ → ℂ)
    (hSupp : ∀ t, psi t ≠ 0 → t ∈ Set.Icc (1/64:ℝ) 64)
    (n : ℕ) (hn : psi ((n:ℝ)/X) ≠ 0) :
    0 < (n:ℤ)+s ∧ (n:ℤ)+s ≤ (⌈65*X⌉₊:ℤ) ∧
      n ≤ ⌈65*X⌉₊ ∧ X/64 ≤ (n:ℝ) := by
  have hp := hSupp ((n:ℝ)/X) hn
  have hlo : X/64 ≤ (n:ℝ) := by
    have hh := (le_div_iff₀ hX).mp hp.1
    linarith
  have hhi : (n:ℝ) ≤ 64*X := (div_le_iff₀ hX).mp hp.2
  have hshift := abs_le.mp hs
  have hpos : 0 < (n:ℝ)+(s:ℝ) := by linarith
  have htop : (n:ℝ)+(s:ℝ) ≤ 65*X := by linarith
  have hcap : 65*X ≤ (⌈65*X⌉₊:ℝ) := Nat.le_ceil _
  refine ⟨?_,?_,?_,hlo⟩
  · exact_mod_cast hpos
  · exact_mod_cast htop.trans hcap
  · have hh : (n:ℝ) ≤ (⌈65*X⌉₊:ℝ) := hhi.trans (by linarith)
    exact_mod_cast hh

/-- Literal finite absolute harmonic envelope. Both multiplicity-counted
ordinary divisor sums remain present; its definition contains no estimate. -/
def parityHarmonicDivisorEnvelope434
    (X : ℝ) (s : ℤ) (psi : ℝ → ℂ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 M, ‖psi ((n:ℝ)/X)‖/(n:ℝ) *
    (n.divisors.card:ℝ)^2 * (((n:ℤ)+s).toNat.divisors.card:ℝ)^2

/-- The complete cutoff envelope costs exactly 15+Cpsi powers of L.
The proof applies the fourth divisor moment to the literal two endpoints
and has no frequency, character or unproved error-bound premise. -/
theorem parity_harmonic_cutoff_divisor_envelope434
    (L X K Cpsi : ℝ) (hL : 1 ≤ L) (hX : 1 ≤ X) (hK : 0 ≤ K)
    (s : ℤ) (hs : |(s:ℝ)| ≤ X/128)
    (hLog : Real.log (⌈65*X⌉₊:ℝ) ≤ 2*L)
    (psi : ℝ → ℂ)
    (hSupp : ∀ t, psi t ≠ 0 → t ∈ Set.Icc (1/64:ℝ) 64)
    (hPsi : ∀ t, ‖psi t‖ ≤ K*L^Cpsi) (M : ℕ) :
    parityHarmonicDivisorEnvelope434 X s psi M ≤
      (64*66*(3:ℝ)^15) * K * L^(15+Cpsi) := by
  classical
  let S : Finset ℕ := (Finset.Ioc 0 M).filter (fun n : ℕ => psi ((n:ℝ)/X) ≠ 0)
  let Y := ⌈65*X⌉₊
  let B := 64*K*L^Cpsi/X
  have hLp : 0 < L := by linarith
  have hXp : 0 < X := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgeom (n : ℕ) (hn : n ∈ S) :=
    parity_harmonic_cutoff_shift_support434 X hXp s hs psi hSupp n
      (Finset.mem_filter.mp hn).2
  have hS : S ⊆ Finset.Ioc 0 Y := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp
      (Finset.mem_filter.mp hn).1).1,(hgeom n hn).2.2.1⟩
  have hShift : ∀ n ∈ S, 0 < (n:ℤ)+s ∧ (n:ℤ)+s ≤ (Y:ℤ) := by
    intro n hn
    exact ⟨(hgeom n hn).1,(hgeom n hn).2.1⟩
  have hcoef (n : ℕ) (hn : n ∈ S) : ‖psi ((n:ℝ)/X)‖/(n:ℝ) ≤ B := by
    have hnpos : 0 < (n:ℝ) := by
      exact_mod_cast (Finset.mem_Ioc.mp (hS hn)).1
    apply (div_le_iff₀ hnpos).mpr
    calc
      _ ≤ K*L^Cpsi := hPsi _
      _ = B*(X/64) := by dsimp [B]; field_simp
      _ ≤ B*(n:ℝ) := mul_le_mul_of_nonneg_left (hgeom n hn).2.2.2 hB
  have hY : (Y:ℝ) ≤ 66*X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 65*X by positivity)
    dsimp only [Y]
    linarith
  have hY1 : 1 ≤ (Y:ℝ) := by
    have hh : 65*X ≤ (Y:ℝ) := Nat.le_ceil _
    linarith
  have hbase : 0 ≤ 1+Real.log (Y:ℝ) := by
    have hh := Real.log_nonneg hY1
    linarith
  have hlog : 1+Real.log (Y:ℝ) ≤ 3*L := by
    change Real.log (Y:ℝ) ≤ 2*L at hLog
    linarith
  have heq : parityHarmonicDivisorEnvelope434 X s psi M =
      ∑ n ∈ S, ‖psi ((n:ℝ)/X)‖/(n:ℝ) *
        (n.divisors.card:ℝ)^2 * (((n:ℤ)+s).toNat.divisors.card:ℝ)^2 := by
    symm
    dsimp only [parityHarmonicDivisorEnvelope434,S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with hh
    · rfl
    · have hz : psi ((n:ℝ)/X)=0 := not_ne_iff.mp hh
      simp only [hz,norm_zero,zero_div,zero_mul]
  rw [heq]
  calc
    _ ≤ ∑ n ∈ S, B*((n.divisors.card:ℝ)^2 *
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hcoef n hn) (by positivity)
    _ = B*(∑ n ∈ S, (n.divisors.card:ℝ)^2 *
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^2) := by rw [Finset.mul_sum]
    _ ≤ B*((Y:ℝ)*(1+Real.log (Y:ℝ))^15) :=
      mul_le_mul_of_nonneg_left
        (parity_translated_tau_square_product_sum434 S Y s hS hShift) hB
    _ ≤ B*((66*X)*(3*L)^15) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact mul_le_mul hY (pow_le_pow_left₀ hbase hlog 15)
        (by positivity) (by positivity)
    _ = (64*66*(3:ℝ)^15)*K*L^(15+Cpsi) := by
      have h15 : L^(15:ℝ) = L^(15:ℕ) := Real.rpow_natCast L 15
      rw [Real.rpow_add hLp, h15]
      dsimp only [B]
      field_simp
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualParityReturnSaving -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

/-- Actual unconditional return saving with the same original source tuple
and positive-witness parameters supplied by B645. There is no assumed
uniform theta bound in this statement. Both the complete interval sum
and its actual normalized average are bounded. -/
theorem b648_eventually_actual_parity_return_saving434
    (E Cfreq Ck gamma : ℝ) (hE : 0 < E) (hgamma : 0 < gamma) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      let N := 2*Nat.ceil (L^(13/25:ℝ))
      0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧ 0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (zeta : ℝ),
      |zeta| ≤ L^Cfreq → ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (lo hi : ℕ), Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
        ‖b648ActualParityReturnPathSum434 L hS J m hmJ Q h xi zeta (2*k) N lo hi‖ ≤
          ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ)) ∧
        ‖b648ActualParityReturnPathSum434 L hS J m hmJ Q h xi zeta (2*k) N lo hi /
          (((hi-lo:ℕ):ℝ):ℂ)‖ ≤ L^(-E*(N:ℝ)) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hPhysical⟩ :=
    b645_eventually_actual_parity_physical_saving434 E Cfreq Ck gamma hE hgamma
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hPhysical] with L hPhysical
  dsimp only at hPhysical ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,hPhysical⟩ := hPhysical
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,?_⟩
  intro hS zeta hzeta k hk hkcap lo hi hH
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let N := 2*Nat.ceil (L^(13/25:ℝ))
  let H : ℝ := ((hi-lo:ℕ):ℝ)
  let P := b648ActualParityReturnPathSum434 L hS J m hmJ Q h xi zeta (2*k) N lo hi
  have hP : ‖P‖ ≤ H*L^(-E*(N:ℝ)) := by
    dsimp only [P]
    rw [← b648_actual_parity_return_integral434]
    simpa only [sub_zero,abs_one,mul_one] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
        (fun theta _ => hPhysical hS zeta theta hzeta k hk hkcap lo hi hH)
  refine ⟨hP,?_⟩
  have hHpos : 0 < H := (Real.exp_pos (gamma*L)).trans_le hH
  change ‖P/(H:ℂ)‖ ≤ L^(-E*(N:ℝ))
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hHpos]
  apply (div_le_iff₀ hHpos).2
  simpa only [mul_comm] using hP
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityMomentSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000

/-- Exact real trace over the independent seed set used by the block
endpoint theorem. No roots at the boundary of the enlarged carrier
are added to the moment sum. -/
theorem b654_actual_parity_seed_trace434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m ≤ J) (Q : ℕ) (h xi zeta : ℝ)
    (shift : ℤ) (positions : Finset ℤ) (R lo hi : ℕ) :
    let A := b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta shift positions
    let u := b654ActualParityPositionRoot434 L hS J positions
    (∑ n ∈ b654ParitySeedPositions434 lo hi,
      (inner ℂ (u n) (((A.comp A.adjoint)^R) (u n))).re) =
    (b654ActualParityPhysicalMomentSum434 L hS J m hmJ Q h xi zeta shift positions R lo hi).re := by
  dsimp only
  rw [b654_sum_seed_positions434]
  unfold b654ActualParityPhysicalMomentSum434
  exact (map_sum Complex.reLm _ _).symm

/-- UNCONDITIONAL original physical positive-operator moment saving.
The original source tuple is chosen before L and is exactly the B648
tuple. The full actual RAW+comparison operator, every original mark,
the same integer positions, both V masses, and shift 2k are retained.
No hCRT, hMass, spectral/trace identity, window assumption or RMS bound
remains. CRT is applied only over the original LONG seed interval. -/
theorem b654_eventually_actual_parity_moment_saving434
    (E Cfreq Ck gamma : ℝ) (hE : 0 < E) (hgamma : 0 < gamma) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      let R := Nat.ceil (L^(13/25:ℝ))
      let N := 2*R
      0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧ 0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (zeta : ℝ),
      |zeta| ≤ L^Cfreq → ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (lo hi : ℕ), Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
        let moment := b654ActualParityPhysicalMomentSum434 L hS J m hmJ Q h xi zeta (2*k)
          (b654ParityIntervalWindow434 J Ck L lo hi) R lo hi
        ‖moment‖ ≤ ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ)) ∧
        moment.re ≤ ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ)) := by
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hReturn⟩ :=
    b648_eventually_actual_parity_return_saving434 E Cfreq Ck gamma hE hgamma
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  filter_upwards [hReturn,b654_eventually_actual_parity_masses_positive434,
    eventually_ge_atTop (Real.exp 1)] with L hReturn hMass hL
  dsimp only at hReturn ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,hReturn⟩ := hReturn
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,?_⟩
  intro hS zeta hzeta k hk hkcap lo hi hH
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let R := Nat.ceil (L^(13/25:ℝ))
  let N := 2*R
  let M := b654ActualParityPhysicalMomentSum434 L hS J m hmJ Q h xi zeta (2*k)
    (b654ParityIntervalWindow434 J Ck L lo hi) R lo hi
  have hEq := b654_actual_parity_moment_eq_return434 L hL hS J m hmJ Q h xi zeta Ck
    k hkcap lo hi (hMass.2.2 hS).1 (hMass.2.2 hS).2
  have hb := (hReturn hS zeta hzeta k hk hkcap lo hi hH).1
  have hnorm : ‖M‖ ≤ ((hi-lo:ℕ):ℝ)*L^(-E*(N:ℝ)) := by
    dsimp only [M]
    rw [hEq]
    exact hb
  exact ⟨hnorm,(Complex.re_le_norm M).trans hnorm⟩
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityFirstVector -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.SpectralEndpoint
set_option autoImplicit false

/-- The source first endpoint in the actual physical Euclidean norm.
Every ordered mark at n receives exactly sqrt(mu0)*c(n); positions
outside the original seed interval receive zero. The common mu0 is the
original product of BOTH V masses, with no Haar or mark-count factor. -/
def b655ActualParityFirstVector434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ) (c : ℤ → ℂ) :
    EuclideanSpace ℂ (B654ActualParityState434 L hS J positions) :=
  b652FirstPositionVector434 (fun x => x.val.1.val)
    (Real.sqrt (b650IntegerStateMass434
      (SG:=SourceNativeMemorySG434 20 L hS) (BG:=sourceNativeOriginalBigType434 20 L)
      J 1 (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L)) : ℂ)
    (b654ParitySeedPositions434 lo hi) c

/-- The first vector is the exact coefficient-weighted sum of the actual
full-mark source roots, with only seed positions in the sum. -/
theorem b655_actual_parity_first_vector_frame434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ) (c : ℤ → ℂ) :
    b655ActualParityFirstVector434 L hS J positions lo hi c =
      ∑ n ∈ b654ParitySeedPositions434 lo hi,
        c n • b654ActualParityPositionRoot434 L hS J positions n := by
  exact b652_first_position_frame434 _ _ _ _
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FinitePhysicalPairing -/

section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 10000000

variable {α F : Type*} [Fintype α] [DecidableEq α] [Fintype F]

/-- Every finite physical frame is summed as a complex scalar before
taking the pairing. In particular, signed patterns are not separated by
absolute values. -/
def b658FrameMatrix434 (row : α → α → F → ℂ) : Matrix α α ℂ :=
  Matrix.of (fun x y => ∑ t : F, row x y t)

/-- Literal finite Euclidean pairing expansion, with the full first
position fibre and an arbitrary marked second endpoint. -/
theorem b658_seed_frame_pairing434 (pos : α → ℤ) (w : ℂ)
    (I : Finset ℤ) (c : ℤ → ℂ) (g : EuclideanSpace ℂ α)
    (row : α → α → F → ℂ) :
    inner ℂ (b652FirstPositionVector434 pos w I c)
      ((b658FrameMatrix434 row).toEuclideanLin g) =
    ∑ x : α, ∑ y : α, ∑ t : F,
      if pos x ∈ I then star (c (pos x)) * star w * row x y t * g.ofLp y else 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    b652FirstPositionVector434, WithLp.ofLp_toLp, Matrix.mulVec,
    dotProduct, Pi.star_apply, b658FrameMatrix434, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hi : pos x ∈ I
  · simp only [hi, ite_true, star_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro t ht
    ring
  · simp only [hi, ite_false, star_zero, mul_zero, Finset.sum_const_zero]

/-- Finite, fully integrable Fubini for the original pairing. Its frame
hypotheses are discharged by the literal B658 physical-frame inversion
in the next module. No RMS estimate or bound is used here. -/
theorem b658_seed_frame_fourier_fubini434 (pos : α → ℤ) (w : ℂ)
    (I : Finset ℤ) (c : ℤ → ℂ) (g : EuclideanSpace ℂ α)
    (u : ℤ → ℝ) (a : ℝ → ℂ)
    (row : ℝ → α → α → F → ℂ) (cut : α → α → F → ℂ)
    (hInt : ∀ x : α, pos x ∈ I → ∀ y : α, ∀ t : F,
      Integrable (fun xi : ℝ => a xi *
        (star (b658FourierPhase434 (-xi) (u (pos x))) * row xi x y t)))
    (hInv : ∀ x : α, pos x ∈ I → ∀ y : α, ∀ t : F,
      (∫ xi : ℝ, a xi *
        (star (b658FourierPhase434 (-xi) (u (pos x))) * row xi x y t)) = cut x y t) :
    Integrable (fun xi : ℝ => a xi *
      inner ℂ (b652FirstPositionVector434 pos w I
        (fun n => b658FourierPhase434 (-xi) (u n) * c n))
        ((b658FrameMatrix434 (row xi)).toEuclideanLin g)) ∧
    (∫ xi : ℝ, a xi *
      inner ℂ (b652FirstPositionVector434 pos w I
        (fun n => b658FourierPhase434 (-xi) (u n) * c n))
        ((b658FrameMatrix434 (row xi)).toEuclideanLin g)) =
      inner ℂ (b652FirstPositionVector434 pos w I c)
        ((b658FrameMatrix434 cut).toEuclideanLin g) := by
  let term := fun (x y : α) (t : F) (xi : ℝ) =>
    if pos x ∈ I then
      (a xi * (star (b658FourierPhase434 (-xi) (u (pos x))) * row xi x y t)) *
        (star (c (pos x)) * star w * g.ofLp y)
    else (0:ℂ)
  have ht (x y : α) (t : F) : Integrable (term x y t) := by
    by_cases hi : pos x ∈ I
    · simpa only [term, hi, ite_true] using
        (hInt x hi y t).mul_const (star (c (pos x)) * star w * g.ofLp y)
    · simp only [term, hi, ite_false]
      constructor
      · exact aestronglyMeasurable_const
      · simp [HasFiniteIntegral]
  have he (xi : ℝ) :
      a xi * inner ℂ
        (b652FirstPositionVector434 pos w I (fun n => b658FourierPhase434 (-xi) (u n) * c n))
        ((b658FrameMatrix434 (row xi)).toEuclideanLin g) =
      ∑ x : α, ∑ y : α, ∑ t : F, term x y t xi := by
    rw [b658_seed_frame_pairing434]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hi : pos x ∈ I
    · simp only [hi, ite_true, term, star_mul]
      ring
    · simp only [hi, ite_false, term, mul_zero]
  have hsum : Integrable (fun xi : ℝ => ∑ x : α, ∑ y : α, ∑ t : F, term x y t xi) := by
    apply integrable_finsetSum
    intro x hx
    apply integrable_finsetSum
    intro y hy
    exact integrable_finsetSum _ (fun t _ => ht x y t)
  constructor
  · exact hsum.congr (Filter.Eventually.of_forall (fun xi => (he xi).symm))
  · simp_rw [he]
    rw [integral_finsetSum _ (fun x _ => by
      apply integrable_finsetSum
      intro y hy
      exact integrable_finsetSum _ (fun t _ => ht x y t))]
    rw [b658_seed_frame_pairing434]
    apply Finset.sum_congr rfl
    intro x hx
    rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun t _ => ht x y t))]
    apply Finset.sum_congr rfl
    intro y hy
    rw [integral_finsetSum _ (fun t _ => ht x y t)]
    apply Finset.sum_congr rfl
    intro t ht'
    by_cases hi : pos x ∈ I
    · simp only [term, hi, ite_true]
      rw [integral_mul_const, hInv x hi y t]
      ring
    · simp only [term, hi, ite_false, integral_zero]
end Green64Analytic.SourceBlockSieve

end

end

/-! ## FourierEndpointBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The genuine Fourier endpoint twist preserves the ORIGINAL full-mark
Euclidean first-vector norm exactly. No mark fibre is normalized. -/
theorem b658_first_position_fourier_norm434
    {α : Type*} [Fintype α] (pos : α → ℤ) (w : ℂ)
    (I : Finset ℤ) (c : ℤ → ℂ) (u : ℤ → ℝ) (v : ℝ) :
    ‖b652FirstPositionVector434 pos w I
      (fun n => b658FourierPhase434 (-v) (u n) * c n)‖ =
    ‖b652FirstPositionVector434 pos w I c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hi : pos x ∈ I
  · simp only [b652FirstPositionVector434, WithLp.ofLp_toLp, hi, ite_true,
      norm_mul, b658_fourier_phase_norm434, one_mul]
  · simp only [b652FirstPositionVector434, WithLp.ofLp_toLp, hi, ite_false]

/-- Same exact norm identity for the actual source first vector. -/
theorem b658_actual_parity_first_fourier_norm434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (positions : Finset ℤ) (lo hi : ℕ)
    (c : ℤ → ℂ) (Z v : ℝ) :
    ‖b655ActualParityFirstVector434 L hS J positions lo hi
      (fun n => b658FourierPhase434 (-v) (Real.log ((n:ℝ)/Z)) * c n)‖ =
    ‖b655ActualParityFirstVector434 L hS J positions lo hi c‖ := by
  exact b658_first_position_fourier_norm434 _ _ _ c _ v

/-- Fix the spectral exponent BEFORE forming the ideal tuple: the
Fourier band |v|<=L^F and original phase bound |zeta|<=L^C require only
max(C,F)+1. The constant 2*pi is absorbed by the eventual L threshold,
not by any parameter depending on J or on Fourier-tail accuracy. -/
theorem b658_actual_fourier_frequency_band434 (L C F zeta v : ℝ)
    (hL : 1+2*Real.pi ≤ L)
    (hzeta : |zeta| ≤ L^C) (hv : |v| ≤ L^F) :
    |zeta-2*Real.pi*v| ≤ L^(max C F+1) := by
  have hL1 : 1 ≤ L := by linarith [Real.pi_pos]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hC := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left C F)
  have hF := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right C F)
  have htwo : 0 ≤ 2*Real.pi := by positivity
  have hterm : |2*Real.pi*v| ≤ (2*Real.pi)*L^F := by
    rw [abs_mul,abs_of_nonneg htwo]
    exact mul_le_mul_of_nonneg_left hv htwo
  calc
    _ ≤ |zeta| + |2*Real.pi*v| := abs_sub _ _
    _ ≤ L^C + (2*Real.pi)*L^F := add_le_add hzeta hterm
    _ ≤ (1+2*Real.pi)*L^(max C F) := by
      nlinarith [mul_le_mul_of_nonneg_left hF htwo]
    _ ≤ L*L^(max C F) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _)
    _ = L^(max C F+1) := by rw [Real.rpow_add hLp,Real.rpow_one]; ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## ActualParityEndpointSaving -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.SourceBlockSieve
open Green64FullPhysicalE Green64Analytic.SpectralEndpoint
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 18000

/-- The original full physical S02 endpoint saving. The actual source
moment estimate is proved unconditionally in B654 and is applied with
E+2*Cnorm+1 BEFORE choosing the source tuple. Csup may be chosen AFTER
that tuple. Only the first endpoint is position-constant; the second
endpoint is completely arbitrary on all physical marks. The same
original RAW-plus-comparison Knu, original V masses and shift 2k remain.
There is no RMS, trace, density, CRT, locality or mass premise. -/
theorem b655_eventually_actual_parity_endpoint_saving434
    (E Cfreq Ck gamma Cnorm : ℝ)
    (hE : 0 < E) (hgamma : 0 < gamma) (hCk : 0 ≤ Ck) (hCnorm : 0 ≤ Cnorm) :
    ∃ (m : ℕ) (D HH : ℝ) (Cq Cxi J : ℕ) (hmJ : m ≤ J),
      1 ≤ m ∧ 0 ≤ D ∧ 0 ≤ HH ∧
      ∀ (Csup : ℝ), 0 ≤ Csup →
      ∀ᶠ L : ℝ in atTop,
      let Q : ℕ := Nat.ceil (4*L^(D+1))
      let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
      let xi : ℝ := L^(-(Cxi:ℝ))
      0 < Q ∧ (Q:ℝ) ≤ L^Cq ∧ 0 < h ∧ h+h ≤ 1 ∧ 0 < xi ∧ xi⁻¹ ≤ L^Cxi ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (zeta : ℝ),
      |zeta| ≤ L^Cfreq → ∀ (k : ℤ), k ≠ 0 → (k.natAbs:ℝ) ≤ L^Ck →
      ∀ (lo hi : ℕ), Real.exp (gamma*L) ≤ ((hi-lo:ℕ):ℝ) →
      ∀ (c : ℤ → ℂ),
        (∀ n ∈ b654ParitySeedPositions434 lo hi, ‖c n‖ ≤ Real.exp (Csup*Real.sqrt L)) →
      ∀ (g : EuclideanSpace ℂ (B654ActualParityState434 L hS J
        (b654ParityIntervalWindow434 J Ck L lo hi))),
        ‖b655ActualParityFirstVector434 L hS J (b654ParityIntervalWindow434 J Ck L lo hi) lo hi c‖ ≤
          Real.sqrt ((hi-lo:ℕ):ℝ)*L^Cnorm →
        ‖g‖ ≤ Real.sqrt ((hi-lo:ℕ):ℝ)*L^Cnorm →
        ‖inner ℂ
          (b655ActualParityFirstVector434 L hS J (b654ParityIntervalWindow434 J Ck L lo hi) lo hi c)
          (b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta (2*k)
            (b654ParityIntervalWindow434 J Ck L lo hi) g)‖ ≤ ((hi-lo:ℕ):ℝ)*L^(-E) := by
  let E' := E+2*Cnorm+1
  have hE' : 0 < E' := by dsimp [E']; linarith
  obtain ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,hMoment⟩ :=
    b654_eventually_actual_parity_moment_saving434 E' Cfreq Ck gamma hE' hgamma
  refine ⟨m,D,HH,Cq,Cxi,J,hmJ,hm,hD,hHH,?_⟩
  intro Csup hCsup
  filter_upwards [hMoment,
    b651_eventually_parity_localization_factor434 J Ck Csup hCk hCsup,
    eventually_ge_atTop (Real.sqrt 3*Real.exp (1+2*Csup)),
    eventually_ge_atTop (Real.exp 1)] with L hMoment hLoc hConstant hLarge
  dsimp only at hMoment ⊢
  obtain ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,hMoment⟩ := hMoment
  refine ⟨hQ,hQcap,hh,hhcap,hxi,hxicap,hS,?_⟩
  intro hS zeta hzeta k hk hkcap lo hi hLong c hc g hf hg
  let Q : ℕ := Nat.ceil (4*L^(D+1))
  let h : ℝ := Real.log 2/((Nat.ceil (4*L^HH):ℕ):ℝ)
  let xi : ℝ := L^(-(Cxi:ℝ))
  let R := Nat.ceil (L^(13/25:ℝ))
  let positions := b654ParityIntervalWindow434 J Ck L lo hi
  let X : ℝ := ((hi-lo:ℕ):ℝ)
  let I := b654ParitySeedPositions434 lo hi
  let H : ℤ := b651ParityWindowSize434 J Ck L
  let C : ℝ := Real.exp (Csup*Real.sqrt L)
  let pos : B654ActualParityState434 L hS J positions → ℤ := fun x => x.val.1.val
  let w : ℂ := Real.sqrt (b650IntegerStateMass434
    (SG:=SourceNativeMemorySG434 20 L hS) (BG:=sourceNativeOriginalBigType434 20 L)
    J 1 (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
  let K := b654ActualParityPhysicalMatrix434 L hS J m hmJ Q h xi zeta (2*k) positions
  let A := b654ActualParityPhysicalOperator434 L hS J m hmJ Q h xi zeta (2*k) positions
  let f := b655ActualParityFirstVector434 L hS J positions lo hi c
  let T := (b654ActualParityPhysicalMomentSum434 L hS J m hmJ Q h xi zeta (2*k)
    positions R lo hi).re
  let p : ℝ := 1-(R:ℝ)⁻¹
  let q : ℝ := (2*(R:ℝ))⁻¹
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLarge
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hR : 1 ≤ R := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hLp _)
  have hX : 1 ≤ X := (Real.one_le_exp (mul_nonneg hgamma.le hLp.le)).trans hLong
  have hH : 1 ≤ H := by dsimp [H,b651ParityWindowSize434]; omega
  have hstep : ∀ x y, K x y ≠ 0 → |pos y-pos x| ≤ H := by
    intro x y hxy
    exact b655_actual_parity_matrix_locality434 L hLarge hS J m hmJ Q h xi zeta Ck
      k hkcap positions x y hxy
  have hTrace : (∑ n ∈ I, (inner ℂ (b652PositionRoot434 pos w n)
      (((A.comp A.adjoint)^R) (b652PositionRoot434 pos w n))).re)=T :=
    b654_actual_parity_seed_trace434 L hS J m hmJ Q h xi zeta (2*k) positions R lo hi
  have hPositive := b649_positive_power434 (A.comp A.adjoint) A.isPositive_self_comp_adjoint R
  have hT0 : 0 ≤ T := by
    rw [←hTrace]
    exact Finset.sum_nonneg fun n _ => hPositive.re_inner_nonneg_right _
  have hT : T ≤ X*L^(-E'*(2*(R:ℝ))) := by
    simpa only [T,X,R,Nat.cast_mul,Nat.cast_ofNat] using
      (hMoment hS zeta hzeta k hk hkcap lo hi hLong).2
  have hCE : C^2=Real.exp (2*Csup*Real.sqrt L) := by
    dsimp [C]
    rw [sq,←Real.exp_add]
    congr 1
    ring
  have hFactor : ((H:ℝ)*C^2)^q ≤ Real.exp (1+2*Csup) := by
    rw [hCE]
    simpa only [H,q,R,Int.cast_natCast,one_div] using hLoc
  have hEndpoint := b652_mark_independent_position_endpoint434
    pos H hH K hstep R hR w I c C hc g
  change ‖inner ℂ f (A g)‖ ≤
    Real.sqrt 3*‖g‖*‖f‖^p*((H:ℝ)*C^2)^q*
      (∑ n ∈ I, (inner ℂ (b652PositionRoot434 pos w n)
        (((A.comp A.adjoint)^R) (b652PositionRoot434 pos w n))).re)^q at hEndpoint
  rw [hTrace] at hEndpoint
  have hBudget := b655_endpoint_power_budget434 X L E' Cnorm ‖f‖ ‖g‖ T R
    hX hL1 hCnorm hR (norm_nonneg _) hT0 hf hg hT
  have hFactor0 : 0 ≤ ((H:ℝ)*C^2)^q :=
    Real.rpow_nonneg (mul_nonneg (by exact_mod_cast (show 0 ≤ H by omega)) (sq_nonneg C)) _
  change ‖inner ℂ f (A g)‖ ≤ X*L^(-E)
  calc
    _ ≤ Real.sqrt 3*‖g‖*‖f‖^p*((H:ℝ)*C^2)^q*T^q := hEndpoint
    _ = (Real.sqrt 3*((H:ℝ)*C^2)^q)*(‖g‖*‖f‖^p*T^q) := by ring
    _ ≤ (Real.sqrt 3*Real.exp (1+2*Csup))*(X*L^(-E'+2*Cnorm)) := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left hFactor (Real.sqrt_nonneg _)) hBudget
      · exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
          (Real.rpow_nonneg hT0 _)
      · positivity
    _ ≤ L*(X*L^(-E'+2*Cnorm)) :=
      mul_le_mul_of_nonneg_right hConstant (mul_nonneg (zero_le_one.trans hX) (Real.rpow_nonneg hLp.le _))
    _ = X*L^(-E) := by
      have he : -E'+2*Cnorm=-E-1 := by dsimp [E']; ring
      rw [he]
      calc
        L*(X*L^(-E-1)) = X*(L^(1:ℝ)*L^(-E-1)) := by rw [Real.rpow_one]; ring
        _ = X*L^(1+(-E-1)) := by rw [←Real.rpow_add hLp]
        _ = X*L^(-E) := by congr 2; ring
end Green64Analytic.SourceBlockSieve

end

end

/-! ## OrdinaryMarkedDivisor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The literal ordinary part is coprime to EVERY positive P-supported
integer, including repeated powers. This is arithmetic of the original
prime-factor partition, independent of J and of any norm estimate. -/
theorem b656_ordinary_coprime_P_supported434
    (Pall : Finset ℕ) (n D : ℕ) (hD : D≠0) (hP : D.primeFactors⊆Pall) :
    Nat.Coprime (sourceOriginalOrdinaryPart Pall n) D := by
  unfold sourceOriginalOrdinaryPart
  apply Nat.Coprime.prod_left
  intro p hp
  have hmem := Finset.mem_sdiff.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hmem.1
  have hc : Nat.Coprime p D := hprime.coprime_iff_not_dvd.mpr (by
    intro hd
    exact hmem.2 (hP (Nat.mem_primeFactors.mpr ⟨hprime,hd,hD⟩)))
  exact hc.pow_left _

/-- Exact removal of the whole fixed marked product BEFORE taking a
coefficient norm or a divisor moment: n_* divides n/D. -/
theorem b656_ordinary_divides_removed_marked_product434
    (Pall : Finset ℕ) (n D : ℕ) (hn : n≠0) (hD : D≠0)
    (hdiv : D∣n) (hP : D.primeFactors⊆Pall) :
    sourceOriginalOrdinaryPart Pall n ∣ n/D := by
  have hc := b656_ordinary_coprime_P_supported434 Pall n D hD hP
  have hd := source_ordinary_part_dvd Pall n hn
  have he : n=D*(n/D) := (Nat.mul_div_cancel' hdiv).symm
  have hd' : sourceOriginalOrdinaryPart Pall n ∣ D * (n / D) := by
    simpa only [← he] using hd
  exact hc.dvd_of_dvd_mul_left hd'

/-- Any finite product of the actual P primes has the required support.
The product here keeps repeated factors; distinctness is only needed by
the separate proof that a marked product divides its physical integer. -/
theorem b656_P_prime_product_support434 {I : Type} [Fintype I]
    (Pall : Finset ℕ) (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hP : ∀ i, p i∈Pall) :
    (∏ i, p i)≠0 ∧ (∏ i, p i).primeFactors⊆Pall := by
  refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero),?_⟩
  intro q hq
  by_contra hnot
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hc : Nat.Coprime q (∏ i, p i) := by
    apply Nat.coprime_fintype_prod_right_iff.mpr
    intro i
    apply (Nat.coprime_primes hqprime (hp i)).mpr
    intro he
    exact hnot (he ▸ hP i)
  exact (hqprime.coprime_iff_not_dvd.mp hc) (Nat.mem_primeFactors.mp hq).2.1

/-- The true prime-slot norm after removal of a fixed complete physical
mark product. Its fourth-moment exponent is independent of that product,
of the number of marks, of J and of the number of groups. -/
theorem b656_prime_core_removed_marks_bound434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (ha : ∀ m, ‖F.alpha m‖≤A) (hc : ∀ r, ‖F.residual r‖≤C)
    (n D : ℕ) (hn : n≠0) (hD : D≠0) (hdiv : D∣n)
    (hP : D.primeFactors⊆Finset.univ.biUnion P) :
    ‖primeSlotCoreValue P F n‖ ≤ A*C*((n/D).divisors.card:ℝ)^2 := by
  have hnpos : 0<n := Nat.pos_of_ne_zero hn
  have hquot : n/D≠0 := Nat.ne_of_gt
    (Nat.div_pos (Nat.le_of_dvd hnpos hdiv) (Nat.pos_of_ne_zero hD))
  have hd := b656_ordinary_divides_removed_marked_product434
    (Finset.univ.biUnion P) n D hn hD hdiv hP
  have hcard : ((sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n).divisors.card:ℝ) ≤
      ((n/D).divisors.card:ℝ) := Nat.cast_le.mpr
    (b656_divisors_card_mono434 _ _ hquot hd)
  exact (b656_prime_core_norm_le_divisor_square434 P F A C hA hC ha hc n).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (mul_nonneg hA hC))
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## PhysicalEndpointCoefficient -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
open Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ)

/-- The original endpoint half-power, evaluated on ONE physical integer
before the Euclidean sqrt(mu0) lift. It depends on no mark-list choices.
Only its extension to positions with no physical states uses Nat.sub. -/
def b656IntegerEndpointDamping434 (q : ℝ) (n : ℤ) : ℝ :=
  (∏ g : SG, (Real.sqrt q) ^
    (Green64SmallHaar.omega (smallMod g) (fun p => (n:ZMod (smallMod g p))) - (J+ell))) *
  (∏ g : BG, (Real.sqrt q) ^
    (Green64SmallHaar.omega (bigMod g) (fun p => (n:ZMod (bigMod g p))) - (J+ell)))

/-- At every genuine physical state this is EXACTLY the extra S04
endpoint factor, expressed using the same native endpointDamping as the
operator row. It is separate from the row's two damping factors. -/
theorem b656_integer_endpoint_damping_native434
    (q : ℝ) (positions : Finset ℤ)
    (x : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) :
    b656IntegerEndpointDamping434 SP smallMod BP bigMod J ell q x.val.1.val =
      (∏ g : SG, Green64SmallHaar.endpointDamping (smallMod g) (J+ell) q (x.val.2.1 g)) *
      (∏ g : BG, Green64SmallHaar.endpointDamping (bigMod g) (J+ell) q (x.val.2.2 g)) := by
  unfold b656IntegerEndpointDamping434 Green64SmallHaar.endpointDamping
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    have h := funext (x.property.1 g)
    rw [h]
  · apply Finset.prod_congr rfl
    intro g hg
    have h := funext (x.property.2 g)
    rw [h]

theorem b656_integer_endpoint_damping_unit434 (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (n : ℤ) :
    0≤b656IntegerEndpointDamping434 SP smallMod BP bigMod J ell q n ∧
    b656IntegerEndpointDamping434 SP smallMod BP bigMod J ell q n≤1 := by
  have hs : Real.sqrt q≤1 := by nlinarith [Real.sq_sqrt hq0,Real.sqrt_nonneg q]
  have hp (a : ℕ) : 0≤(Real.sqrt q)^a ∧ (Real.sqrt q)^a≤1 :=
    ⟨pow_nonneg (Real.sqrt_nonneg q) _,pow_le_one₀ (Real.sqrt_nonneg q) hs⟩
  unfold b656IntegerEndpointDamping434
  constructor
  · exact mul_nonneg (Finset.prod_nonneg (fun _ _ => (hp _).1))
      (Finset.prod_nonneg (fun _ _ => (hp _).1))
  · exact (mul_le_of_le_one_left
      (Finset.prod_nonneg (fun _ _ => (hp _).1))
      (Finset.prod_le_one₀ (fun _ _ => (hp _).1) (fun _ _ => (hp _).2))).trans
      (Finset.prod_le_one₀ (fun _ _ => (hp _).1) (fun _ _ => (hp _).2))

/-- Literal S04 coefficient n^(it) F0(n) q^((omega-Ms)/2).
For the first endpoint set t=-a1; for the second set t=a2. This
coefficient is defined BEFORE multiplying by sqrt(mu0). -/
def b656IntegerPrimeEndpointCoefficient434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (q t : ℝ) (n : ℤ) : ℂ :=
  if 0<n then imaginaryPower n.toNat t * primeSlotCoreValue P F n.toNat *
    (b656IntegerEndpointDamping434 SP smallMod BP bigMod J ell q n : ℂ) else 0

theorem b656_integer_prime_endpoint_norm434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (q t : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (n : ℤ) :
    ‖b656IntegerPrimeEndpointCoefficient434 SP smallMod BP bigMod J ell P F q t n‖ ≤
      ‖primeSlotCoreValue P F n.toNat‖ := by
  unfold b656IntegerPrimeEndpointCoefficient434
  by_cases hn : 0<n
  · rw [ite_eq_left hn,norm_mul,norm_mul,
      b656_imaginary_power_norm434 n.toNat (by omega),one_mul]
    have hd := b656_integer_endpoint_damping_unit434 SP smallMod BP bigMod J ell q hq0 hq1 n
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd.1]
    exact mul_le_of_le_one_right (norm_nonneg _) hd.2
  · rw [ite_eq_right hn,norm_zero]
    exact norm_nonneg _

/-- True removed-mark bound for the literal physical endpoint coefficient.
The only scalar multiplier is the input coefficient product A*C, with
no mark count, Haar mass, damping loss, J or group-count exponent. -/
theorem b656_integer_prime_endpoint_removed_marks434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (q t A C : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (hA : 0≤A) (hC : 0≤C)
    (ha : ∀ m, ‖F.alpha m‖≤A) (hc : ∀ r, ‖F.residual r‖≤C)
    (n : ℤ) (hn : 0<n) (D : ℕ) (hD : D≠0) (hdiv : D∣n.toNat)
    (hP : D.primeFactors⊆Finset.univ.biUnion P) :
    ‖b656IntegerPrimeEndpointCoefficient434 SP smallMod BP bigMod J ell P F q t n‖ ≤
      A*C*((n.toNat/D).divisors.card:ℝ)^2 := by
  exact (b656_integer_prime_endpoint_norm434 SP smallMod BP bigMod J ell P F q t hq0 hq1 n).trans
    (b656_prime_core_removed_marks_bound434 P F A C hA hC ha hc n.toNat D
      (by omega) hD hdiv hP)
end Green64FullPhysicalE

end

end

/-! ## PhysicalSourcePower -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option linter.unusedSectionVars false

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g, Fintype (SP g)] [∀ g, DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p, NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g, Fintype (BP g)] [∀ g, DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p, NeZero (bigMod g p)]
variable (J ell : ℕ)

/-- Original S04 real half-powers at a genuine physical state.
There is NO truncated subtraction left: every physical group has at
least J+ell distinct marks, so omega-(J+ell) is the exact real exponent. -/
theorem b656_integer_endpoint_source_half_powers434
    (q : ℝ) (hq : 0≤q) (positions : Finset ℤ)
    (x : B650IntegerPhysicalState434 SP smallMod BP bigMod J ell positions) :
    b656IntegerEndpointDamping434 SP smallMod BP bigMod J ell q x.val.1.val =
      (∏ g : SG, q ^ (((Green64SmallHaar.omega (smallMod g)
        (fun p => (x.val.1.val:ZMod (smallMod g p))):ℝ) - (J+ell:ℕ))/2)) *
      (∏ g : BG, q ^ (((Green64SmallHaar.omega (bigMod g)
        (fun p => (x.val.1.val:ZMod (bigMod g p))):ℝ) - (J+ell:ℕ))/2)) := by
  rw [b656_integer_endpoint_damping_native434]
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    rw [Green64SmallHaar.endpointDamping_eq_source_rpow _ _ q hq]
    rw [Nat.cast_sub (Green64SmallHaar.omega_ge_M _ _ (x.val.2.1 g))]
    rw [funext (x.property.1 g)]
  · apply Finset.prod_congr rfl
    intro g hg
    rw [Green64SmallHaar.endpointDamping_eq_source_rpow _ _ q hq]
    rw [Nat.cast_sub (Green64SmallHaar.omega_ge_M _ _ (x.val.2.2 g))]
    rw [funext (x.property.2 g)]
end Green64FullPhysicalE

end

end

/-! ## PhysicalUnitFactors -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- EXACT E4.1 root multiplier: original P-only epsilon, the dyadic
factor X/n, and the true root Mellin phase (n/Z)^(-iv). -/
def b656SourceRootMultiplier434 {G : Type} [Fintype G]
    (P : G → Finset ℕ) (tw : Bool) (X Z v : ℝ) (n : ℕ) : ℂ :=
  (groupSign P tw n : ℂ) * ((X/(n:ℝ) : ℝ):ℂ) *
    (((n:ℝ)/Z : ℝ):ℂ) ^ (-Complex.I*(v:ℂ))

theorem b656_source_root_multiplier_norm434 {G : Type} [Fintype G]
    (P : G → Finset ℕ) (tw : Bool) (X Z v : ℝ) (n : ℕ)
    (hX : 0≤X) (hZ : 0<Z) (hn : 0<n) (hXn : X≤(n:ℝ)) :
    ‖b656SourceRootMultiplier434 P tw X Z v n‖≤1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hsgn : ‖(groupSign P tw n:ℂ)‖=1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    cases tw <;> simp [groupSign,abs_pow]
  have hphase : ‖(((n:ℝ)/Z:ℝ):ℂ)^(-Complex.I*(v:ℂ))‖=1 := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hnR hZ) (-Complex.I*(v:ℂ))
    simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,
      mul_zero,sub_zero,Real.rpow_zero] using h
  have hrat : 0≤X/(n:ℝ) := div_nonneg hX hnR.le
  unfold b656SourceRootMultiplier434
  rw [norm_mul,norm_mul,hsgn,hphase,one_mul,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrat]
  exact (div_le_one hnR).mpr hXn

/-- Any actual unit root multiplier preserves the coefficient sup and
removed-mark budgets. The statement acts BEFORE the sqrt(mu0) lift. -/
theorem b656_endpoint_unit_multiplier434 (η c : ℂ) (hη : ‖η‖≤1) :
    ‖η*c‖≤‖c‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hη
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## QFibreBasicsNative -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

noncomputable def sourceEndpointCollisionCount {A : Type} (S : Finset A)
    (endpoint : A → ℕ) (v : ℕ) : ℕ := (S.filter (fun a => endpoint a=v)).card

theorem source_endpoint_fibre_norm_le {A : Type} (S : Finset A) (endpoint : A → ℕ)
    (weight : A → ℂ) (v : ℕ) (B : ℝ)
    (hweight : ∀ a  ∈  S, endpoint a=v  →  ‖weight a‖≤B) :
    ‖sourceEndpointFibre S endpoint weight v‖ ≤ (sourceEndpointCollisionCount S endpoint v:ℝ)*B := by
  unfold sourceEndpointFibre
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a  ∈  S.filter (fun a => endpoint a=v), B := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha,heq⟩ := Finset.mem_filter.mp ha
      exact hweight a ha heq
    _ = _ := by simp [sourceEndpointCollisionCount]

theorem ordered_skip_phase_norm (n : ℕ) (Q : Fin n → Finset ℕ)
    (δ : Fin n → Bool) (s ξ : Fin n → ℝ) (a : OrderedQSkip n Q δ) :
    ‖orderedSkipPhase s ξ a‖=1 := by
  simp [orderedSkipPhase,norm_prod]

theorem source_actual_sorted_factorial_norm_exact
    (r d : ℕ) :
    ‖sourceActualSortedFactorial r d‖ =
      ∏ _j : Fin (d+1), (1:ℝ)/(r.factorial:ℝ) := by
  unfold sourceActualSortedFactorial
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp

noncomputable def sourceArbitraryPrimeTupleFibre
    (I : Type) [Fintype I] (Q : I → Finset ℕ) (e : ℕ) :
    Finset ((i : I) → {p : ℕ // p ∈ Q i}) :=
  (Finset.univ : Finset ((i : I) → {p : ℕ // p ∈ Q i})).filter
    (fun a => (∏ i : I, (a i).val) = e)

theorem source_prime_tuple_fibre_card_arbitrary
    (I : Type) [Fintype I] (Q : I → Finset ℕ) (e : ℕ)
    (hPrime : ∀ i p, p ∈ Q i → p.Prime) :
    (sourceArbitraryPrimeTupleFibre I Q e).card ≤
      (Fintype.card I).factorial := by
  classical
  let enc : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let F : ((i : I) → {p : ℕ // p ∈ Q i}) → List ℕ :=
    fun a => List.ofFn (fun j : Fin (Fintype.card I) => (a (enc.symm j)).val)
  have hinj : Function.Injective F := by
    intro a b hab
    have he : (fun j : Fin (Fintype.card I) => (a (enc.symm j)).val) =
        (fun j : Fin (Fintype.card I) => (b (enc.symm j)).val) :=
      List.ofFn_injective hab
    funext i
    have hi := congrFun he (enc i)
    rw [enc.symm_apply_apply i] at hi
    exact Subtype.ext hi
  have hperm (a : (i : I) → {p : ℕ // p ∈ Q i})
      (ha : a ∈ sourceArbitraryPrimeTupleFibre I Q e) :
      List.Perm (F a) e.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · calc
        (F a).prod = ∏ j : Fin (Fintype.card I), (a (enc.symm j)).val :=
          List.prod_ofFn
        _ = ∏ i : I, (a i).val :=
          Equiv.prod_comp enc.symm (fun i : I => (a i).val)
        _ = e := (Finset.mem_filter.mp ha).2
    · intro p hp
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
      exact hPrime (enc.symm j) _ (a (enc.symm j)).property
  have himage : (sourceArbitraryPrimeTupleFibre I Q e).image F ⊆
      e.primeFactorsList.permutations.toFinset := by
    intro l hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr (hperm a ha))
  by_cases hEmpty : (sourceArbitraryPrimeTupleFibre I Q e).Nonempty
  · obtain ⟨a,ha⟩ := hEmpty
    have hlen : e.primeFactorsList.length = Fintype.card I := by
      have hh := (hperm a ha).length_eq
      calc
        e.primeFactorsList.length = (F a).length := hh.symm
        _ = Fintype.card I := by simp [F]
    calc
      (sourceArbitraryPrimeTupleFibre I Q e).card =
          ((sourceArbitraryPrimeTupleFibre I Q e).image F).card :=
            (Finset.card_image_iff.mpr (fun a ha b hb h => hinj h)).symm
      _ ≤ e.primeFactorsList.permutations.toFinset.card :=
        Finset.card_le_card himage
      _ ≤ e.primeFactorsList.permutations.length :=
        List.toFinset_card_le _
      _ = (Fintype.card I).factorial := by rw [List.length_permutations,hlen]
  · have hf : (sourceArbitraryPrimeTupleFibre I Q e).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
    rw [hf]
    exact Nat.zero_le _

theorem source_partial_group_prime_factorization
    {B : Type} [Fintype B] [DecidableEq B]
    (I : B → Type) [∀ b, Fintype (I b)]
    (Q : B → Finset ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (f : (b : B) → (i : I b) → {p // p ∈ Q b})
    (b0 : B) (p : ℕ) (hp : p ∈ Q b0) :
    (∏ b : B, ∏ i : I b, (f b i).val).factorization p =
      ((Finset.univ : Finset (I b0)).filter
        (fun i => (f b0 i).val = p)).card := by
  classical
  have hNonzero (b : B) : (∏ i : I b, (f b i).val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun i hi => (hPrime b _ (f b i).property).ne_zero)
  have hFactor : (∏ b : B, ∏ i : I b, (f b i).val).factorization p =
      ∑ b : B, ((Finset.univ : Finset (I b)).filter
           (fun i => (f b i).val = p)).card := by
    rw [Nat.factorization_prod (by intro b hb; exact hNonzero b)]
    simp only [Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl (fun b hb =>
      source_prime_tuple_factorization_count
        (fun i : I b => (f b i).val)
        (fun i => hPrime b _ (f b i).property) p)
  rw [hFactor]
  apply Finset.sum_eq_single b0
  · intro b hb hneq
    apply Finset.card_eq_zero.mpr
    ext i
    have hne : (f b i).val ≠ p := by
      intro heq
      exact hneq (hDisjoint b b0 p (heq ▸ (f b i).property) hp)
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ b0))

theorem source_partial_group_products_determined
    {B : Type} [Fintype B] [DecidableEq B]
    (I : B → Type) [∀ b, Fintype (I b)]
    (Q : B → Finset ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c)
    (f g : (b : B) → (i : I b) → {p // p ∈ Q b})
    (htotal : (∏ b : B, ∏ i : I b, (f b i).val) =
       (∏ b : B, ∏ i : I b, (g b i).val))
    (b0 : B) :
    (∏ i : I b0, (f b0 i).val) =
      (∏ i : I b0, (g b0 i).val) := by
  classical
  let u := ∏ i : I b0, (f b0 i).val
  let v := ∏ i : I b0, (g b0 i).val
  have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i hi => (hPrime b0 _ (f b0 i).property).ne_zero)
  have hv : v ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i hi => (hPrime b0 _ (g b0 i).property).ne_zero)
  apply Nat.eq_of_factorization_eq hu hv
  intro p
  have hFacF := source_prime_tuple_factorization_count
    (fun i : I b0 => (f b0 i).val)
    (fun i => hPrime b0 _ (f b0 i).property) p
  have hFacG := source_prime_tuple_factorization_count
    (fun i : I b0 => (g b0 i).val)
    (fun i => hPrime b0 _ (g b0 i).property) p
  change u.factorization p = _ at hFacF
  change v.factorization p = _ at hFacG
  by_cases hp : p ∈ Q b0
  · have hf := source_partial_group_prime_factorization
      I Q hPrime hDisjoint f b0 p hp
    have hg := source_partial_group_prime_factorization
      I Q hPrime hDisjoint g b0 p hp
    rw [htotal] at hf
    exact hFacF.trans (hf.symm.trans (hg.trans hFacG.symm))
  · rw [hFacF,hFacG]
    have hzeroF : ((Finset.univ : Finset (I b0)).filter
      (fun i => (f b0 i).val = p)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext i
      have hne : (f b0 i).val ≠ p := by
        intro he
        exact hp (he ▸ (f b0 i).property)
      simp [hne]
    have hzeroG : ((Finset.univ : Finset (I b0)).filter
      (fun i => (g b0 i).val = p)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext i
      have hne : (g b0 i).val ≠ p := by
        intro he
        exact hp (he ▸ (g b0 i).property)
      simp [hne]
    rw [hzeroF,hzeroG]
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## QGroupedCollisionNative -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

noncomputable def sourceGroupedPrimeTupleFibre
    {B : Type} [Fintype B] [DecidableEq B]
    (I : B → Type) [∀ b, Fintype (I b)]
    (Q : B → Finset ℕ) (e : ℕ) :
    Finset ((b : B) → (i : I b) → {p : ℕ // p ∈ Q b}) :=
  (Finset.univ : Finset ((b : B) → (i : I b) → {p : ℕ // p ∈ Q b})).filter
    (fun a => (∏ b : B, ∏ i : I b, (a b i).val) = e)

theorem source_grouped_prime_fibre_card_le_factorial_product
    {B : Type} [Fintype B] [DecidableEq B]
    (I : B → Type) [∀ b, Fintype (I b)]
    (Q : B → Finset ℕ) (e : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    (sourceGroupedPrimeTupleFibre I Q e).card ≤
      ∏ b : B, (Fintype.card (I b)).factorial := by
  classical
  let S := sourceGroupedPrimeTupleFibre I Q e
  by_cases hEmpty : S.Nonempty
  · obtain ⟨a0,ha0⟩ := hEmpty
    let groupProduct : B → ℕ := fun b =>
      ∏ i : I b, (a0 b i).val
    let Fib : (b : B) → Finset ((i : I b) → {p : ℕ // p ∈ Q b}) :=
      fun b => sourceArbitraryPrimeTupleFibre (I b) (fun _ => Q b) (groupProduct b)
    have hfib (a : {a // a ∈ S}) (b : B) : a.val b ∈ Fib b := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact source_partial_group_products_determined I Q hPrime hDisjoint
        a.val a0
        (by
          have hh : (∏ b : B, ∏ i : I b, (a.val b i).val) = e :=
            (Finset.mem_filter.mp a.property).2
          have hh0 : (∏ b : B, ∏ i : I b, (a0 b i).val) = e :=
            (Finset.mem_filter.mp ha0).2
          exact hh.trans hh0.symm)
        b
    let encode : {a // a ∈ S} → ((b : B) → Fib b) :=
      fun a b => ⟨a.val b, hfib a b⟩
    have hinj : Function.Injective encode := by
      intro a b hab
      apply Subtype.ext
      funext i j
      have hh := congrFun hab i
      exact congrFun (congrArg Subtype.val hh) j
    have hCard :
        S.card ≤ ∏ b : B, (Fib b).card := by
      calc
        S.card = Fintype.card {a // a ∈ S} :=
          (Fintype.card_coe S).symm
        _ ≤ Fintype.card ((b : B) → Fib b) :=
          Fintype.card_le_of_injective encode hinj
        _ = ∏ b : B, (Fib b).card := by
          rw [Fintype.card_pi]
          apply Finset.prod_congr rfl
          intro b hb
          exact Fintype.card_coe (Fib b)
    calc
      S.card ≤ ∏ b : B, (Fib b).card := hCard
      _ ≤ ∏ b : B, (Fintype.card (I b)).factorial := by
        apply Finset.prod_le_prod₀
        · intro b hb; exact Nat.zero_le _
        · intro b hb
          exact source_prime_tuple_fibre_card_arbitrary
            (I b) (fun _ => Q b) (groupProduct b)
            (fun _ p hp => hPrime b p hp)
  · have hS : S.card=0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
    rw [hS]
    exact Nat.zero_le _

noncomputable def sourceIndexedGroupedPrimeFibre
    (T : Type) [Fintype T]
    {B : Type} [Fintype B] [DecidableEq B]
    (label : T → B) (Q : B → Finset ℕ) (e : ℕ) :
    Finset ((i : T) → {p : ℕ // p ∈ Q (label i)}) :=
  (Finset.univ : Finset ((i : T) → {p : ℕ // p ∈ Q (label i)})).filter
    (fun a => (∏ i : T, (a i).val) = e)

theorem source_indexed_grouped_prime_fibre_factorial
    (T : Type) [Fintype T]
    {B : Type} [Fintype B] [DecidableEq B]
    (label : T → B) (Q : B → Finset ℕ) (e : ℕ)
    (hPrime : ∀ b p, p ∈ Q b → p.Prime)
    (hDisjoint : ∀ b c p, p ∈ Q b → p ∈ Q c → b = c) :
    (sourceIndexedGroupedPrimeFibre T label Q e).card ≤
      ∏ b : B, (Fintype.card {i : T // label i = b}).factorial := by
  classical
  let I : B → Type := fun b => {i : T // label i=b}
  let f : ((i : T) → {p : ℕ // p ∈ Q (label i)}) →
      ((b : B) → (j : I b) → {p : ℕ // p ∈ Q b}) :=
    fun a b j =>
      ⟨(a j.val).val, by
        have hp := (a j.val).property
        simpa only [j.property] using hp⟩
  have hProd (a : (i : T) → {p : ℕ // p ∈ Q (label i)}) :
      (∏ b : B, ∏ j : I b, (f a b j).val) =
       ∏ i : T, (a i).val := by
    exact Fintype.prod_fiberwise label (fun i => (a i).val)
  have hInj : Function.Injective f := by
    intro a b hab
    funext i
    have hh := congrFun (congrFun hab (label i)) (⟨i,rfl⟩ : I (label i))
    exact Subtype.ext (congrArg Subtype.val hh)
  have hFib (a : {a // a ∈ sourceIndexedGroupedPrimeFibre T label Q e}) :
      f a.val ∈ sourceGroupedPrimeTupleFibre I Q e := by
    simp only [sourceGroupedPrimeTupleFibre, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hProd]
    exact (Finset.mem_filter.mp a.property).2
  have hSubcard :
      (sourceIndexedGroupedPrimeFibre T label Q e).card ≤
        (sourceGroupedPrimeTupleFibre I Q e).card := by
    calc
      (sourceIndexedGroupedPrimeFibre T label Q e).card =
        Fintype.card {a // a ∈ sourceIndexedGroupedPrimeFibre T label Q e} :=
          (Fintype.card_coe _).symm
      _ ≤ Fintype.card {a // a ∈ sourceGroupedPrimeTupleFibre I Q e} :=
        Fintype.card_le_of_injective
          (fun a => (⟨f a.val,hFib a⟩ :
            {a // a ∈ sourceGroupedPrimeTupleFibre I Q e}))
          (by
            intro a b hab
            apply Subtype.ext
            exact hInj (congrArg Subtype.val hab))
      _ = (sourceGroupedPrimeTupleFibre I Q e).card :=
        Fintype.card_coe _
  exact hSubcard.trans
    (source_grouped_prime_fibre_card_le_factorial_product I Q e hPrime hDisjoint)

theorem source_labelled_slot_collision_card_le_of_finset
    (T : Type) [Fintype T]
    {B : Type} [Fintype B] [DecidableEq B]
    (Qslot : T → Finset ℕ) (label : T → B) (Qband : B → Finset ℕ)
    (S : Finset ((z : T) → {p : ℕ // p ∈ Qslot z}))
    (e : ℕ)
    (hSame : ∀ z, Qslot z = Qband (label z))
    (hPrime : ∀ b p, p ∈ Qband b → p.Prime)
    (hDisj : ∀ b c p, p ∈ Qband b → p ∈ Qband c → b=c) :
    sourceEndpointCollisionCount S
      (fun a => ∏ z : T, (a z).val) e ≤
    ∏ b : B, (Fintype.card {z : T // label z=b}).factorial := by
  classical
  let φ : ((z : T) → {p : ℕ // p ∈ Qslot z}) →
      ((z : T) → {p : ℕ // p ∈ Qband (label z)}) :=
    fun a z => ⟨(a z).val, by rw [←hSame z]; exact (a z).property⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    funext z
    have hz := congrFun hab z
    have hval : (a z).val = (b z).val := by
      simpa only [φ] using congrArg Subtype.val hz
    exact Subtype.ext hval
  let F := S.filter (fun a => (∏ z : T, (a z).val) = e)
  have hsub : F.image φ ⊆ sourceIndexedGroupedPrimeFibre T label Qband e := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hp : (∏ z : T, (b z).val) = e :=
      (Finset.mem_filter.mp hb).2
    simpa only [φ] using hp
  have hcard : F.card ≤
      (sourceIndexedGroupedPrimeFibre T label Qband e).card := by
    calc
      F.card = (F.image φ).card :=
        (Finset.card_image_iff.mpr (fun a ha b hb he => hinj he)).symm
      _ ≤ (sourceIndexedGroupedPrimeFibre T label Qband e).card :=
        Finset.card_le_card hsub
  exact hcard.trans
    (source_indexed_grouped_prime_fibre_factorial
      T label Qband e hPrime hDisj)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## QResidualUnitNative -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

theorem source_actual_sorted_skip_collision_le_factorial_power
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length → Bool)
    (h : ℕ) :
    let n := (sourceOrderedLabels r
      (sourceActualSortedScales r d L) b slot).length
    let Q := sourceActualSortedQ r d L b slot
    sourceEndpointCollisionCount
      (Finset.univ : Finset (OrderedQSkip n Q δ))
      orderedSkipProduct h ≤ r.factorial^(d+1) := by
  dsimp only
  let n := (sourceOrderedLabels r
    (sourceActualSortedScales r d L) b slot).length
  let T := {z : Fin n // ¬δ z=true}
  let Q := sourceActualSortedQ r d L b slot
  let lab := fun z : Fin n =>
    (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot z).val.1
  have hprime : ∀ j p, p ∈ sourceOriginalQActualBands r d L j → p.Prime :=
    source_original_Q_actual_prime r d L
  have hdisj : ∀ j k p, p ∈ sourceOriginalQActualBands r d L j →
       p ∈ sourceOriginalQActualBands r d L k → j=k :=
    source_original_Q_actual_all_disjoint r d L hr hL
  have hSame (z : T) : Q z.val =
      sourceOriginalQActualBands r d L (lab z.val) := rfl
  have hCollision := source_labelled_slot_collision_card_le_of_finset T
    (fun z : T => Q z.val) (fun z : T => lab z.val)
    (sourceOriginalQActualBands r d L)
    (Finset.univ : Finset (OrderedQSkip n Q δ))
    h hSame hprime hdisj
  have hTerm (j : Fin (d+1)) :
      Fintype.card {z : T // lab z.val=j} ≤ r := by
    let F : {z : T // lab z.val=j} → Fin r := fun z =>
      (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b slot
        z.val.val).val.2
    have hinj : Function.Injective F := by
      intro z w he
      apply Subtype.ext
      apply Subtype.ext
      apply (sourceSortedLabelEquiv r
        (sourceActualSortedScales r d L) b slot).injective
      exact Subtype.ext (Prod.ext (z.property.trans w.property.symm) he)
    calc
      Fintype.card {z : T // lab z.val=j} ≤ Fintype.card (Fin r) :=
        Fintype.card_le_of_injective F hinj
      _ = r := Fintype.card_fin _
  have hEq : (orderedSkipProduct : OrderedQSkip n Q δ → ℕ) =
      (fun a => ∏ z : T, (a z).val) := rfl
  rw [hEq]
  calc
    sourceEndpointCollisionCount
       (Finset.univ : Finset (OrderedQSkip n Q δ))
       (fun a => ∏ z : T, (a z).val) h ≤
      ∏ j : Fin (d+1), (Fintype.card {z : T // lab z.val=j}).factorial :=
        hCollision
    _ ≤ ∏ _j : Fin (d+1), r.factorial := by
      apply Finset.prod_le_prod₀
      · intro j hj; exact Nat.zero_le _
      · intro j hj
        exact Nat.factorial_le (hTerm j)
    _ = r.factorial^(d+1) := by simp

theorem source_actual_factorial_collision_cancels (r d : ℕ) :
    (r.factorial:ℝ)^(d+1) *
      ‖sourceActualSortedFactorial r d‖ = 1 := by
  have hnorm := source_actual_sorted_factorial_norm_exact r d
  have hf : (r.factorial:ℝ) ≠ 0 := by positivity
  have hnorm2 : ‖sourceActualSortedFactorial r d‖ =
      ((r.factorial:ℝ)⁻¹)^(d+1) := by
    simpa [one_div] using hnorm
  rw [hnorm2, ←mul_pow]
  simp [hf]

theorem source_native_residual_norm_le_one
    (r d : ℕ) (L : ℝ) (hr : 1 ≤ r) (hL : 0 < L)
    (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (σ₀ σ₁ : ℝ) (t : ℕ) :
    ‖(sourceNativePrimeCore r d L b slot δ ξ K alpha q χ σ₀ σ₁).residual t‖ ≤ 1 := by
  let n := (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length
  let Q := sourceActualSortedQ r d L b slot
  let s := sourceActualSortedFrequencyScales r d L b slot
  let S := (Finset.univ : Finset (OrderedQSkip n Q δ))
  have hb := source_endpoint_fibre_norm_le S orderedSkipProduct
    (fun a => sourceActualSortedFactorial r d * orderedSkipPhase s ξ a) t
    ‖sourceActualSortedFactorial r d‖ (by
      intro a ha he
      simp only [norm_mul,ordered_skip_phase_norm,mul_one,le_refl])
  have hc : (sourceEndpointCollisionCount S orderedSkipProduct t : ℝ) ≤
      (r.factorial : ℝ)^(d+1) := by
    exact_mod_cast source_actual_sorted_skip_collision_le_factorial_power r d L hr hL b slot δ t
  change ‖sourceEndpointFibre S orderedSkipProduct
    (fun a => sourceActualSortedFactorial r d * orderedSkipPhase s ξ a) t‖ ≤ 1
  calc
    _ ≤ (sourceEndpointCollisionCount S orderedSkipProduct t : ℝ) *
        ‖sourceActualSortedFactorial r d‖ := hb
    _ ≤ (r.factorial : ℝ)^(d+1) * ‖sourceActualSortedFactorial r d‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = 1 := source_actual_factorial_collision_cancels r d
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualFineNativeInputs -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Pointwise arithmetic input package; below it is proved for the actual
fine coefficients and original sorted deleted-slot residual, with no
sup, L2, distribution, collision or RMS premise. -/
def B656UnitRoughPrimeCore434 (L : ℝ) (F : PrimeSlotCore) : Prop :=
  (∀ n : ℕ, ‖F.alpha n‖≤1) ∧ (∀ n : ℕ, ‖F.residual n‖≤1) ∧
  (∀ n : ℕ, F.alpha n≠0 → rough (Real.exp (Real.sqrt L)) n)

/-- The actual source core and BOTH Parity endpoint cores satisfy unit
coefficient/residual bounds and the original exp(sqrt L) alpha support.
The TRUE residual uses the complete moving Q family, every labelled skip
allocation, every Q Fourier parameter and the original factorial. The
actual prime band's endpoints, both Mellin exponents and character stay.
No lower bound exp(sqrt L) is imposed on the distinguished Q prime. -/
theorem b656_actual_fine_native_and_parity_inputs434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        B656UnitRoughPrimeCore434 L F ∧
        ∀ xi1 xi2 rho sigma : ℝ,
          B656UnitRoughPrimeCore434 L
            (b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma) ∧
          B656UnitRoughPrimeCore434 L
            (b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma) := by
  filter_upwards [b629_actual_fine_coefficient_and_rough_support434
    S beta gamma hS hbeta hgamma,eventually_ge_atTop (1:ℝ)] with L hcoeff hL
  refine ⟨hL,?_⟩
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  have ha : ∀ n, ‖F.alpha n‖≤1 := by
    intro n
    by_cases hnK : n∈K
    · simpa only [F,sourceNativePrimeCore,restrictSequence,hnK,ite_true] using
        (hcoeff prime l u hlow n).1
    · simp only [F,sourceNativePrimeCore,restrictSequence,hnK,ite_false,norm_zero]
      norm_num
  have hc : ∀ n, ‖F.residual n‖≤1 := by
    intro n
    exact source_native_residual_norm_le_one r d L hr (zero_lt_one.trans_le hL)
      b slot δ ξ K (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1 n
  have hs : ∀ n, F.alpha n≠0 → rough (Real.exp (Real.sqrt L)) n := by
    intro n hn
    have hraw : b629ActualFineAlpha434 prime L S gamma l u n≠0 := by
      intro hz
      apply hn
      simp only [F,sourceNativePrimeCore,restrictSequence,hz,ite_self]
    have hcell : n∈Finset.Icc l u := by
      by_contra hnot
      exact hraw (by simp only [b629ActualFineAlpha434,hnot,ite_false])
    have hl : 0<l := by
      have h : (0:ℝ)<l := (Real.exp_pos _).trans_le hlow
      exact_mod_cast h
    exact ⟨lt_of_lt_of_le hl (Finset.mem_Icc.mp hcell).1,(hcoeff prime l u hlow n).2 hraw⟩
  refine ⟨⟨ha,hc,hs⟩,?_⟩
  intro xi1 xi2 rho sigma
  constructor
  · refine ⟨ha,?_,hs⟩
    intro n
    simpa only [b633ParityEFirstCore434,norm_star] using hc n
  · refine ⟨ha,?_,hs⟩
    intro n
    simpa only [b633ParitySecondCore434,norm_star] using hc n
end Green64Analytic.Parity

end

end

/-! ## RoughPartCount -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/- Exact source-selected legacy arithmetic from task-b9e665139d2c. -/

noncomputable def sourceLargePrimePart (W : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p : ℕ => W < (p:ℝ))).prod
    (fun p : ℕ => p ^ (n.factorization p))

theorem source_rough_divisor_primeFactors_subset
    (W : ℝ) (n d : ℕ)
    (hn : n ≠ 0) (hdvd : d ∣ n) (hr : rough W d) :
    d.primeFactors ⊆ n.primeFactors.filter (fun p => W < (p:ℝ)) := by
  intro p hp
  have hPrime := (Nat.mem_primeFactors.mp hp).1
  have hpd := (Nat.mem_primeFactors.mp hp).2.1
  have hpN : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hPrime, dvd_trans hpd hdvd, hn⟩
  exact Finset.mem_filter.mpr ⟨hpN, hr.2 p hPrime hpd⟩

theorem source_rough_divisor_dvd_largePrimePart
    (W : ℝ) (n d : ℕ)
    (hn : n ≠ 0) (hdvd : d ∣ n) (hr : rough W d) :
    d ∣ sourceLargePrimePart W n := by
  have hsub := source_rough_divisor_primeFactors_subset W n d hn hdvd hr
  have hf := (Nat.factorization_le_iff_dvd hr.1.ne' hn).mpr hdvd
  unfold sourceLargePrimePart
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hr.1.ne']
  exact (Finset.prod_dvd_prod_of_dvd
    (s := d.primeFactors)
    (fun p => p ^ (d.factorization p))
    (fun p => p ^ (n.factorization p))
    (fun p hp => Nat.pow_dvd_pow p (hf p))).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ hsub)

theorem source_large_prime_succ_le_two_pow (e : ℕ) :
    e+1 ≤ 2^e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      have h1 : e+2 ≤ 2*(e+1) := by omega
      have h2 := Nat.mul_le_mul_left 2 ih
      calc
        e+1+1 = e+2 := by omega
        _ ≤ 2*(e+1) := h1
        _ ≤ 2*(2^e) := h2
        _ = 2^(e+1) := by simp [pow_succ, mul_comm]

theorem source_large_prime_part_card_divisors_le_two_pow
    (W : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (sourceLargePrimePart W n).divisors.card ≤
      2^((n.primeFactors.filter (fun p : ℕ => W < (p:ℝ))).sum
        (fun p : ℕ => n.factorization p)) := by
  let P : Finset ℕ := n.primeFactors.filter (fun p => W < (p:ℝ))
  let e : {p // p ∈ P} → ℕ := fun z => n.factorization z.val
  have hPrime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hBig : sourceLargePrimePart W n =
      sourceOriginalPPrimePowerProduct P e := by
    unfold sourceLargePrimePart sourceOriginalPPrimePowerProduct
    have hh : (∏ z : {p // p ∈ P}, z.val ^ (n.factorization z.val)) =
        ∏ p ∈ P, p ^ (n.factorization p) := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.prod_attach P (fun p => p ^ (n.factorization p)))
    exact hh.symm
  have hBig0 : sourceLargePrimePart W n ≠ 0 := by
    rw [hBig]
    exact source_original_P_power_product_ne_zero P hPrime e
  have hSupp : (sourceLargePrimePart W n).primeFactors ⊆ P := by
    rw [hBig]
    exact source_original_P_power_primeFactors_subset P hPrime e
  have hVal (p : ℕ) (hp : p ∈ P) :
      (sourceLargePrimePart W n).factorization p = n.factorization p := by
    rw [hBig, source_original_P_power_factorization_at P hPrime e p hp]
  rw [Nat.card_divisors hBig0]
  calc
    (∏ p ∈ (sourceLargePrimePart W n).primeFactors,
        ((sourceLargePrimePart W n).factorization p+1)) ≤
      ∏ p ∈ (sourceLargePrimePart W n).primeFactors,
        2^(n.factorization p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        omega
      · intro p hp
        rw [hVal p (hSupp hp)]
        exact source_large_prime_succ_le_two_pow _
    _ ≤ ∏ p ∈ P, 2^(n.factorization p) := by
      apply Finset.prod_le_prod_of_subset_of_one_le hSupp
      intro p hp _
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide : (2:ℕ)≠0))
    _ = 2^(∑ p ∈ P, n.factorization p) := by
      exact Finset.prod_pow_eq_pow_sum P (fun p => n.factorization p) 2
    _ = _ := by rfl

theorem source_rough_divisors_card_le_large_prime_two_pow
    (W : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (n.divisors.filter (fun d => rough W d)).card ≤
      2^((n.primeFactors.filter (fun p : ℕ => W < (p:ℝ))).sum
        (fun p : ℕ => n.factorization p)) := by
  have hBig0 : sourceLargePrimePart W n ≠ 0 := by
    unfold sourceLargePrimePart
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors
      (Finset.mem_filter.mp hp).1).ne_zero
  have hsub : n.divisors.filter (fun d => rough W d) ⊆
      (sourceLargePrimePart W n).divisors := by
    intro d hd
    obtain ⟨hdiv,hr⟩ := Finset.mem_filter.mp hd
    have hdn := (Nat.mem_divisors.mp hdiv).1
    exact Nat.mem_divisors.mpr
      ⟨source_rough_divisor_dvd_largePrimePart W n d hn hdn hr,hBig0⟩
  exact (Finset.card_le_card hsub).trans
    (source_large_prime_part_card_divisors_le_two_pow W n hn)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## RoughDivisorBound -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/- Exact source-selected legacy arithmetic from task-b9e665139d2c. -/

theorem source_large_prime_exponent_log_mass
    (W : ℝ) (n : ℕ) (hn : n ≠ 0) (hW : 1 < W) :
    ((n.primeFactors.filter (fun p : ℕ => W < (p:ℝ))).sum
      (fun p : ℕ => n.factorization p) : ℝ)*Real.log W ≤
      Real.log (n:ℝ) := by
  let P : Finset ℕ := n.primeFactors.filter (fun p : ℕ => W < (p:ℝ))
  have hWp : 0 < W := zero_lt_one.trans hW
  have hLogW : 0 < Real.log W := Real.log_pos hW
  have hterms (p : ℕ) (hp : p ∈ P) :
      (n.factorization p:ℝ)*Real.log W ≤
        (n.factorization p:ℝ)*Real.log (p:ℝ) := by
    have hpBound : W ≤ (p:ℝ) :=
      (Finset.mem_filter.mp hp).2.le
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hWp hpBound) (Nat.cast_nonneg _)
  have hsum :
      (∑ p ∈ P, (n.factorization p:ℝ)*Real.log W) ≤
      ∑ p ∈ n.primeFactors,
        (n.factorization p:ℝ)*Real.log (p:ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, (n.factorization p:ℝ)*Real.log (p:ℝ) :=
        Finset.sum_le_sum (fun p hp => hterms p hp)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun p : ℕ => W < (p:ℝ)) n.primeFactors) (fun p hp _ => by
          have hPrime := Nat.prime_of_mem_primeFactors hp
          exact mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by exact_mod_cast hPrime.one_le)))
  have hLogFact : Real.log (n:ℝ) =
      ∑ p ∈ n.primeFactors,
        (n.factorization p:ℝ)*Real.log (p:ℝ) := by
    simpa only [Finsupp.sum, Nat.support_factorization] using
      (Real.log_nat_eq_sum_factorization n)
  have hCast : (∑ p ∈ P, (n.factorization p:ℝ))*Real.log W =
      ∑ p ∈ P, (n.factorization p:ℝ)*Real.log W := by
    rw [Finset.sum_mul]
  change (∑ p ∈ P, (n.factorization p:ℝ))*Real.log W ≤ _
  rw [hCast,hLogFact]
  exact hsum

theorem source_rough_divisors_card_le_exp_log
    (W : ℝ) (n : ℕ) (hn : n ≠ 0) (hW : 1 < W) :
    ((n.divisors.filter (fun d => rough W d)).card:ℝ) ≤
      Real.exp (Real.log (n:ℝ)/Real.log W) := by
  let E : ℕ := (n.primeFactors.filter (fun p : ℕ => W < (p:ℝ))).sum
    (fun p : ℕ => n.factorization p)
  have hLogW : 0 < Real.log W := Real.log_pos hW
  have hMass : (E:ℝ)*Real.log W ≤ Real.log (n:ℝ) := by
    simpa only [E, Nat.cast_sum] using
      (source_large_prime_exponent_log_mass W n hn hW)
  have hE : (E:ℝ) ≤ Real.log (n:ℝ)/Real.log W :=
    (le_div_iff₀ hLogW).mpr hMass
  have hC := source_rough_divisors_card_le_large_prime_two_pow W n hn
  change (n.divisors.filter (fun d => rough W d)).card ≤ 2^E at hC
  have hCast : ((n.divisors.filter (fun d => rough W d)).card:ℝ) ≤
      (2:ℝ)^E := by exact_mod_cast hC
  have hExp2 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hPow : (2:ℝ)^E ≤ (Real.exp 1)^E :=
    pow_le_pow_left₀ (by norm_num) hExp2 E
  have hEx : (Real.exp 1)^E = Real.exp (E:ℝ) := by
    rw [← Real.exp_nat_mul]
    simp only [mul_one]
  exact hCast.trans (hPow.trans
    (hEx.le.trans (Real.exp_le_exp.mpr hE)))

theorem source_rough_divisors_card_le_exp_two_sqrt
    (L : ℝ) (hL : 1 ≤ L) (n : ℕ) (hn : n ≠ 0)
    (hN : (n:ℝ) ≤ Real.exp (L+Real.sqrt L)) :
    ((n.divisors.filter (fun d => rough (Real.exp (Real.sqrt L)) d)).card:ℝ) ≤
      Real.exp (2*Real.sqrt L) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hSqrt : 0 < Real.sqrt L := Real.sqrt_pos.2 hLp
  have hSqrt1 : 1 ≤ Real.sqrt L := by
    simpa only [Real.sqrt_one] using (Real.sqrt_le_sqrt hL)
  have hW : 1 < Real.exp (Real.sqrt L) := by
    have hh := Real.exp_strictMono hSqrt
    simpa only [Real.exp_zero] using hh
  have hC := source_rough_divisors_card_le_exp_log
    (Real.exp (Real.sqrt L)) n hn hW
  have hnpos : (0:ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hLogN : Real.log (n:ℝ) ≤ L+Real.sqrt L := by
    calc
      _ ≤ Real.log (Real.exp (L+Real.sqrt L)) :=
        Real.log_le_log hnpos hN
      _ = _ := Real.log_exp _
  have hLogW : Real.log (Real.exp (Real.sqrt L)) = Real.sqrt L :=
    Real.log_exp _
  rw [hLogW] at hC
  have hEq : (Real.sqrt L+1)*Real.sqrt L = L+Real.sqrt L := by
    have hh := Real.sq_sqrt (zero_le_one.trans hL)
    nlinarith [hh]
  have hExpBound : Real.log (n:ℝ)/Real.sqrt L ≤ 2*Real.sqrt L := by
    have hdiv : Real.log (n:ℝ)/Real.sqrt L ≤
        Real.sqrt L+1 := by
      apply (div_le_iff₀ hSqrt).mpr
      nlinarith [hLogN,hEq]
    linarith
  exact hC.trans (Real.exp_le_exp.mpr hExpBound)

theorem source_rough_divisors_uniform_source_range_eventually
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop,
      ∀ n : ℕ, n ≠ 0 →
        (n:ℝ) ≤ C*Real.exp L+2 →
        ((n.divisors.filter (fun d =>
          rough (Real.exp (Real.sqrt L)) d)).card:ℝ) ≤
          Real.exp (2*Real.sqrt L) := by
  have hSqrt : Tendsto (fun L : ℝ => Real.sqrt L) atTop atTop :=
    Real.tendsto_sqrt_atTop
  have hLarge : ∀ᶠ L : ℝ in atTop,
      C+1 ≤ Real.sqrt L :=
    hSqrt.eventually (eventually_ge_atTop (C+1))
  filter_upwards [hLarge, eventually_ge_atTop (1:ℝ)]
    with L hS hL n hn hnBound
  have hLp : 0 ≤ L := zero_le_one.trans hL
  have hExp1 : 1 ≤ Real.exp L := Real.one_le_exp hLp
  have hCexp : C+2 ≤ Real.exp (Real.sqrt L) := by
    linarith [Real.add_one_le_exp (Real.sqrt L)]
  have hExpBound : (n:ℝ) ≤ Real.exp (L+Real.sqrt L) := by
    calc
      _ ≤ C*Real.exp L+2 := hnBound
      _ ≤ (C+2)*Real.exp L := by nlinarith [hExp1]
      _ ≤ Real.exp (Real.sqrt L)*Real.exp L :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos L).le
      _ = Real.exp (L+Real.sqrt L) := by
        rw [← Real.exp_add,add_comm]
  exact source_rough_divisors_card_le_exp_two_sqrt L hL n hn hExpBound
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## RoughCoreSup -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Both genuine cofactor and prime slots are counted among the rough
divisors of the original ordinary part. This is a pointwise sup budget,
not a cancellation claim. All characters and both Mellin phases remain. -/
theorem b656_prime_core_norm_le_rough_divisor_square434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (W A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (ha : ∀ m, ‖F.alpha m‖≤A) (hc : ∀ r, ‖F.residual r‖≤C)
    (hrough : ∀ m, F.alpha m≠0 → rough W m) (hlo : W<(F.lo:ℝ)) (n : ℕ) :
    ‖primeSlotCoreValue P F n‖ ≤ A*C*
      (((sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n).divisors.filter
        (fun d => rough W d)).card:ℝ)^2 := by
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n
  let R := ns.divisors.filter (fun d => rough W d)
  let T : ℕ → ℕ → ℂ := fun m p =>
    if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
      F.alpha m*F.character m*imaginaryPower m F.sigma₀*
        imaginaryPower p F.sigma₁*F.residual (ns/m/p) else 0
  have hpr (p : ℕ) (hg : p.Prime ∧ p∈Finset.Icc F.lo F.hi) : rough W p := by
    refine ⟨hg.1.pos,?_⟩
    intro l hl hld
    have he : l=p := (Nat.dvd_prime hg.1).mp hld |>.resolve_left hl.ne_one
    subst l
    exact hlo.trans_le (Nat.cast_le.mpr (Finset.mem_Icc.mp hg.2).1)
  have hz (m p : ℕ) (hp : p∈ns.divisors) (hnot : p∉R) : T m p=0 := by
    by_cases hg : p.Prime ∧ p∈Finset.Icc F.lo F.hi
    · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hp,hpr p hg⟩))
    · simp only [T,hg,ite_false]
  have ht (m : ℕ) (hm : m∈ns.divisors) (p : ℕ) (hp : p∈ns.divisors) :
      ‖T m p‖≤A*C := by
    by_cases hg : p.Prime ∧ p∈Finset.Icc F.lo F.hi
    · dsimp only [T]
      rw [ite_eq_left hg]
      simp only [norm_mul,
        b656_imaginary_power_norm434 m (Nat.pos_of_mem_divisors hm),
        b656_imaginary_power_norm434 p (Nat.pos_of_mem_divisors hp),mul_one]
      have hchar : ‖F.character m‖≤1 := F.character.norm_le_one (m:ZMod F.q)
      calc
        _ ≤ (A*1)*C := mul_le_mul (mul_le_mul (ha m) hchar (norm_nonneg _) hA)
          (hc _) (norm_nonneg _) (mul_nonneg hA zero_le_one)
        _ = _ := by rw [mul_one]
    · simp only [T,hg,ite_false,norm_zero]
      exact mul_nonneg hA hC
  have hin (m : ℕ) (hm : m∈ns.divisors) :
      ‖∑ p∈(ns/m).divisors, T m p‖ ≤
        if rough W m then (R.card:ℝ)*(A*C) else 0 := by
    by_cases hr : rough W m
    · rw [ite_eq_left hr]
      have hd : (ns/m).divisors⊆ns.divisors := by
        intro p hp
        exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hp).1.trans
          ⟨m,(Nat.div_mul_cancel (Nat.mem_divisors.mp hm).1).symm⟩,
          (Nat.mem_divisors.mp hm).2⟩
      calc
        _ ≤ ∑ p∈(ns/m).divisors, ‖T m p‖ := norm_sum_le _ _
        _ ≤ ∑ p∈ns.divisors, ‖T m p‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hd (fun p _ _ => norm_nonneg _)
        _ = ∑ p∈R, ‖T m p‖ := by
          symm
          exact Finset.sum_subset (Finset.filter_subset _ _) (fun p hp hnot => by
            rw [hz m p hp hnot,norm_zero])
        _ ≤ ∑ _p∈R, A*C := Finset.sum_le_sum (fun p hp => ht m hm p (Finset.mem_filter.mp hp).1)
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    · have ha0 : F.alpha m=0 := by by_contra hne; exact hr (hrough m hne)
      simp only [hr,ite_false,T,ha0,zero_mul,ite_self,Finset.sum_const_zero,norm_zero,le_refl]
  change ‖∑ m∈ns.divisors, ∑ p∈(ns/m).divisors, T m p‖≤_
  calc
    _ ≤ ∑ m∈ns.divisors, (if rough W m then (R.card:ℝ)*(A*C) else 0) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => hin m hm))
    _ = ∑ _m∈R, (R.card:ℝ)*(A*C) := by rw [Finset.sum_filter]
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; dsimp only [R]; ring
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## RoughAlphaCoreSup -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact logarithmic bound for the number of distinct genuine prime
slots dividing n. Repetitions in n only strengthen the log budget. -/
theorem b656_prime_factors_card_log434 (n : ℕ) (hn : n≠0) :
    (n.primeFactors.card:ℝ) ≤ Real.log (n:ℝ)/Real.log 2 := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog2).mpr
  calc
    _ = ∑ _p∈n.primeFactors, Real.log 2 := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ ∑ p∈n.primeFactors, (n.factorization p:ℝ)*Real.log (p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hp2 : (2:ℝ)≤p := by exact_mod_cast hpr.two_le
      have hfac : (1:ℝ)≤n.factorization p := by
        exact_mod_cast hpr.factorization_pos_of_dvd hn (Nat.mem_primeFactors.mp hp).2.1
      have hlogp : Real.log 2≤Real.log (p:ℝ) := Real.log_le_log (by norm_num) hp2
      exact hlogp.trans (le_mul_of_one_le_left (hlog2.le.trans hlogp) hfac)
    _ = Real.log (n:ℝ) := by
      symm
      simpa only [Finsupp.sum,Nat.support_factorization] using Real.log_nat_eq_sum_factorization n

/-- The source cofactor alpha is rough. The distinguished prime need
NOT lie above exp(sqrt L): it remains the actual moving Q slot. -/
theorem b656_prime_core_norm_le_rough_alpha_times_prime_count434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (W A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (ha : ∀ m, ‖F.alpha m‖≤A) (hc : ∀ r, ‖F.residual r‖≤C)
    (hrough : ∀ m, F.alpha m≠0 → rough W m) (n : ℕ) :
    ‖primeSlotCoreValue P F n‖ ≤ A*C*
      (((sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n).divisors.filter
        (fun d => rough W d)).card:ℝ) *
      ((sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n).primeFactors.card:ℝ) := by
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n
  let R := ns.divisors.filter (fun d => rough W d)
  let Q := ns.primeFactors
  let T : ℕ → ℕ → ℂ := fun m p =>
    if p.Prime ∧ p∈Finset.Icc F.lo F.hi then
      F.alpha m*F.character m*imaginaryPower m F.sigma₀*
        imaginaryPower p F.sigma₁*F.residual (ns/m/p) else 0
  have hz (m p : ℕ) (hp : p∈ns.divisors) (hnot : p∉Q) : T m p=0 := by
    by_cases hg : p.Prime ∧ p∈Finset.Icc F.lo F.hi
    · exact False.elim (hnot (Nat.mem_primeFactors.mpr
        ⟨hg.1,(Nat.mem_divisors.mp hp).1,(Nat.mem_divisors.mp hp).2⟩))
    · simp only [T,hg,ite_false]
  have ht (m : ℕ) (hm : m∈ns.divisors) (p : ℕ) (hp : p∈ns.divisors) :
      ‖T m p‖≤A*C := by
    by_cases hg : p.Prime ∧ p∈Finset.Icc F.lo F.hi
    · dsimp only [T]
      rw [ite_eq_left hg]
      simp only [norm_mul,
        b656_imaginary_power_norm434 m (Nat.pos_of_mem_divisors hm),
        b656_imaginary_power_norm434 p (Nat.pos_of_mem_divisors hp),mul_one]
      have hchar : ‖F.character m‖≤1 := F.character.norm_le_one (m:ZMod F.q)
      calc
        _ ≤ (A*1)*C := mul_le_mul (mul_le_mul (ha m) hchar (norm_nonneg _) hA)
          (hc _) (norm_nonneg _) (mul_nonneg hA zero_le_one)
        _ = _ := by rw [mul_one]
    · simp only [T,hg,ite_false,norm_zero]
      exact mul_nonneg hA hC
  have hin (m : ℕ) (hm : m∈ns.divisors) :
      ‖∑ p∈(ns/m).divisors, T m p‖ ≤
        if rough W m then (Q.card:ℝ)*(A*C) else 0 := by
    by_cases hr : rough W m
    · rw [ite_eq_left hr]
      have hd : (ns/m).divisors⊆ns.divisors := by
        intro p hp
        exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hp).1.trans
          ⟨m,(Nat.div_mul_cancel (Nat.mem_divisors.mp hm).1).symm⟩,
          (Nat.mem_divisors.mp hm).2⟩
      calc
        _ ≤ ∑ p∈(ns/m).divisors, ‖T m p‖ := norm_sum_le _ _
        _ ≤ ∑ p∈ns.divisors, ‖T m p‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hd (fun p _ _ => norm_nonneg _)
        _ = ∑ p∈Q, ‖T m p‖ := by
          symm
          exact Finset.sum_subset (by
            intro p hp
            exact Nat.mem_divisors.mpr ⟨(Nat.mem_primeFactors.mp hp).2.1,(Nat.mem_primeFactors.mp hp).2.2⟩) (fun p hp hnot => by
            rw [hz m p hp hnot,norm_zero])
        _ ≤ ∑ _p∈Q, A*C := Finset.sum_le_sum (fun p hp => ht m hm p
          (Nat.mem_divisors.mpr ⟨(Nat.mem_primeFactors.mp hp).2.1,(Nat.mem_primeFactors.mp hp).2.2⟩))
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    · have ha0 : F.alpha m=0 := by by_contra hne; exact hr (hrough m hne)
      simp only [hr,ite_false,T,ha0,zero_mul,ite_self,Finset.sum_const_zero,norm_zero,le_refl]
  change ‖∑ m∈ns.divisors, ∑ p∈(ns/m).divisors, T m p‖≤_
  calc
    _ ≤ ∑ m∈ns.divisors, (if rough W m then (Q.card:ℝ)*(A*C) else 0) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun m hm => hin m hm))
    _ = ∑ _m∈R, (Q.card:ℝ)*(A*C) := by rw [Finset.sum_filter]
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; dsimp only [R,Q]; ring
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## UniformCoreSup -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Quantitative exp(5 sqrt L) bound for the TRUE prime-slot core:
only alpha is exp(sqrt L)-rough; the distinguished prime ranges over
its full original moving band, including bands reaching L^20. -/
theorem b656_actual_range_prime_core_sup434
    {G : Type} [Fintype G] (P : G → Finset ℕ) (F : PrimeSlotCore)
    (L : ℝ) (hL : 1≤L)
    (ha : ∀ m, ‖F.alpha m‖≤1) (hc : ∀ r, ‖F.residual r‖≤1)
    (hrough : ∀ m, F.alpha m≠0 → rough (Real.exp (Real.sqrt L)) m)
    (n : ℕ) (hn : n≠0) (hN : (n:ℝ)≤Real.exp (2*L)) :
    ‖primeSlotCoreValue P F n‖ ≤ Real.exp (5*Real.sqrt L) := by
  let ns := sourceOriginalOrdinaryPart (Finset.univ.biUnion P) n
  have hd : ns∣n := source_ordinary_part_dvd _ n hn
  have hns0 : ns≠0 := by
    intro hz
    exact hn (by simpa only [hz,zero_dvd_iff] using hd)
  have hnsN : (ns:ℝ)≤Real.exp (2*L) :=
    (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)).trans hN
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hhalf : (1/2:ℝ)≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have hs0 := Real.sqrt_nonneg L
  have hsq := Real.sq_sqrt (zero_le_one.trans hL)
  have hs1 : 1≤Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
  have hsL : Real.sqrt L≤L := by nlinarith
  have hlogns : Real.log (ns:ℝ)≤2*L := by
    have h := Real.log_le_log (show (0:ℝ)<ns by exact_mod_cast Nat.pos_of_ne_zero hns0) hnsN
    simpa only [Real.log_exp] using h
  have hSpos : 0<Real.sqrt L := zero_lt_one.trans_le hs1
  have hR0 := source_rough_divisors_card_le_exp_log
    (Real.exp (Real.sqrt L)) ns hns0 (Real.one_lt_exp_iff.mpr hSpos)
  rw [Real.log_exp] at hR0
  have hdivS : Real.log (ns:ℝ)/Real.sqrt L≤2*Real.sqrt L := by
    apply (div_le_iff₀ hSpos).mpr
    nlinarith
  have hR := hR0.trans (Real.exp_le_exp.mpr hdivS)
  have hlogdiv : Real.log (ns:ℝ)/Real.log 2≤4*L := by
    apply (div_le_iff₀ hlog2).mpr
    nlinarith
  have hexp : 4*L≤Real.exp (3*Real.sqrt L) := by
    have hh := Real.quadratic_le_exp_of_nonneg (show 0≤3*Real.sqrt L by positivity)
    nlinarith
  have hPrime : (ns.primeFactors.card:ℝ)≤Real.exp (3*Real.sqrt L) :=
    (b656_prime_factors_card_log434 ns hns0).trans (hlogdiv.trans hexp)
  have hc0 := b656_prime_core_norm_le_rough_alpha_times_prime_count434
    P F (Real.exp (Real.sqrt L)) 1 1 zero_le_one zero_le_one ha hc hrough n
  simp only [one_mul] at hc0
  calc
    _ ≤ (((ns.divisors.filter (fun d => rough (Real.exp (Real.sqrt L)) d)).card:ℝ) *
        (ns.primeFactors.card:ℝ)) := hc0
    _ ≤ Real.exp (2*Real.sqrt L)*Real.exp (3*Real.sqrt L) :=
      mul_le_mul hR hPrime (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

/-- Every fixed multiple of the original exp L range (plus the literal
shift buffer 2) lies in the quantitative sup range eventually. -/
theorem b656_eventually_physical_position_range434 (Cpos : ℝ) :
    ∀ᶠ L : ℝ in atTop, 1≤L ∧
      ∀ n : ℕ, (n:ℝ)≤Cpos*Real.exp L+2 →
        (n:ℝ)≤Real.exp (2*L) := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop (Cpos+1),
    eventually_ge_atTop (1:ℝ)] with L hS hL
  refine ⟨hL,?_⟩
  intro n hn
  have hExp1 : 1≤Real.exp L := Real.one_le_exp (zero_le_one.trans hL)
  have hCexp : Cpos+2≤Real.exp (Real.sqrt L) := by
    linarith [Real.add_one_le_exp (Real.sqrt L)]
  calc
    _ ≤ Cpos*Real.exp L+2 := hn
    _ ≤ (Cpos+2)*Real.exp L := by nlinarith
    _ ≤ Real.exp (Real.sqrt L)*Real.exp L :=
      mul_le_mul_of_nonneg_right hCexp (Real.exp_pos L).le
    _ = Real.exp (L+Real.sqrt L) := by rw [←Real.exp_add,add_comm]
    _ ≤ Real.exp (2*L) := by
      apply Real.exp_le_exp.mpr
      have hs1 : 1≤Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL
      have hsq := Real.sq_sqrt (zero_le_one.trans hL)
      nlinarith
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualParityArithmeticBounds -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.ShiftTwoTerminal Green64Analytic.SourceBlockSieve
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14000000

/-- Unconditional arithmetic input estimates for the TWO original Parity
endpoint cores with the actual canonical prime/rough fine alpha and the
same true sorted-Q residual. Both exp(5 sqrt L) sup bounds and the
removed-mark tau(n/D)^2 bounds are conclusions. Character/frequency,
allocation, moving depth and every original prime-slot endpoint remain.
There is no coefficient, residual, sup, norm, RMS or error hypothesis. -/
theorem b656_actual_parity_arithmetic_bounds434
    (S beta gamma : ℝ) (hS : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r d : ℕ), 1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ {G : Type} [Fintype G] (P : G → Finset ℕ) (n : ℕ), 0<n →
          (n:ℝ)≤Real.exp (2*L) →
          ‖primeSlotCoreValue P E n‖≤Real.exp (5*Real.sqrt L) ∧
          ‖primeSlotCoreValue P H n‖≤Real.exp (5*Real.sqrt L) ∧
          ∀ D : ℕ, D≠0 → D∣n → D.primeFactors⊆Finset.univ.biUnion P →
            ‖primeSlotCoreValue P E n‖≤((n/D).divisors.card:ℝ)^2 ∧
            ‖primeSlotCoreValue P H n‖≤((n/D).divisors.card:ℝ)^2 := by
  filter_upwards [b656_actual_fine_native_and_parity_inputs434 S beta gamma hS hbeta hgamma]
    with L hinputs
  intro prime l u hlow r d hr b slot δ ξ K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma G _ P n hn hN
  let F := sourceNativePrimeCore r d L b slot δ ξ K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let H := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hh := (hinputs.2 prime l u hlow r d hr b slot δ ξ K q chi s0 s1).2 xi1 xi2 rho sigma
  have he : B656UnitRoughPrimeCore434 L E := hh.1
  have hg : B656UnitRoughPrimeCore434 L H := hh.2
  refine ⟨b656_actual_range_prime_core_sup434 P E L hinputs.1
      he.1 he.2.1 he.2.2 n (Nat.ne_of_gt hn) hN,
    b656_actual_range_prime_core_sup434 P H L hinputs.1
      hg.1 hg.2.1 hg.2.2 n (Nat.ne_of_gt hn) hN,?_⟩
  intro D hD hdiv hP
  constructor
  · simpa only [one_mul] using b656_prime_core_removed_marks_bound434
      P E 1 1 zero_le_one zero_le_one he.1 he.2.1 n D (Nat.ne_of_gt hn) hD hdiv hP
  · simpa only [one_mul] using b656_prime_core_removed_marks_bound434
      P H 1 1 zero_le_one zero_le_one hg.1 hg.2.1 n D (Nat.ne_of_gt hn) hD hdiv hP
end Green64Analytic.Parity

end

end

