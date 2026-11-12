module

public import Green64.Library.Weights.RawSharedRestoration
public import Green64.Library.Weights.Part113
public import Green64.Library.Weights.Part114
public import Green64.Library.Weights.RawSharedCarrier
public import Green64.Library.Weights.Part112
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part033
public import Green64.Library.Correlation.Part072

@[expose] public section

/-!
# Weights / Part115

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## RawSharedPower -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 22000

/-- The literal RAW defect has J shared slots per complete group and no
auxiliary labels. Its constant vanishes for J=0. -/
def parityRawSharedDefectConstant434 (J : ℕ) : ℝ :=
  (8*(J : ℝ))*(4/Real.log 2)+(8*(J : ℝ))^2

theorem parity_raw_shared_defect_constant_nonneg434 (J : ℕ) :
    0 ≤ parityRawSharedDefectConstant434 J := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold parityRawSharedDefectConstant434
  positivity

/-- The complete original RAW shared-label collision count, without a
comparison probe or any auxiliary term. -/
theorem parity_actual_raw_shared_defect_numerator434
    (L : ℝ) (hL : Real.exp 2 ≤ L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J w wp : ℕ)
    (hw : (w.log2 : ℝ) ≤ 2*L/Real.log 2)
    (hwp : (wp.log2 : ℝ) ≤ 2*L/Real.log 2) :
    let I := (g : B645ActualGroup434 L hS) × parityRawSharedSlots434 J
    (Fintype.card I : ℝ)*((w.log2 : ℝ)+(wp.log2 : ℝ))+
      (Fintype.card I : ℝ)^2 ≤ parityRawSharedDefectConstant434 J*L^2 := by
  let G := B645ActualGroup434 L hS
  let I := (g : G) × parityRawSharedSlots434 J
  have hL0 : 0 < L := (Real.exp_pos _).trans_le hL
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hG : (Fintype.card G : ℝ) ≤ 8*L :=
    (parity_actual_full_group_card_eight434 L hL hS).trans (by gcongr)
  have hI : (Fintype.card I : ℝ)=(J : ℝ)*(Fintype.card G : ℝ) := by
    exact_mod_cast parity_raw_shared_index_card434 (G:=G) J
  have hIC : (Fintype.card I : ℝ) ≤ 8*(J : ℝ)*L := by
    rw [hI]
    calc
      _ ≤ (J : ℝ)*(8*L) := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = _ := by ring
  change (Fintype.card I : ℝ)*((w.log2 : ℝ)+(wp.log2 : ℝ))+
    (Fintype.card I : ℝ)^2 ≤ _
  calc
    _ ≤ (8*(J : ℝ)*L)*(2*L/Real.log 2+2*L/Real.log 2)+
        (8*(J : ℝ)*L)^2 := by gcongr
    _ = parityRawSharedDefectConstant434 J*L^2 := by
      unfold parityRawSharedDefectConstant434
      ring

/-- Direct specialization of the actual full marked-weight theorem to
one free mark in every SMALL and BIG group. No comparison pattern or kernel
is introduced. The exponent is fixed before L and before all endpoints. -/
theorem parity_eventually_actual_raw_marked_log_budget434 :
    ∃ Em : ℝ,0 ≤ Em ∧
    ∀ᶠ L : ℝ in atTop,1 < L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (n : ℕ),
        ‖actualBigMarkDecoration (b645ActualBand434 L hS) (fun _ => 1) (1/2)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (fun _ => 1) n‖ ≤ L^Em := by
  have hv : 0 < Real.log (6/5 : ℝ)/2 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨Em,hEm,hUniform⟩ := source_marked_weight_log_power
    (1/2) (Real.log (6/5 : ℝ)/2) 8 1
    (by norm_num) (by norm_num) hv (by norm_num)
  refine ⟨Em,hEm,?_⟩
  filter_upwards [parity_eventually_actual_full_mass_floor434,
    parity_eventually_actual_restoration_group_budget434] with L hMass hBudget
  refine ⟨hMass.1,hMass.2.1,?_⟩
  intro hS n
  exact hUniform L hMass.1.le (b645ActualBand434 L hS) (fun _ => 1)
    (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
    (fun _ => 1) (hBudget.2 hS).1 (fun _ => le_rfl)
    (fun g => (hMass.2.2 hS g).1) (fun _ => by simp) n

/-- Genuine r20 quantitative restoration for the literal RAW K=1 slice.
All marked, prime, mass and damping bounds are discharged internally. Both
original endpoint divisor exclusions and every labelled shared draw remain. -/
theorem parity_eventually_actual_raw_shared_power434 (J : ℕ) :
    ∃ Em : ℝ,0 ≤ Em ∧
    ∀ᶠ L : ℝ in atTop,Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (Y w wp : ℕ),
        0 < w → w ≤ Y → 0 < wp → wp ≤ Y → Real.log (Y : ℝ) ≤ 2*L →
        ‖parityRawRestoredSlice434 J (b645ActualBand434 L hS)
            (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
            (1/2) w wp-
          parityRawStrippedSlice434 (b645ActualBand434 L hS)
            (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
            (1/2) w wp‖ ≤
          (2*parityRawSharedDefectConstant434 J/(Real.log (6/5 : ℝ)/2))*
            L^(8*(J+1 : ℝ)*Real.log 2+2*Em+2)*Real.exp (-(L^(1/10 : ℝ))) := by
  obtain ⟨Em,hEm,hM⟩ := parity_eventually_actual_raw_marked_log_budget434
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hM,parity_eventually_actual_raw_shared_restoration434,
    eventually_ge_atTop (Real.exp 2)] with L hMark hRest hL
  refine ⟨hL,hMark.2.1,?_⟩
  intro hS Y w wp hw hwY hwp hwpY hLog
  let D : ℝ := 8*(J+1 : ℝ)*Real.log 2
  let C := parityRawSharedDefectConstant434 J
  let v : ℝ := Real.log (6/5 : ℝ)/2
  have hv : 0 < v := source_actual_P_uniform_mass_floor_positive
  have hC : 0 ≤ C := parity_raw_shared_defect_constant_nonneg434 J
  have hL0 : 0 < L := (Real.exp_pos _).trans_le hL
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hL
  have hD : 0 ≤ D := by
    have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [D]
    positivity
  have hOne : 1 ≤ L^D := Real.one_le_rpow hL1.le hD
  have hdamp := parity_actual_full_damping_tight_budget434 L hL hS J
  have hd : (1/2 : ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS) : ℝ))+1 ≤ 2*L^D := by
    change (1/2 : ℝ)^(-2*((J+1)*Fintype.card (B645ActualGroup434 L hS) : ℝ)) ≤ L^D at hdamp
    linarith
  have hnum := parity_actual_raw_shared_defect_numerator434 L hL hS J w wp
    (parity_log2_of_positive_cap434 L w Y hw hwY hLog)
    (parity_log2_of_positive_cap434 L wp Y hwp hwpY hLog)
  have hpowers : L^D*L^Em*L^Em*L^2=L^(D+2*Em+2) := by
    simp only [two_mul,Real.rpow_add hL0,Real.rpow_two]
    ring
  have he := hRest.2.2 hS J w wp hw hwp
  dsimp only at he hnum
  refine he.trans ?_
  calc
    _ ≤ (2*L^D)*(L^Em)*(L^Em)*(C*L^2/(Real.exp (L^(1/10 : ℝ))*v)) := by
      gcongr
      · exact hMark.2.2 hS w
      · exact hMark.2.2 hS wp
    _ = (2*C/v)*(L^D*L^Em*L^Em*L^2)*(Real.exp (L^(1/10 : ℝ)))⁻¹ := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [hpowers,Real.exp_neg]

/-- With zero shared slots the genuine RAW defect is exactly zero.
This is a literal RAW statement, not a canonical empty-comparison identity. -/
theorem parity_eventually_actual_raw_shared_zero434 :
    ∀ᶠ L : ℝ in atTop,1 < L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (w wp : ℕ),
        0 < w → 0 < wp →
        parityRawRestoredSlice434 0 (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) w wp=
        parityRawStrippedSlice434 (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) w wp := by
  filter_upwards [parity_eventually_actual_raw_shared_restoration434] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro hS w wp hw hwp
  have he := h.2.2 hS 0 w wp hw hwp
  dsimp only at he
  simp only [parity_raw_shared_index_card434,zero_mul,Nat.cast_zero,zero_add,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_div,mul_zero] at he
  exact sub_eq_zero.mp (norm_le_zero_iff.mp he)
end Green64Analytic.Parity

end

end

/-! ## RawSourceChannel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Independent stripped RAW harmonic functional: the signed 2*k guard,
both complete one-free-slot marked lists and original endpoint arithmetic
are retained. A supplied weight acts at the STRIPPED endpoints w,wp.
This definition makes no equality claim about the physical shared sum or
its caps at DR*w,DR*wp; their quantitative restoration is separate. -/
def parityRawStrippedHarmonic434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ→ℂ) (Wgt : ℕ→ℕ→ℂ) : ℂ :=
  ∑ w∈N,∑ wp∈N,
    if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
      Wgt w wp *
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
          (-(rho+xi3)) (-rho) tw psi 1 w wp *
        parityRawStrippedSlice434 (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2 : ℝ) w wp
    else 0

/-- Balanced native phases and common valuation parity give the original
source arithmetic kernel. The kernel keeps the ordinary-part divisor
expansion, original prime/interval gates and harmonic inverse. -/
theorem parity_raw_stripped_original_arithmetic434
    (L rho xi3 Z : ℝ) (F G : PrimeSlotCore) (tw : Bool)
    (psi : ℝ→ℂ) (w wp : ℕ) :
    parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp =
      psi ((w : ℝ)/Z)/(w : ℂ) *
        imaginaryPower w (rho+xi3)*imaginaryPower wp (-rho)*
        star (primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F w)*
        primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G wp *
        ((groupSign (sourceOriginalPAllActualBands 20 L) tw w*
          groupSign (sourceOriginalPAllActualBands 20 L) tw wp : ℝ) : ℂ) := by
  have hstar (x : ℝ) : star (x : ℂ)=(x : ℂ) := by simp
  unfold parityHarmonicStrippedArithmetic434 parityHarmonicSourceArithmetic434
    parityHarmonicEndpointArithmetic434 sourceOriginalPureMellinPhase434
  simp only [Nat.cast_one,mul_one,Complex.ofReal_zero,mul_zero,
    Complex.cpow_zero,Real.log_one,Complex.exp_zero,star_mul,hstar]
  rw [←b633_imaginary_power_conjugate434]
  simp only [neg_neg]
  push_cast
  ring

/-- Exact finite signed-shift collapse on any positive carrier. No target
cardinality or extra normalization appears, and both signs of k survive. -/
theorem parity_raw_positive_pair_collapse434
    (N : Finset ℕ) (hN : ∀ n∈N,0<n) (k : ℤ) (hk : k≠0)
    (A : ℕ→ℕ→ℂ) :
    (∑ w∈N,∑ wp∈N,if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then A w wp else 0) =
      ∑ w∈N,if 0<(w : ℤ)+2*k ∧ ((w : ℤ)+2*k).toNat∈N
        then A w ((w : ℤ)+2*k).toNat else 0 := by
  have h2 : (2*k)≠0 := mul_ne_zero (by norm_num) hk
  apply Finset.sum_congr rfl
  intro w hw
  let t := ((w : ℤ)+2*k).toNat
  by_cases hs : 0<(w : ℤ)+2*k
  · have hcast : (t : ℤ)=(w : ℤ)+2*k := Int.toNat_of_nonneg hs.le
    have heq (wp : ℕ) : (wp : ℤ)=(w : ℤ)+2*k ↔ wp=t := by
      rw [←hcast]
      exact Nat.cast_inj
    have hrow (wp : ℕ) :
        (if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then A w wp else 0) =
        if wp=t then A w t else 0 := by
      by_cases ht : wp=t
      · subst wp
        rw [if_pos ⟨h2,hcast⟩,if_pos rfl]
      · rw [if_neg (fun hh=>ht ((heq wp).mp hh.2)),if_neg ht]
    simp_rw [hrow]
    simp [hs,t]
  · have hzero : (∑ wp∈N,if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then A w wp else 0)=0 := by
      apply Finset.sum_eq_zero
      intro wp hwp
      have hwp0 : (0 : ℤ)<wp := by exact_mod_cast hN wp hwp
      have hn : ¬((2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k) := by
        intro hh
        exact hs (hh.2 ▸ hwp0)
      rw [if_neg hn]
    rw [hzero]
    simp only [hs,false_and,ite_false]

/-- The exact one-position original B521 channel term. BOTH original
Ppart caps are explicitly inserted at the stripped endpoint positions.
This does not assert their equality with the physical DR-dependent caps. -/
theorem parity_raw_stripped_original_B521_term434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (k : ℤ) (F G : PrimeSlotCore) (tw : Bool)
    (psi : ℝ→ℂ) (w : ℕ) (hs : 0<(w : ℤ)+2*k) :
    let wp := ((w : ℤ)+2*k).toNat
    parityOriginalPhysicalPairPcap434 L w wp *
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp *
      parityRawStrippedSlice434 (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (1/2 : ℝ) w wp =
      sourceNativeGatedGramKernel (sourceOriginalPAllActualBands 20 L)
        (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
        F G k (rho+xi3) (-rho) (fun n=>psi ((n : ℝ)/Z)/(n : ℂ)) w *
        ((groupSign (sourceOriginalPAllActualBands 20 L) tw w*
          groupSign (sourceOriginalPAllActualBands 20 L) tw wp : ℝ) : ℂ) := by
  dsimp only
  rw [parity_raw_stripped_original_arithmetic434,parity_actual_raw_stripped_source_weight434 L hL hS,
    parity_actual_B521_gate_factor434,if_pos hs]
  ring

/-- Genuine exact correspondence of the independently defined finite
stripped RAW construction with the original r20 B521 gated channel.
The target-carrier indicator is still explicit; later actual support
geometry removes it. No whole physical-channel equality or cap loss is
assumed, and the source caps are the literal floor(exp(L/44)) gates. -/
theorem parity_raw_stripped_original_B521_channel434
    (L : ℝ) (hL : 1<L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (k : ℤ) (hk : k≠0)
    (N : Finset ℕ) (hN : ∀ n∈N,0<n) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ→ℂ) :
    parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi
        (parityOriginalPhysicalPairPcap434 L) =
      sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
        (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
        F G k (rho+xi3) (-rho)
        (fun n=>if ((n : ℤ)+2*k).toNat∈N then psi ((n : ℝ)/Z)/(n : ℂ) else 0)
        tw tw := by
  unfold parityRawStrippedHarmonic434 sourceNativeGatedChannel
  rw [parity_raw_positive_pair_collapse434 N hN k hk]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hs : 0<(w : ℤ)+2*k
  · by_cases ht : ((w : ℤ)+2*k).toNat∈N
    · simp only [hs,ht,and_self,ite_true]
      simpa only [sourceNativeGatedGramKernel,ht,ite_true] using
        parity_raw_stripped_original_B521_term434 L hL hS rho xi3 Z k F G tw psi w hs
    · simp only [hs,ht,and_false,ite_false]
      simp only [sourceNativeGatedGramKernel,ht,ite_false,zero_mul,ite_self]
  · simp only [hs,false_and,ite_false]
    simp only [sourceNativeGatedGramKernel,hs,false_and,ite_false,zero_mul]
end Green64Analytic.Parity

end

end

/-! ## RawSharedHarmonic -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 26000

/-- Literal absolute harmonic error of genuine RAW shared restoration.
Both divisor-square factors and the complete signed shift are retained. -/
def parityRawSharedHarmonicEnvelope434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J : ℕ) (X : ℝ) (s : ℤ) (psi : ℝ → ℂ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 M,
    ‖psi ((n : ℝ)/X)‖/(n : ℝ)*(n.divisors.card : ℝ)^2*
      (((n : ℤ)+s).toNat.divisors.card : ℝ)^2*
      ‖parityRawRestoredSlice434 J (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) n ((n : ℤ)+s).toNat-
        parityRawStrippedSlice434 (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) n ((n : ℤ)+s).toNat‖

/-- The actual RAW pointwise restoration and genuine harmonic fourth-moment
estimate give a complete polynomial-exponential error, uniform in the
original finite endpoint cap M. No Q, cell mass or auxiliary factor occurs. -/
theorem parity_eventually_actual_raw_shared_harmonic434 (J : ℕ) :
    ∃ Em : ℝ,0 ≤ Em ∧
    ∀ᶠ L : ℝ in atTop,Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
        (X K Cpsi : ℝ) (s : ℤ) (psi : ℝ → ℂ) (M : ℕ),
        1 ≤ X → 0 ≤ K → |(s : ℝ)| ≤ X/128 → Real.log (⌈65*X⌉₊ : ℝ) ≤ 2*L →
        (∀ t,psi t ≠ 0 → t ∈ Set.Icc (1/64 : ℝ) 64) →
        (∀ t,‖psi t‖ ≤ K*L^Cpsi) →
        parityRawSharedHarmonicEnvelope434 L hS J X s psi M ≤
          (2*parityRawSharedDefectConstant434 J/(Real.log (6/5 : ℝ)/2))*
            (64*66*(3 : ℝ)^15)*K*
            L^(8*(J+1 : ℝ)*Real.log 2+2*Em+17+Cpsi)*Real.exp (-(L^(1/10 : ℝ))) := by
  obtain ⟨Em,hEm,hR⟩ := parity_eventually_actual_raw_shared_power434 J
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hR] with L hRest
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro hS X K Cpsi s psi M hX hK hs hLog hSupp hPsi
  have hL1 : 1 < L := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hRest.1
  have hLp : 0 < L := by linarith
  have hXp : 0 < X := by linarith
  let Y := ⌈65*X⌉₊
  let C : ℝ := 2*parityRawSharedDefectConstant434 J/(Real.log (6/5 : ℝ)/2)
  let D : ℝ := 8*(J+1 : ℝ)*Real.log 2
  let B : ℝ := C*L^(D+2*Em+2)*Real.exp (-(L^(1/10 : ℝ)))
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (by norm_num) (parity_raw_shared_defect_constant_nonneg434 J))
    source_actual_P_uniform_mass_floor_positive.le
  have hB : 0 ≤ B := by dsimp [B];positivity
  let err := fun w wp =>
    parityRawRestoredSlice434 J (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2) w wp-
    parityRawStrippedSlice434 (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2) w wp
  have hpoint (n : ℕ) (hn : n ∈ Finset.Ioc 0 M) (hp : psi ((n : ℝ)/X) ≠ 0) :
      ‖err n ((n : ℤ)+s).toNat‖ ≤ B := by
    have hg := parity_harmonic_cutoff_shift_support434 X hXp s hs psi hSupp n hp
    have hnp : 0 < ((n : ℤ)+s).toNat := by omega
    have hnpy : ((n : ℤ)+s).toNat ≤ Y := by dsimp [Y];omega
    exact hRest.2.2 hS Y n ((n : ℤ)+s).toNat
      (Finset.mem_Ioc.mp hn).1 hg.2.2.1 hnp hnpy hLog
  have henv : parityRawSharedHarmonicEnvelope434 L hS J X s psi M ≤
      B*parityHarmonicDivisorEnvelope434 X s psi M := by
    unfold parityRawSharedHarmonicEnvelope434 parityHarmonicDivisorEnvelope434
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hp : psi ((n : ℝ)/X)=0
    · simp [hp]
    · calc
        _ ≤ (‖psi ((n : ℝ)/X)‖/(n : ℝ)*(n.divisors.card : ℝ)^2*
            (((n : ℤ)+s).toNat.divisors.card : ℝ)^2)*B :=
          mul_le_mul_of_nonneg_left (hpoint n hn hp) (by positivity)
        _ = _ := by ring
  have hpow : L^(D+2*Em+2)*L^(15+Cpsi)=L^(D+2*Em+17+Cpsi) := by
    rw [←Real.rpow_add hLp]
    congr 1
    ring
  calc
    _ ≤ B*parityHarmonicDivisorEnvelope434 X s psi M := henv
    _ ≤ B*((64*66*(3 : ℝ)^15)*K*L^(15+Cpsi)) :=
      mul_le_mul_of_nonneg_left
        (parity_harmonic_cutoff_divisor_envelope434 L X K Cpsi hL1.le hX hK s hs hLog psi hSupp hPsi M) hB
    _ = C*(64*66*(3 : ℝ)^15)*K*L^(D+2*Em+17+Cpsi)*Real.exp (-(L^(1/10 : ℝ))) := by
      dsimp only [B]
      calc
        _ = C*(64*66*(3 : ℝ)^15)*K*(L^(D+2*Em+2)*L^(15+Cpsi))*Real.exp (-(L^(1/10 : ℝ))) := by ring
        _ = _ := by rw [hpow]

/-- Exact difference of the independently defined restored and stripped
RAW harmonic constructions. A common weight is kept at quotient endpoints;
this identity makes no claim about physical DR-dependent caps. -/
theorem parity_raw_restored_stripped_difference434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ) :
    parityRawRestoredHarmonic434 L hS J rho xi3 Z k N F G tw psi Wgt-
      parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi Wgt =
    ∑ w ∈ N,∑ wp ∈ N,if (2*k) ≠ 0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
      Wgt w wp*parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp*
      (parityRawRestoredSlice434 J (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) w wp-
        parityRawStrippedSlice434 (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (1/2) w wp) else 0 := by
  unfold parityRawRestoredHarmonic434 parityRawStrippedHarmonic434
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wp hwp
  split_ifs <;> ring

/-- Exact signed-shift collapse controls the complete weighted RAW
restoration difference by its harmonic envelope with no target-cardinality
loss. Actual endpoint bounds and scale conditions are discharged next. -/
theorem parity_raw_restored_stripped_envelope434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty) (J : ℕ)
    (rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (M : ℕ) (hN : N ⊆ Finset.Ioc 0 M)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ) (Wgt : ℕ → ℕ → ℂ)
    (hWgt : ∀ w wp,‖Wgt w wp‖ ≤ 1)
    (hF : ∀ n : ℕ,0 < n → ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F n‖ ≤ (n.divisors.card : ℝ)^2)
    (hG : ∀ n : ℕ,0 < n → ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G n‖ ≤ (n.divisors.card : ℝ)^2) :
    ‖parityRawRestoredHarmonic434 L hS J rho xi3 Z k N F G tw psi Wgt-
      parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi Wgt‖ ≤
      parityRawSharedHarmonicEnvelope434 L hS J Z (2*k) psi M := by
  let aa := fun w wp => Wgt w wp*parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
    (-(rho+xi3)) (-rho) tw psi 1 w wp
  let ee := fun w wp =>
    parityRawRestoredSlice434 J (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2) w wp-
    parityRawStrippedSlice434 (b645ActualBand434 L hS)
      (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
      (1/2) w wp
  let bb := fun (w : ℕ) => ‖psi ((w : ℝ)/Z)‖/(w : ℝ)*(w.divisors.card : ℝ)^2*
    (((w : ℤ)+2*k).toNat.divisors.card : ℝ)^2
  have hb (w : ℕ) : 0 ≤ bb w := by dsimp [bb];positivity
  have ha (w : ℕ) (hw : w ∈ N) (wp : ℕ) (hwp : wp ∈ N)
      (hshift : (wp : ℤ)=(w : ℤ)+2*k) : ‖aa w wp‖ ≤ bb w := by
    have hwpos := (Finset.mem_Ioc.mp (hN hw)).1
    have hwppos := (Finset.mem_Ioc.mp (hN hwp)).1
    have he : wp=((w : ℤ)+2*k).toNat := by
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hshift
    have hPair := mul_le_mul (hF w hwpos) (hG wp hwppos) (norm_nonneg _) (sq_nonneg _)
    have hArith : ‖parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp‖ ≤ bb w := by
      rw [parity_harmonic_stripped_arithmetic_norm434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp hwpos hwppos]
      simp only [Nat.cast_one,mul_one]
      calc
        _ = (w : ℝ)⁻¹*(‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F w‖*
          ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G wp‖)*‖psi ((w : ℝ)/Z)‖ := by ring
        _ ≤ (w : ℝ)⁻¹*((w.divisors.card : ℝ)^2*(wp.divisors.card : ℝ)^2)*‖psi ((w : ℝ)/Z)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPair (by positivity)) (norm_nonneg _)
        _ = bb w := by dsimp [bb];rw [he];ring
    dsimp only [aa]
    rw [norm_mul]
    exact (mul_le_mul (hWgt w wp) hArith (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [parity_raw_restored_stripped_difference434]
  exact parity_finite_weighted_restoration_envelope434 N M hN (2*k) ((2*k) ≠ 0) aa ee bb hb ha
end Green64Analytic.Parity

end

end

/-! ## ActualRawRestoration -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 28000

/-- Actual B633 endpoint bounds and the true harmonic scale geometry
remove every analytic premise from the weighted RAW restoration estimate.
The finite carrier is any positive set: its size costs nothing because the
original cutoff controls the harmonic fourth-moment envelope. -/
theorem parity_eventually_actual_raw_restoration_error434
    (J : ℕ) (S beta gamma CZ Ck : ℝ)
    (hSfine : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma) (hCZ : 0 ≤ CZ) :
    ∃ Em : ℝ,0 ≤ Em ∧
    ∀ᶠ L : ℝ in atTop,Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ → |(k : ℝ)| ≤ L^Ck →
        ∀ (Kpsi Cpsi : ℝ),0 ≤ Kpsi → ∀ (tw : Bool) (psi : ℝ → ℂ),
          (∀ t,psi t ≠ 0 → t ∈ Set.Icc (1/64 : ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
        ∀ (N : Finset ℕ),(∀ n ∈ N,0 < n) →
        ∀ (Wgt : ℕ → ℕ → ℂ),(∀ w wp,‖Wgt w wp‖ ≤ 1) →
          ‖parityRawRestoredHarmonic434 L hS J rho xi3 Z k N E G tw psi Wgt-
            parityRawStrippedHarmonic434 L hS rho xi3 Z k N E G tw psi Wgt‖ ≤
            (2*parityRawSharedDefectConstant434 J/(Real.log (6/5 : ℝ)/2))*
              (64*66*(3 : ℝ)^15)*Kpsi*
              L^(8*(J+1 : ℝ)*Real.log 2+2*Em+17+Cpsi)*Real.exp (-(L^(1/10 : ℝ))) := by
  obtain ⟨Em,hEm,hRest⟩ := parity_eventually_actual_raw_shared_harmonic434 J
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hRest,
    parity_eventually_actual_B633_core_tau434 S beta gamma hSfine hbeta hgamma,
    parity_eventually_harmonic_scale_budget434 CZ Ck hCZ] with L hRest hCore hGeom
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk Kpsi Cpsi hK tw psi hSupp hPsi N hNpos Wgt hWgt
  let F := sourceNativePrimeCore r d L b slot δ ξ Kset
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let M := N.sup id
  have hN : N ⊆ Finset.Ioc 0 M := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hNpos n hn,Finset.le_sup (f:=id) hn⟩
  have hBoth := hCore.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1 xi1 xi2 rho sigma
  have hFinite := parity_raw_restored_stripped_envelope434 L hS J rho xi3 Z k N M hN
    E G tw psi Wgt hWgt (fun n hn => (hBoth n hn).1) (fun n hn => (hBoth n hn).2)
  have hb := hGeom.2 Z hZlo hZhi 1 (by norm_num)
    (by simpa only [Nat.cast_one] using Real.one_le_exp (Real.sqrt_nonneg L)) k hk
  simp only [Nat.cast_one,Int.cast_one,mul_one] at hb
  have hEnv := hRest.2.2 hS Z Kpsi Cpsi (2*k) psi M hb.1 hK hb.2.1 hb.2.2 hSupp hPsi
  exact hFinite.trans hEnv

/-- Genuine weighted RAW restoration saving. J, cutoff growth, fine
operator precision and requested saving are all fixed before L and before
any actual endpoint/operator tuple or bounded quotient weight. -/
theorem parity_eventually_actual_raw_restoration_saving434
    (J : ℕ) (S beta gamma CZ Ck Cpsi Kpsi A : ℝ)
    (hSfine : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hCZ : 0 ≤ CZ) (hK : 0 ≤ Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ → |(k : ℝ)| ≤ L^Ck →
        ∀ (tw : Bool) (psi : ℝ → ℂ),
          (∀ t,psi t ≠ 0 → t ∈ Set.Icc (1/64 : ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
        ∀ (N : Finset ℕ),(∀ n ∈ N,0 < n) →
        ∀ (Wgt : ℕ → ℕ → ℂ),(∀ w wp,‖Wgt w wp‖ ≤ 1) →
          ‖parityRawRestoredHarmonic434 L hS J rho xi3 Z k N E G tw psi Wgt-
            parityRawStrippedHarmonic434 L hS rho xi3 Z k N E G tw psi Wgt‖ ≤ L^(-A) := by
  obtain ⟨Em,hEm,hRest⟩ := parity_eventually_actual_raw_restoration_error434
    J S beta gamma CZ Ck hSfine hbeta hgamma hCZ
  let K := (2*parityRawSharedDefectConstant434 J/(Real.log (6/5 : ℝ)/2))*(64*66*(3 : ℝ)^15)*Kpsi
  let e := 8*(J+1 : ℝ)*Real.log 2+2*Em+17+Cpsi
  filter_upwards [hRest,eventually_source_fixed_poly_exp_saving
    (1/10 : ℝ) K e A (by norm_num)] with L hRest hSave
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk tw psi hSupp hPsi N hNpos Wgt hWgt
  have hBound := hRest.2.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
    xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk Kpsi Cpsi hK tw psi hSupp hPsi N hNpos Wgt hWgt
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hSave.1
  exact hBound.trans (by simpa only [Real.rpow_neg hLpos.le,one_div] using hSave.2)

/-- Full genuine uncapped physical RAW to independently defined stripped
RAW harmonic restoration. The original physical construction is retained;
its shared reindex is proved and its error is derived. Both unscaled and
one-external-Z bounds are returned, with no comparison or Q/xi loss. -/
theorem parity_eventually_actual_physical_raw_stripping434
    (J : ℕ) (S beta gamma CZ Ck Cpsi Kpsi A : ℝ)
    (hSfine : 0 < S) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hCZ : 0 ≤ CZ) (hK : 0 ≤ Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L) ≤ (l : ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ → (k.natAbs : ℝ) ≤ L^Ck →
        ∀ (tw : Bool) (psi : ℝ → ℂ),
          (∀ t,psi t ≠ 0 → t ∈ Set.Icc (1/64 : ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
          let N := parityPositiveNaturalPositions434
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
          let diff := parityRawHarmonicPhysicalAggregate434 L hS J (-xi3) Z k
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
            1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi (fun _ _ => 1)-
            parityRawStrippedHarmonic434 L hS rho xi3 Z k N E G tw psi (fun _ _ => 1)
          ‖diff‖ ≤ L^(-A) ∧ ‖(Z : ℂ)*diff‖ ≤ Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_raw_restoration_saving434 J S beta gamma CZ Ck Cpsi Kpsi A
    hSfine hbeta hgamma hCZ hK,parity_eventually_raw_harmonic_restored434 J CZ] with L hRest hExact
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk tw psi hSupp hPsi
  let F := sourceNativePrimeCore r d L b slot δ ξ Kset
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  have hLpos : 0 < L := (Real.exp_pos _).trans_le hRest.1
  have hZ : 0 < Z := (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hLpos _)).trans_le hZlo
  have hkReal : |(k : ℝ)| ≤ L^Ck := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hk
  have hNpos : ∀ n ∈ N,0 < n := by
    intro n hn
    exact ((parity_positive_natural_positions_mem434 _ n).mp hn).1
  have hBound := hRest.2.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
    xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hkReal tw psi hSupp hPsi N hNpos
    (fun _ _ => 1) (fun _ _ => by simp)
  have he := hExact.2 hS rho xi3 Ck Z k hk hZ hZhi psi hSupp E G tw
  rw [he]
  refine ⟨hBound,?_⟩
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hZ]
  exact mul_le_mul_of_nonneg_left hBound hZ.le
end Green64Analytic.Parity

end

end

/-! ## RawSourceNormalized -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
open Green64Analytic.CorrelationD Green64Analytic.CorrelationMellin
open Green64Analytic.ShiftTwoTerminal Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 28000

/-- Convert the ORIGINAL physical normalized cutoff t*psi(t), after
division by the positive stripped source endpoint, into exactly one
global factor 1/Z. The exceptional n=0 is discharged by the original
positive support of psi, not by redefining the target carrier. -/
theorem parity_raw_original_normalized_source_coefficient434
    (Z : ℝ) (hZ : 0 < Z) (psi : ℝ → ℂ)
    (hSupport : ∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64)
    (n : ℕ) :
    (((n : ℝ)/Z : ℝ) : ℂ) * psi ((n : ℝ)/Z) / (n : ℂ) =
      (Z : ℂ)⁻¹ * psi ((n : ℝ)/Z) := by
  by_cases hn : n = 0
  · subst n
    have hz : psi 0 = 0 := by
      by_contra hne
      have hbad := (hSupport 0 hne).1
      norm_num at hbad
    simp [hz]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hZC : (Z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hZ)
    push_cast
    field_simp

/-- The exact finite original B521 source channel for the normalized
raw cutoff uses only a single outer 1/Z and the ORIGINAL target
support guard, signed 2*k, original Ppart gates and full r20 marked
weights. This is the STRIPPED identity; physical-to-stripped restoration
is a separate quantitative obligation. -/
theorem parity_raw_stripped_original_B521_normalized434
    (L : ℝ) (hL : 1 < L)
    (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (hZ : 0 < Z) (k : ℤ) (hk : k ≠ 0)
    (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ → ℂ)
    (hSupport : ∀ t : ℝ, psi t ≠ 0 → (1/64 : ℝ) ≤ t ∧ t ≤ 64) :
    parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw
      (fun t => (t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L) =
    sourceNativeGatedChannel N (sourceOriginalPAllActualBands 20 L)
      (sourceActualSortedPPartSupport 20 L ⌊Real.exp (L/44)⌋₊)
      F G k (rho+xi3) (-rho)
      (fun n => if ((n : ℤ)+2*k).toNat∈N then
        (Z : ℂ)⁻¹ * psi ((n : ℝ)/Z) else 0) tw tw := by
  have hSrc := parity_raw_stripped_original_B521_channel434 L hL hS rho xi3 Z
    k hk N hN F G tw (fun t => (t : ℂ)*psi t)
  have hEq : (fun n : ℕ =>
      if ((n : ℤ)+2*k).toNat∈N then
        (((n : ℝ)/Z : ℝ) : ℂ)*psi ((n : ℝ)/Z)/(n : ℂ) else 0) =
      (fun n : ℕ =>
        if ((n : ℤ)+2*k).toNat∈N then
          (Z : ℂ)⁻¹*psi ((n : ℝ)/Z) else 0) := by
    funext n
    split_ifs
    · exact parity_raw_original_normalized_source_coefficient434 Z hZ psi hSupport n
    · rfl
  simpa only [hEq] using hSrc
end Green64Analytic.Parity

end

end

/-! ## RawZeroShared -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 28000

/-- The literal J=0 RAW has no shared slots and hence DR=1. The one
endpoint-free slot remains present in every group. This is not an
empty-comparison assertion. -/
theorem parity_raw_zero_shared_dilation434
    {G : Type} [Fintype G] [DecidableEq G]
    (s : ∀ g : G,parityRawSharedSlots434 0 → ℕ) :
    sourceB574SharedDilation434 (0+1)
      (fun _ : G=>parityRawSharedSlots434 0) s=1 := by
  letI : IsEmpty (parityRawSharedSlots434 0) := ⟨fun i=>by
    have hi := (parity_raw_shared_slot_mem434 0 i.val).mp i.property
    omega⟩
  unfold sourceB574SharedDilation434
  simp

/-- Exact identity of the physical quotient carrier when DR=1. -/
theorem parity_raw_unit_quotient_positions434 (positions : Finset ℤ) :
    paritySharedQuotientPositions434 positions 1=parityPositiveNaturalPositions434 positions := by
  ext n
  rw [parity_shared_quotient_mem_iff434 positions 1 n (by norm_num),
    parity_positive_natural_positions_mem434]
  simp only [one_mul]

/-- Genuine weighted J=0 physical RAW equals the independently defined
restored RAW on the same positive carrier. DR=1 is proved before weights
are moved: thus ANY endpoint weight, including both original physical caps,
is retained exactly at w,wp. Source seed removal uses the existing actual
completion theorem. No carrier equality, clean event or cap relocation is
assumed, and the finite physical positions are arbitrary. -/
theorem parity_eventually_raw_zero_harmonic_restored434 (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1 ≤ L ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (rho xi3 Z : ℝ),0<Z → Z≤Real.exp L*L^CZ →
    ∀ (k : ℤ) (positions : Finset ℤ) (F G : PrimeSlotCore)
      (tw : Bool) (psi : ℝ→ℂ),
      (∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
    ∀ Wgt : ℕ→ℕ→ℂ,
      parityRawHarmonicPhysicalAggregate434 L hS 0 (-xi3) Z k positions
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi Wgt =
      parityRawRestoredHarmonic434 L hS 0 rho xi3 Z k
        (parityPositiveNaturalPositions434 positions) F G tw psi Wgt := by
  filter_upwards [parity_eventually_raw_shared_scalar_slice434 0 CZ] with L hStrip
  refine ⟨hStrip.1,?_⟩
  intro hS rho xi3 Z hZ hZhi k positions F G tw psi hSupp Wgt
  let E := fun _ : B645ActualGroup434 L hS=>parityRawSharedSlots434 0
  let ss := Fintype.piFinset
    (fun i : (g : B645ActualGroup434 L hS) × E g=>b645ActualBand434 L hS i.1)
  let N := parityPositiveNaturalPositions434 positions
  let R := fun (s : (g : B645ActualGroup434 L hS) × E g → ℕ) (w wp : ℕ)=>
    if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+2*k then
      Wgt w wp*parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
        (-(rho+xi3)) (-rho) tw psi 1 w wp*
      parityRawPhysicalSlice434 0 (b645ActualBand434 L hS)
        (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
        (1/2) w wp (fun g i=>s ⟨g,i⟩)
    else 0
  have hfirst : parityRawHarmonicPhysicalAggregate434 L hS 0 (-xi3) Z k positions
      1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi Wgt =
      ∑ s∈ss,∑ w∈N,∑ wp∈N,R s w wp := by
    unfold parityRawHarmonicPhysicalAggregate434
    dsimp only
    simp only [parity_raw_zero_shared_dilation434,one_mul,parity_raw_unit_quotient_positions434]
    apply Finset.sum_congr rfl
    intro s hs
    have hsmem : ∀ g i,s ⟨g,i⟩∈b645ActualBand434 L hS g :=
      fun g i=>(Fintype.mem_piFinset.mp hs) ⟨g,i⟩
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro wp hwp
    have hw0 := ((parity_positive_natural_positions_mem434 positions w).mp hw).1
    have hwp0 := ((parity_positive_natural_positions_mem434 positions wp).mp hwp).1
    have he := hStrip.2 hS (fun g i=>s ⟨g,i⟩) hsmem rho xi3 Z hZ hZhi
      psi hSupp F G tw w wp hw0 hwp0
    dsimp only at he
    rw [parity_raw_zero_shared_dilation434] at he
    dsimp only [R]
    split_ifs
    · simpa only [mul_assoc] using congrArg (fun z=>(Wgt w wp)*z) he
    · rfl
  calc
    _ = ∑ s∈ss,∑ w∈N,∑ wp∈N,R s w wp := hfirst
    _ = ∑ w∈N,∑ wp∈N,∑ s∈ss,R s w wp :=
      (parity_shared_position_sum_order434 N ss R).symm
    _ = _ := by
      unfold parityRawRestoredHarmonic434
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro wp hwp
      dsimp only [R]
      split_ifs
      · rw [←Finset.mul_sum]
        rfl
      · simp only [Finset.sum_const_zero]
end Green64Analytic.Parity

end

end

/-! ## RawZeroStripped -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 26000

/-- The actual zero shared-defect theorem gives exact weighted harmonic
restoration on ANY positive finite carrier. Both complete endpoint-free
marked products remain in the independent stripped definition. -/
theorem parity_eventually_raw_zero_restored_stripped434 :
    ∀ᶠ L : ℝ in atTop,1<L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ),
      (∀ n∈N,0<n) →
    ∀ (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ→ℂ) (Wgt : ℕ→ℕ→ℂ),
      parityRawRestoredHarmonic434 L hS 0 rho xi3 Z k N F G tw psi Wgt =
      parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi Wgt := by
  filter_upwards [parity_eventually_actual_raw_shared_zero434] with L hZero
  refine ⟨hZero.1,hZero.2.1,?_⟩
  intro hS rho xi3 Z k N hN F G tw psi Wgt
  unfold parityRawRestoredHarmonic434 parityRawStrippedHarmonic434
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro wp hwp
  split_ifs
  · rw [hZero.2.2 hS w wp (hN w hw) (hN wp hwp)]
  · rfl

/-- Exact physical-to-stripped RAW at J=0, with arbitrary endpoint weights
and arbitrary finite physical positions. DR=1 and the zero collision defect
are derived from the genuine original RAW constructions. This theorem is
valid in particular for the ORIGINAL paircap and its complement; it does
not transfer caps through a nontrivial shared divisor. -/
theorem parity_eventually_raw_zero_physical_stripped434 (CZ : ℝ) :
    ∀ᶠ L : ℝ in atTop,Real.exp 1≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
    ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
      (rho xi3 Z : ℝ),0<Z → Z≤Real.exp L*L^CZ →
    ∀ (k : ℤ) (positions : Finset ℤ) (F G : PrimeSlotCore)
      (tw : Bool) (psi : ℝ→ℂ),
      (∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
    ∀ Wgt : ℕ→ℕ→ℂ,
      parityRawHarmonicPhysicalAggregate434 L hS 0 (-xi3) Z k positions
        1 (parityDyadicLimit434 L) F G (-(rho+xi3)) (-rho) tw 0 psi Wgt =
      parityRawStrippedHarmonic434 L hS rho xi3 Z k
        (parityPositiveNaturalPositions434 positions) F G tw psi Wgt := by
  filter_upwards [parity_eventually_raw_zero_harmonic_restored434 CZ,
    parity_eventually_raw_zero_restored_stripped434] with L hPhysical hZero
  refine ⟨hPhysical.1,hZero.2.1,?_⟩
  intro hS rho xi3 Z hZ hZhi k positions F G tw psi hSupp Wgt
  rw [hPhysical.2 hS rho xi3 Z hZ hZhi k positions F G tw psi hSupp Wgt]
  exact hZero.2.2 hS rho xi3 Z k _
    (fun n hn=>((parity_positive_natural_positions_mem434 positions n).mp hn).1)
    F G tw psi Wgt

/-- Literal linearity in the supplied endpoint weight, before any support
or analytic bound. It exposes the genuine cap-loss difference without
changing either independently defined functional. -/
theorem parity_raw_stripped_weight_sub434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (rho xi3 Z : ℝ) (k : ℤ) (N : Finset ℕ) (F G : PrimeSlotCore)
    (tw : Bool) (psi : ℝ→ℂ) (U V : ℕ→ℕ→ℂ) :
    parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi (fun n np=>U n np-V n np) =
      parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi U-
      parityRawStrippedHarmonic434 L hS rho xi3 Z k N F G tw psi V := by
  unfold parityRawStrippedHarmonic434
  symm
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wp hwp
  split_ifs <;> ring
end Green64Analytic.Parity

end

end

/-! ## RawQuotientCapLoss -/

section

open Filter Real
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
open Green64Analytic.CorrelationMellin Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 30000

/-- Genuine quotient-endpoint Ppart cap insertion for the independently
constructed STRIPPED RAW. This uses the already proved physical RAW cap
tail at J=0, whose DR=1 and exact weighted physical-to-stripped identity
have now been proved. It never moves a cap through nontrivial DR. The
physical r20 family, both complete one-free-slot products, full masses,
original B633 cores, cutoff and signed2k are unchanged. The saving precision
is requested before L and the complete operator tuple; no cap-error
hypothesis or canonical empty-comparison kernel appears. -/
theorem parity_eventually_actual_raw_quotient_cap_loss434
    (S beta gamma CZ Ck Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma)
    (hCZ : 0≤CZ) (hK : 0≤Kpsi) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l : ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (delta : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (freq : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot delta freq K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k : ℝ)|≤L^Ck →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
          (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ positions : Finset ℤ,
        let N := parityPositiveNaturalPositions434 positions
        let U := parityRawStrippedHarmonic434 L hS rho xi3 Z k N Ecore Gcore tw psi (fun _ _=>1)
        let C := parityRawStrippedHarmonic434 L hS rho xi3 Z k N Ecore Gcore tw psi
          (parityOriginalPhysicalPairPcap434 L)
        ‖U-C‖≤L^(-A) ∧ ‖(Z : ℂ)*(U-C)‖≤Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_raw_cap_aggregate_saving434
      0 S beta gamma CZ Ck Cpsi Kpsi A hSfine hbeta hgamma hCZ hK,
    parity_eventually_raw_zero_physical_stripped434 CZ] with L hCap hExact
  refine ⟨hCap.1,hCap.2.1,?_⟩
  intro prime l u hlow r e hr b slot delta freq K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk tw psi hSupp hPsi positions
  let F := sourceNativePrimeCore r e L b slot delta freq K
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let N := parityPositiveNaturalPositions434 positions
  let U := parityRawStrippedHarmonic434 L hS rho xi3 Z k N Ecore Gcore tw psi (fun _ _=>1)
  let C := parityRawStrippedHarmonic434 L hS rho xi3 Z k N Ecore Gcore tw psi
    (parityOriginalPhysicalPairPcap434 L)
  have hLp : 0<L := (Real.exp_pos _).trans_le hCap.1
  have hZ : 0<Z := (mul_pos (Real.exp_pos L)
    (Real.rpow_pos_of_pos hLp (-CZ))).trans_le hZlo
  have h := hCap.2.2 prime l u hlow r e hr b slot delta freq K q chi s0 s1
    xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk
    1 (parityDyadicLimit434 L) tw psi hSupp hPsi positions
  have he := hExact.2.2 hS rho xi3 Z hZ hZhi k positions Ecore Gcore tw psi hSupp
    (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np)
  change parityRawHarmonicPhysicalAggregate434 L hS 0 (-xi3) Z k positions
      1 (parityDyadicLimit434 L) Ecore Gcore (-(rho+xi3)) (-rho) tw 0 psi
      (fun n np=>1-parityOriginalPhysicalPairPcap434 L n np) = _ at he
  rw [he,parity_raw_stripped_weight_sub434] at h
  change ‖U-C‖≤L^(-A) at h
  refine ⟨h,?_⟩
  change ‖(Z : ℂ)*(U-C)‖≤Z*L^(-A)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hZ]
  exact mul_le_mul_of_nonneg_left h hZ.le

/-- The same genuine quotient cap loss for the original normalized cutoff
t*psi(t), with all its norm data derived from the ORIGINAL log derivative
budget. This is uniform in the complete positive physical carrier and
actual operator frequencies; exactly one exterior Z is retained. -/
theorem parity_eventually_actual_normalized_raw_quotient_cap_loss434
    (S beta gamma CZ Ck Cpsi A : ℝ) (Kpsi : ℕ→ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma)
    (hCZ : 0≤CZ) (hCpsi : 0≤Cpsi) (hK : ∀ j,0≤Kpsi j) :
    ∀ᶠ L : ℝ in atTop,Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ),Real.exp (beta*L)≤(l : ℝ) →
      ∀ (r e : ℕ),1≤ r → ∀ (b : Fin (e+1)) (slot : Fin r)
        (delta : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→Bool)
        (freq : Fin (sourceOrderedLabels r (sourceActualSortedScales r e L) b slot).length→ℝ)
        (K : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r e L b slot delta freq K
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let Ecore := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let Gcore := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (xi3 Z : ℝ) (k : ℤ),
          Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ → |(k : ℝ)|≤L^Ck →
        ∀ (tw : Bool) (psi : ℝ→ℂ), ContDiff ℝ ∞ psi →
          (∀ t,psi t≠0 → (1/64 : ℝ)≤t ∧ t≤64) →
          sourceLogDerivativeBudget Cpsi Kpsi L (fun u=>psi (Real.exp u)) →
        ∀ positions : Finset ℤ,
        let N := parityPositiveNaturalPositions434 positions
        let U := parityRawStrippedHarmonic434 L hS rho xi3 Z k N Ecore Gcore tw
          (fun t=>(t : ℂ)*psi t) (fun _ _=>1)
        let C := parityRawStrippedHarmonic434 L hS rho xi3 Z k N Ecore Gcore tw
          (fun t=>(t : ℂ)*psi t) (parityOriginalPhysicalPairPcap434 L)
        ‖U-C‖≤L^(-A) ∧ ‖(Z : ℂ)*(U-C)‖≤Z*L^(-A) := by
  let KH := sourceNormalizedLogDerivativeConstants 64 Kpsi
  have hKH : ∀ j,0≤KH j :=
    source_normalized_log_derivative_constants_nonneg 64 Kpsi (by norm_num) hK
  filter_upwards [parity_eventually_actual_raw_quotient_cap_loss434
    S beta gamma CZ Ck Cpsi (KH 0) A hSfine hbeta hgamma hCZ (hKH 0)] with L hLoss
  refine ⟨hLoss.1,hLoss.2.1,?_⟩
  intro prime l u hlow r e hr b slot delta freq K q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk tw psi hSmooth hSupp hReg positions
  let psiH : ℝ→ℂ := fun t=>(t : ℂ)*psi t
  have hLp : 0<L := (Real.exp_pos _).trans_le hLoss.1
  have hL1 : 1<L := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ)<2)).trans_le hLoss.1
  have hSuppH : ∀ t,psiH t≠0 → (1/64 : ℝ)≤t ∧ t≤64 := by
    intro t ht
    apply hSupp t
    intro hz
    exact ht (by simp only [psiH,hz,mul_zero])
  have hRegH : sourceLogDerivativeBudget Cpsi KH L (fun u=>psiH (Real.exp u)) :=
    source_actual_normalized_log_derivative_budget 64 Cpsi L Kpsi psi
      (by norm_num) hCpsi hK hL1.le hSmooth hSupp hReg
  have hNorm : ∀ t,‖psiH t‖≤KH 0*L^Cpsi := by
    intro t
    by_cases ht : psiH t=0
    · rw [ht,norm_zero]
      exact mul_nonneg (hKH 0) (Real.rpow_nonneg hLp.le _)
    · have htp : 0<t := by linarith [(hSuppH t ht).1]
      simpa only [iteratedDeriv_zero,Nat.cast_zero,zero_add,mul_one,Real.exp_log htp]
        using hRegH 0 (Real.log t)
  exact hLoss.2.2 prime l u hlow r e hr b slot delta freq K q chi s0 s1
    xi1 xi2 rho sigma hS xi3 Z k hZlo hZhi hk tw psiH hSuppH hNorm positions
end Green64Analytic.Parity

end

end

/-! ## WeightedRestorationError -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- Independently specified literal stripped target, on the same original
finite positive carrier and with the same original auxiliary atom. -/
def parityActualWeightedStrippedComparison434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) : ℂ :=
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  ∑ w∈N,∑ wp∈N,
    if (2*k)≠0 ∧ (wp : ℤ)=(w : ℤ)+(2*k)*(c : ℤ) then
      parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp *
        (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p => p.val) J m
          (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
        sourceB574CanonicalStrippedSlice434 J 1 m hmJ
          (parityFullProbePattern434 (SourceNativeMemorySG434 20 L hS) m nu) Q h h xi
          (b645ActualBand434 L hS)
          (Sum.elim (SourceNativeMemorySmallMass434 20 L hS) (sourceNativeOriginalVbig434 20 L))
          (parityFullProbeAuxLift434 (SourceNativeMemorySG434 20 L hS) m nu
            (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux))
          (1/2 : ℝ) w wp
    else 0

/-- Literal difference of the two original weighted constructions. -/
def parityActualWeightedRestorationDifference434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) : ℂ :=
  parityActualWeightedRestoredComparison434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k F G tw psi aux -
  parityActualWeightedStrippedComparison434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k F G tw psi aux

/-- Exact difference identity preserves the full arithmetic multiplier and auxiliary atom. -/
theorem parity_actual_weighted_restoration_difference_exact434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu) :
    parityActualWeightedRestorationDifference434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k F G tw psi aux =
    let c := parityActualProbeAuxD434 L J m hmJ nu aux
    let N := parityPositiveNaturalPositions434
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
    (sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ) *
    ∑ w∈N,∑ wp∈N,
      if (2*k)≠0 ∧ (wp:ℤ)=(w:ℤ)+(2*k)*(c:ℤ) then
        parityHarmonicStrippedArithmetic434 L (-xi3) Z F G (-(rho+xi3)) (-rho) tw psi c w wp *
        parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q h h xi
          (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux) w wp
      else 0 := by
  unfold parityActualWeightedRestorationDifference434 parityActualWeightedRestoredComparison434
    parityActualWeightedStrippedComparison434
  dsimp only
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wp hwp
  split_ifs
  · unfold parityActualCanonicalSharedRestorationError434
    ring
  · ring

/-- Finite weighted-to-harmonic error transfer with both divisor-square weights.
Actual core bounds and geometry are supplied in the next specialization. -/
theorem parity_actual_weighted_restoration_difference_envelope434
    (L : ℝ) (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
    (J m : ℕ) (hmJ : m≤J)
    (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
    (Q : ℕ) (h xi rho xi3 Ck Z : ℝ) (k : ℤ)
    (F G : PrimeSlotCore) (tw : Bool) (psi : ℝ → ℂ)
    (aux : ParityActualProbeAux434 L J m hmJ nu)
    (M : ℕ)
    (hN : parityPositiveNaturalPositions434
      (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L)) ⊆ Finset.Ioc 0 M)
    (hF : ∀ n : ℕ,0<n → ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F n‖≤(n.divisors.card:ℝ)^2)
    (hG : ∀ n : ℕ,0<n → ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G n‖≤(n.divisors.card:ℝ)^2) :
    ‖parityActualWeightedRestorationDifference434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k F G tw psi aux‖ ≤
      ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
        (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ *
      parityActualSharedHarmonicErrorEnvelope434 L hS J m hmJ nu Q h h xi
        (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)
        (Z*(parityActualProbeAuxD434 L J m hmJ nu aux:ℝ))
        ((2*k)*(parityActualProbeAuxD434 L J m hmJ nu aux:ℤ)) psi M := by
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let s : ℤ := (2*k)*(c:ℤ)
  let aa : ℕ → ℕ → ℂ := parityHarmonicStrippedArithmetic434 L (-xi3) Z F G
    (-(rho+xi3)) (-rho) tw psi c
  let ee : ℕ → ℕ → ℂ := parityActualCanonicalSharedRestorationError434 L hS J m hmJ nu Q h h xi
    (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)
  let bb : ℕ → ℝ := fun w=>‖psi ((w:ℝ)/(Z*(c:ℝ)))‖/(w:ℝ)*
    (w.divisors.card:ℝ)^2*((((w:ℤ)+s).toNat).divisors.card:ℝ)^2
  have hb (w : ℕ) : 0≤bb w := by dsimp [bb];positivity
  have ha (w : ℕ) (hw : w∈N) (wp : ℕ) (hwp : wp∈N)
      (hshift : (wp:ℤ)=(w:ℤ)+s) : ‖aa w wp‖≤bb w := by
    have hwpos : 0<w := (Finset.mem_Ioc.mp (hN hw)).1
    have hwppos : 0<wp := (Finset.mem_Ioc.mp (hN hwp)).1
    have he : wp=((w:ℤ)+s).toNat := by
      have hh := congrArg Int.toNat hshift
      simpa only [Int.toNat_natCast] using hh
    have hPair : ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F w‖*
        ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G wp‖≤
        (w.divisors.card:ℝ)^2*(wp.divisors.card:ℝ)^2 :=
      mul_le_mul (hF w hwpos) (hG wp hwppos) (norm_nonneg _) (sq_nonneg _)
    dsimp only [aa]
    rw [parity_harmonic_stripped_arithmetic_norm434 L (-xi3) Z F G
      (-(rho+xi3)) (-rho) tw psi c w wp hwpos hwppos]
    calc
      _ = (w:ℝ)⁻¹*(‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) F w‖*
        ‖primeSlotCoreValue (sourceOriginalPAllActualBands 20 L) G wp‖)*
        ‖psi ((w:ℝ)/(Z*(c:ℝ)))‖ := by ring
      _ ≤ (w:ℝ)⁻¹*((w.divisors.card:ℝ)^2*(wp.divisors.card:ℝ)^2)*
        ‖psi ((w:ℝ)/(Z*(c:ℝ)))‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPair (by positivity)) (norm_nonneg _)
      _ = bb w := by dsimp [bb];rw [he];ring
  have hh := parity_finite_weighted_restoration_envelope434 N M hN s ((2*k)≠0) aa ee bb hb ha
  rw [parity_actual_weighted_restoration_difference_exact434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k F G tw psi aux]
  dsimp only
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact hh
end Green64Analytic.Parity

end

end

/-! ## ActualWeightedRestoration -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- Genuine quantitative weighted restoration for the actual B633 endpoint
cores and every original typed auxiliary draw. The error is the literal
Restored-Stripped difference; all endpoint norm, auxiliary size and harmonic
geometry premises are discharged internally. The huge original finite
carrier is harmless: M is its supremum and the proved error envelope is
uniform in M through the original cutoff support. Both inverse cell masses
and the complete auxiliary atom remain in the quantitative bound. -/
theorem parity_eventually_actual_weighted_restoration_error434
    (J : ℕ) (S beta gamma CZ Ck : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0≤CZ) :
    ∃ Em : ℝ,0≤Em ∧
    ∀ᶠ L : ℝ in atTop, Real.exp 2≤L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L)≤(l:ℝ) →
      ∀ (r d : ℕ),1≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m≤J)
          (nu : SourceOriginalProbePattern434 (sourceNativeOriginalBigType434 20 L) m)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),
          0<h → 0<xi → Real.exp L*L^(-CZ)≤Z → Z≤Real.exp L*L^CZ →
          |(k:ℝ)|≤L^Ck →
        ∀ (Kpsi Cpsi : ℝ),0≤Kpsi → ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖≤Kpsi*L^Cpsi) →
        ∀ aux : ParityActualProbeAux434 L J m hmJ nu,
          ‖parityActualWeightedRestorationDifference434 L hS J m hmJ nu Q h xi rho xi3 Ck Z k E G tw psi aux‖≤
          ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
            (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu) aux : ℂ)‖ *
          ((2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2))*
            ((Q:ℝ)^4*(xi⁻¹)^2)*(64*66*(3:ℝ)^15)*Kpsi*
            L^(16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi)*Real.exp (-(L^(1/10:ℝ)))) := by
  obtain ⟨Em,hEm,hRest⟩ := parity_eventually_actual_shared_harmonic_error434 J
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hRest,
    parity_eventually_actual_B633_core_tau434 S beta gamma hSfine hbeta hgamma,
    parity_eventually_actual_typed_aux_sqrt434 J,
    parity_eventually_harmonic_scale_budget434 CZ Ck hCZ] with L hRest hCore hAux hGeom
  refine ⟨hRest.1,hRest.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma
  intro hS m hmJ nu Q h xi xi3 Z k hh hxi hZlo hZhi hk Kpsi Cpsi hK tw psi hSupp hPsi aux
  let F := sourceNativePrimeCore r d L b slot δ ξ Kset
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let c := parityActualProbeAuxD434 L J m hmJ nu aux
  let N := parityPositiveNaturalPositions434
    (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
  let M : ℕ := N.sup id
  have hN : N⊆Finset.Ioc 0 M := by
    intro n hn
    apply Finset.mem_Ioc.mpr
    refine ⟨(parity_positive_natural_positions_mem434 _ n).mp hn |>.1,?_⟩
    exact Finset.le_sup (f:=id) hn
  have hBoth := hCore.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1 xi1 xi2 rho sigma
  have hFinite := parity_actual_weighted_restoration_difference_envelope434 L hS J m hmJ nu
    Q h xi rho xi3 Ck Z k E G tw psi aux M hN
    (fun n hn=>(hBoth n hn).1) (fun n hn=>(hBoth n hn).2)
  have hc := hAux.2 hS m hmJ nu aux
  have hb := hGeom.2 Z hZlo hZhi c hc.1 hc.2 k hk
  have hEnv := hRest.2.2 hS m hmJ nu Q h h xi
    (sourceOriginalProbeMemoryAuxValues434 (sourceNativeOriginalTb434 20 L) J m hmJ nu aux)
    (Z*(c:ℝ)) Kpsi Cpsi ((2*k)*(c:ℤ)) psi M
    hh hh hxi hb.1 hK hb.2.1 hb.2.2 hSupp hPsi
  exact hFinite.trans (mul_le_mul_of_nonneg_left hEnv (norm_nonneg _))
end Green64Analytic.Parity

end

end

/-! ## ActualWeightedRestorationAggregate -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- The literal actual weighted Restored-Stripped error is summed over the
FULL original comparison-pattern family and each untilted labelled auxiliary
law. Its auxiliary mass is exactly one; its only family loss is the proved
BIG-group logarithmic power. No auxiliary-dependent stripped scalar or free
ban is removed, and both cell inverse masses remain Q^4*xi^(-2). -/
theorem parity_eventually_actual_weighted_restoration_family434
    (J : ℕ) (S beta gamma CZ Ck : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0 ≤ CZ) :
    ∃ Em : ℝ,0 ≤ Em ∧
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m ≤ J)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),
          0<h → 0<xi → Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
          |(k:ℝ)| ≤ L^Ck →
        ∀ (Kpsi Cpsi : ℝ),0 ≤ Kpsi → ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
        ‖∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
          ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
            parityActualWeightedRestorationDifference434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux‖ ≤ 
          (2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2))*
            ((Q:ℝ)^4*(xi⁻¹)^2)*(64*66*(3:ℝ)^15)*Kpsi*
            L^(16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi+
              (J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*Real.exp (-(L^(1/10:ℝ))) := by
  obtain ⟨Em,hEm,hFixed⟩ := parity_eventually_actual_weighted_restoration_error434
    J S beta gamma CZ Ck hSfine hbeta hgamma hCZ
  refine ⟨Em,hEm,?_⟩
  filter_upwards [hFixed,parity_eventually_actual_typed_aux_mass434 J] with L hFixed hMass
  refine ⟨hFixed.1,hFixed.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk
    Kpsi Cpsi hK tw psi hSupp hPsi
  let F := sourceNativePrimeCore r d L b slot δ ξ Kset
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  let I := ↥(sourceOriginalTwoBlockProbePatterns434
    (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m)
  let D : (nu : I) → ParityActualProbeAux434 L J m hmJ nu.val → ℂ := fun nu aux =>
    parityActualWeightedRestorationDifference434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux
  let mu : (nu : I) → ParityActualProbeAux434 L J m hmJ nu.val → ℝ := fun nu aux =>
    ‖(sourceAuxMass (SourceNativeMemoryBP434 20 L) (fun _ p=>p.val) J m
      (sourceNativeOriginalVbig434 20 L) (sourceOriginalProbeMemoryPattern434 J m hmJ nu.val) aux : ℂ)‖
  let B := (2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2))*
      ((Q:ℝ)^4*(xi⁻¹)^2)*(64*66*(3:ℝ)^15)*Kpsi*
      L^(16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi)*Real.exp (-(L^(1/10:ℝ)))
  have hLpos : 0<L := lt_trans zero_lt_one hMass.1
  have hLexp : Real.exp 1 ≤ L :=
    (Real.exp_le_exp.mpr (by norm_num : (1:ℝ) ≤ 2)).trans hFixed.1
  have hB : 0 ≤ B := by
    have hC := parity_shared_defect_constant_nonneg434 J
    have hv := source_actual_P_uniform_mass_floor_positive
    dsimp [B]
    positivity
  have hOne (nu : I) (aux : ParityActualProbeAux434 L J m hmJ nu.val) :
      ‖D nu aux‖ ≤ mu nu aux*B := by
    exact hFixed.2.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
      xi1 xi2 rho sigma hS m hmJ nu.val Q h xi xi3 Z k hh hxi hZlo hZhi hk
      Kpsi Cpsi hK tw psi hSupp hPsi aux
  have hAux (nu : I) : ‖∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,D nu aux‖ ≤ B := by
    calc
      _  ≤  ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,‖D nu aux‖ := norm_sum_le _ _
      _  ≤  ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,mu nu aux*B :=
        Finset.sum_le_sum (fun aux haux=>hOne nu aux)
      _ = (∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,mu nu aux)*B :=
        (Finset.sum_mul _ _ _).symm
      _ = B := by
        have hm : (∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,mu nu aux)=1 :=
          (hMass.2.2 hS m hmJ nu.val).2
        rw [hm,one_mul]
  have hcardM := parity_actual_probe_family_card434 L hLexp hS m
  have hC0 : 0 ≤ 3+(Real.log 2)⁻¹ := by
    have ht : 0<Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hExponent : (m:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2 ≤ 
      (J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hmJ) hC0)
      (Real.log_nonneg (by norm_num))
  have hcard : (Fintype.card I:ℝ) ≤ L^((J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2) := by
    simpa only [I,Fintype.card_coe] using
      hcardM.trans (Real.rpow_le_rpow_of_exponent_le hMass.1.le hExponent)
  change ‖∑ nu : I,∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,D nu aux‖ ≤ _
  calc
    _  ≤  ∑ nu : I,‖∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,D nu aux‖ := norm_sum_le _ _
    _  ≤  ∑ _nu : I,B := Finset.sum_le_sum (fun nu hnu=>hAux nu)
    _ = (Fintype.card I:ℝ)*B := by simp
    _  ≤  L^((J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)*B := mul_le_mul_of_nonneg_right hcard hB
    _ = _ := by
      dsimp [B]
      rw [Real.rpow_add hLpos (16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi)
        ((J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2)]
      ring
end Green64Analytic.Parity

end

end

/-! ## ActualWeightedRestorationSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- Complete actual weighted restoration saving with the true auxiliary
law and all patterns. All precision, cell and cutoff parameters are fixed
BEFORE L. Both reciprocal cell masses cost 4*CQ+2*Cxi; no inverse mass or
auxiliary dependence has been dropped. -/
theorem parity_eventually_actual_weighted_restoration_family_saving434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0 ≤ CZ) (hK : 0 ≤ Kpsi) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m ≤ J)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),
          0<h → 0<xi → Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
          |(k:ℝ)| ≤ L^Ck →
        (Q:ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
        ‖∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
          ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
            parityActualWeightedRestorationDifference434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux‖ ≤
          L^(-A) := by
  obtain ⟨Em,hEm,hFamily⟩ := parity_eventually_actual_weighted_restoration_family434
    J S beta gamma CZ Ck hSfine hbeta hgamma hCZ
  let C := 2*paritySharedDefectConstant434 J/(Real.log (6/5:ℝ)/2)
  let K := C*(64*66*(3:ℝ)^15)*Kpsi
  let e := 16*(J+1:ℝ)*Real.log 2+2*Em+16+Cpsi+
    (J:ℝ)*(3+(Real.log 2)⁻¹)*Real.log 2
  let ec := 4*CQ+2*Cxi
  filter_upwards [hFamily,
    eventually_source_fixed_poly_exp_saving (1/10:ℝ) K (e+ec) A (by norm_num)] with L hFamily hSave
  refine ⟨hFamily.1,hFamily.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  have hLpos : 0<L := lt_of_lt_of_le zero_lt_one hSave.1
  have hBound := hFamily.2.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
    xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk
    Kpsi Cpsi hK tw psi hSupp hPsi
  have hC : 0 ≤ C := by
    have hc := parity_shared_defect_constant_nonneg434 J
    have hv := source_actual_P_uniform_mass_floor_positive
    dsimp [C]
    positivity
  have hCell : (Q:ℝ)^4*(xi⁻¹)^2 ≤ L^ec := by
    calc
      _ ≤ (L^CQ)^4*(L^Cxi)^2 :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 4)
          (pow_le_pow_left₀ (inv_nonneg.mpr hxi.le) hXi 2)
          (sq_nonneg _) (pow_nonneg (Real.rpow_nonneg hLpos.le CQ) 4)
      _ = L^ec := by
        rw [← Real.rpow_natCast (L^CQ) 4,← Real.rpow_natCast (L^Cxi) 2,
          ← Real.rpow_mul hLpos.le,← Real.rpow_mul hLpos.le,
          ← Real.rpow_add hLpos]
        congr 1
        dsimp [ec]
        ring
  have hPow : L^ec*L^e=L^(e+ec) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ C*((Q:ℝ)^4*(xi⁻¹)^2)*(64*66*(3:ℝ)^15)*Kpsi*L^e*Real.exp (-(L^(1/10:ℝ))) := hBound
    _ ≤ C*L^ec*(64*66*(3:ℝ)^15)*Kpsi*L^e*Real.exp (-(L^(1/10:ℝ))) := by gcongr
    _ = K*(L^ec*L^e)*Real.exp (-(L^(1/10:ℝ))) := by dsimp [K];ring
    _ = K*L^(e+ec)*Real.exp (-(L^(1/10:ℝ))) := by rw [hPow]
    _ ≤ L^(-A) := by
      simpa only [Real.rpow_neg hLpos.le,one_div] using hSave.2
end Green64Analytic.Parity

end

end

/-! ## ActualHarmonicStrippedSaving -/

section

open Filter Topology
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 26000

/-- The UNCHANGED independently defined uncapped H_T equals its literal RAW
branch plus the independently defined full weighted Stripped comparison
family up to any prescribed inverse-log error. Actual B633 core bounds,
true auxiliary product laws, complete pattern cost and BOTH cell inverse
masses are accounted for. Auxiliary-dependent cutoff, shift and free ban
remain inside the Stripped expectation. Physical cap insertion is separate. -/
theorem parity_eventually_actual_harmonic_stripped_error434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0 ≤ CZ) (hK : 0 ≤ Kpsi) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m ≤ J)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),
          0<h → 0<xi → Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
          |(k:ℝ)| ≤ L^Ck →
        (Q:ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
        ‖(parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
            (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
            1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
            ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
              parityActualWeightedStrippedComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux)‖ ≤ L^(-A) := by
  filter_upwards [parity_eventually_actual_weighted_restoration_family_saving434
    J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A hSfine hbeta hgamma hCZ hK,
    parity_eventually_harmonic_weighted_restored434 J CZ] with L hSave hJoin
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  let F := sourceNativePrimeCore r d L b slot δ ξ Kset
    (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
  let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
  let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
  have hLpos : 0<L := (Real.exp_pos 2).trans_le hSave.1
  have hZpos : 0<Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos (-CZ))).trans_le hZlo
  have hkNat : (k.natAbs:ℝ) ≤ L^Ck := by simpa only [Nat.cast_natAbs,Int.cast_abs] using hk
  have hj := hJoin.2 hS m hmJ Q h xi rho xi3 Ck Z k hkNat hZpos hZhi psi
    (fun t ht=>hSupp t ht) E G tw
  have hs := hSave.2.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
    xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  rw [hj,add_sub_cancel_left]
  simpa only [parityActualWeightedRestorationDifference434,Finset.sum_sub_distrib] using hs

/-- The same genuine full restoration estimate with exactly ONE external Z.
Requested A and all fixed cutoff/cell budgets precede L; the final right side
is Z*L^(-A), without hidden division or a second Z. -/
theorem parity_eventually_actual_harmonic_outer_Z_stripped_error434
    (J : ℕ) (S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A : ℝ)
    (hSfine : 0<S) (hbeta : 0<beta) (hgamma : 0<gamma) (hCZ : 0 ≤ CZ) (hK : 0 ≤ Kpsi) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      (sourceNativeOriginalSmallIndices434 20 L).Nonempty ∧
      ∀ (prime : Bool) (l u : ℕ), Real.exp (beta*L) ≤ (l:ℝ) →
      ∀ (r d : ℕ),1 ≤ r → ∀ (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (Kset : Finset ℕ) (q : ℕ) (chi : DirichletCharacter ℂ q) (s0 s1 : ℝ),
        let F := sourceNativePrimeCore r d L b slot δ ξ Kset
          (b629ActualFineAlpha434 prime L S gamma l u) q chi s0 s1
        ∀ xi1 xi2 rho sigma : ℝ,
        let E := b633ParityEFirstCore434 F.alpha F.residual q chi F.lo F.hi xi2 rho sigma
        let G := b633ParitySecondCore434 F.alpha F.residual q chi F.lo F.hi xi1 rho sigma
        ∀ (hS : (sourceNativeOriginalSmallIndices434 20 L).Nonempty)
          (m : ℕ) (hmJ : m ≤ J)
          (Q : ℕ) (h xi xi3 Z : ℝ) (k : ℤ),
          0<h → 0<xi → Real.exp L*L^(-CZ) ≤ Z → Z ≤ Real.exp L*L^CZ →
          |(k:ℝ)| ≤ L^Ck →
        (Q:ℝ) ≤ L^CQ → xi⁻¹ ≤ L^Cxi →
        ∀ (tw : Bool) (psi : ℝ→ℂ),
          (∀ t,psi t≠0 → t∈Set.Icc (1/64:ℝ) 64) →
          (∀ t,‖psi t‖ ≤ Kpsi*L^Cpsi) →
        ‖(Z:ℂ)*(parityHarmonicPhysical434 L hS J m hmJ Q h xi (-xi3) Z Ck k
            (parityDyadicDepth434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          parityActualHarmonicRawPositiveFibreSum434 L hS J m hmJ Q h xi (-xi3) Z k
            (b654ParityIntervalWindow434 J Ck L 1 (parityDyadicLimit434 L))
            1 (parityDyadicLimit434 L) E G (-(rho+xi3)) (-rho) tw 0 psi -
          ∑ nu : ↥(sourceOriginalTwoBlockProbePatterns434
            (sourceNativeOriginalBigBlockA434 20 L) (sourceNativeOriginalBigBlockB434 20 L) m),
            ∑ aux : ParityActualProbeAux434 L J m hmJ nu.val,
              parityActualWeightedStrippedComparison434 L hS J m hmJ nu.val Q h xi rho xi3 Ck Z k E G tw psi aux)‖ ≤ Z*L^(-A) := by
  filter_upwards [parity_eventually_actual_harmonic_stripped_error434
    J S beta gamma CZ Ck CQ Cxi Cpsi Kpsi A hSfine hbeta hgamma hCZ hK] with L hSave
  refine ⟨hSave.1,hSave.2.1,?_⟩
  intro prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
  dsimp only
  intro xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  have hLpos : 0<L := (Real.exp_pos 2).trans_le hSave.1
  have hZpos : 0<Z :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLpos (-CZ))).trans_le hZlo
  have hs := hSave.2.2 prime l u hlow r d hr b slot δ ξ Kset q chi s0 s1
    xi1 xi2 rho sigma hS m hmJ Q h xi xi3 Z k hh hxi hZlo hZhi hk hQ hXi tw psi hSupp hPsi
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hZpos.le]
  exact mul_le_mul_of_nonneg_left hs hZpos.le
end Green64Analytic.Parity

end

end

