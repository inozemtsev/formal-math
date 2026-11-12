module

public import Green64.Library.Sieve.Foundations.Part012
public import Green64.Library.Weights.Part111
public import Green64.Library.Weights.Part112
public import Green64.Library.Weights.Part113
public import Green64.Library.Sieve.Foundations.Part011
public import Green64.Library.Analysis.Estimates.Part015
public import Green64.Library.Sieve.Foundations.Part010
public import Green64.Library.Correlation.Part072
public import Green64.Library.Sieve.Foundations.Part009

@[expose] public section

/-!
# Sieve / Foundations / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalB590OutsideEPreCauchy -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Literal historical Parity(4.5) OUTSIDE selected-e window on the
ORIGINAL h=-2 B590 Fourier box: all 20! Q prime labelled tuples,
W1, odd multiplicity parity, Psi and the true mn=u+2 alpha/beta.
No proxy e-support assumption: outside branches are kept as the actual
truncated Fourier integrals (which need not be zero individually). -/
def parityOriginalShiftTwoBilinearOutsideEBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (parityOriginalB590BoxPhysicalOutsideEAtU434 d L E u band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- TRUE outside-e-box pre-Cauchy bound after summing all h=-2
alpha_m beta_n factorisations. The retained beta/4 source Ppart has
arbitrary small L^-A leakage; the discarded part has only its honest
source Fourier-variation times the exact W1(u)tau(u+2) mass.
This is a bound on a literal COMPLEX source bilinear difference, not
an unconnected variation budget or artificial zero of Fourier gates. -/
theorem parity_eventually_original_hminus2_outside_e_box_pre_cauchy434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearOutsideEBox434
        (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β
        ⌊2*Real.exp L⌋₊ L‖ ≤
      Acoef*Bcoef *
        ((L^(-A)) *
          (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
            sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
            ((u+2).divisors.card:ℝ)) +
        (∑ δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool,
          parityOriginalB590FourierBranchVariation434 δ) *
        (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
          (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
            else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
            ((u+2).divisors.card:ℝ))) := by
  filter_upwards [parity_eventually_original_B590_outside_e_Psi_pointwise_bound434
    beta A hbeta jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 band hb slot
    K J α β Acoef Bcoef hA hB hα hβ
  let Y := ⌊2*Real.exp L⌋₊
  let w : ℕ → ℝ := fun u => sourceOriginalW1
    (sourceOriginalPAllActualBands 20 L) u
  let t : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length → Bool,
    parityOriginalB590FourierBranchVariation434 δ
  let c : ℕ → ℝ := fun u => if parityOriginalPhysicalPcapBeta434 beta L u then 0 else t
  let Q : ℕ → ℂ := fun u => parityOriginalB590BoxPhysicalOutsideEAtU434
    (sourceOriginalLiteralDepth 20 L) L E u band slot L *
    (Psi ((u:ℝ)/Real.exp L):ℂ)
  let F : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
      α z.1*β z.2
  have hU (u : ℕ) : ‖Q u‖ ≤ w u*(L^(-A)+c u) :=
    h.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1 u band hb slot
  have hF (u : ℕ) : ‖F u‖ ≤
      ((u+2).divisors.card:ℝ)*Acoef*Bcoef :=
    parity_original_shift_two_bilinear_fibre_norm_le_tau434 K J u
      α β Acoef Bcoef hA hB hα hβ
  have hw (u : ℕ) : 0 ≤ w u := source_original_W1_nonneg _ _
  have ht : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hPow : 0 ≤ L^(-A) := Real.rpow_nonneg (by linarith [h.1]) _
  have hc (u : ℕ) : 0 ≤ c u := by
    dsimp [c]
    split <;> positivity
  have hterm (u : ℕ) :
      ‖Q u * F u‖ ≤ Acoef*Bcoef *
        (w u * ((u+2).divisors.card:ℝ) * (L^(-A)+c u)) := by
    rw [norm_mul]
    have hn : 0 ≤ (w u*(L^(-A)+c u)) :=
      mul_nonneg (hw u) (add_nonneg hPow (hc u))
    have hn2 : 0 ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef := by positivity
    calc
      _ ≤ (w u*(L^(-A)+c u))*
          (((u+2).divisors.card:ℝ)*Acoef*Bcoef) :=
        mul_le_mul (hU u) (hF u) (norm_nonneg _) hn
      _ = _ := by ring
  unfold parityOriginalShiftTwoBilinearOutsideEBox434
  calc
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y, ‖Q u * F u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        Acoef*Bcoef*(w u*((u+2).divisors.card:ℝ)*(L^(-A)+c u)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact hterm u
    _ = Acoef*Bcoef *
        (∑ u ∈ Finset.Ioc 0 Y, w u*((u+2).divisors.card:ℝ)*(L^(-A)+c u)) := by
      rw [Finset.mul_sum]
    _ = Acoef*Bcoef *
        (L^(-A)*(∑ u ∈ Finset.Ioc 0 Y,
          w u*((u+2).divisors.card:ℝ)) +
         t*(∑ u ∈ Finset.Ioc 0 Y,
          (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
            else w u)*((u+2).divisors.card:ℝ))) := by
      congr 1
      have hSplit (u : ℕ) :
          w u * ((u+2).divisors.card:ℝ) * (L^(-A)+c u) =
          L^(-A)*(w u*((u+2).divisors.card:ℝ)) +
          t*((if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
              else w u)*((u+2).divisors.card:ℝ)) := by
        by_cases hp : parityOriginalPhysicalPcapBeta434 beta L u
        · simp [c,hp]
          ring
        · simp [c,hp]
          ring
      conv_lhs =>
        arg 2
        ext u
        rw [hSplit u]
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalW1PointwisePolylog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Fixed original P-group mass floor, with TRUE moving original group
family, independent of eventual Type II accuracy A. -/
def parityOriginalW1GroupFloor434 : ℝ := Real.log (12/11:ℝ)/4

/-- Fixed exponent for genuine source W1; we deliberately retain the
conservative native `k*2^-(k-1)≤2` and full group count `≤4log L`.
This is sufficient for arbitrary inverse-log Rankin savings. -/
def parityOriginalW1PolylogExponent434 : ℝ :=
  4*Real.log (2/parityOriginalW1GroupFloor434)

/-- Every full source W1 has the exact original all-P-group pointwise
bound `(2/ν)^#groups`, where ν is the REAL group reciprocal mass floor.
No replacement by a Q weight or an assumed W1≤1 bound. -/
theorem parity_original_actual_W1_pointwise_group_floor434
    (L : ℝ)
    (hFloor : ∀ g : sourceOriginalPAllGroupType 20 L,
      parityOriginalW1GroupFloor434 ≤
      ∑ p ∈ sourceOriginalPAllActualBands 20 L g, (p:ℝ)⁻¹)
    (u : ℕ) :
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u ≤
      (2/parityOriginalW1GroupFloor434)^
        (Fintype.card (sourceOriginalPAllGroupType 20 L)) := by
  have hν : 0 < parityOriginalW1GroupFloor434 := by
    unfold parityOriginalW1GroupFloor434
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  unfold sourceOriginalW1
  calc
    _ ≤ ∏ _g : sourceOriginalPAllGroupType 20 L,
      2/parityOriginalW1GroupFloor434 := by
      apply Finset.prod_le_prod₀
      · intro g hg
        unfold shiftTwoOriginalGroupFactor
        positivity
      · intro g hg
        unfold shiftTwoOriginalGroupFactor
        have hV := hFloor g
        have hvp : 0 < ∑ p ∈ sourceOriginalPAllActualBands 20 L g,
            (p:ℝ)⁻¹ := hν.trans_le hV
        calc
          _ ≤ 2/(∑ p ∈ sourceOriginalPAllActualBands 20 L g, (p:ℝ)⁻¹) :=
            div_le_div_of_nonneg_right (source_half_mark_le_two _) hvp.le
          _ ≤ 2/parityOriginalW1GroupFloor434 :=
            div_le_div_of_nonneg_left (by norm_num) hν hV
    _ = _ := by simp [div_pow]

/-- Kernel-checked original Parity (1.4) polynomial-in-log majorant, with
a conservative fixed exponent instead of the sharper paper exponent 3.
The full actual moving group count is retained (including SMALL).
This bound is uniform in u and the later inverse-log precision. -/
theorem parity_eventually_original_actual_W1_pointwise_polylog434 :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℕ,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u ≤
        L^parityOriginalW1PolylogExponent434 := by
  filter_upwards [source_original_P_all_reciprocal_floor_eventually 20,
    eventually_ge_atTop (Real.exp (2:ℝ))] with L hFloor hL
  intro u
  have hν : 0 < parityOriginalW1GroupFloor434 := by
    unfold parityOriginalW1GroupFloor434
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  let C : ℝ := 2/parityOriginalW1GroupFloor434
  have hC : 0 < C := div_pos (by norm_num) hν
  have hCOne : 1 ≤ C := by
    dsimp [C,parityOriginalW1GroupFloor434]
    have hv : Real.log (12/11:ℝ) ≤ 1 := by
      have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<12/11)
      linarith
    apply (le_div_iff₀ hν).mpr
    dsimp [parityOriginalW1GroupFloor434] at *
    linarith
  have hGroup : ((Fintype.card (sourceOriginalPAllGroupType 20 L)):ℝ) ≤
      4*Real.log L := by
    simpa only [sourceOriginalPAllGroupType,Fintype.card_coe] using
      parity_original_all_group_indices_card_four434 20 L hL
  have hRaw := parity_original_actual_W1_pointwise_group_floor434 L hFloor u
  have hLogC : 0 ≤ Real.log C := Real.log_nonneg hCOne
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  calc
    _ ≤ C^(Fintype.card (sourceOriginalPAllGroupType 20 L)) := hRaw
    _ = C^((Fintype.card (sourceOriginalPAllGroupType 20 L):ℝ)) := by
      rw [Real.rpow_natCast]
    _ ≤ L^parityOriginalW1PolylogExponent434 := by
      rw [Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hLp]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hGroup hLogC
      dsimp [parityOriginalW1PolylogExponent434]
      change Real.log C * (Fintype.card (sourceOriginalPAllGroupType 20 L):ℝ) ≤
        Real.log L * (4*Real.log C)
      nlinarith [hh]
end Green64Analytic.Parity

end

end

/-! ## OriginalBetaShiftedPairTail -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Physical Ppart beta/4 Rankin tail controlled for the TRUE signed
shift z->z+s at BOTH ordinary-core endpoints. This is a quantitative
positive majorant for the original Parity (4.17) Cauchy source and is
UNIFORM over all integer shifts s with positive endpoints in (0,Y].
The first endpoint n must violate the actual beta/4 cap; the second
endpoint retains its ENTIRE original W1 and squared divisor cost.
No Fourier coefficient, alpha_m or character has been silently bounded. -/
theorem parity_eventually_original_beta_shifted_bad_first_W1_tau2_tail434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      ∀ (Y : ℕ) (S : Finset ℕ) (s : ℤ),
        1 ≤ Y → Real.log (Y:ℝ) ≤ 2*L →
        S ⊆ Finset.Ioc 0 Y →
        (∀ n∈S, 0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) →
        (∀ n∈S, ¬parityOriginalPhysicalPcapBeta434 beta L n) →
        (∑ n∈S, (n.divisors.card:ℝ)^2 *
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^2 *
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n *
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
            (((n:ℤ)+s).toNat)) ≤
          (Y:ℝ)*(3:ℝ)^128*L^(-A) := by
  let CW : ℝ := parityOriginalW1PolylogExponent434
  let Prec : ℝ := 2*A+3*CW+255
  filter_upwards [parity_eventually_original_actual_W1_pointwise_polylog434,
    parity_eventually_original_beta_physical_Pcap_discard_all_log434
      beta Prec hbeta,
    eventually_ge_atTop (Real.exp 2)] with L hW hTail hL
  refine ⟨hL,?_⟩
  intro Y S s hY hLog hSub hShift hBad
  let P := sourceOriginalPAllActualBands 20 L
  let w : ℕ → ℝ := sourceOriginalW1 P
  let a : ℕ → ℝ := fun n => (n.divisors.card:ℝ)^2*
    (((n:ℤ)+s).toNat.divisors.card:ℝ)^2
  have hLp : 0 < L := (Real.exp_pos 2).trans_le hL
  have hw0 (n : ℕ) : 0 ≤ w n := source_original_W1_nonneg P n
  have hcap (n : ℕ) : w n ≤ L^CW := hW n
  have hb (n : ℕ) (hn : n∈S) : (w n)^2 ≤ L^CW*w n := by
    nlinarith [mul_nonneg (hw0 n) (sub_nonneg.mpr (hcap n))]
  have hc (n : ℕ) (hn : n∈S) :
      0 ≤ w (((n:ℤ)+s).toNat) ∧
      w (((n:ℤ)+s).toNat) ≤ L^CW :=
    ⟨hw0 _,hcap _⟩
  have hTailSub : S ⊆ (Finset.Ioc 0 Y).filter
      (fun n => ⌊Real.exp ((beta/4)*L)⌋₊ <
        sourceOriginalPPrimePart
          (Finset.univ.biUnion P) n) := by
    intro n hn
    have hFail := hBad n hn
    unfold parityOriginalPhysicalPcapBeta434 at hFail
    exact Finset.mem_filter.mpr ⟨hSub hn,by
      change ⌊Real.exp ((beta/4)*L)⌋₊ <
        sourceOriginalPPrimePart (sourceNativeOriginalG434 20 L) n
      exact Nat.lt_of_not_ge hFail⟩
  have hMass : (∑ n∈S, w n) ≤ (Y:ℝ)*L^(-Prec) := by
    have hExact := parity_actual_original_beta_physical_Pcap_discard_exact434 beta L Y
    have hFilt : (∑ n∈S, w n) ≤
        ∑ n ∈ (Finset.Ioc 0 Y).filter
          (fun n => ⌊Real.exp ((beta/4)*L)⌋₊ <
            sourceOriginalPPrimePart (Finset.univ.biUnion P) n), w n :=
      Finset.sum_le_sum_of_subset_of_nonneg hTailSub (by
        intro n hn hnot; exact hw0 n)
    change (∑ n∈S, w n) ≤ _
    exact hFilt.trans (hExact.symm ▸ hTail Y)
  have hYR : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY
  have hbase : 0 ≤ 1+Real.log (Y:ℝ) := by
    have hh := Real.log_nonneg hYR
    linarith
  have hlog3 : 1+Real.log (Y:ℝ) ≤ 3*L := by
    have hL1 : 1≤L := by linarith [(Real.add_one_le_exp 2)]
    linarith
  have hmoment : (∑ n∈S,(a n)^2) ≤
      (Y:ℝ)*(3:ℝ)^255*L^(255:ℝ) := by
    have hm := parity_translated_tau_four_product_sum434 S Y s hSub hShift
    have heq : (∑ n∈S,(a n)^2) =
        ∑ n∈S,(n.divisors.card:ℝ)^4*
        (((n:ℤ)+s).toNat.divisors.card:ℝ)^4 := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [a]
      ring
    rw [heq]
    calc
      _ ≤ (Y:ℝ)*(1+Real.log (Y:ℝ))^255 := hm
      _ ≤ (Y:ℝ)*(3*L)^255 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hlog3 255)
          (Nat.cast_nonneg Y)
      _ = _ := by
        rw [show L^(255:ℝ)=L^(255:ℕ) from Real.rpow_natCast L 255,mul_pow]
        ring
  have hCS := parity_higher_mark_tail_cauchy434 S a w
    (fun n => w (((n:ℤ)+s).toNat)) w
    ((Y:ℝ)*(3:ℝ)^255*L^(255:ℝ)) (L^CW) (L^CW)
    ((Y:ℝ)*L^(-Prec))
    (by positivity) (by positivity) (by positivity)
    hb hc hmoment hMass
  have hpower : L^(255:ℝ)*(L^CW)^2*L^CW*L^(-Prec)=
      (L^(-A))^2 := by
    simp only [pow_two,←Real.rpow_add hLp]
    congr 1
    dsimp [Prec]
    ring
  have hright : ((Y:ℝ)*(3:ℝ)^255*L^(255:ℝ))*(L^CW)^2*
      L^CW*((Y:ℝ)*L^(-Prec)) =
      (Y:ℝ)^2*(3:ℝ)^255*(L^(-A))^2 := by
    calc
      _ = (Y:ℝ)^2*(3:ℝ)^255*(L^(255:ℝ)*(L^CW)^2*L^CW*L^(-Prec)) := by ring
      _ = _ := by rw [hpower]
  rw [hright] at hCS
  have hconst : (3:ℝ)^255 ≤ ((3:ℝ)^128)^2 := by norm_num
  have hsquare : (∑ n∈S,a n*w n*w (((n:ℤ)+s).toNat))^2 ≤
      ((Y:ℝ)*(3:ℝ)^128*L^(-A))^2 := by
    calc
      _ ≤ (Y:ℝ)^2*(3:ℝ)^255*(L^(-A))^2 := hCS
      _ ≤ (Y:ℝ)^2*((3:ℝ)^128)^2*(L^(-A))^2 := by gcongr
      _ = _ := by ring
  have hsum0 : 0 ≤ ∑ n∈S,a n*w n*w (((n:ℤ)+s).toNat) := by
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (mul_nonneg (by dsimp [a];positivity) (hw0 n)) (hw0 _)
  exact (sq_le_sq₀ hsum0 (by positivity)).mp hsquare
end Green64Analytic.Parity

end

end

/-! ## OriginalBetaShiftedPairBoth -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18500000

/-- The same source beta/4 Rankin saving when the OTHER original
shifted physical endpoint z+s has a large original Ppart. The full
positive original marked W1(z) W1(z+s) and BOTH true divisor-square
costs remain; the reindexing uses the signed integral shift and its
inverse, not a monotonicity assumption about complex correlations. -/
theorem parity_eventually_original_beta_shifted_bad_second_W1_tau2_tail434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      ∀ (Y : ℕ) (S : Finset ℕ) (s : ℤ),
        1 ≤ Y → Real.log (Y:ℝ) ≤ 2*L →
        S ⊆ Finset.Ioc 0 Y →
        (∀ n∈S, 0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) →
        (∀ n∈S, ¬parityOriginalPhysicalPcapBeta434 beta L
          (((n:ℤ)+s).toNat)) →
        (∑ n∈S, (n.divisors.card:ℝ)^2 *
          (((n:ℤ)+s).toNat.divisors.card:ℝ)^2 *
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n *
          sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
            (((n:ℤ)+s).toNat)) ≤
          (Y:ℝ)*(3:ℝ)^128*L^(-A) := by
  filter_upwards [parity_eventually_original_beta_shifted_bad_first_W1_tau2_tail434
    beta A hbeta] with L h
  refine ⟨h.1,?_⟩
  intro Y S s hY hLog hSub hShift hBad
  let f : ℕ → ℕ := fun n => ((n:ℤ)+s).toNat
  let S' : Finset ℕ := S.image f
  have hfpos (n : ℕ) (hn : n∈S) : 0 < (n:ℤ)+s := (hShift n hn).1
  have hfback (n : ℕ) (hn : n∈S) : (((f n:ℤ)-s).toNat) = n := by
    have hnp := hfpos n hn
    dsimp [f]
    omega
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro n hn m hm heq
    have hnp := hfpos n hn
    have hmp := hfpos m hm
    dsimp [f] at heq
    omega
  have hSub' : S' ⊆ Finset.Ioc 0 Y := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    have hshift := hShift n hn
    dsimp [f]
    rw [Finset.mem_Ioc]
    omega
  have hShift' : ∀ m∈S',0<(m:ℤ)-s ∧ (m:ℤ)-s≤(Y:ℤ) := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    have hshift := hShift n hn
    have hpos : 0 < n := (Finset.mem_Ioc.mp (hSub hn)).1
    have hle : n ≤ Y := (Finset.mem_Ioc.mp (hSub hn)).2
    dsimp [f]
    omega
  have hBad' : ∀ m∈S', ¬parityOriginalPhysicalPcapBeta434 beta L m := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    exact hBad n hn
  have hBound := h.2 Y S' (-s) hY hLog hSub' hShift' hBad'
  let W : ℕ → ℝ := sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
  let R : ℕ → ℝ := fun n =>
    (n.divisors.card:ℝ)^2 * (f n).divisors.card^2 * W n * W (f n)
  let R' : ℕ → ℝ := fun m =>
    (m.divisors.card:ℝ)^2 * (((m:ℤ)-s).toNat.divisors.card:ℝ)^2 *
    W m * W (((m:ℤ)-s).toNat)
  have heq (n : ℕ) (hn : n∈S) : R' (f n)=R n := by
    dsimp [R,R']
    rw [hfback n hn]
    ring
  have hSum : (∑ m ∈ S', R' m) = ∑ n∈S,R n := by
    unfold S'
    rw [Finset.sum_image (by
      intro n hn m hm heq
      exact hinj hn hm heq)]
    apply Finset.sum_congr rfl
    intro n hn
    exact heq n hn
  change (∑ n∈S,R n) ≤ _
  rw [←hSum]
  exact hBound

/-- Complete actual beta/4 original physical TWO-ENDPOINT discarded
Rankin error for each signed k, on any real original Z-dyad satisfying
log Y≤2L. The discarded pair is defined using both genuine moving P
valuations, without pretending an old 1/44 cap is equivalent. The
source error is bounded by shifted divisor SQUARE moments and full
original W1 at BOTH endpoints, uniformly in s including s=2k.
This is a positive error MAJORANT, not yet the whole Parity(4.17) complex
cofactor transfer (which still needs a pointwise domination of cores). -/
theorem parity_eventually_original_beta_shifted_pair_W1_tau2_tail434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, Real.exp 2 ≤ L ∧
      ∀ (Y : ℕ) (S : Finset ℕ) (s : ℤ),
        1 ≤ Y → Real.log (Y:ℝ) ≤ 2*L →
        S ⊆ Finset.Ioc 0 Y →
        (∀ n∈S, 0<(n:ℤ)+s ∧ (n:ℤ)+s≤(Y:ℤ)) →
        (∑ n∈S,
          (if parityOriginalPhysicalPcapBeta434 beta L n ∧
              parityOriginalPhysicalPcapBeta434 beta L (((n:ℤ)+s).toNat)
           then (0:ℝ)
           else (n.divisors.card:ℝ)^2 *
             (((n:ℤ)+s).toNat.divisors.card:ℝ)^2 *
             sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n *
             sourceOriginalW1 (sourceOriginalPAllActualBands 20 L)
               (((n:ℤ)+s).toNat))) ≤
          2*(Y:ℝ)*(3:ℝ)^128*L^(-A) := by
  filter_upwards [parity_eventually_original_beta_shifted_bad_first_W1_tau2_tail434
    beta A hbeta,
    parity_eventually_original_beta_shifted_bad_second_W1_tau2_tail434
    beta A hbeta] with L hFirst hSecond
  refine ⟨hFirst.1,?_⟩
  intro Y S s hY hLog hSub hShift
  let G : ℕ → ℝ := fun n =>
    (n.divisors.card:ℝ)^2 *
      (((n:ℤ)+s).toNat.divisors.card:ℝ)^2 *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) n *
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) (((n:ℤ)+s).toNat)
  let S1 : Finset ℕ := S.filter (fun (n : ℕ) => ¬parityOriginalPhysicalPcapBeta434 beta L n)
  let S2 : Finset ℕ := S.filter (fun (n : ℕ) => ¬parityOriginalPhysicalPcapBeta434 beta L
      (((n:ℤ)+s).toNat))
  have hFirstBound : (∑ n∈S1,G n) ≤ (Y:ℝ)*(3:ℝ)^128*L^(-A) := by
    apply hFirst.2 Y S1 s hY hLog
    · intro n hn; exact hSub (Finset.mem_filter.mp hn).1
    · intro n hn; exact hShift n (Finset.mem_filter.mp hn).1
    · intro n hn; exact (Finset.mem_filter.mp hn).2
  have hSecondBound : (∑ n∈S2,G n) ≤ (Y:ℝ)*(3:ℝ)^128*L^(-A) := by
    apply hSecond.2 Y S2 s hY hLog
    · intro n hn; exact hSub (Finset.mem_filter.mp hn).1
    · intro n hn; exact hShift n (Finset.mem_filter.mp hn).1
    · intro n hn; exact (Finset.mem_filter.mp hn).2
  have hnonneg (n : ℕ) : 0 ≤ G n := by
    dsimp [G]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (source_original_W1_nonneg _ _))
      (source_original_W1_nonneg _ _)
  calc
    (∑ n∈S, if parityOriginalPhysicalPcapBeta434 beta L n ∧
        parityOriginalPhysicalPcapBeta434 beta L (((n:ℤ)+s).toNat)
        then (0:ℝ) else G n) ≤
      ∑ n∈S, ((if parityOriginalPhysicalPcapBeta434 beta L n then (0:ℝ)
        else G n) +
        (if parityOriginalPhysicalPcapBeta434 beta L (((n:ℤ)+s).toNat)
        then (0:ℝ) else G n)) := by
          apply Finset.sum_le_sum
          intro n hn
          by_cases h1 : parityOriginalPhysicalPcapBeta434 beta L n <;>
            by_cases h2 : parityOriginalPhysicalPcapBeta434 beta L
              (((n:ℤ)+s).toNat) <;>
            simp [h1,h2,hnonneg n] <;> linarith [hnonneg n]
    _ = (∑ n∈S1,G n)+(∑ n∈S2,G n) := by
      rw [Finset.sum_add_distrib]
      simp only [S1,S2, Finset.sum_filter, ite_not]
    _ ≤ 2*(Y:ℝ)*(3:ℝ)^128*L^(-A) := by
      linarith [hFirstBound,hSecondBound]
end Green64Analytic.Parity

end

end

/-! ## OriginalReservedHFullPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- True original Parity(4.9) physical v-side coefficient bound for the
literal reserved-Q prime H(v*) convolution, P-group W1 and original
multiplicity-counted odd projector:

`|a_v^physical(v)| <= L^C_W1 * tau(v*)`.

The exponent C_W1 is the fixed SOURCE original-group exponent, entirely
independent of later K0, Fourier moment H, beta cutoff accuracy and
reserved Q-mark. This follows from the native H divisor count and
verified ORIGINAL W1 pointwise geometry; it does NOT assume the
manuscript epsilon(v) sign equals the odd projector. -/
theorem parity_eventually_original_reserved_physical_aV_polylog_tau434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (K : Finset ℕ) (alpha : ℕ → ℂ)
        (q : ℕ) (χ : DirichletCharacter ℂ q)
        (σ₀ σ₁ σ ρ : ℝ) (vStar v : ℕ), 0 < vStar →
      ‖parityOriginalReservedPhysicalAV434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ K alpha
          q χ σ₀ σ₁ σ ρ vStar v‖ ≤
        L^parityOriginalW1PolylogExponent434 *
          (vStar.divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_gt_atTop (0:ℝ)] with L hW hLp
  intro band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v hvStar
  have hV := parity_original_reserved_physical_aV_norm_le_W1_tau434
    (sourceOriginalLiteralDepth 20 L) L hLp band slot δ ξ K alpha
    q χ σ₀ σ₁ σ ρ vStar v hvStar
  have hWv := hW v
  have hTau : 0 ≤ (vStar.divisors.card:ℝ) := Nat.cast_nonneg _
  exact hV.trans (mul_le_mul_of_nonneg_right hWv hTau)

/-- The SAME historical Parity(4.8) literal reserved-prime × skipped-Q
source DOUBLE SUM with all actual factorial/odd-parity/P weights obeys
the uniform Parity(4.9)-type `L^C_W1 tau(v*)` source bound. -/
theorem parity_eventually_original_reserved_physical_double_sum_polylog_tau434 :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (K : Finset ℕ) (alpha : ℕ → ℂ)
        (q : ℕ) (χ : DirichletCharacter ℂ q)
        (σ₀ σ₁ σ ρ : ℝ) (vStar v : ℕ), 0 < vStar →
      ‖parityOriginalReservedPhysicalSourceDoubleSum434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ K alpha
          q χ σ₀ σ₁ σ ρ vStar v‖ ≤
        L^parityOriginalW1PolylogExponent434 *
          (vStar.divisors.card:ℝ) := by
  filter_upwards [parity_eventually_original_reserved_physical_aV_polylog_tau434]
    with L h
  intro band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v hvStar
  rw [parity_original_reserved_physical_double_sum_eq_aV434]
  exact h band slot δ ξ K alpha q χ σ₀ σ₁ σ ρ vStar v hvStar
end Green64Analytic.Parity

end

end

/-! ## OriginalWeightedDivisorCauchy -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Exact Cauchy before the original Type II Cauchy: multiplying a
Rankin-small nonnegative source weight with a shifted divisor count
costs only its second moment and a pointwise weight bound. In particular
no pointwise τ(u+2)≤polylog is silently assumed. -/
theorem parity_original_weighted_divisor_square_le_mass_moment434
    (S : Finset ℕ) (w t : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hw : ∀ u ∈ S, 0 ≤ w u ∧ w u ≤ W) :
    (∑ u ∈ S, w u * t u)^2 ≤
      (∑ u ∈ S, w u) * (W*(∑ u ∈ S, (t u)^2)) := by
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun u => Real.sqrt (w u))
    (fun u => Real.sqrt (w u)*t u)
  have hL : (∑ u ∈ S, Real.sqrt (w u) *
       (Real.sqrt (w u)*t u)) = (∑ u ∈ S, w u * t u) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [←mul_assoc, Real.mul_self_sqrt (hw u hu).1]
  have hA : (∑ u ∈ S, (Real.sqrt (w u))^2) = ∑ u ∈ S, w u := by
    apply Finset.sum_congr rfl
    intro u hu
    exact Real.sq_sqrt (hw u hu).1
  have hB : (∑ u ∈ S, (Real.sqrt (w u)*t u)^2) ≤
      W*(∑ u ∈ S, (t u)^2) := by
    calc
      _ = ∑ u ∈ S, w u*(t u)^2 := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [mul_pow, Real.sq_sqrt (hw u hu).1]
      _ ≤ ∑ u ∈ S, W*(t u)^2 := by
        apply Finset.sum_le_sum
        intro u hu
        exact mul_le_mul_of_nonneg_right (hw u hu).2 (sq_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [hL, hA] at hCauchy
  exact hCauchy.trans (mul_le_mul_of_nonneg_left hB
    (Finset.sum_nonneg (fun u hu => (hw u hu).1)))
end Green64Analytic.Parity

end

end

/-! ## OriginalShiftedDivisorRankinMoment -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- The TRUE shifted h=-2 divisor square moment is bounded by the
actual fourth divisor moment with the original u+2 shift. No pointwise
polylog divisor assumption, squarefree simplification or missing shift. -/
theorem parity_original_shift_two_divisor_square_moment434
    (Y : ℕ) :
    (∑ u ∈ Finset.Ioc 0 Y, (((u+2).divisors.card:ℝ)^2)) ≤
      ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^15 := by
  let S := Finset.Ioc 0 Y
  have hS : ∀ u ∈ S, 0 < (u:ℤ)+(2:ℤ) ∧
      (u:ℤ)+2 ≤ ((Y+2:ℕ):ℤ) := by
    intro u hu
    have hu' := Finset.mem_Ioc.mp hu
    omega
  have hM := parity_translated_tau_four_sum434 S (Y+2) 2 hS
  have hPart : (∑ u ∈ S, (((u+2).divisors.card:ℝ)^2)) ≤
      (∑ u ∈ S, (((u+2).divisors.card:ℝ)^4)) := by
    apply Finset.sum_le_sum
    intro u hu
    have hn : 0 < u+2 := by omega
    have hmem : 1 ∈ (u+2).divisors := Nat.mem_divisors.mpr
      ⟨one_dvd _, by omega⟩
    have hCard : (1:ℝ) ≤ ((u+2).divisors.card:ℝ) := by
      have hc := Finset.card_pos.mpr ⟨1,hmem⟩
      exact_mod_cast hc
    have hsq : (1:ℝ) ≤ ((u+2).divisors.card:ℝ)^2 := by
      nlinarith
    have hnonneg := mul_nonneg (sq_nonneg ((u+2).divisors.card:ℝ))
      (sub_nonneg.mpr hsq)
    nlinarith [hnonneg]
  have hEq :
      (∑ u ∈ S, (((u+2).divisors.card:ℝ)^4)) =
      (∑ u ∈ S, ((((u:ℤ)+(2:ℤ)).toNat.divisors.card:ℝ)^4)) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hCast : ((u:ℤ)+(2:ℤ)).toNat = u+2 := by omega
    rw [hCast]
  rw [hEq] at hPart
  exact hPart.trans hM


/-- The actual original β/4 discarded W1 mass, weighted by the TRUE
shifted divisor τ(u+2), has its complete Cauchy budget from native
P Rankin mass, source pointwise W1 and shifted fourth divisor moment.
It is not yet an asymptotic error estimate: that follows by choosing
Rankin precision after the fixed W1/divisor exponents. -/
theorem parity_original_beta_discarded_W1_shifted_tau_cauchy434
    (beta L : ℝ) (hL : 0 < L)
    (hW : ∀ u : ℕ,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u ≤
        L^parityOriginalW1PolylogExponent434)
    (Y : ℕ) :
    (∑ u ∈ Finset.Ioc 0 Y,
      (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
        ((u+2).divisors.card:ℝ))^2 ≤
      (∑ u ∈ Finset.Ioc 0 Y,
        if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
      (L^parityOriginalW1PolylogExponent434 *
        (((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^15)) := by
  let w : ℕ → ℝ := fun u =>
    if parityOriginalPhysicalPcapBeta434 beta L u then 0
    else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let t : ℕ → ℝ := fun u => ((u+2).divisors.card:ℝ)
  have hWNonneg : 0 ≤ L^parityOriginalW1PolylogExponent434 :=
    Real.rpow_nonneg (le_of_lt hL) _
  have hw (u : ℕ) (hu : u ∈ Finset.Ioc 0 Y) :
      0 ≤ w u ∧ w u ≤ L^parityOriginalW1PolylogExponent434 := by
    dsimp only [w]
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simp [hc,hWNonneg]
    · simpa only [if_neg hc] using
        (show 0 ≤ sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u ∧
             sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u ≤
               L^parityOriginalW1PolylogExponent434 from
         ⟨source_original_W1_nonneg _ _,hW u⟩)
  have hC := parity_original_weighted_divisor_square_le_mass_moment434
    (Finset.Ioc 0 Y) w t
    (L^parityOriginalW1PolylogExponent434) hWNonneg hw
  have hT := parity_original_shift_two_divisor_square_moment434 Y
  dsimp only [w,t] at hC
  exact hC.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hT hWNonneg)
    (Finset.sum_nonneg (by intro u hu; by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u <;> simp [hc,source_original_W1_nonneg])))
end Green64Analytic.Parity

end

end

/-! ## OriginalShiftedTauScale -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Source `u in [exp L,2exp L]`, shifted h=-2: the actual fourth
moment controls the genuine translated second divisor moment with
only a fixed factor L^16. The huge explicit start L≥3^16 is harmless
and avoids hiding any fixed asymptotic constants. -/
theorem parity_original_shift_two_tau_square_original_x_scale434
    (L : ℝ) (hL : (3:ℝ)^16 ≤ L) :
    (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (((u+2).divisors.card:ℝ)^2)) ≤
      Real.exp L * L^16 := by
  let Y := ⌊2*Real.exp L⌋₊
  have hLp : 0 < L := by nlinarith
  have hExp : 0 < Real.exp L := Real.exp_pos _
  have hFloor : (Y:ℝ) ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  have hTwo : 2 ≤ Real.exp L := by
    have hExpLower := Real.add_one_le_exp L
    nlinarith
  have hY : ((Y+2:ℕ):ℝ) ≤ 3*Real.exp L := by
    push_cast
    linarith
  have hYPos : 0 < ((Y+2:ℕ):ℝ) := by exact_mod_cast (show 0<Y+2 by omega)
  have hLog : Real.log ((Y+2:ℕ):ℝ) ≤ Real.log 3 + L := by
    have hh := Real.log_le_log hYPos hY
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.exp_ne_zero L), Real.log_exp] at hh
    exact hh
  have hlog3 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have hYone : 1 ≤ ((Y+2:ℕ):ℝ) := by exact_mod_cast (show 1≤Y+2 by omega)
  have hbase : 0 ≤ 1+Real.log ((Y+2:ℕ):ℝ) := by
    have hh := Real.log_nonneg hYone
    linarith
  have hLge1 : 1 ≤ L := by nlinarith
  have hLogBound : 1+Real.log ((Y+2:ℕ):ℝ) ≤ 3*L := by
    linarith
  have hMoment := parity_original_shift_two_divisor_square_moment434 Y
  have hExpNonneg : 0 ≤ Real.exp L := hExp.le
  calc
    _ ≤ ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^15 := hMoment
    _ ≤ (3*Real.exp L)*(3*L)^15 :=
      mul_le_mul hY (pow_le_pow_left₀ hbase hLogBound 15)
        (pow_nonneg (by positivity) _) (by positivity)
    _ = (3:ℝ)^16*Real.exp L*L^15 := by ring
    _ ≤ L*Real.exp L*L^15 := by
      have hh := mul_le_mul_of_nonneg_right hL
        (mul_nonneg hExpNonneg (pow_nonneg hLp.le 15))
      nlinarith
    _ = Real.exp L*L^16 := by ring

theorem parity_original_shift_two_tau_four_envelope_original_x_scale434
    (L : ℝ) (hL : (3:ℝ)^16 ≤ L) :
    ((⌊2*Real.exp L⌋₊+2:ℕ):ℝ)*
      (1+Real.log ((⌊2*Real.exp L⌋₊+2:ℕ):ℝ))^15 ≤
      Real.exp L * L^16 := by
  let Y := ⌊2*Real.exp L⌋₊
  have hLp : 0 < L := by nlinarith
  have hExp : 0 < Real.exp L := Real.exp_pos _
  have hFloor : (Y:ℝ) ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  have hTwo : 2 ≤ Real.exp L := by
    have hExpLower := Real.add_one_le_exp L
    nlinarith
  have hY : ((Y+2:ℕ):ℝ) ≤ 3*Real.exp L := by
    push_cast
    linarith
  have hYPos : 0 < ((Y+2:ℕ):ℝ) := by exact_mod_cast (show 0<Y+2 by omega)
  have hLog : Real.log ((Y+2:ℕ):ℝ) ≤ Real.log 3 + L := by
    have hh := Real.log_le_log hYPos hY
    rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (Real.exp_ne_zero L), Real.log_exp] at hh
    exact hh
  have hlog3 : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  have hYone : 1 ≤ ((Y+2:ℕ):ℝ) := by exact_mod_cast (show 1≤Y+2 by omega)
  have hbase : 0 ≤ 1+Real.log ((Y+2:ℕ):ℝ) := by
    have hh := Real.log_nonneg hYone
    linarith
  have hLge1 : 1 ≤ L := by nlinarith
  have hLogBound : 1+Real.log ((Y+2:ℕ):ℝ) ≤ 3*L := by
    linarith
  have hExpNonneg : 0 ≤ Real.exp L := hExp.le
  calc
    _ ≤ (3*Real.exp L)*(3*L)^15 :=
      mul_le_mul hY (pow_le_pow_left₀ hbase hLogBound 15)
        (pow_nonneg (by positivity) _) (by positivity)
    _ = (3:ℝ)^16*Real.exp L*L^15 := by ring
    _ ≤ L*Real.exp L*L^15 := by
      have hh := mul_le_mul_of_nonneg_right hL
        (mul_nonneg hExpNonneg (pow_nonneg hLp.le 15))
      nlinarith
    _ = Real.exp L*L^16 := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalRankinPrecision -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- Explicit safe order of precision in the ORIGINAL h=-2 bilinear
Rankin discard: after the fixed W1 source exponent C and true τ^4
moment budget 16, choose original Rankin accuracy 2A+C+20.
This verifies all resulting L powers for ANY real requested A;
no hidden adjustment of Pcap beta, reserved Q index or K0. -/
theorem parity_original_bilinear_Rankin_precision_budget434
    (L A : ℝ) (hL : (3:ℝ)^16 ≤ L) :
    2*L^(-(2*A+parityOriginalW1PolylogExponent434+20)) *
      L^parityOriginalW1PolylogExponent434 * L^16 ≤ (L^(-A))^2 := by
  let C := parityOriginalW1PolylogExponent434
  let D := 2*A+C+20
  have hLp : 0 < L := by nlinarith
  have h2 : 2 ≤ L := by nlinarith
  have hPow4 : 2 ≤ L^4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) h2 4
    norm_num at hp
    linarith
  have hSmall : 2*(L^4)⁻¹ ≤ 1 := by
    rw [←div_eq_mul_inv]
    exact (div_le_iff₀ (pow_pos hLp 4)).mpr (by linarith)
  have hFixed : L^(-D)*L^C*L^16 = L^(-2*A-4) := by
    calc
      _ = L^(-D+C)*L^16 := by rw [Real.rpow_add hLp]
      _ = L^(-D+C) * L^(16:ℝ) := by
        exact congrArg (fun z : ℝ => L^(-D+C)*z)
          (Real.rpow_natCast L 16).symm
      _ = L^(-D+C+16) := (Real.rpow_add hLp (-D+C) 16).symm
      _ = L^(-2*A-4) := by
        congr 1
        dsimp [D]
        ring
  have hSplit : L^(-2*A-4) = L^(-2*A)*(L^4)⁻¹ := by
    calc
      _ = L^(-2*A + (-4:ℝ)) := by ring
      _ = L^(-2*A)*L^(-4:ℝ) := Real.rpow_add hLp _ _
      _ = L^(-2*A)*(L^4)⁻¹ := by
        rw [Real.rpow_neg hLp.le]
        exact congrArg (fun z : ℝ => L^(-2*A)*z⁻¹)
          (Real.rpow_natCast L 4)
  have hSquare : (L^(-A))^2 = L^(-2*A) := by
    have h := Real.rpow_mul hLp.le (-A) (2:ℝ)
    have hNat : (L^(-A))^2 = (L^(-A))^(2:ℝ) :=
      (Real.rpow_natCast _ _).symm
    calc
      _ = (L^(-A))^(2:ℝ) := hNat
      _ = L^((-A)*2) := h.symm
      _ = L^(-2*A) := by congr 1; ring
  change 2*L^(-D)*L^C*L^16 ≤ (L^(-A))^2
  rw [show 2*L^(-D)*L^C*L^16 = 2*(L^(-D)*L^C*L^16) by ring,
    hFixed, hSplit, hSquare]
  have hPos : 0 ≤ L^(-2*A) := Real.rpow_nonneg hLp.le _
  calc
    _ = L^(-2*A)*(2*(L^4)⁻¹) := by ring
    _ ≤ L^(-2*A)*1 := mul_le_mul_of_nonneg_left hSmall hPos
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalW1ShiftedTauTotalMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 13000000

/-- Actual original Parity h=-2 shifted first divisor moment is bounded by
the true translated SECOND divisor moment. This is a literal
arithmetic fact τ(u+2)≥1, not a fabricated pointwise polylog τ bound. -/
theorem parity_original_shift_two_tau_first_le_second_moment434
    (Y : ℕ) :
    (∑ u ∈ Finset.Ioc 0 Y, ((u+2).divisors.card:ℝ)) ≤
      (∑ u ∈ Finset.Ioc 0 Y, (((u+2).divisors.card:ℝ)^2)) := by
  apply Finset.sum_le_sum
  intro u hu
  have hn : 0 < u+2 := by omega
  have hmem : 1 ∈ (u+2).divisors := Nat.mem_divisors.mpr
    ⟨one_dvd _, by omega⟩
  have hCard : (1:ℝ) ≤ ((u+2).divisors.card:ℝ) := by
    have hc := Finset.card_pos.mpr ⟨1,hmem⟩
    exact_mod_cast hc
  nlinarith [sq_nonneg (((u+2).divisors.card:ℝ)-1)]

/-- ORIGINAL P-W1(u) times TRUE shifted τ(u+2) has polynomial total
absolute factorisation mass over the real original u≤2exp L carrier.
The exponent C_W1+16 is fixed and K0-independent, from genuine source
W1 moving-group reciprocal floor and the translated fourth divisor
moment. This is the source absolute-mass input needed to combine the
Parity(4.6) Fourier tail with arithmetic before Type II Cauchy. -/
theorem parity_eventually_original_W1_shifted_tau_total_mass_polylog434 :
    ∀ᶠ L : ℝ in atTop,
      (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) ≤
        Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16 := by
  filter_upwards [parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_ge_atTop ((3:ℝ)^16)] with L hW hL
  let Y := ⌊2*Real.exp L⌋₊
  have hLp : 0 < L := by nlinarith
  have hNonneg : 0 ≤ L^parityOriginalW1PolylogExponent434 :=
    Real.rpow_nonneg hLp.le _
  have hFirst := parity_original_shift_two_tau_first_le_second_moment434 Y
  have hSecond := parity_original_shift_two_tau_square_original_x_scale434 L hL
  have hBound :
      (∑ u ∈ Finset.Ioc 0 Y,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) ≤
      (∑ u ∈ Finset.Ioc 0 Y,
        L^parityOriginalW1PolylogExponent434 * ((u+2).divisors.card:ℝ)) := by
    apply Finset.sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_right (hW u) (Nat.cast_nonneg _)
  calc
    _ ≤ (∑ u ∈ Finset.Ioc 0 Y,
        L^parityOriginalW1PolylogExponent434 * ((u+2).divisors.card:ℝ)) := hBound
    _ = L^parityOriginalW1PolylogExponent434 *
        (∑ u ∈ Finset.Ioc 0 Y, ((u+2).divisors.card:ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ L^parityOriginalW1PolylogExponent434 *
        (∑ u ∈ Finset.Ioc 0 Y, (((u+2).divisors.card:ℝ)^2)) :=
          mul_le_mul_of_nonneg_left hFirst hNonneg
    _ ≤ L^parityOriginalW1PolylogExponent434 * (Real.exp L*L^16) :=
          mul_le_mul_of_nonneg_left hSecond hNonneg
    _ = Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16 := by
          ring
end Green64Analytic.Parity

end

end

/-! ## OriginalB590ArithmeticFourierTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Exact original h=-2 SOURCE Fourier tail requested precision AFTER
paying the independently verified full W1(u)·τ(u+2) arithmetic mass:
requested A' = A+C_W1+16. No adjustment to original B590 CF or K0. -/
def parityOriginalB590ArithmeticFourierTailAccuracy434 (A : ℝ) : ℝ :=
  A + parityOriginalW1PolylogExponent434 + 16

/-- Algebraic cancellation of the true W1 polylog mass and shifted
divisor fourth-moment cost with original B590 Fourier inverse-log
tail. The power identity is valid for arbitrary real requested A. -/
theorem parity_original_B590_arithmetic_fourier_power_cancel434
    (L A : ℝ) (hL : 0 < L) :
    L^parityOriginalW1PolylogExponent434 * L^16 *
      L^(-parityOriginalB590ArithmeticFourierTailAccuracy434 A) = L^(-A) := by
  have h16 : L^16 = L^(16:ℝ) := (Real.rpow_natCast L 16).symm
  rw [h16]
  calc
    L^parityOriginalW1PolylogExponent434 * L^(16:ℝ) *
        L^(-parityOriginalB590ArithmeticFourierTailAccuracy434 A) =
      Real.exp (Real.log L*parityOriginalW1PolylogExponent434) *
      Real.exp (Real.log L*16) *
      Real.exp (Real.log L*(-parityOriginalB590ArithmeticFourierTailAccuracy434 A)) := by
        rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hL,
          Real.rpow_def_of_pos hL]
    _ = Real.exp (Real.log L*(-A)) := by
      rw [←Real.exp_add, ←Real.exp_add]
      congr 1
      unfold parityOriginalB590ArithmeticFourierTailAccuracy434
      ring
    _ = L^(-A) := (Real.rpow_def_of_pos hL _).symm

/-- SOURCE Parity §4.2 actual Fourier cutoff |ξ_i|>L costs arbitrary
pre-Cauchy O_A(exp L L^-A) AFTER paying the full original W1/P-parity
and all literal h=-2 `mn=u+2` factorization divisors, not only the
unweighted Schwartz Fourier mass. The result is the product of the
exact independently verified original absolute arithmetic envelope
`sum W1(u)τ(u+2)` and the TRUE 2^N×N original Fourier frequency-tail
union; no invented τ pointwise bound or CH^N growth.
It is a *quantitative source error BUDGET*: the further assertion that
a particular truncated full historical e/v Fourier integral has a
difference bounded by this product still needs an exact multi-dimensional
B590 Fourier product-measure Fubini and a weighted triangle inequality. -/
theorem parity_eventually_original_B590_arithmetic_fourier_tail_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20),
      let N : ℕ := (sourceOrderedLabels 20
        (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
        band slot).length
      ((∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) *
       (∑ δ : Fin N → Bool, ∑ i : Fin N,
        parityOriginalB590OneCoordinateFourierTail434 δ i L)) ≤
        Real.exp L * L^(-A) := by
  let A' := parityOriginalB590ArithmeticFourierTailAccuracy434 A
  filter_upwards [parity_eventually_original_W1_shifted_tau_total_mass_polylog434,
    parity_eventually_original_B590_actual_fourier_tail_all_log434 A',
    eventually_ge_atTop (1:ℝ)] with L hMass hTail hL
  intro band slot
  dsimp only
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
        ((u+2).divisors.card:ℝ)
  let N := (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length
  let T : ℝ := ∑ δ : Fin N → Bool, ∑ i : Fin N,
    parityOriginalB590OneCoordinateFourierTail434 δ i L
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hMN : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hRp : 0 ≤ L^(-A') := Real.rpow_nonneg hLp.le _
  have hBound := hTail band slot
  have hFactor : M*T ≤
      (Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16) * L^(-A') := by
    calc
      M*T ≤ M*L^(-A') := mul_le_mul_of_nonneg_left hBound hMN
      _ ≤ (Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16) *
            L^(-A') := mul_le_mul_of_nonneg_right hMass hRp
  calc
    _ ≤ (Real.exp L * L^parityOriginalW1PolylogExponent434 * L^16) * L^(-A') := hFactor
    _ = Real.exp L *
        (L^parityOriginalW1PolylogExponent434 * L^16 * L^(-A')) := by ring
    _ = Real.exp L * L^(-A) := by
      rw [parity_original_B590_arithmetic_fourier_power_cancel434 L A hLp]
end Green64Analytic.Parity

end

end

/-! ## OriginalWeightedShiftedRankinAllLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- FULL original Parity §4.1 weighted pre-Cauchy Rankin bound with true
h=-2 shifted divisor factor τ(u+2), uniformly over all u≤2exp L.
No pointwise τ≤L^C assumption: a true translated fourth divisor
moment and the original moving W1≤L^C are interpolated by finite
Cauchy with the arbitrary-precision physical beta/4 Rankin tail.
The accuracy chosen inside Rankin is `2A+C_W1+20`, AFTER geometry and
beta are fixed. This is a genuine unconditional all-log saving. -/
theorem parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
    (beta A : ℝ) (hbeta : 0 < beta) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^16 ≤ L ∧
      (∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
        (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
          else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
          ((u+2).divisors.card:ℝ)) ≤
      Real.exp L * L^(-A) := by
  let D := 2*A+parityOriginalW1PolylogExponent434+20
  filter_upwards [parity_eventually_original_beta_physical_Pcap_discard_all_log434
      beta D hbeta,
    parity_eventually_original_actual_W1_pointwise_polylog434,
    eventually_ge_atTop ((3:ℝ)^16)] with L hRankin hW hL
  refine ⟨hL,?_⟩
  let Y := ⌊2*Real.exp L⌋₊
  let w : ℕ → ℝ := fun u =>
    if parityOriginalPhysicalPcapBeta434 beta L u then 0
    else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let t : ℕ → ℝ := fun u => ((u+2).divisors.card:ℝ)
  let M := ∑ u ∈ Finset.Ioc 0 Y, w u
  let N := ∑ u ∈ Finset.Ioc 0 Y, w u*t u
  let V := ((Y+2:ℕ):ℝ)*(1+Real.log ((Y+2:ℕ):ℝ))^15
  have hLp : 0 < L := by nlinarith
  have hWpos : 0 ≤ L^parityOriginalW1PolylogExponent434 :=
    Real.rpow_nonneg hLp.le _
  have hDpos : 0 ≤ L^(-D) := Real.rpow_nonneg hLp.le _
  have hMnonneg : 0 ≤ M := by
    unfold M w
    apply Finset.sum_nonneg
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simp [hc]
    · simpa [hc] using source_original_W1_nonneg
        (sourceOriginalPAllActualBands 20 L) u
  have hNnonneg : 0 ≤ N := by
    unfold N w t
    apply Finset.sum_nonneg
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simp [hc]
    · simp only [if_neg hc]
      exact mul_nonneg
        (source_original_W1_nonneg (sourceOriginalPAllActualBands 20 L) u)
        (Nat.cast_nonneg _)
  have hMass : M ≤ (Y:ℝ)*L^(-D) := hRankin Y
  have hMoment := parity_original_shift_two_tau_four_envelope_original_x_scale434 L hL
  have hCauchy := parity_original_beta_discarded_W1_shifted_tau_cauchy434
    beta L hLp hW Y
  have hFloor : (Y:ℝ) ≤ 2*Real.exp L := Nat.floor_le (by positivity)
  have hS : N^2 ≤ (Real.exp L*L^(-A))^2 := by
    calc
      _ ≤ M*(L^parityOriginalW1PolylogExponent434*V) := hCauchy
      _ ≤ ((Y:ℝ)*L^(-D))*(L^parityOriginalW1PolylogExponent434*V) :=
        mul_le_mul_of_nonneg_right hMass
          (mul_nonneg hWpos (by
            dsimp [V]
            positivity))
      _ ≤ ((Y:ℝ)*L^(-D))*(L^parityOriginalW1PolylogExponent434*
          (Real.exp L*L^16)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hMoment hWpos
            · exact mul_nonneg (Nat.cast_nonneg _) hDpos
      _ ≤ ((2*Real.exp L)*L^(-D)) *
          (L^parityOriginalW1PolylogExponent434*(Real.exp L*L^16)) := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right hFloor hDpos
            · positivity
      _ = (Real.exp L)^2 *
          (2*L^(-D)*L^parityOriginalW1PolylogExponent434*L^16) := by ring
      _ ≤ (Real.exp L)^2 * (L^(-A))^2 := by
            exact mul_le_mul_of_nonneg_left
              (parity_original_bilinear_Rankin_precision_budget434 L A hL)
              (sq_nonneg _)
      _ = (Real.exp L*L^(-A))^2 := by ring
  have hGoalNonneg : 0 ≤ Real.exp L*L^(-A) :=
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hLp.le _)
  exact (sq_le_sq₀ hNnonneg hGoalNonneg).mp hS
end Green64Analytic.Parity

end

end

/-! ## OriginalB590OutsideEAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact original Parity e-window cutoff precision accounting:
W1 shifted-divisor cost Cw+16 is paid before choosing the pointwise
Fourier-box outside-window precision. -/
def parityOriginalOutsideEBoxRetainedAccuracy434 (A : ℝ) : ℝ :=
  A+parityOriginalW1PolylogExponent434+16

/-- The discarded beta/4 Ppart mass has arbitrary Rankin precision
chosen AFTER the genuine original all-branch Fourier exponent Cf. -/
def parityOriginalOutsideEBoxDiscardAccuracy434 (A : ℝ) : ℝ :=
  A+parityOriginalB590FixedFourierPolynomialExponent434

/-- The original real Fourier variation exponent and Rankin precision
cancel exactly, independently of all later Type II K0 choices. -/
theorem parity_original_outside_e_discarded_power_cancel434
    (L A : ℝ) (hL : 0 < L) :
    L^parityOriginalB590FixedFourierPolynomialExponent434 *
      L^(-parityOriginalOutsideEBoxDiscardAccuracy434 A) = L^(-A) := by
  rw [←Real.rpow_add hL]
  have hh : parityOriginalB590FixedFourierPolynomialExponent434 -
      parityOriginalOutsideEBoxDiscardAccuracy434 A = -A := by
    unfold parityOriginalOutsideEBoxDiscardAccuracy434
    ring
  simpa only [neg_add_eq_sub,sub_eq_add_neg] using
    (show L^(parityOriginalB590FixedFourierPolynomialExponent434 +
      -parityOriginalOutsideEBoxDiscardAccuracy434 A) = L^(-A) by rw [show parityOriginalB590FixedFourierPolynomialExponent434 +
      -parityOriginalOutsideEBoxDiscardAccuracy434 A = -A from by
        dsimp [parityOriginalOutsideEBoxDiscardAccuracy434]; ring])

/-- FULL unconditional original Parity §4.2 (4.5) source e-window
truncation: the ACTUAL h=-2 complex α_m β_n Fourier-BOX contribution
from selected e OUTSIDE `[E*L^-88,E]` is negligible with arbitrary
inverse-log precision, uniformly in all original reserved Q slots and
all originally allowed `1≤E≤exp((1-beta)L)`.
The retained beta/4 original Ppart uses true real f0/f1 gate support,
and outside window the truncated integral is bounded by Fourier tails,
not assumed zero. The discarded Ppart gets the original weighted
shifted-divisor Rankin estimate times genuine Fourier variation. All
original factorial W1/P parity and source `mn=u+2` factors are kept.
The constant 2 is explicit; accuracy A and beta are arbitrary fixed
parameters. This establishes support truncation for the integrated
source object, NOT pointwise ξ support or finished Parity(4.7) a_e. -/
theorem parity_eventually_original_hminus2_outside_e_fourier_box_all_log434
    (beta A : ℝ) (hbeta : 0 < beta)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ beta/4) :
    ∀ᶠ L : ℝ in atTop,
      2 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-beta)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearOutsideEBox434
        (sourceOriginalLiteralDepth 20 L) L E band slot Psi K J α β
        ⌊2*Real.exp L⌋₊ L‖ ≤
        2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  let D := parityOriginalOutsideEBoxRetainedAccuracy434 A
  let R := parityOriginalOutsideEBoxDiscardAccuracy434 A
  filter_upwards [parity_eventually_original_hminus2_outside_e_box_pre_cauchy434
      beta D hbeta jQ hBand,
    parity_eventually_original_W1_shifted_tau_total_mass_polylog434,
    parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
      beta R hbeta,
    parity_eventually_original_B590_actual_full_fourier_variation_polylog434]
    with L hPre hTotal hDiscard hVariation
  refine ⟨hPre.1,hPre.2.1,?_⟩
  intro E hE hEcap Psi hSupport hPsi0 hPsi1 band hb slot
    K J α β Acoef Bcoef hA hB hα hβ
  let Y := ⌊2*Real.exp L⌋₊
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
    ((u+2).divisors.card:ℝ)
  let V : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
    band slot).length → Bool, parityOriginalB590FourierBranchVariation434 δ
  let B : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
     else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
     ((u+2).divisors.card:ℝ)
  have hLp : 0 < L := by linarith [hPre.1]
  have hMass : M ≤ Real.exp L*L^parityOriginalW1PolylogExponent434*L^16 := hTotal
  have hV : V ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 :=
    hVariation band slot
  have hDiscardBound : B ≤ Real.exp L*L^(-R) := hDiscard.2
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hVnonneg : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro δ hδ
    unfold parityOriginalB590FourierBranchVariation434
    exact Finset.prod_nonneg (by intro i hi; exact integral_nonneg (fun ξ => norm_nonneg _))
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply Finset.sum_nonneg
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 beta L u
    · simp [hc]
    · simp only [if_neg hc]
      exact mul_nonneg (source_original_W1_nonneg _ _) (Nat.cast_nonneg _)
  have hD0 : 0 ≤ L^(-D) := Real.rpow_nonneg hLp.le _
  have hR0 : 0 ≤ L^(-R) := Real.rpow_nonneg hLp.le _
  have hCF0 : 0 ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 :=
    Real.rpow_nonneg hLp.le _
  have hFirst : L^(-D)*M ≤ Real.exp L*L^(-A) := by
    calc
      _ ≤ L^(-D)*(Real.exp L*L^parityOriginalW1PolylogExponent434*L^16) :=
        mul_le_mul_of_nonneg_left hMass hD0
      _ = Real.exp L*(L^parityOriginalW1PolylogExponent434*L^16*L^(-D)) := by ring
      _ = Real.exp L*L^(-A) := by
        have h := parity_original_B590_arithmetic_fourier_power_cancel434 L A hLp
        change L^parityOriginalW1PolylogExponent434*L^16*L^(-D) = L^(-A) at h
        rw [h]
  have hSecond : V*B ≤ Real.exp L*L^(-A) := by
    calc
      _ ≤ V*(Real.exp L*L^(-R)) := mul_le_mul_of_nonneg_left hDiscardBound hVnonneg
      _ ≤ L^parityOriginalB590FixedFourierPolynomialExponent434 *
          (Real.exp L*L^(-R)) :=
        mul_le_mul_of_nonneg_right hV
          (mul_nonneg (Real.exp_nonneg _) hR0)
      _ = Real.exp L*(L^parityOriginalB590FixedFourierPolynomialExponent434*
          L^(-R)) := by ring
      _ = Real.exp L*L^(-A) := by
        rw [parity_original_outside_e_discarded_power_cancel434 L A hLp]
  have hPreBound := hPre.2.2 E hE hEcap Psi hSupport hPsi0 hPsi1
    band hb slot K J α β Acoef Bcoef hA hB hα hβ
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
  calc
    _ ≤ (Acoef*Bcoef)*(L^(-D)*M+V*B) := hPreBound
    _ ≤ (Acoef*Bcoef)*((Real.exp L*L^(-A))+(Real.exp L*L^(-A))) :=
      mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hAB
    _ = 2*Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearBufferAllLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16500000

/-- ORIGINAL actual beta/4 Ppart discarded W1-tau shifted mass has
zero contribution at u=0, since source Pprimepart(0)=1 and the
beta/4 cap retains it. This converts the exact source XA range to
the Rankin (0,Y] interval without deleting any physical u. -/
theorem parity_original_beta_shifted_tau_Pcap_range_eq_Ioc434
    (beta L : ℝ) (hbeta : 0 < beta) (hL : 0 ≤ L) (Y : ℕ) :
    (∑ u ∈ Finset.range (Y+1),
      (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
        ((u+2).divisors.card:ℝ)) =
    ∑ u ∈ Finset.Ioc 0 Y,
      (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
        ((u+2).divisors.card:ℝ) := by
  let f : ℕ → ℝ := fun u =>
    (if parityOriginalPhysicalPcapBeta434 beta L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
      ((u+2).divisors.card:ℝ)
  have hZero : f 0 = 0 := by
    simp [f,parity_original_beta_Ppart_cap_at_zero434 beta L hbeta hL]
  change (∑ u ∈ Finset.range (Y+1), f u) = ∑ u ∈ Finset.Ioc 0 Y, f u
  induction Y with
  | zero => simp [hZero]
  | succ Y ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le Y)]
      rw [ih]

/-- COMPLETE ORIGINAL source Parity §4.1–§4.2 h=-2 bilinear B590
allocation-error saving, BEFORE Cauchy in the Type II proof.
For every fixed requested inverse-log exponent A, arbitrary b_*>0,
fixed reserved Q band jQ satisfying the ACTUAL beta/4 prime cap,
all ORIGINAL finite K,J supports, and completely arbitrary complex
alpha_m,beta_n with bounds ‖alpha_m‖≤Acoef, ‖beta_n‖≤Bcoef,
the exact finite original factor-pair error `mn=u+2`, with original
20! labelled Q tuple, W1, multiplicity parity, smooth f0/f1 and
Psi∈[0,1] supported [1,2], has the uniform bound
`‖preCauchyError‖ ≤ Acoef Bcoef exp(L) L^(-A)`.
The proof uses the TRUE fourth divisor moment at u+2 and positive
original beta/4 Rankin; it is NOT the unresolved historical Parity (4.7)
Fourier/Mellin coefficient or signed Parity (4.17) character correlation. -/
theorem parity_eventually_original_shift_two_bilinear_B590_pre_cauchy_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearBufferError434
        (sourceOriginalLiteralDepth 20 L) L E band slot
        Psi K J α β (⌊2*Real.exp L⌋₊)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_beta_Pcap_discard_W1_shifted_tau_all_log434
      betaP A hbetaP,
    parity_eventually_original_reserved_Q_band_in_moving_depth434 jQ] with
    L hRankin hDepth
  refine ⟨hRankin.1,hDepth,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hLp : 0 < L := by nlinarith [hRankin.1]
  have hBandActual : (6/5:ℝ)*sourceOriginalQActualExponent 20 band.val ≤
      betaP/4 := by
    rw [hb]
    exact hBand
  have hPre := parity_original_shift_two_bilinear_buffer_pre_cauchy_tau434
    betaP hbetaP (sourceOriginalLiteralDepth 20 L) L E hLp
    hElo hEhi Psi hSupport hPsi0 hPsi1 band hBandActual slot
    K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hRange := parity_original_beta_shifted_tau_Pcap_range_eq_Ioc434
    betaP L hbetaP (le_of_lt hLp) ⌊2*Real.exp L⌋₊
  have hIte :
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) =
      (∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
        (if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
         else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u) *
          ((u+2).divisors.card:ℝ)) := by
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hc : parityOriginalPhysicalPcapBeta434 betaP L u <;> simp [hc]
  rw [hIte,hRange] at hPre
  have hWeight := hRankin.2
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hAcoef hBcoef
  calc
    _ ≤ Acoef*Bcoef*(∑ u ∈ Finset.Ioc 0 ⌊2*Real.exp L⌋₊,
      (if parityOriginalPhysicalPcapBeta434 betaP L u then (0:ℝ)
        else sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u)*
      ((u+2).divisors.card:ℝ)) := hPre
    _ ≤ Acoef*Bcoef*(Real.exp L*L^(-A)) :=
      mul_le_mul_of_nonneg_left hWeight hAB
    _ = Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearPreCauchyAudit -/

section

/- Entire original Parity 4.3 h=-2 pre-Cauchy Rankin source chain; standalone independent kernel import audit, not paper SOURCE review. -/
open Green64Analytic.Parity

end

/-! ## OriginalBilinearSourcePhysical -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16500000

/-- Literal ORIGINAL h=-2 bilinear source sum before Parity §4 Cauchy.
The alpha_m,beta_n are arbitrary complex coefficients on finite K,J,
`mn=u+2` is enforced exactly, and the ORIGINAL unsmoothed
sourceOriginalA/Ψ include the real multiplicity Ω parity projector. -/
def parityOriginalShiftTwoBilinearSource434
    (d : ℕ) (L : ℝ) (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    ((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
      (sourceOriginalPAllActualBands 20 L) u *
      Psi ((u:ℝ)/Real.exp L) : ℝ) : ℂ) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1 * β z.2)

/-- Complete ORIGINAL physical Q-labelled, reserved-slot and actual
B590-smooth f0/f1 selected-e representation at Fourier frequency ξ=0,
with ALL factorial/orbit repetitions, source P W1/parity and original
bilinear `mn=u+2` weights. Not the post-integration Parity(4.7) a_e. -/
def parityOriginalShiftTwoBilinearB590Physical434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    ((∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot
        (fun _ => 0) z) *
      (Psi ((u:ℝ)/Real.exp L) : ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1 * β z.2)

/-- The literal original h=-2 source bilinear sum MINUS its FULL
real physical B590 ξ=0 labelled model is EXACTLY the true original
f0/f1 allocation defect weighted by the same alpha_m,beta_n and
`mn=u+2`. No support, Rankin or asymptotic assumptions; this is
an algebraic SOURCE equality before squaring. -/
theorem parity_original_shift_two_bilinear_source_minus_B590_exact434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearSource434 d L Psi K J α β Y -
      parityOriginalShiftTwoBilinearB590Physical434
        d L E band slot Psi K J α β Y =
      parityOriginalShiftTwoBilinearBufferError434
        d L E band slot Psi K J α β Y := by
  unfold parityOriginalShiftTwoBilinearSource434
    parityOriginalShiftTwoBilinearB590Physical434
    parityOriginalShiftTwoBilinearBufferError434
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hA := parity_actual_original_A_full_Q_buffered_allocation_defect434
    d L E hL u band slot
  have hM := parity_actual_original_A_zero_freq_full_branch_mass_exact434
    d L E u band slot
  have hScalar :
    ((sourceOriginalA 20 (sourceOriginalQActualBands 20 d L)
        (sourceOriginalPAllActualBands 20 L) u : ℝ) : ℂ) -
    (∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot
        (fun _ => 0) z) =
    ((parityOriginalFullQBufferDefectAtU434 d L E band slot u : ℝ):ℂ) := by
    rw [hM]
    exact_mod_cast hA
  rw [← sub_mul]
  simp only [Complex.ofReal_mul]
  rw [← sub_mul]
  rw [hScalar]
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearSourcePhysicalAllLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- ORIGINAL h=-2 Parity §4.1--4.2 bilinear SOURCE-to-PHYSICAL
quantitative transfer BEFORE Type II Cauchy, with its original
alpha_m,beta_n, exact mn=u+2, complete r0=20 factorial-labelled
Q/P family, parity Ω projector, and real Psi. The entire true
B590 all-assignment allocation defect is O_A(exp(L)L^-A) for
any requested A, uniformly for bounded coefficients. This is at
original B509 Fourier frequency zero, not historical post-integration
a_e(4.7) or full signed E4.1 / TypeII(4.2). -/
theorem parity_eventually_original_shift_two_bilinear_source_to_physical_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          (⌊2*Real.exp L⌋₊) -
        parityOriginalShiftTwoBilinearB590Physical434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β (⌊2*Real.exp L⌋₊)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_shift_two_bilinear_B590_pre_cauchy_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1 slot
    K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hLpos : 0 < L := by nlinarith [h.1]
  rw [parity_original_shift_two_bilinear_source_minus_B590_exact434
    (sourceOriginalLiteralDepth 20 L) L E hLpos band slot Psi
    K J α β (⌊2*Real.exp L⌋₊)]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearPhysicalEFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- FULL original h=-2 physical B509 selected-e fibre with original
reserved q, W1/P odd-parity transferred to physical v, all real
B590 f0/f1 assignments, and the SAME original alpha_m,beta_n with
mn=u+2. Valid at any source Fourier frequency ξ; historical a_e
still needs Fourier/Mellin integration and c_r/H factorization. -/
def parityOriginalShiftTwoBilinearPhysicalEFibre434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    ((∑ e ∈ ((Finset.univ : Finset
       (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
          (parityActualOriginalAFullBranchE434 d L band slot)),
       sourceEndpointFibre
         (Finset.univ : Finset
           (parityActualOriginalAFullBranchCarrier434 d L band slot))
         (parityActualOriginalAFullBranchE434 d L band slot)
         (parityActualOriginalAFullBranchVWeight434
           d L E u band slot ξ) e) *
       (Psi ((u:ℝ)/Real.exp L) : ℂ)) *
       (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
         α z.1*β z.2)

/-- Exact B590 ξ=0 physical full-labelled source sum equals the
full B509 selected-e/v fibre after transfer of original W1/parity.
This is a genuine SOURCE reindex with same bilinear alpha_m/beta_n;
at u=0 we use Ψ(0)=0 instead of dropping a physical endpoint. -/
theorem parity_original_shift_two_B590_physical_eq_B509_e_v_fibre434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearB590Physical434
       d L E band slot Psi K J α β Y =
    parityOriginalShiftTwoBilinearPhysicalEFibre434
       d L E band slot (fun _ => 0) Psi K J α β Y := by
  unfold parityOriginalShiftTwoBilinearB590Physical434
    parityOriginalShiftTwoBilinearPhysicalEFibre434
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hzero : u=0
  · subst u
    simp [hPsi0]
  · rw [parity_actual_original_A_full_source_to_e_v_sum434
       d L hL hd E u hzero band slot (fun _ => 0)]
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearEFibreAllLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- The actual Parity original h=-2 bilinear SOURCE is within arbitrary
pre-Cauchy inverse-log accuracy of the selected-e/v original W1/P
physical B509 fibre at ξ=0, for bounded arbitrary alpha_m,beta_n,
all source factorials, source reserved prime and true `mn=u+2`.
This is a Fourier-zero source-to-e-fibre theorem; it does not identify
the historical post-integrated Parity(4.7) coefficient a_e or yield
Parity signed (4.17) / complete Type II (4.2). -/
theorem parity_eventually_original_shift_two_bilinear_B509_e_fibre_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          (⌊2*Real.exp L⌋₊) -
        parityOriginalShiftTwoBilinearPhysicalEFibre434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          (fun _ => 0) Psi K J α β (⌊2*Real.exp L⌋₊)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_shift_two_bilinear_source_to_physical_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hLp : 0 < L := by nlinarith [h.1]
  have hPsiZero := parity_original_Psi_support_zero434 Psi hSupport
  rw [←parity_original_shift_two_B590_physical_eq_B509_e_v_fibre434
    (sourceOriginalLiteralDepth 20 L) L E hLp rfl
    band slot Psi hPsiZero K J α β (⌊2*Real.exp L⌋₊)]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearEFibreAudit -/

section

/- Source original full h=-2 bilinear B590/B509 physical selected-e/v Rankin all-log kernel closure. No paper SOURCE review or E4.1 claim. -/
open Green64Analytic.Parity

end

/-! ## OriginalBilinearFullFourierFibre -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- The full ORIGINAL B590 smooth Q-assignment source after inserting
the genuine B509 Fourier phase at any real frequency vector, still
weighted by original h=-2 bilinear alpha/beta and original Ψ.
The Fourier phase is not identified with the Fourier *integral* here. -/
def parityOriginalShiftTwoBilinearFullFourierSource434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ u ∈ Finset.range (Y+1),
    ((∑ z : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchWeight434 d L E u band slot ξ z) *
      (Psi ((u:ℝ)/Real.exp L) : ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1 * β z.2)

/-- Source-original h=-2 full B590/B509 bilinear Fourier-phase
transfer to selected-e and physical reserved-Q/P-weighted v, for
EVERY physical real ξ and every original alpha/beta coefficient.
The u=0 endpoint is controlled only by the literal Ψ(0)=0 condition.
No post-FT/Mellin Parity(4.7) coefficient or Fourier integral assumed. -/
theorem parity_original_shift_two_full_fourier_source_eq_selected_e_v_fibre434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearFullFourierSource434
       d L E band slot ξ Psi K J α β Y =
    parityOriginalShiftTwoBilinearPhysicalEFibre434
       d L E band slot ξ Psi K J α β Y := by
  unfold parityOriginalShiftTwoBilinearFullFourierSource434
    parityOriginalShiftTwoBilinearPhysicalEFibre434
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hzero : u=0
  · subst u
    simp [hPsi0]
  · rw [parity_actual_original_A_full_source_to_e_v_sum434
      d L hL hd E u hzero band slot ξ]
end Green64Analytic.Parity

end

end

/-! ## OriginalB590AllBranchArithmeticFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- The entire original r0=20 factorial-labelled Q/P physical source
at a fixed u and arbitrary original B509 χ, now with ALL Q tuples
and ALL B590 δ branches inside ONE true N-dimensional source Fourier
integral. All actual W1/P parity, source full-Q gate and B509
selected/skipped prime characters are preserved in the arithmetic
coefficient. Both integrability and finite-sum Fubini are derived. -/
theorem parity_original_B590_full_A_all_labelled_fourier_integral434
    (d : ℕ) (L E : ℝ) (u : ℕ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ) :
    let C := parityActualOriginalAFullBranchCarrier434 d L band slot
    let F := fun (z : C) (ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) z.1
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot z.2 i).val) ξ
    Integrable (fun ξ => ∑ z : C, F z ξ) ∧
    (∑ z : C, parityActualOriginalAFullBranchWeight434 d L E u band slot χ z) =
      ∫ ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ,
        ∑ z : C, F z ξ := by
  dsimp only
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let F := fun (z : C) (ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) z.1
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot z.2 i).val) ξ
  have hInt (z : C) (_hz : z ∈ (Finset.univ : Finset C)) : Integrable (F z) :=
    parity_original_B590_full_branch_arithmetic_fourier_integrable434
      d L E u band slot χ z
  refine ⟨integrable_finsetSum Finset.univ hInt, ?_⟩
  calc
    (∑ z : C, parityActualOriginalAFullBranchWeight434 d L E u band slot χ z) =
      ∑ z : C, ∫ ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ,
        F z ξ := by
          apply Finset.sum_congr rfl
          intro z hz
          exact parity_original_B590_full_branch_weight_fourier_integral434
            d L E u band slot χ z
    _ = _ := (integral_finsetSum Finset.univ hInt).symm

/-- The same equality after original source Psi and the complete
pre-Cauchy shifted `mn=u+2` αβ fibre: no extra growth, no dropped
u=0 term, and the B509 χ phase remains arbitrary. -/
theorem parity_original_B590_hminus2_bilinear_all_labelled_full_fourier434
    (d : ℕ) (L E : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ) (K J : Finset ℕ)
    (α β : ℕ → ℂ) (Y : ℕ) :
    let C := parityActualOriginalAFullBranchCarrier434 d L band slot
    let F := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      ∑ z : C,
        parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) z.1
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot z.2 i).val) ξ
    Integrable (fun ξ => ∑ u ∈ Finset.range (Y+1),
      F u ξ * ((Psi ((u:ℝ)/Real.exp L):ℂ) *
        (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α t.1*β t.2))) ∧
    parityOriginalShiftTwoBilinearFullFourierSource434
      d L E band slot χ Psi K J α β Y =
    ∫ ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ,
      ∑ u ∈ Finset.range (Y+1),
        F u ξ * ((Psi ((u:ℝ)/Real.exp L):ℂ) *
          (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
            α t.1*β t.2)) := by
  dsimp only
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let F := fun (u : ℕ) (ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ) =>
      ∑ z : C,
        parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
          parityOriginalB590AllGateFourierIntegrand434 E
            (sourceActualSortedFrequencyScales 20 d L band slot) z.1
            (fun i => (parityActualSourceRemainingFullQTuple434
              d L band slot z.2 i).val) ξ
  have hF (u : ℕ) : Integrable (F u) :=
    (parity_original_B590_full_A_all_labelled_fourier_integral434
      d L E u band slot χ).1
  let G : ℕ → ℂ := fun u =>
    (Psi ((u:ℝ)/Real.exp L):ℂ) *
      (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α t.1*β t.2)
  have hInt (u : ℕ) (_hu : u ∈ Finset.range (Y+1)) :
      Integrable (fun ξ => F u ξ * G u) := (hF u).mul_const _
  refine ⟨integrable_finsetSum (Finset.range (Y+1)) hInt, ?_⟩
  unfold parityOriginalShiftTwoBilinearFullFourierSource434
  calc
    (∑ u ∈ Finset.range (Y+1),
      ((∑ z : C, parityActualOriginalAFullBranchWeight434 d L E u band slot χ z) *
        (Psi ((u:ℝ)/Real.exp L) : ℂ)) *
        (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α t.1 * β t.2)) =
    ∑ u ∈ Finset.range (Y+1), ∫ ξ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → ℝ,
        F u ξ * G u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [(parity_original_B590_full_A_all_labelled_fourier_integral434
            d L E u band slot χ).2]
          rw [integral_mul_const]
          ring
    _ = _ := (integral_finsetSum (Finset.range (Y+1)) hInt).symm
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearFullFourierAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Complete original Parity (4.3),(4.6),(4.7) SOURCE **pre-Cauchy**
bridge to the TRUE multi-dimensional B590 gate Fourier integral.

For each arbitrary fixed beta>0 and all-log accuracy A, the historical
original `sourceOriginalA` h=-2 bilinear sum over mn=u+2 with original
W1(P,u), odd multiplicity parity, 20! labelled Q orbit, and bounded
complex α_m,β_n is within `Acoef*Bcoef*exp(L)*L^(-A)` of the N-dimensional
Lebesgue Fourier integral over all original Schwartz f0/f1 gates. The
source B509 selected/skipped phase is fixed at χ=0 here, as required
before inserting its separate Fourier representation. The arithmetic
factorials, Q product support, original Ψ and every allocation δ
remain literal and no Fourier ξ=0 shortcut is used.

It does NOT assert the historical final Parity(4.7) `a_e(e)`, original
H(v*) c_r factorization, (4.17) signed correlations or Type II(4.2). -/
theorem parity_eventually_original_hminus2_source_to_full_fourier_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      let d := sourceOriginalLiteralDepth 20 L
      let N := (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length
      let χ : Fin N → ℝ := fun _ => 0
      let C := parityActualOriginalAFullBranchCarrier434 d L band slot
      let F := fun (u : ℕ) (ξ : Fin N → ℝ) =>
        ∑ z : C,
          parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
            parityOriginalB590AllGateFourierIntegrand434 E
              (sourceActualSortedFrequencyScales 20 d L band slot) z.1
              (fun i => (parityActualSourceRemainingFullQTuple434
                d L band slot z.2 i).val) ξ
      let G := fun ξ : Fin N → ℝ =>
        ∑ u ∈ Finset.range (⌊2*Real.exp L⌋₊+1),
          F u ξ * ((Psi ((u:ℝ)/Real.exp L):ℂ) *
            (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
              α t.1*β t.2))
      Integrable G ∧
      ‖parityOriginalShiftTwoBilinearSource434 d L Psi K J α β
          (⌊2*Real.exp L⌋₊) -
        (∫ ξ : Fin N → ℝ, G ξ)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_shift_two_bilinear_source_to_physical_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1 slot
    K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let χ : Fin N → ℝ := fun _ => 0
  have hFourier := parity_original_B590_hminus2_bilinear_all_labelled_full_fourier434
    d L E band slot χ Psi K J α β (⌊2*Real.exp L⌋₊)
  have hOriginal := h.2.2 band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hAtZero :
      parityOriginalShiftTwoBilinearB590Physical434
        d L E band slot Psi K J α β (⌊2*Real.exp L⌋₊) =
      parityOriginalShiftTwoBilinearFullFourierSource434
        d L E band slot χ Psi K J α β (⌊2*Real.exp L⌋₊) := rfl
  rw [hAtZero,hFourier.2] at hOriginal
  exact ⟨hFourier.1,hOriginal⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearFourierBox -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact original physical h=-2 bilinear sum after truncating ALL
N-dimensional B590 source Fourier frequencies to [-T,T], with
factorial Q/P W1/parity and true mn=u+2 αβ on original finite K,J.
The B509 phase is fixed at χ=0; Fourier integration still covers ALL
B590 gates, not one ξ point. -/
def parityOriginalShiftTwoBilinearFourierBox434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Y : ℕ) (T : ℝ) : ℂ :=
  ∑ u ∈ Finset.Ioc 0 Y,
    (parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T *
      (Psi ((u:ℝ)/Real.exp L):ℂ)) *
      (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
        α z.1*β z.2)

/-- Uniform exact finite-sum boundary handling for any complex source
u-carrier expression when the original Ψ(0)=0; no phantom u=0 term. -/
theorem parity_original_sum_range_eq_Ioc_of_zero434
    (Y : ℕ) (F : ℕ → ℂ) (hZero : F 0=0) :
    (∑ u ∈ Finset.range (Y+1), F u) =
      ∑ u ∈ Finset.Ioc 0 Y, F u := by
  induction Y with
  | zero => simp [hZero]
  | succ Y ih =>
      rw [Finset.sum_range_succ, Finset.sum_Ioc_succ_top (Nat.zero_le Y)]
      rw [ih]

/-- The ORIGINAL full smoothed B590/B509 h=-2 sum at χ=0 matches
the literal W1/factorial/parity full-A(u) carrier on (0,Y] whenever
Ψ(0)=0. No support part is omitted. -/
theorem parity_original_hminus2_full_fourier_source_eq_fullA_carrier434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0=0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearFullFourierSource434 d L E band slot
      (fun _ => 0) Psi K J α β Y =
    ∑ u ∈ Finset.Ioc 0 Y,
      (parityOriginalB590FullPhysicalAAtU434 d L E u band slot *
        (Psi ((u:ℝ)/Real.exp L):ℂ)) *
        (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α z.1*β z.2) := by
  unfold parityOriginalShiftTwoBilinearFullFourierSource434
  rw [parity_original_sum_range_eq_Ioc_of_zero434]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [parity_original_B590_full_physical_A_is_source_zero_freq434]
  · simp [hPsi0]

/-- Literal original h=-2 complex αβ bilinear full-B590 minus
Fourier-box error is bounded before Type II Cauchy by the genuine
W1(P,u)·τ(u+2) absolute arithmetic mass multiplied by the ACTUAL
all-δ one-coordinate Fourier-tail union. Source Ψ supported in
[1,2], 0≤Ψ≤1, all original Q labels, parity and factorials retained.
This is a direct norm-of-a-difference statement, not just a separate
error budget product. -/
theorem parity_original_hminus2_full_fourier_minus_box_le_arithmetic_tail434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0=0)
    (hPsiPos : ∀ x, 0 ≤ Psi x) (hPsiLe : ∀ x, Psi x ≤ 1)
    (K J : Finset ℕ) (α β : ℕ → ℂ)
    (Acoef Bcoef : ℝ) (hA : 0 ≤ Acoef) (hB : 0 ≤ Bcoef)
    (hα : ∀ m ∈ K, ‖α m‖ ≤ Acoef)
    (hβ : ∀ n ∈ J, ‖β n‖ ≤ Bcoef)
    (Y : ℕ) (T : ℝ) :
    ‖parityOriginalShiftTwoBilinearFullFourierSource434 d L E band slot
        (fun _ => 0) Psi K J α β Y -
      parityOriginalShiftTwoBilinearFourierBox434 d L E band slot
        Psi K J α β Y T‖ ≤
    (Acoef*Bcoef) *
      (∑ u ∈ Finset.Ioc 0 Y,
        sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
          ((u+2).divisors.card:ℝ)) *
      (∑ δ : Fin (sourceOrderedLabels 20
        (sourceActualSortedScales 20 d L) band slot).length → Bool,
        ∑ i : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 d L) band slot).length,
          parityOriginalB590OneCoordinateFourierTail434 δ i T) := by
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let t : ℝ := ∑ δ : Fin N → Bool, ∑ i : Fin N,
    parityOriginalB590OneCoordinateFourierTail434 δ i T
  let w : ℕ → ℝ := fun u => sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u
  let D : ℕ → ℂ := fun u =>
    parityOriginalB590FullPhysicalAAtU434 d L E u band slot -
      parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T
  let B : ℕ → ℂ := fun u =>
    ∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u, α z.1*β z.2
  have hTu : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro δ hd
    apply Finset.sum_nonneg
    intro i hi
    unfold parityOriginalB590OneCoordinateFourierTail434
    exact mul_nonneg
      (setIntegral_nonneg measurableSet_Icc.compl (fun ξ _ => norm_nonneg _))
      (Finset.prod_nonneg (by intro j hj; exact integral_nonneg (fun ξ => norm_nonneg _)))
  have hw (u : ℕ) : 0 ≤ w u := source_original_W1_nonneg _ _
  have hBu (u : ℕ) : ‖B u‖ ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef :=
    parity_original_shift_two_bilinear_fibre_norm_le_tau434 K J u α β
      Acoef Bcoef hA hB hα hβ
  have hDu (u : ℕ) : ‖D u‖ ≤ w u*t :=
    parity_original_B590_full_physical_A_minus_box_le_W1_tail434
      d L E hL u band slot T
  have hTerm (u : ℕ) :
      ‖(D u*(Psi ((u:ℝ)/Real.exp L):ℂ))*B u‖ ≤
      (Acoef*Bcoef)*(w u*((u+2).divisors.card:ℝ))*t := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hΨ0 := hPsiPos ((u:ℝ)/Real.exp L)
    have hΨ1 := hPsiLe ((u:ℝ)/Real.exp L)
    rw [abs_of_nonneg hΨ0]
    have hB0 : 0 ≤ ((u+2).divisors.card:ℝ)*Acoef*Bcoef := by
      positivity
    have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
    have hWt : 0 ≤ w u*t := mul_nonneg (hw u) hTu
    calc
      _ ≤ (w u*t)*Psi ((u:ℝ)/Real.exp L)*
            (((u+2).divisors.card:ℝ)*Acoef*Bcoef) := by
              exact mul_le_mul
                (mul_le_mul_of_nonneg_right (hDu u) hΨ0)
                (hBu u) (norm_nonneg _) (mul_nonneg hWt hΨ0)
      _ ≤ (w u*t)*(((u+2).divisors.card:ℝ)*Acoef*Bcoef) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_of_le_one_right hWt hΨ1) hB0
      _ = _ := by ring
  rw [parity_original_hminus2_full_fourier_source_eq_fullA_carrier434
    d L E band slot Psi hPsi0 K J α β Y]
  unfold parityOriginalShiftTwoBilinearFourierBox434
  rw [←Finset.sum_sub_distrib]
  have hTermDiff :
      (∑ u ∈ Finset.Ioc 0 Y,
        ((parityOriginalB590FullPhysicalAAtU434 d L E u band slot *
             (Psi ((u:ℝ)/Real.exp L):ℂ)) * B u -
         (parityOriginalB590BoxPhysicalAAtU434 d L E u band slot T *
             (Psi ((u:ℝ)/Real.exp L):ℂ)) * B u)) =
      ∑ u ∈ Finset.Ioc 0 Y,
        (D u*(Psi ((u:ℝ)/Real.exp L):ℂ))*B u := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [D]
    ring
  rw [hTermDiff]
  calc
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        ‖(D u*(Psi ((u:ℝ)/Real.exp L):ℂ))*B u‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ Finset.Ioc 0 Y,
        (Acoef*Bcoef)*(w u*((u+2).divisors.card:ℝ))*t := by
      apply Finset.sum_le_sum
      intro u hu
      exact hTerm u
    _ = (Acoef*Bcoef)*
        (∑ u ∈ Finset.Ioc 0 Y, w u*((u+2).divisors.card:ℝ))*t := by
          rw [←Finset.sum_mul, ←Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- SOURCE Parity §4.2, ORIGINAL full h=-2 αβ B590/B509 physical
Fourier N-dimensional integral versus the literal Fourier BOX
[-L,L]^N, with arbitrary inverse-log accuracy and all factorial Q,
W1 parity, real Psi, true mn=u+2 arithmetic. The error bound is
directly on the difference of the two complex physical expressions,
not a disconnected total-variation budget. The fixed source
Schwartz moment H is chosen after the arithmetic exponent, and all
original reserved Q bands/slots are uniform. -/
theorem parity_eventually_original_hminus2_full_fourier_minus_box_all_log434
    (A : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      0 < L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (E : ℝ) (Psi : ℝ → ℝ), Psi 0=0 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearFullFourierSource434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          (fun _ => 0) Psi K J α β (⌊2*Real.exp L⌋₊) -
        parityOriginalShiftTwoBilinearFourierBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β (⌊2*Real.exp L⌋₊) L‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_B590_arithmetic_fourier_tail_all_log434 A,
    eventually_gt_atTop (0:ℝ)] with L hBudget hLp
  refine ⟨hLp,?_⟩
  intro band slot E Psi hPsi0 hPsiPos hPsi1 K J α β
    Acoef Bcoef hA hB hα hβ
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let M : ℝ := ∑ u ∈ Finset.Ioc 0 Y,
    sourceOriginalW1 (sourceOriginalPAllActualBands 20 L) u *
      ((u+2).divisors.card:ℝ)
  let T : ℝ := ∑ δ : Fin (sourceOrderedLabels 20
    (sourceActualSortedScales 20 d L) band slot).length → Bool,
    ∑ i : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length,
      parityOriginalB590OneCoordinateFourierTail434 δ i L
  have hNorm := parity_original_hminus2_full_fourier_minus_box_le_arithmetic_tail434
    d L E hLp band slot Psi hPsi0 hPsiPos hPsi1
    K J α β Acoef Bcoef hA hB hα hβ Y L
  have hTail := hBudget band slot
  have hAB : 0 ≤ Acoef*Bcoef := mul_nonneg hA hB
  calc
    _ ≤ (Acoef*Bcoef)*M*T := hNorm
    _ = (Acoef*Bcoef)*(M*T) := by ring
    _ ≤ (Acoef*Bcoef)*(Real.exp L*L^(-A)) :=
      mul_le_mul_of_nonneg_left hTail hAB
    _ = Acoef*Bcoef*Real.exp L*L^(-A) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearSelectedEOuter -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15500000

/-- Exact Parity §4.2 B509 e-first bilinear physical object: one fixed
source-selected e fibre containing the FULL original Q-labelled
factorial/orbit sums, with all h=-2 m,n multiplicities, W1(v),
reserved prime, odd parity, real Ψ(u/x) and arbitrary Fourier ξ.
No a_e(4.7) factorization has been asserted: the Mellin split of Ψ
and Fourier integration are outstanding. -/
def parityOriginalShiftTwoBilinearSelectedEOuter434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) : ℂ :=
  ∑ e ∈ ((Finset.univ : Finset
    (parityActualOriginalAFullBranchCarrier434 d L band slot)).image
       (parityActualOriginalAFullBranchE434 d L band slot)),
    ∑ u ∈ Finset.range (Y+1),
      (sourceEndpointFibre
        (Finset.univ : Finset
          (parityActualOriginalAFullBranchCarrier434 d L band slot))
        (parityActualOriginalAFullBranchE434 d L band slot)
        (parityActualOriginalAFullBranchVWeight434
          d L E u band slot ξ) e *
       (Psi ((u:ℝ)/Real.exp L) : ℂ)) *
       (∑ z ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
         α z.1*β z.2)

/-- Exact complete physical B509 h=-2 e-fibre sum reorders into the
source selected-e OUTER sum, for EVERY frequency vector ξ, before
any Fourier/Mellin or arbitrary-beta Parity (4.17) estimate. -/
theorem parity_original_shift_two_physical_fibre_eq_selected_e_outer434
    (d : ℕ) (L E : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearPhysicalEFibre434
      d L E band slot ξ Psi K J α β Y =
    parityOriginalShiftTwoBilinearSelectedEOuter434
      d L E band slot ξ Psi K J α β Y := by
  unfold parityOriginalShiftTwoBilinearPhysicalEFibre434
    parityOriginalShiftTwoBilinearSelectedEOuter434
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_mul, Finset.sum_mul]

/-- The FULL original B590/B509 h=-2 Fourier-phase source is exactly
its literal selected-e outer first decomposition, with the physical
original W1/parity/reserved-Q in the v-weight. This is the source
algebraic prerequisite for Parity (4.7), not a_e itself. -/
theorem parity_original_shift_two_fourier_source_eq_selected_e_outer434
    (d : ℕ) (L E : ℝ) (hL : 0 < L)
    (hd : d = sourceOriginalLiteralDepth 20 L)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ) (hPsi0 : Psi 0 = 0)
    (K J : Finset ℕ) (α β : ℕ → ℂ) (Y : ℕ) :
    parityOriginalShiftTwoBilinearFullFourierSource434
      d L E band slot ξ Psi K J α β Y =
    parityOriginalShiftTwoBilinearSelectedEOuter434
      d L E band slot ξ Psi K J α β Y := by
  rw [parity_original_shift_two_full_fourier_source_eq_selected_e_v_fibre434
    d L E hL hd band slot ξ Psi hPsi0 K J α β Y]
  exact parity_original_shift_two_physical_fibre_eq_selected_e_outer434
    d L E band slot ξ Psi K J α β Y
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearSelectedEOuterAllLog -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Actual original h=-2 source bilinear to original selected-e OUTER
pre-Cauchy Parity §4.2 B509 physical decomposition, with complete original
factorial-orbit Q tuple, original P W1/multiplicity parity, reserved
prime, and arbitrary alpha_m,beta_n with mn=u+2. Uniform absolute
O_A(x L^-A) Rankin error at ξ=0, before the nontrivial Fourier/Mellin
transforms needed for historical Parity(4.7) a_e(e). -/
theorem parity_eventually_original_shift_two_bilinear_selected_e_outer_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          (⌊2*Real.exp L⌋₊) -
        parityOriginalShiftTwoBilinearSelectedEOuter434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          (fun _ => 0) Psi K J α β (⌊2*Real.exp L⌋₊)‖ ≤
        Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_shift_two_bilinear_B509_e_fibre_all_log434
    betaP A hbetaP jQ hBand] with L h
  refine ⟨h.1,h.2.1,?_⟩
  intro band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  rw [← parity_original_shift_two_physical_fibre_eq_selected_e_outer434
    (sourceOriginalLiteralDepth 20 L) L E band slot (fun _ => 0)
    Psi K J α β (⌊2*Real.exp L⌋₊)]
  exact h.2.2 band hb E hElo hEhi Psi hSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
end Green64Analytic.Parity

end

end

/-! ## OriginalBilinearSelectedEFullAudit -/

section

/- All original Parity §4.1–4.2 h=-2 bilinear alpha/beta SOURCE→ B590/B509 selected-e OUTER finite Fourier-phase & ξ=0 Rankin saving modules, kernel import audit only. -/
open Green64Analytic.Parity

end

/-! ## OriginalPsiEVMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- EXACT historical Parity §4.2 one-dimensional Mellin split of the
ORIGINAL real Ψ(e*v/x), for positive integers e,v and x>0, with
actual source Fourier convention 2π and truly independent phases
on e and v. No invented Mellin coefficient or swapped infinite
integral; equality derives from certified Schwartz Fourier inversion.
The psi smoothness and support are explicitly present, not inferred
from merely 0≤Ψ≤1. -/
theorem parity_original_real_Psi_e_v_mellin_exact434
    (Z : ℝ) (hZ : 0 < Z) (e v : ℕ) (he : 0 < e) (hv : 0 < v)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) :
    (Psi (((e:ℝ)*(v:ℝ))/Z) : ℂ) =
      ∫ s : ℝ,
        (𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
        (sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
          sourceOriginalPureMellinPhase434 (2*Real.pi*s) v) := by
  let psi : ℝ → ℂ := fun t => (Psi t : ℂ)
  have hev : 0 < e*v := Nat.mul_pos he hv
  have hM := parity_actual_cutoff_mellin_integral434
    Z psi (e*v) 1 hZ hev (by norm_num) hSmooth hSupport
  have hL : psi (((e*v:ℕ):ℝ)/(Z*((1:ℕ):ℝ))) =
    (Psi (((e:ℝ)*(v:ℝ))/Z) : ℂ) := by
      simp [psi,Nat.cast_mul]
  calc
    _ = psi (((e*v:ℕ):ℝ)/(Z*((1:ℕ):ℝ))) := hL.symm
    _ = _ := hM
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with s
      have hOne : sourceOriginalPureMellinPhase434 (-2*Real.pi*s) 1 = 1 := by
        simp [sourceOriginalPureMellinPhase434]
      rw [hOne, mul_one]
      rw [source_original_pure_mellin_product_factor434
        (2*Real.pi*s) e v he hv]
end Green64Analytic.Parity

end

end

/-! ## OriginalSourceToFourierBoxAllLog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- ORIGINAL Parity §4.1–4.2 h=-2 source-to-TRUNCATED physical Fourier
representation, with a genuine explicit all-log absolute source error.
For fixed beta>0 and arbitrary inverse-log accuracy A, the literal
unsmoothed `sourceOriginalA` bilinear α_mβ_n sum over `mn=u+2` is
within `2*Acoef*Bcoef*exp(L)*L^-A` of the full r0=20/Q/P factorial-
parity B590 ξ-Fourier integral with EACH of its N=20(d+1)-1 true
Q-gate frequencies truncated to [-L,L].

Both errors are genuine complex N-dimensional integral differences:
original beta/4 Ppart Rankin source→full-Fourier, and the independently
proved original Schwartz frequency-tail + true W1(u)τ(u+2) arithmetic
Cauchy source bound. All δ, reserved Q primes, multiplicity Ω parity,
and original Ψ are retained. No fake ξ=0 integration, no 2^N double
loss, no dependence of the Schwartz constants on K0.

This is NOT historical Parity(4.7) `a_e(e)` coefficient identification,
original H(v*)/c_r factorisation, (4.17) correlation, Type II (4.2),
or the final Green64 theorem. -/
theorem parity_eventually_original_hminus2_source_to_fourier_box_all_log434
    (betaP A : ℝ) (hbetaP : 0 < betaP)
    (jQ : ℕ)
    (hBand : (6/5:ℝ)*sourceOriginalQActualExponent 20 jQ ≤ betaP/4) :
    ∀ᶠ L : ℝ in atTop,
      (3:ℝ)^16 ≤ L ∧ jQ ≤ sourceOriginalLiteralDepth 20 L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)), band.val=jQ →
      ∀ (E : ℝ), 1 ≤ E → E ≤ Real.exp ((1-betaP)*L) →
      ∀ (Psi : ℝ → ℝ), Function.support Psi ⊆ Set.Icc 1 2 →
        (∀ t, 0 ≤ Psi t) → (∀ t, Psi t ≤ 1) →
      ∀ (slot : Fin 20) (K J : Finset ℕ) (α β : ℕ → ℂ)
        (Acoef Bcoef : ℝ), 0 ≤ Acoef → 0 ≤ Bcoef →
        (∀ m ∈ K, ‖α m‖ ≤ Acoef) →
        (∀ n ∈ J, ‖β n‖ ≤ Bcoef) →
      ‖parityOriginalShiftTwoBilinearSource434
          (sourceOriginalLiteralDepth 20 L) L Psi K J α β
          (⌊2*Real.exp L⌋₊) -
        parityOriginalShiftTwoBilinearFourierBox434
          (sourceOriginalLiteralDepth 20 L) L E band slot
          Psi K J α β (⌊2*Real.exp L⌋₊) L‖ ≤
      2*Acoef*Bcoef*Real.exp L*L^(-A) := by
  filter_upwards [parity_eventually_original_hminus2_source_to_full_fourier_all_log434
      betaP A hbetaP jQ hBand,
    parity_eventually_original_hminus2_full_fourier_minus_box_all_log434 A]
    with L hSource hBox
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro band hb E hElo hEhi Psi hPsiSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  let d := sourceOriginalLiteralDepth 20 L
  let Y := ⌊2*Real.exp L⌋₊
  let χ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
    band slot).length → ℝ := fun _ => 0
  let S : ℂ := parityOriginalShiftTwoBilinearSource434 d L Psi K J α β Y
  let P : ℂ := parityOriginalShiftTwoBilinearFullFourierSource434
    d L E band slot χ Psi K J α β Y
  let B : ℂ := parityOriginalShiftTwoBilinearFourierBox434
    d L E band slot Psi K J α β Y L
  have hFirst := hSource.2.2 band hb E hElo hEhi Psi hPsiSupport hPsi0 hPsi1
    slot K J α β Acoef Bcoef hAcoef hBcoef hα hβ
  have hFourier := parity_original_B590_hminus2_bilinear_all_labelled_full_fourier434
    d L E band slot χ Psi K J α β Y
  have hAtZero :
      parityOriginalShiftTwoBilinearB590Physical434
        d L E band slot Psi K J α β Y = P := rfl
  let N := (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L) band slot).length
  let C := parityActualOriginalAFullBranchCarrier434 d L band slot
  let F := fun (u : ℕ) (ξ : Fin N → ℝ) =>
    ∑ z : C,
      parityOriginalB590FullBranchArithmetic434 d L u band slot χ z *
        parityOriginalB590AllGateFourierIntegrand434 E
          (sourceActualSortedFrequencyScales 20 d L band slot) z.1
          (fun i => (parityActualSourceRemainingFullQTuple434
            d L band slot z.2 i).val) ξ
  let G := fun (ξ : Fin N → ℝ) =>
    ∑ u ∈ Finset.range (Y+1),
      F u ξ * ((Psi ((u:ℝ)/Real.exp L):ℂ) *
        (∑ t ∈ parityOriginalShiftTwoPositivePairFibre434 K J u,
          α t.1*β t.2))
  have hSourceBound : ‖S - (∫ ξ : Fin N → ℝ, G ξ)‖ ≤
      Acoef*Bcoef*Real.exp L*L^(-A) := hFirst.2
  have hPIntegral : P = ∫ ξ : Fin N → ℝ, G ξ := hFourier.2
  have hFullBound : ‖S-P‖ ≤ Acoef*Bcoef*Real.exp L*L^(-A) := by
    rw [hPIntegral]
    exact hSourceBound
  have hSecond := hBox.2 band slot E Psi
    (parity_original_Psi_support_zero434 Psi hPsiSupport)
    hPsi0 hPsi1 K J α β Acoef Bcoef hAcoef hBcoef hα hβ

  change ‖P-B‖ ≤ Acoef*Bcoef*Real.exp L*L^(-A) at hSecond
  change ‖S-B‖ ≤ 2*Acoef*Bcoef*Real.exp L*L^(-A)
  calc
    _ = ‖(S-P)+(P-B)‖ := by ring
    _ ≤ ‖S-P‖+‖P-B‖ := norm_add_le _ _
    _ ≤ (Acoef*Bcoef*Real.exp L*L^(-A)) +
      (Acoef*Bcoef*Real.exp L*L^(-A)) := add_le_add hFullBound hSecond
    _ = _ := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalSourceTuplePsiMellin -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Full literal Parity §4.2 Mellin source mapping for the actual original
20!-labelled complete Q tuple and its beta-independent reserved prime.
The exact source product indicator (all Q primes equals u_*) gives
u=e*v with v=reserved Q × skipped ordered Q × original multiplicity
P-part. The original REAL Ψ(u/Z) then separates into independent Mellin
phases of precisely this selected e and original physical v, with the
true 2π Fourier convention. This is the source-facing finite step before
historical Parity(4.7) coefficient a_e, NOT an integrated B590 family. -/
theorem parity_original_fullQ_labelled_Psi_source_ev_mellin_exact434
    (d : ℕ) (L Z : ℝ) (hZ : 0 < Z)
    (u : ℕ) (hu : u ≠ 0)
    (f : (j : Fin (d+1)) → Fin 20 →
      {q : ℕ // q ∈ sourceOriginalQActualBands 20 d L j})
    (hf : (∏ j : Fin (d+1), ∏ i : Fin 20, (f j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → Bool)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) :
    let p := parityActualSourceRemainingFullQTuple434 d L band slot f
    let e := paritySourceOrderedAllocatedE434 δ p
    let v := (f band slot).val * paritySourceOrderedAllocatedV434 δ p *
      sourceOriginalPPrimePart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
    (Psi ((u:ℝ)/Z) : ℂ) =
      ∫ s : ℝ,
        (𝓕 (parityOriginalLogCutoff434
          (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
        Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
        (sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
          sourceOriginalPureMellinPhase434 (2*Real.pi*s) v) := by
  dsimp only
  let p := parityActualSourceRemainingFullQTuple434 d L band slot f
  let e := paritySourceOrderedAllocatedE434 δ p
  let v := (f band slot).val * paritySourceOrderedAllocatedV434 δ p *
    sourceOriginalPPrimePart
      (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  have hev : e*v=u := parity_actual_original_A_labelled_allocated_ev_exact434
    d L u hu f hf band slot δ
  have hevNZ : e*v ≠ 0 := by rw [hev]; exact hu
  have he : 0 < e := Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hevNZ).1
  have hv : 0 < v := Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hevNZ).2
  have hM := parity_original_real_Psi_e_v_mellin_exact434
    Z hZ e v he hv Psi hSmooth hSupport
  have hCast : ((e:ℝ)*(v:ℝ)) = (u:ℝ) := by
    exact_mod_cast hev
  rw [hCast] at hM
  exact hM
end Green64Analytic.Parity

end

end

/-! ## OriginalBranchMellinSource -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- Literal separated ORIGINAL Parity source Mellin factor for each B590
Q-labelled branch x=(δ,fullQ) and actual integer u. Selected e depends
only on δ and original Q primes; physical v contains reserved q,
complementary Q primes and FULL Ppart(u). No false u=e*v assumption
on tuples outside the source original full-Q product support. -/
def parityOriginalFullQBranchMellinIntegral434
    (d : ℕ) (L Z : ℝ)
    (band : Fin (d+1)) (slot : Fin 20)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (u : ℕ) (x : parityActualOriginalAFullBranchCarrier434 d L band slot) : ℂ :=
  let P := sourceOriginalPAllActualBands 20 L
  let p := parityActualSourceRemainingFullQTuple434 d L band slot x.2
  let e := paritySourceOrderedAllocatedE434 x.1 p
  let v := (x.2 band slot).val * paritySourceOrderedAllocatedV434 x.1 p *
    sourceOriginalPPrimePart (Finset.univ.biUnion P) u
  ∫ s : ℝ,
    (𝓕 (parityOriginalLogCutoff434
      (fun t : ℝ => (Psi t : ℂ)) hSmooth hSupport) : 𝓢(ℝ,ℂ)) s *
    Complex.exp (((-2*Real.pi*s*Real.log Z : ℝ) : ℂ)*Complex.I) *
    (sourceOriginalPureMellinPhase434 (2*Real.pi*s) e *
      sourceOriginalPureMellinPhase434 (2*Real.pi*s) v)

/-- For EVERY original actual B590 Q branch (not just after summing),
original physical `W1(v)*parity*factorial*FourierPhase` times the
original real Ψ(u/Z) equals the same exact original source weight
times its genuine separated e/v Mellin integral. If a labelled-Q
product does not represent original u_*, the actual physical weight
is zero and no illegitimate u=e*v equality is invoked. -/
theorem parity_original_fullQ_B590_branch_Psi_source_mellin_exact434
    (d : ℕ) (L E Z : ℝ) (hZ : 0 < Z)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64)
    (x : parityActualOriginalAFullBranchCarrier434 d L band slot) :
    parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ x *
      (Psi ((u:ℝ)/Z) : ℂ) =
    parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ x *
      parityOriginalFullQBranchMellinIntegral434 d L Z band slot
        Psi hSmooth hSupport u x := by
  by_cases hGate : (∏ j : Fin (d+1), ∏ i : Fin 20, (x.2 j i).val) =
      sourceOriginalOrdinaryPart
        (Finset.univ.biUnion (sourceOriginalPAllActualBands 20 L)) u
  · have hM := parity_original_fullQ_labelled_Psi_source_ev_mellin_exact434
      d L Z hZ u hu x.2 hGate band slot x.1 Psi hSmooth hSupport
    dsimp only at hM
    change (Psi ((u:ℝ)/Z) : ℂ) =
      parityOriginalFullQBranchMellinIntegral434 d L Z band slot
        Psi hSmooth hSupport u x at hM
    rw [hM]
  · unfold parityActualOriginalAFullBranchVWeight434
    dsimp only
    simp only [if_neg hGate, zero_mul]

/-- Exact ORIGINAL full Q-labelled finite source sum with the real
Ψ(u/Z) is the original B590/B509 physical v-weighted sum with its
Mellin integral separated into a true selected-e phase and physical
reserved-Q/P v phase, BEFORE Fubini and historical Parity(4.7) a_e.
Every factorial/orbit repetition and original multiplicity parity
is left inside the coefficient. -/
theorem parity_original_fullQ_B590_branch_sum_mellin_exact434
    (d : ℕ) (L E Z : ℝ) (hZ : 0 < Z)
    (u : ℕ) (hu : u ≠ 0)
    (band : Fin (d+1)) (slot : Fin 20)
    (ξ : Fin (sourceOrderedLabels 20 (sourceActualSortedScales 20 d L)
      band slot).length → ℝ)
    (Psi : ℝ → ℝ)
    (hSmooth : ContDiff ℝ ∞ (fun t : ℝ => (Psi t : ℂ)))
    (hSupport : ∀ t : ℝ, (Psi t : ℂ) ≠ 0 → (1/64:ℝ) ≤ t ∧ t ≤ 64) :
    (∑ x : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ x *
        (Psi ((u:ℝ)/Z) : ℂ)) =
    ∑ x : parityActualOriginalAFullBranchCarrier434 d L band slot,
      parityActualOriginalAFullBranchVWeight434 d L E u band slot ξ x *
        parityOriginalFullQBranchMellinIntegral434
          d L Z band slot Psi hSmooth hSupport u x := by
  apply Finset.sum_congr rfl
  intro x hx
  exact parity_original_fullQ_B590_branch_Psi_source_mellin_exact434
    d L E Z hZ u hu band slot ξ Psi hSmooth hSupport x
end Green64Analytic.Parity

end

end

