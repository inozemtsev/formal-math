module

public import Green64.Library.Correlation.Part066
public import Green64.Library.Weights.Part086
public import Green64.Library.Analysis.Estimates.Part010

@[expose] public section

/-!
# Weights / Part095

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## TrueActualPQBandsTaggedSupport -/

section

open scoped BigOperators Classical
noncomputable section
-- sourceOriginalPAllActualBands is already provided by the native import closure.
-- Reuse that original declaration instead of redeclaring an identical body.

namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 8500000

/-- Verbatim original T P-part support from SourcePhysicalActualGlobalIntegral.
Actual P-prime powers are unrestricted; only prime factors belong to the
true P-all-group bands and the positive integer is ≤H. -/
noncomputable def sourceActualSortedPPartSupport
    (r : ℕ) (L : ℝ) (H : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).filter
    (fun v => v.primeFactors ⊆ Finset.univ.biUnion (sourceOriginalPAllActualBands r L))

/-- Positivity of the actual original Q-dyadic band prime labels. This is
a consequence of the EXACT original closed prime band definition, not an
additional analytic bound. -/
theorem source_native_B537_actual_Q_band_prime434
    (r d : ℕ) (L : ℝ) (b : Fin (d+1)) (i : Fin r)
    (j : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b i).length)
    (p : ℕ) (hp : p ∈ sourceActualSortedQ r d L b i j) :
    p.Prime := by
  unfold sourceActualSortedQ sourceOrderedPrimeBands at hp
  exact sourceOriginalQActualBands_prime434 r d L
    (sourceSortedLabelEquiv r (sourceActualSortedScales r d L) b i j).val.1 p hp

/-- Literal original actual source T tagged S.image e consists ONLY of
positive physical integer positions. Includes EXACT original K cofactor,
Q-closed prime bands, repeated QSkip products, original unrestricted
P-supported v≤H and no substitute group law. This DISCHARGES the tagged
position positivity premise of B535 without any user-supplied hQ/hD/hR. -/
theorem source_native_B537_original_ACTUAL_QP_tagged_position_nonzero434
    (r d H : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (K : Finset ℕ) (hK : ∀ m ∈ K, 0 < m) :
    let Q := sourceActualSortedQ r d L b slot
    let D := sourceOriginalQActualBands r d L b
    let R := sourceActualSortedPPartSupport r L H
    ∀ z ∈ (sourceQPPhysicalTagSet Q δ K D R).image
      (fun a => sourceQPTagM a * sourceQPTagH a), z ≠ 0 := by
  dsimp only
  let Q := sourceActualSortedQ r d L b slot
  let D := sourceOriginalQActualBands r d L b
  let R := sourceActualSortedPPartSupport r L H
  have hD : ∀ p ∈ D, 0 < p := by
    intro p hp
    exact (sourceOriginalQActualBands_prime434 r d L b p hp).pos
  have hR : ∀ v ∈ R, 0 < v := by
    intro v hv
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
  have hQ : ∀ j p, p ∈ Q j → 0 < p := by
    intro j p hp
    exact (source_native_B537_actual_Q_band_prime434 r d L b slot j p hp).pos
  exact source_native_B536_true_tagged_image_nonzero434 Q δ K D R
    hK hD hR hQ
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualD61StationaryFourierLine -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve
set_option autoImplicit false
set_option maxHeartbeats 9000000

/-- Literal original T physical support S.image e, including the complete
QSkip choices and original P-part support. -/
noncomputable def sourceNativeB541ActualPositions434
    (r d H : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (K : Finset ℕ) : Finset ℕ :=
  (sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot) δ K
    (sourceOriginalQActualBands r d L b)
    (sourceActualSortedPPartSupport r L H)).image
      (fun a => sourceQPTagM a * sourceQPTagH a)

/-- The actual original Fourier projection, with the three inner coordinates
written separately. This is the fully expanded production
SourceNativeFrequencyChannel data: SAME negative xi residual, alpha/K,
P gates, actual positions and zero distinguished-prime Mellin frequency. -/
noncomputable def sourceNativeB541ActualJointProjected434
    (r d H : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (χ : DirichletCharacter ℂ k.natAbs)
    (ρ ζ0 ζ1 ζ2 : ℝ) (psi : ℕ → ℂ) : ℂ :=
  let P := sourceOriginalPAllActualBands r L
  let R := sourceActualSortedPPartSupport r L H
  let S := sourceNativeB541ActualPositions434 r d H L b slot δ K
  let F := sourceNativePrimeCore r d L b slot δ (fun j => -ξ j) K alpha
    k.natAbs χ (2*Real.pi*ρ-2*Real.pi*ζ1) 0
  let G := sourceNativePrimeCore r d L b slot δ (fun j => -ξ j) K alpha
    k.natAbs χ (2*Real.pi*ζ0+2*Real.pi*ρ) 0
  sourceNativeB522GatedPhysicalProjected434 S P R F G k
    (2*Real.pi*ρ+2*Real.pi*ζ2) (-(2*Real.pi*ρ)) psi

/-- The explicit ORIGINAL physical total variation at the stationary
joint-frequency line; no polynomial bound or cancellation is assumed. -/
noncomputable def sourceNativeB541ActualZeroVariation434
    (r d H : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (χ : DirichletCharacter ℂ k.natAbs) (psi : ℕ → ℂ) : ℝ :=
  let P := sourceOriginalPAllActualBands r L
  let R := sourceActualSortedPPartSupport r L H
  let S := sourceNativeB541ActualPositions434 r d H L b slot δ K
  let F := sourceNativePrimeCore r d L b slot δ (fun j => -ξ j) K alpha
    k.natAbs χ 0 0
  ∑ z ∈ S, ‖sourceNativeGatedGramKernel P R F F k 0 0 psi z *
    (((1-groupSign P true z)/2)*
     ((1-groupSign P true (((z:ℤ)+2*k).toNat))/2) : ℝ)‖

/-- The long cofactor lower bound is inherited by every ACTUAL physical
position, rather than imposed separately on the tagged image. Every Q
and P multiplicity remains in the tag. -/
theorem source_native_B541_actual_positions_lower434
    (r d H : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (K : Finset ℕ) (U : ℝ) (hK : ∀ m ∈ K, U ≤ (m:ℝ)) :
    ∀ z ∈ sourceNativeB541ActualPositions434 r d H L b slot δ K,
      U ≤ (z:ℝ) := by
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨htag,hv⟩ := Finset.mem_product.mp ha
  obtain ⟨hm,hrest⟩ := Finset.mem_product.mp htag
  obtain ⟨hp,hskip⟩ := Finset.mem_product.mp hrest
  have hpPos : 0 < a.1.2.1 :=
    (sourceOriginalQActualBands_prime434 r d L b _ hp).pos
  have hvPos : 0 < a.2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).1
  have hSkipPos : 0 < orderedSkipProduct a.1.2.2 := by
    unfold orderedSkipProduct
    apply Finset.prod_pos
    intro i hi
    exact (source_native_B537_actual_Q_band_prime434 r d L b slot
      i.val (a.1.2.2 i).val (a.1.2.2 i).property).pos
  have hHPos : 0 < sourceQPTagH a :=
    Nat.mul_pos (Nat.mul_pos hpPos hSkipPos) hvPos
  have hMul : sourceQPTagM a ≤ sourceQPTagM a * sourceQPTagH a := by
    exact Nat.le_mul_of_pos_right _ hHPos
  exact (hK _ hm).trans (by exact_mod_cast hMul)

/-- Both true shifted endpoints are long when the signed shift is at most
half the actual cofactor lower floor. The toNat conversion is justified. -/
theorem source_native_B541_signed_shift_lower434
    (z : ℕ) (k : ℤ) (U : ℝ) (hU : 0 < U)
    (hz : U ≤ (z:ℝ)) (hk : |((2*k:ℤ):ℝ)| ≤ U/2) :
    U/2 ≤ ((((z:ℤ)+2*k).toNat:ℕ):ℝ) := by
  have hlow : U/2 ≤ (z:ℝ)+((2*k:ℤ):ℝ) := by
    have habs := neg_abs_le (((2*k:ℤ):ℝ))
    linarith
  have hzI : 0 ≤ (z:ℤ)+2*k := by
    have : (0:ℝ) ≤ (z:ℝ)+((2*k:ℤ):ℝ) := by linarith
    exact_mod_cast this
  have heq : ((((z:ℤ)+2*k).toNat:ℕ):ℝ) = (z:ℝ)+((2*k:ℤ):ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hzI)
  rwa [heq]

/-- Along the ACTUAL joint line zeta=(-rho,rho,0), both cofactor Mellin
frequencies and both prime frequencies vanish exactly, while xi and the
literal QSkip residual remain arbitrary and fixed. Thus the ENTIRE native
projected correlation is close to its rho=0 value, with a genuine explicit
relative total-variation error. This is NOT a bound on either signed value
and NOT a claim about the two Fourier integrals (the line has measure zero). -/
theorem source_native_B541_actual_D61_stationary_line434
    (r d H : ℕ) (L : ℝ) (b : Fin (d+1)) (slot : Fin r)
    (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (K : Finset ℕ) (alpha : ℕ → ℂ)
    (k : ℤ) (χ : DirichletCharacter ℂ k.natAbs)
    (ρ U : ℝ) (psi : ℕ → ℂ)
    (hU : 0 < U) (hK : ∀ m ∈ K, U ≤ (m:ℝ))
    (hk : |((2*k:ℤ):ℝ)| ≤ U/2) :
    ‖sourceNativeB541ActualJointProjected434 r d H L b slot δ ξ K alpha k χ
        ρ (-ρ) ρ 0 psi -
      sourceNativeB541ActualJointProjected434 r d H L b slot δ ξ K alpha k χ
        0 0 0 0 psi‖ ≤
      (|2*Real.pi*ρ| * |((2*k:ℤ):ℝ)| / (U/2)) *
        sourceNativeB541ActualZeroVariation434 r d H L b slot δ ξ K alpha k χ psi := by
  let S := sourceNativeB541ActualPositions434 r d H L b slot δ K
  let P := sourceOriginalPAllActualBands r L
  let R := sourceActualSortedPPartSupport r L H
  let F := sourceNativePrimeCore r d L b slot δ (fun j => -ξ j) K alpha
    k.natAbs χ 0 0
  have hZ : 0 < U/2 := by positivity
  have hlo : ∀ z ∈ S, U/2 ≤ (z:ℝ) := by
    intro z hz
    have hh := source_native_B541_actual_positions_lower434 r d H L b slot δ K U hK z hz
    linarith
  have hhi : ∀ z ∈ S, U/2 ≤ ((((z:ℤ)+2*k).toNat:ℕ):ℝ) := by
    intro z hz
    exact source_native_B541_signed_shift_lower434 z k U hU
      (source_native_B541_actual_positions_lower434 r d H L b slot δ K U hK z hz) hk
  have hPhase := source_native_B540_full_P_gated_projected_phase_transport434
    S P R F F k (2*Real.pi*ρ) (-(2*Real.pi*ρ)) (U/2) psi hZ hlo hhi
  have hSigma : 2*Real.pi*(-ρ)+2*Real.pi*ρ = 0 := by ring
  simpa only [sourceNativeB541ActualJointProjected434,
    sourceNativeB541ActualZeroVariation434,sub_self,hSigma,mul_zero,
    add_zero,zero_add,neg_zero,add_neg_cancel,abs_neg,S,P,R,F] using hPhase

/-- Every fixed polynomial is dominated by the TRUE physical lower
scale exp(L/2); no bound on an arithmetic coefficient mass is involved. -/
theorem source_native_B541_exp_half_dominates434
    (n : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 ≤ L ∧ C*L^n ≤ Real.exp (L/2) := by
  have hGrow : Filter.Tendsto
      (fun L : ℝ => Real.exp (L/2) / L^n) Filter.atTop Filter.atTop := by
    have hh := tendsto_exp_mul_div_rpow_atTop
      (n:ℝ) (1/2:ℝ) (by norm_num : (0:ℝ)<1/2)
    simpa only [Real.rpow_natCast,one_div,mul_comm (2:ℝ)⁻¹,←div_eq_mul_inv] using hh
  filter_upwards [hGrow.eventually (Filter.eventually_ge_atTop C),
    Filter.eventually_ge_atTop (1:ℝ)] with L hRatio hL
  refine ⟨hL,?_⟩
  exact (le_div_iff₀ (pow_pos (by linarith : 0<L) n)).mp hRatio

/-- On the actual exponentially large physical support, polynomially
bounded Fourier rho and integer shift give a relative outer-phase
error below EVERY fixed inverse power of L. This is a bound on the
phase prefactor only; the actual total variation remains explicit. -/
theorem source_native_B541_stationary_prefactor_eventually434
    (A B F : ℕ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 ≤ L ∧ ∀ (rho : ℝ) (k : ℤ) (U : ℝ),
        |rho| ≤ L^F → |((2*k:ℤ):ℝ)| ≤ L^B →
        Real.exp (L/2) ≤ U →
        |2*Real.pi*rho| * |((2*k:ℤ):ℝ)| / (U/2) ≤ 1/(L^A) := by
  filter_upwards [source_native_B541_exp_half_dominates434
    (A+B+F) (4*Real.pi)] with L hL
  refine ⟨hL.1,?_⟩
  intro rho k U hrho hk hU
  have hLp : 0 < L := by linarith [hL.1]
  have hUp : 0 < U := (Real.exp_pos (L/2)).trans_le hU
  have hFirst : |2*Real.pi*rho| ≤ 2*Real.pi*L^F := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hrho (by positivity)
  have hNumerator :
      |2*Real.pi*rho| * |((2*k:ℤ):ℝ)| ≤ (2*Real.pi*L^F)*L^B :=
    mul_le_mul hFirst hk (abs_nonneg _) (by positivity)
  apply (div_le_div_iff₀ (by positivity : 0<U/2) (pow_pos hLp A)).mpr
  calc
    (|2*Real.pi*rho| * |((2*k:ℤ):ℝ)|)*L^A ≤
        ((2*Real.pi*L^F)*L^B)*L^A :=
      mul_le_mul_of_nonneg_right hNumerator (pow_nonneg hLp.le A)
    _ = 2*Real.pi*L^(A+B+F) := by rw [pow_add,pow_add]; ring
    _ ≤ 1*(U/2) := by linarith [hL.2]

/-- The same original scale hypotheses also imply the TRUE signed
shift stays within half the physical lower endpoint, eventually. -/
theorem source_native_B541_actual_small_shift_eventually434
    (B : ℕ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 ≤ L ∧ ∀ (k : ℤ) (U : ℝ),
        |((2*k:ℤ):ℝ)| ≤ L^B → Real.exp (L/2) ≤ U →
        |((2*k:ℤ):ℝ)| ≤ U/2 := by
  filter_upwards [source_native_B541_exp_half_dominates434 B 2] with L hL
  refine ⟨hL.1,?_⟩
  intro k U hk hU
  linarith [hL.2]


/-- On exponentially long actual tagged support, the full original native
projection is relatively constant along the joint stationary line, to
arbitrary inverse-polynomial accuracy. The variation is retained and this
is not an RMS saving or an assertion about an integral over frequencies. -/
theorem source_native_B541_actual_D61_stationary_eventually434
    (A B Fexp : ℕ) :
    ∀ᶠ L : ℝ in Filter.atTop,
      1 ≤ L ∧ ∀ (r d H : ℕ) (b : Fin (d+1)) (slot : Fin r)
        (δ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
        (K : Finset ℕ) (alpha : ℕ → ℂ) (k : ℤ)
        (χ : DirichletCharacter ℂ k.natAbs) (ρ : ℝ) (psi : ℕ → ℂ),
        (∀ m ∈ K, Real.exp (L/2) ≤ (m:ℝ)) →
        |ρ| ≤ L^Fexp → |((2*k:ℤ):ℝ)| ≤ L^B →
        ‖sourceNativeB541ActualJointProjected434 r d H L b slot δ ξ K alpha k χ
            ρ (-ρ) ρ 0 psi -
          sourceNativeB541ActualJointProjected434 r d H L b slot δ ξ K alpha k χ
            0 0 0 0 psi‖ ≤
          (1/L^A) * sourceNativeB541ActualZeroVariation434
            r d H L b slot δ ξ K alpha k χ psi := by
  filter_upwards [source_native_B541_stationary_prefactor_eventually434 A B Fexp,
    source_native_B541_actual_small_shift_eventually434 B] with L hp hs
  refine ⟨hp.1,?_⟩
  intro r d H b slot δ ξ K alpha k χ ρ psi hK hρ hk
  have hVar : 0 ≤ sourceNativeB541ActualZeroVariation434
      r d H L b slot δ ξ K alpha k χ psi := by
    unfold sourceNativeB541ActualZeroVariation434
    positivity
  exact (source_native_B541_actual_D61_stationary_line434
    r d H L b slot δ ξ K alpha k χ ρ (Real.exp (L/2)) psi
    (Real.exp_pos _) hK (hs.2 k _ hk le_rfl)).trans
      (mul_le_mul_of_nonneg_right (hp.2 ρ k _ hρ hk le_rfl) hVar)
end Green64Analytic.ShiftTwoTerminal

end

end

/-! ## ActualComparisonCofactorSampling -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- The actual two cofactor divisibilities in an initial physical interval.
The signed comparison shift is arbitrary; no positive-shift substitution. -/
noncomputable def sourceNativeB547CofactorPositions434
    (N m t : ℕ) (s : ℤ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun z => m ∣ z ∧ (t:ℤ) ∣ (z:ℤ)+s)

/-- True comparison shift 2kD preserves rough-cofactor coprimality when D
is W-smooth. Crucially only |2k|<=W is assumed, NOT |2kD|<=W. -/
theorem source_native_B547_smooth_comparison_shift_coprime434
    (W : ℝ) (m t z D : ℕ) (k : ℤ)
    (hm : rough W m) (hk : k ≠ 0)
    (hsmall : ((2*k).natAbs:ℝ) ≤ W)
    (hD : ∀ p : ℕ, p.Prime → p ∣ D → (p:ℝ) ≤ W)
    (hmz : m ∣ z) (htz : (t:ℤ) ∣ (z:ℤ)+2*k*(D:ℤ)) :
    Nat.Coprime m t := by
  change Nat.gcd m t = 1
  by_contra hne
  obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpm := hpg.trans (Nat.gcd_dvd_left m t)
  have hpt := hpg.trans (Nat.gcd_dvd_right m t)
  have hleft : (p:ℤ) ∣ (z:ℤ) := Int.natCast_dvd_natCast.mpr (hpm.trans hmz)
  have hright : (p:ℤ) ∣ (z:ℤ)+2*k*(D:ℤ) :=
    (Int.natCast_dvd_natCast.mpr hpt).trans htz
  have hshift : (p:ℤ) ∣ 2*k*(D:ℤ) := by simpa using dvd_sub hright hleft
  have hpProd : p ∣ (2*k).natAbs*D := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Int.natCast_dvd.mp hshift
  have hpW : (p:ℝ) ≤ W := by
    rcases hp.dvd_mul.mp hpProd with hpk | hpd
    · have hkn : 0 < (2*k).natAbs := Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hk)
      have hle : (p:ℝ) ≤ ((2*k).natAbs:ℝ) := by exact_mod_cast Nat.le_of_dvd hkn hpk
      exact hle.trans hsmall
    · exact hD p hp hpd
  exact (not_le_of_gt (hm.2 p hp hpm)) hpW

/-- Every prime factor of the LITERAL original auxiliary product DA*DB
is <=exp(sqrt L), directly from actual membership and d.hGroup.
Repeated numeric auxiliary values are retained. -/
theorem source_native_B547_actual_aux_product_smooth434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m0 : ℕ) (ν : SourceOriginalProbePattern434 G m0)
    (a : SourceOriginalProbeAuxIndex434 m0 ν → ℕ)
    (ha : a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m0 ν d.Tb)) :
    ∀ p : ℕ, p.Prime →
      p ∣ sourceOriginalProbeDA434 m0 ν a * sourceOriginalProbeDB434 m0 ν a →
      (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
  intro p hp hpd
  rw [← source_original_probe_aux_product_split434] at hpd
  obtain ⟨j,hj,hpj⟩ := hp.prime.exists_mem_finset_dvd hpd
  have hmem := Fintype.mem_piFinset.mp ha j
  have hBound (g : G) (v : ℕ) (hv : v ∈ d.Tb g) :
      0 < v ∧ (v:ℝ) ≤ Real.exp (Real.sqrt L) := by
    refine ⟨(d.hTbPrime g v hv).pos, d.hGroup v ?_⟩
    rw [d.hG]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,hv⟩)
  have hjBound : 0 < a j ∧ (a j:ℝ) ≤ Real.exp (Real.sqrt L) := by
    cases j with
    | inl j => exact hBound j.val.1 _ hmem
    | inr j => exact hBound j.val.1 _ hmem
  have hle : (p:ℝ) ≤ (a j:ℝ) := by exact_mod_cast Nat.le_of_dvd hjBound.1 hpj
  exact hle.trans hjBound.2

/-- Binding the original auxiliary law into the true comparison coprimality
result: there is no independent smoothness premise on the full product. -/
theorem source_native_B547_original_aux_comparison_coprime434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (m0 : ℕ) (ν : SourceOriginalProbePattern434 G m0)
    (a : SourceOriginalProbeAuxIndex434 m0 ν → ℕ)
    (ha : a ∈ Fintype.piFinset (sourceOriginalProbeAuxPrimeSets434 m0 ν d.Tb))
    (m t z : ℕ) (k : ℤ) (hm : rough (Real.exp (Real.sqrt L)) m)
    (hk : k ≠ 0) (hsmall : ((2*k).natAbs:ℝ) ≤ Real.exp (Real.sqrt L))
    (hmz : m ∣ z)
    (htz : (t:ℤ) ∣ (z:ℤ)+2*k*
      ((sourceOriginalProbeDA434 m0 ν a * sourceOriginalProbeDB434 m0 ν a:ℕ):ℤ)) :
    Nat.Coprime m t :=
  source_native_B547_smooth_comparison_shift_coprime434
    _ m t z _ k hm hk hsmall
    (source_native_B547_actual_aux_product_smooth434 d m0 ν a ha) hmz htz

/-- Distinct physical samples with the SAME rough cofactor pair differ by
at least m*t. This keeps the full signed shift, including 2kD. -/
theorem source_native_B547_cofactor_position_unique434
    (N m t z z0 : ℕ) (s : ℤ) (hc : Nat.Coprime m t)
    (hN : N < m*t)
    (hz : z ∈ sourceNativeB547CofactorPositions434 N m t s)
    (hz0 : z0 ∈ sourceNativeB547CofactorPositions434 N m t s) : z = z0 := by
  have hzB := Finset.mem_filter.mp hz
  have hz0B := Finset.mem_filter.mp hz0
  have hUpper : z ≤ N := (Finset.mem_Icc.mp hzB.1).2
  have hUpper0 : z0 ≤ N := (Finset.mem_Icc.mp hz0B.1).2
  have hStep (a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N)
      (hma : m ∣ a) (hmb : m ∣ b)
      (hta : (t:ℤ) ∣ (a:ℤ)+s) (htb : (t:ℤ) ∣ (b:ℤ)+s) : a = b := by
    have hmDiff : m ∣ b-a := Nat.dvd_sub hmb hma
    have htDiffI : (t:ℤ) ∣ (b:ℤ)-(a:ℤ) := by
      convert dvd_sub htb hta using 1 <;> ring
    have htDiff : t ∣ b-a := Int.natCast_dvd_natCast.mp (by
      rw [Int.ofNat_sub hab]
      exact htDiffI)
    have hD := hc.mul_dvd_of_dvd_of_dvd hmDiff htDiff
    by_contra hne
    have hPos : 0 < b-a := by omega
    have hle := Nat.le_of_dvd hPos hD
    omega
  rcases le_total z z0 with h | h
  · exact hStep z z0 h hUpper0 hzB.2.1 hz0B.2.1 hzB.2.2 hz0B.2.2
  · exact (hStep z0 z h hUpper hz0B.2.1 hzB.2.1 hz0B.2.2 hzB.2.2).symm

/-- At an occupied long-cofactor fibre, the arithmetic sample count is
exactly ONE; the complementary Q/P factors have NOT been fixed. -/
theorem source_native_B547_occupied_cofactor_fibre_singleton434
    (N m t z0 : ℕ) (s : ℤ) (hc : Nat.Coprime m t)
    (hN : N < m*t)
    (hz0 : z0 ∈ sourceNativeB547CofactorPositions434 N m t s) :
    sourceNativeB547CofactorPositions434 N m t s = {z0} := by
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hz0,fun z hz => source_native_B547_cofactor_position_unique434 N m t z z0 s hc hN hz hz0⟩

/-- Quantitative obstruction to replacing EACH occupied cofactor fibre by
its complete-period CRT density: absolute counting error >=1/2 and
relative density error >=1 when m*t>=2*N. No original amplitude lower
bound or assertion that a nonzero original fibre exists is made. -/
theorem source_native_B547_occupied_cofactor_density_error434
    (N m t z0 : ℕ) (s : ℤ) (hc : Nat.Coprime m t)
    (hN : 2*N ≤ m*t)
    (hz0 : z0 ∈ sourceNativeB547CofactorPositions434 N m t s) :
    (1/2:ℝ) ≤ |((sourceNativeB547CofactorPositions434 N m t s).card:ℝ) -
        (N:ℝ)/(m*t:ℕ)| ∧
    1 ≤ |((m*t:ℕ):ℝ)/(N:ℝ)*
        ((sourceNativeB547CofactorPositions434 N m t s).card:ℝ)-1| := by
  have hNp : 0 < N := by
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hz0).1
    omega
  have hMt : 0 < m*t := by omega
  have hMtr : (0:ℝ) < (m*t:ℕ) := by exact_mod_cast hMt
  have hNr : (0:ℝ) < N := by exact_mod_cast hNp
  have hNLt : N < m*t := by omega
  rw [source_native_B547_occupied_cofactor_fibre_singleton434 N m t z0 s hc hNLt hz0]
  simp only [Finset.card_singleton,Nat.cast_one,mul_one]
  have hNr2 : (2:ℝ)*(N:ℝ) ≤ (m*t:ℕ) := by exact_mod_cast hN
  have hfrac : (N:ℝ)/(m*t:ℕ) ≤ 1/2 := (div_le_iff₀ hMtr).mpr (by linarith)
  have hrel : (2:ℝ) ≤ ((m*t:ℕ):ℝ)/(N:ℝ) := (le_div_iff₀ hNr).mpr hNr2
  constructor
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1-(N:ℝ)/(m*t:ℕ))]
    linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ ((m*t:ℕ):ℝ)/(N:ℝ)-1)]
    linarith

/-- The ORIGINAL D36 mask supplies the long cofactor floor. This is not a
new mask or a strengthened assumption about the actual coefficient. -/
theorem source_native_B547_original_D36_mask_lower434
    (b η δ L : ℝ) (f : ℕ → ℝ) (m : ℕ)
    (hm : sourceD36OriginalCofactorMask b η δ L f m ≠ 0) :
    Real.exp ((1-η)*L) ≤ (m:ℝ) := by
  unfold sourceD36OriginalCofactorMask at hm
  by_cases h : Real.exp ((1-η)*L) ≤ (m:ℝ) ∧
      (m:ℝ) ≤ Real.exp ((1-b+δ)*L)
  · exact h.1
  · simp only [if_neg h] at hm
    exact False.elim (hm rfl)

/-- Actual D61 long masks force the cofactor modulus above twice every
exp((1+kappa)L) physical cap, eventually. This leaves all cofactors and
all Q/P complementary factors untruncated. -/
theorem source_native_B547_D61_long_modulus_eventually434
    (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧
      ∀ (b η δ : ℝ) (f g : ℕ → ℝ) (m t N : ℕ),
        η ≤ 1/2-κ →
        sourceD36OriginalCofactorMask b η δ L f m ≠ 0 →
        sourceD36OriginalCofactorMask b η δ L g t ≠ 0 →
        (N:ℝ) ≤ Real.exp ((1+κ)*L) → 2*N ≤ m*t := by
  have hGrow : Filter.Tendsto (fun L : ℝ => Real.exp (κ*L))
      Filter.atTop Filter.atTop := by
    simpa using tendsto_exp_mul_div_rpow_atTop 0 κ hκ
  filter_upwards [hGrow.eventually (Filter.eventually_ge_atTop (2:ℝ)),
    Filter.eventually_ge_atTop (1:ℝ)] with L hExp hL
  refine ⟨hL,?_⟩
  intro b η δ f g m t N hη hm ht hN
  have hLp : 0 ≤ L := by linarith
  have hmLong := source_native_B547_original_D36_mask_lower434 b η δ L f m hm
  have htLong := source_native_B547_original_D36_mask_lower434 b η δ L g t ht
  have hLong : Real.exp ((1+2*κ)*L) ≤ ((m*t:ℕ):ℝ) := by
    calc
      _ ≤ Real.exp ((1-η)*L)*Real.exp ((1-η)*L) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ (m:ℝ)*(t:ℝ) := mul_le_mul hmLong htLong (Real.exp_pos _).le (Nat.cast_nonneg _)
      _ = _ := by norm_cast
  have hTwo : (2:ℝ)*(N:ℝ) ≤ ((m*t:ℕ):ℝ) := by
    calc
      _ ≤ Real.exp (κ*L)*Real.exp ((1+κ)*L) :=
        mul_le_mul hExp hN (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((1+2*κ)*L) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hLong
  exact_mod_cast hTwo
end Green64Analytic.ShiftTwoTerminal

end

end

