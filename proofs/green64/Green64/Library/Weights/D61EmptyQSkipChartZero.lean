module

public import Green64.Library.Weights.Part095
public import Green64.Library.Weights.DyadicSelectorEnergy

@[expose] public section

/-!
# Weights / D61EmptyQSkipChartZero

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalD61EmptyQSkipChartZero -/

section

open scoped BigOperators Classical
open Filter
noncomputable section
namespace Green64Analytic.ShiftTwoTerminal
open Green64Analytic.SourceBlockSieve Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- Literal original D61 sigma=1 coefficient: full-cell Delta, original
D36 power mask with slack b0/4, and the original terminal cutoff. -/
noncomputable def sourceNativeB563OriginalD61Alpha434
    (a eta b0 L : ℝ) (m : ℕ) : ℂ :=
  if m ≤ ⌊2*Real.exp L⌋₊+2 then
    sourceD36OriginalCofactorMask a eta (b0/4) L
      (sourceD20FullDelta (L^(-(1:ℝ))) (Real.exp (Real.sqrt L))
        ((Real.exp L)^a)) m else 0

/-- The active original D61 dyad, without changing or recentering Delta. -/
noncomputable def sourceNativeB563OriginalD61ActiveK434
    (a eta b0 L : ℝ) (j : ℕ) : Finset ℕ :=
  (sourceD36DyadicInterval j).filter
    (fun m => sourceNativeB563OriginalD61Alpha434 a eta b0 L m ≠ 0)

/-- The true original alpha mask gives its upper cofactor support. No
alpha size estimate or replacement test is assumed. -/
theorem source_native_B563_actual_D61_alpha_upper434
    (a eta b0 L : ℝ) (m : ℕ)
    (hm : sourceNativeB563OriginalD61Alpha434 a eta b0 L m ≠ 0) :
    (m:ℝ) ≤ Real.exp ((1-a+b0/4)*L) := by
  unfold sourceNativeB563OriginalD61Alpha434 at hm
  split_ifs at hm with hclip
  · unfold sourceD36OriginalCofactorMask at hm
    split_ifs at hm with hmask
    · exact hmask.2
    · exact False.elim (hm rfl)
  · exact False.elim (hm rfl)

/-- The literal all-true allocation has NO skipped labels. -/
theorem source_native_B563_literal_all_true_QSkip_product434
    {n : ℕ} (Q : Fin n → Finset ℕ)
    (u : OrderedQSkip n Q (fun _ => true)) : orderedSkipProduct u=1 := by
  unfold orderedSkipProduct
  apply Finset.prod_eq_one
  intro i _
  exact False.elim (i.property rfl)

/-- Exact endpoint exponent ledger for the actual original D61 active
cofactor dyad, designated Q band and FULL capped P-part support. -/
theorem source_native_B563_actual_empty_tag_upper434
    (r d jK : ℕ) (a eta b0 L sigmaT : ℝ)
    (b : Fin (d+1)) (slot : Fin r)
    (hL : 0 ≤ L) (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
    (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
    (u : SourceQPPhysicalTag (sourceActualSortedQ r d L b slot) (fun _ => true))
    (hu : u ∈ sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot)
      (fun _ => true) (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊)) :
    ((sourceQPTagM u * sourceQPTagH u:ℕ):ℝ) ≤
      Real.exp ((1-a+3*b0/8)*L) ∧
    ((sourceQPTagM u * sourceQPTagH u:ℕ):ℝ) ≤
      Real.exp ((1-5*b0/8)*L) := by
  obtain ⟨hleft,hv⟩ := Finset.mem_product.mp hu
  obtain ⟨hm,hrest⟩ := Finset.mem_product.mp hleft
  obtain ⟨hp,_⟩ := Finset.mem_product.mp hrest
  have hmUpper := source_native_B563_actual_D61_alpha_upper434
    a eta b0 L u.1.1 (Finset.mem_filter.mp hm).2
  have hpUpper : (u.1.2.1:ℝ) ≤ Real.exp ((b0/16)*L) := by
    have hp0 : u.1.2.1 ≤
        ⌊Real.exp (((6/5:ℝ)*sourceOriginalQActualExponent r b.val)*L)⌋₊ :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact ((Nat.le_floor_iff (Real.exp_nonneg _)).mp hp0).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hband hL))
  have hvUpper : (u.2:ℝ) ≤ Real.exp ((b0/16)*L) := by
    have hv0 : u.2 ≤ ⌊(Real.exp L)^sigmaT⌋₊ :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1).2
    have hv1 : (u.2:ℝ) ≤ (Real.exp L)^sigmaT :=
      (Nat.le_floor_iff (Real.rpow_nonneg (Real.exp_nonneg L) _)).mp hv0
    rw [← Real.exp_mul] at hv1
    exact hv1.trans (Real.exp_le_exp.mpr (by nlinarith))
  have htag : ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ) =
      (u.1.1:ℝ)*(u.1.2.1:ℝ)*(u.2:ℝ) := by
    simp only [sourceQPTagM,sourceQPTagH,
      source_native_B563_literal_all_true_QSkip_product434,mul_one]
    push_cast
    ring
  have hbound : ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ) ≤
      Real.exp ((1-a+3*b0/8)*L) := by
    rw [htag]
    calc
      _ ≤ (Real.exp ((1-a+b0/4)*L)*Real.exp ((b0/16)*L))*
          Real.exp ((b0/16)*L) :=
        mul_le_mul (mul_le_mul hmUpper hpUpper (Nat.cast_nonneg _) (Real.exp_nonneg _))
          hvUpper (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  refine ⟨hbound,hbound.trans (Real.exp_le_exp.mpr ?_)⟩
  nlinarith

private theorem B563_profile_zero_left (t : ℝ) (ht : t ≤ 1/2) :
    sourceOriginalB558LiteralDyadicProfile434 t=0 := by
  unfold sourceOriginalB558LiteralDyadicProfile434
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2*t-1 ≤ 0),
    Real.smoothTransition.zero_of_nonpos (by linarith : t-1 ≤ 0),sub_self]

/-- The actual original Z_j formula puts every active empty-QSkip tag
below the LEFT edge of the genuine smooth chart. Both literal eta and
its harmonic u*eta vanish. This is not an ungated RAW support statement. -/
theorem source_native_B563_actual_empty_tag_chart_zero434
    (r d jK j : ℕ) (a eta b0 L sigmaT K0 U V : ℝ)
    (b : Fin (d+1)) (slot : Fin r)
    (hL : 1 ≤ L) (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
    (hK0 : 0 ≤ K0) (hUV : Real.exp L/4 ≤ U*V)
    (hlarge : (64:ℝ) ≤ Real.exp ((5*b0/8)*L))
    (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
    (u : SourceQPPhysicalTag (sourceActualSortedQ r d L b slot) (fun _ => true))
    (hu : u ∈ sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot)
      (fun _ => true) (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊)) :
    let Z := ((U*V)*L^K0/8)*(2:ℝ)^j
    let z := sourceQPTagM u*sourceQPTagH u
    sourceOriginalB558LiteralDyadicProfile434 ((z:ℝ)/Z)=0 ∧
    sourceOriginalB558LiteralHarmonicProfile434 ((z:ℝ)/Z)=0 := by
  dsimp only
  have hLp : 0 ≤ L := by linarith
  have hupper := (source_native_B563_actual_empty_tag_upper434
    r d jK a eta b0 L sigmaT b slot hLp ha hsigma hband u hu).2
  have hExp : (64:ℝ)*Real.exp ((1-5*b0/8)*L) ≤ Real.exp L := by
    have hh := mul_le_mul_of_nonneg_right hlarge
      (Real.exp_nonneg ((1-5*b0/8)*L))
    have he : Real.exp ((5*b0/8)*L)*Real.exp ((1-5*b0/8)*L)=Real.exp L := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    exact hh
  have hM : 1 ≤ L^K0 := Real.one_le_rpow hL hK0
  have hTwo : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hUVpos : 0 < U*V := (by positivity : (0:ℝ) < Real.exp L/4).trans_le hUV
  have hBase : 0 < (U*V)*L^K0/8 := by positivity
  have hZ : 0 < ((U*V)*L^K0/8)*(2:ℝ)^j := by positivity
  have hZlow : Real.exp L/32 ≤ ((U*V)*L^K0/8)*(2:ℝ)^j := by
    calc
      _ ≤ U*V/8 := by linarith
      _ ≤ (U*V)*L^K0/8 := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right hBase.le hTwo
  have harg : ((sourceQPTagM u*sourceQPTagH u:ℕ):ℝ)/
      (((U*V)*L^K0/8)*(2:ℝ)^j) ≤ 1/2 := by
    apply (div_le_iff₀ hZ).mpr
    nlinarith
  have hz := B563_profile_zero_left _ harg
  exact ⟨hz,by simp only [sourceOriginalB558LiteralHarmonicProfile434,hz,mul_zero]⟩

/-- The explicit scalar chart threshold is automatic eventually for the
same fixed positive b0; no new analytic number-theory hypothesis. -/
theorem source_native_B563_chart_threshold_eventually434
    (b0 : ℝ) (hb0 : 0 < b0) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ (64:ℝ) ≤ Real.exp ((5*b0/8)*L) := by
  have hGrow : Tendsto (fun L : ℝ => Real.exp ((5*b0/8)*L)) atTop atTop := by
    simpa using tendsto_exp_mul_div_rpow_atTop 0 (5*b0/8) (by positivity)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    hGrow.eventually (eventually_ge_atTop (64:ℝ))] with L hL hE
  exact ⟨hL,hE⟩

/-- WHOLE actual P-gated D61 frequency channels and their pre-square
four-sign projector vanish on the actual active tagged image when the
literal QSkip allocation is empty. This uses the original sigma=1 Delta,
D36 mask, true R cap, Q bands, physical z and shift 2k, and the actual
three-frequency substitutions. It asserts nothing about ungated RAW or
nonempty allocations. In particular no arbitrary alpha bound is assumed. -/
theorem source_native_B563_actual_D61_empty_frequency_channels_zero434
    (r d jK j : ℕ) (a eta b0 L sigmaT K0 U V : ℝ)
    (b : Fin (d+1)) (slot : Fin r)
    (hL : 1 ≤ L) (ha : b0 ≤ a) (hsigma : sigmaT ≤ b0/16)
    (hK0 : 0 ≤ K0) (hUV : Real.exp L/4 ≤ U*V)
    (hlarge : (64:ℝ) ≤ Real.exp ((5*b0/8)*L))
    (hband : (6/5:ℝ)*sourceOriginalQActualExponent r b.val ≤ b0/16)
    (xi : Fin (sourceOrderedLabels r (sourceActualSortedScales r d L) b slot).length → ℝ)
    (k : ℤ) (chi : DirichletCharacter ℂ k.natAbs) (rho : ℝ) (zeta : Fin 3 → ℝ) :
    let alpha := sourceNativeB563OriginalD61Alpha434 a eta b0 L
    let K := sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK
    let Q := sourceActualSortedQ r d L b slot
    let R := sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊
    let S := (sourceQPPhysicalTagSet Q (fun _ => true) K
      (sourceOriginalQActualBands r d L b) R).image
      (fun u => sourceQPTagM u*sourceQPTagH u)
    let P := sourceOriginalPAllActualBands r L
    let F := sourceNativePrimeCore r d L b slot (fun _ => true)
      (fun i => -xi i) K alpha k.natAbs chi (2*Real.pi*rho-2*Real.pi*zeta 1) 0
    let G := sourceNativePrimeCore r d L b slot (fun _ => true)
      (fun i => -xi i) K alpha k.natAbs chi (2*Real.pi*zeta 0+2*Real.pi*rho) 0
    let Z := ((U*V)*L^K0/8)*(2:ℝ)^j
    let psi : ℕ → ℂ := fun z => (sourceOriginalB558LiteralDyadicProfile434 ((z:ℝ)/Z):ℂ)
    (∀ tw1 tw2, sourceNativeGatedChannel S P R F G k
      (2*Real.pi*rho+2*Real.pi*zeta 2) (-(2*Real.pi*rho)) psi tw1 tw2=0) ∧
    sourceNativeB522GatedPhysicalProjected434 S P R F G k
      (2*Real.pi*rho+2*Real.pi*zeta 2) (-(2*Real.pi*rho)) psi=0 := by
  dsimp only
  have hpsi : ∀ z ∈ (sourceQPPhysicalTagSet (sourceActualSortedQ r d L b slot)
      (fun _ => true) (sourceNativeB563OriginalD61ActiveK434 a eta b0 L jK)
      (sourceOriginalQActualBands r d L b)
      (sourceActualSortedPPartSupport r L ⌊(Real.exp L)^sigmaT⌋₊)).image
        (fun u => sourceQPTagM u*sourceQPTagH u),
      sourceOriginalB558LiteralDyadicProfile434
        ((z:ℝ)/(((U*V)*L^K0/8)*(2:ℝ)^j))=0 := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact (source_native_B563_actual_empty_tag_chart_zero434
      r d jK j a eta b0 L sigmaT K0 U V b slot hL ha hsigma hK0 hUV hlarge hband u hu).1
  constructor
  · intro tw1 tw2
    unfold sourceNativeGatedChannel
    apply Finset.sum_eq_zero
    intro z hz
    simp only [sourceNativeGatedGramKernel,hpsi z hz,Complex.ofReal_zero,zero_mul,ite_self]
  · unfold sourceNativeB522GatedPhysicalProjected434
    apply Finset.sum_eq_zero
    intro z hz
    simp only [sourceNativeGatedGramKernel,hpsi z hz,Complex.ofReal_zero,zero_mul,ite_self]
end Green64Analytic.ShiftTwoTerminal

end

end

