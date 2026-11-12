module

public import Green64.Library.Sieve.Foundations.Part029
public import Green64.Library.Sieve.Foundations.Part026
public import Green64.Library.Sieve.Foundations.Part027
public import Green64.Library.Sieve.Foundations.Part024
public import Green64.Library.Sieve.Foundations.Part028
public import Green64.Library.Sieve.Foundations.Part023

@[expose] public section

/-!
# Sieve / Foundations / Part030

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OriginalHistoricalUngatedNonzeroWeightCells -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Source-correct original Parity full odd-e B509 natural H0/nonzero
eta_eeta_n physical k,Z cells, including e with P group factors.
Before Fourier truncation the new ungated complete SOURCE full
signed χ-weighted sum is EXACTLY its nonzero-weight Z subset;
the excluded Z have literally zero SOURCE coefficients, not an
assumed small signed correlation. -/
def parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : Finset ℕ :=
  ((parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)).filter
    (fun Z => ∃q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0)

/-- Every source-physically attained k/Z cell excluded by the
nonzero-weight selection has zero original eta_e,n weighted signed
character sum for ALL complex H0, alpha, χ and epsilon branches.
Proof is direct finite sum vanishing on the *exact original events*;
this is not a falsely inferred cancellation of a signed superset. -/
theorem parity_original_historical_ungated_full_odd_zero_weight_cell_source_zero434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hNo : ∀q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 = 0)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ = 0 := by
  unfold parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
  apply Finset.sum_eq_zero
  intro q hq
  rw [hNo q hq]
  simp

/-- Any attained binary Z which is absent from the original actual
nonzero-smoothed-cell support contributes EXACTLY ZERO to the
original source complex character sum. In particular no extra
#Z factor is introduced or guessed from a larger Z interval. -/
theorem parity_original_historical_ungated_full_odd_nonselected_Z_source_zero434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (hNot : Z∉parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ = 0 := by
  have hNo : ∀q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
       d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 = 0 := by
    intro q hq
    by_contra hne
    have hnon : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0 := hne
    apply hNot
    unfold parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
    have hsrc := Finset.mem_filter.mp hq
    have hbase := Finset.mem_product.mp hsrc.1
    have hEvent : q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k :=
      Finset.mem_filter.mpr ⟨hsrc.1,hsrc.2.1⟩
    have hZscale := hsrc.2.2.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨q,hEvent,hZscale⟩,⟨q,hq,hnon⟩⟩
  exact parity_original_historical_ungated_full_odd_zero_weight_cell_source_zero434
    d L E V hL band slot δ ξ rho α signed Y e m K J k Z hNo χ

/-- Exact full-odd h=-2 physical original k,χ source signed
character is unchanged by discarding those physically attained Z
cells whose *ENTIRE original weighted source is identically zero*.
This is a legitimate COMPLEX finite summation identity, not a
subset absolute-value inequality; it is applied to the original
UNTRUNCATED weighted Cauchy source, before any Fourier cutoff. -/
theorem parity_original_historical_ungated_full_odd_k_sum_only_nonzero_Z434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    (∑Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ) =
    ∑Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k,
      parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ := by
  let S := (parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)
  let P : ℕ → Prop := fun Z => ∃q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0
  let F : ℕ → ℂ := fun Z => parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ
  change ∑Z∈S,F Z = ∑Z∈S.filter P,F Z
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z hZ
  change F Z = if P Z then F Z else 0
  by_cases hp : P Z
  · simp only [if_pos hp]
  · have hNot : Z∉parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
        d L E V hL band slot δ Y e m K J k := by
      intro hmem
      exact hp (Finset.mem_filter.mp hmem).2
    have hF : F Z=0 :=
      parity_original_historical_ungated_full_odd_nonselected_Z_source_zero434
        d L E V hL band slot δ ξ rho α signed Y e m K J k Z hNot χ
    simp only [if_neg hp,hF]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedNonzeroKShort -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20500000

/-- Every truly populated original corrected natural UNGATED
h=-2 B509 full odd-e k/Z with nonzero physical η_eη_n has
|k|<L^(K0+89) and |k|≤ ceil(L^(K0+89)), including e with all
original P-group prime factors. Long canonical k have EMPTY
nonzero-smoothed source Z carriers, even though their truncated
Fourier kernels cannot be dropped before this full-source filter.
Native proof uses actual new e|u/e|u' determinant and true
moving smooth η_e,L window; no P-free e assumption. -/
theorem parity_original_historical_ungated_full_odd_selected_Z_k_short434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hZ : Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k) :
    (k.natAbs:ℝ)<L^(K0+89) ∧
      k.natAbs≤Nat.ceil (L^(K0+89)) := by
  obtain ⟨q,hq,hw⟩ := (Finset.mem_filter.mp hZ).2
  have hqData := Finset.mem_filter.mp hq
  have hqProd := Finset.mem_product.mp hqData.1
  have hmp := Finset.mem_filter.mp hqProd.1
  have hmpMem := (Finset.mem_erase.mp hmp.1).2
  have hNe : m≠q.1 := (Finset.mem_erase.mp hmp.1).1.symm
  have hk : parityOriginalHistoricalOffdiagK434 e m q.1=k := hmp.2
  have hValid := hqData.2.1
  have hEta : parityOriginalHistoricalDyadicEtaEAtLReal434
      L hL ((e:ℝ)/E) ≠ 0 := by
    unfold parityOriginalHistoricalDyadicEtaWeight434 at hw
    intro h0
    exact hw (by rw [h0,zero_mul])
  have hShift := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
    d L band slot δ Y e m q.1 q.2 he hNe hValid
  rw [hk] at hShift
  have hBound := parity_original_historical_full_odd_k_bound_polylog434
    L U E K0 e m q.1 k hL hU hScale hEta
    (hDyad m hm).1 (hDyad m hm).2
    (hDyad q.1 hmpMem).1 (hDyad q.1 hmpMem).2 hShift
  have hN : k.natAbs≤Nat.ceil (L^(K0+89)) := by
    have hr : (k.natAbs:ℝ)≤(Nat.ceil (L^(K0+89)):ℝ) :=
      (le_of_lt hBound).trans (Nat.le_ceil _)
    exact_mod_cast hr
  exact ⟨hBound,hN⟩

/-- Any original full-odd physical k outside |k|≤ ceil(L^(K0+89))
has NO true nonzero η_eη_n Z cell whatsoever. Its complete
SOURCE original weighted signed sum and full B633 integral vanish;
this theorem does NOT discard a potentially nonzero truncated
Fourier integral of a zero-weight cell before exact filtering. -/
theorem parity_original_historical_ungated_full_odd_long_k_nonzero_Z_empty434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (hU : 0<U) (hScale : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (hLong : Nat.ceil (L^(K0+89)) < k.natAbs) :
    parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k = ∅ := by
  by_cases hS : (parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k).Nonempty
  · obtain ⟨Z,hZ⟩ := hS
    have hShort := (parity_original_historical_ungated_full_odd_selected_Z_k_short434
      d L U E V K0 hL band slot δ Y e m K J k Z
      he hU hScale hm hDyad hZ).2
    omega
  · exact Finset.not_nonempty_iff_eq_empty.mp hS
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPhysicalMassNoPhi -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 23500000

/-- True corrected natural UNGATED original r20 h=-2 B509
cofactor physical l1 mass over real mprime,n at one k/Z;
χ(mprime) norm cannot increase mass, and original Parity2.6 χ
coefficients have l1≤1 NO φ(2|k|) cost. Original SOURCE
nonzero-smoothed Z subcarrier is subset of REAL physical binary
Z image. All comparisons POSITIVE, not signed complex correlations.
This remains true for odd e containing original group P factors. -/
def parityOriginalHistoricalUngatedActualKZRawPairMass434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ) : ℝ :=
  ∑q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ Y e m K J k Z,
    ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1‖

/-- The original χ(m') factor cannot increase the absolute h=-2
B509 physical cofactor pair; it costs no independent character bound. -/
theorem parity_original_historical_ungated_real_k_z_chi_cofactor_mass_le_raw434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    parityOriginalHistoricalUngatedActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z := by
  unfold parityOriginal3DPhysicalFiniteCoefficientMass434
    parityOriginalHistoricalUngatedActualKZRawPairMass434
  apply Finset.sum_le_sum
  intro q hq
  unfold parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_right
    (DirichletCharacter.norm_le_one χ (q.1 : ZMod (2*k.natAbs)))
    (norm_nonneg (parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1))
  simpa only [one_mul] using h

/-- SUMMING all original characters on the SAME genuine physical
k/Z cells never costs φ(2|k|). The true Parity(2.6) cχ has ℓ1≤1,
and every twisted χ(m') H0 cofactor mass is bounded by raw mass. -/
theorem parity_original_historical_ungated_full_odd_chi_k_z_raw_mass_no_phi434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (hk : k≠0)
    (S : Finset ℕ) :
    (∑χ : DirichletCharacter ℂ (2*k.natAbs),
      ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
        (∑Z∈S,
          parityOriginal3DPhysicalFiniteCoefficientMass434
            (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
              d L band slot δ Y e m K J k Z)
            (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
              d L band slot δ ξ rho α signed Y e m k χ))) ≤
    ∑Z∈S,parityOriginalHistoricalUngatedActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z := by
  let R : ℕ → ℝ := fun Z =>
    parityOriginalHistoricalUngatedActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z
  let W : DirichletCharacter ℂ (2*k.natAbs) → ℕ → ℝ := fun χ Z =>
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  have hR : ∀Z∈S,0≤R Z := by
    intro Z hz
    unfold R parityOriginalHistoricalUngatedActualKZRawPairMass434
    exact Finset.sum_nonneg (fun q hq => norm_nonneg _)
  have hW : ∀χ : DirichletCharacter ℂ (2*k.natAbs), ∀Z∈S,
      W χ Z≤R Z := by
    intro χ Z hz
    exact parity_original_historical_ungated_real_k_z_chi_cofactor_mass_le_raw434
      d L band slot δ ξ rho α signed Y e m K J k Z χ
  exact parity_original_historical_character_mask_tail_no_phi_loss434
    k hk S W R hR hW


/-- REAL original full-odd h=-2 physically supported signed pair
ℓ1 mass reindexed EXACTLY through the actual attained dyadic Z
image, with no duplicated physical n and no ghost z. This is the
nonnegative analogue of the earlier complex source Fourier reindex. -/
theorem parity_original_historical_ungated_full_odd_k_Z_real_mass_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (W : (ℕ×ℕ) → ℝ) :
    (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,W q) =
    ∑Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),
      ∑q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,W q := by
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let g := parityOriginalHistoricalPhysicalZScaleOfEvent434 e m
  have h := Finset.sum_image' (s:=S) (g:=g)
    (f:=fun Z => ∑q∈S.filter (fun q=>g q=Z),W q)
    W (by intro q hq; rfl)
  calc
    _ = ∑Z∈S.image g,∑q∈S.filter (fun q=>g q=Z),W q := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [parity_original_historical_ungated_full_odd_Z_event_fibre_exact434
        d L band slot δ Y e m K J k Z he]

/-- Physical k/Z cells whose entire constructed SOURCE smoothing
weight vanishes need not be counted in the RAW positive pair mass.
The selected binary dyadic Z set is a subset of ALL true attained
Z images. Comparing nonnegative real norms here is legitimate;
we do not compare restricted COMPLEX signed correlations. -/
theorem parity_original_historical_ungated_full_odd_nonzero_Z_raw_mass_le_all434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (he : Odd e) :
    (∑Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
       d L E V hL band slot δ Y e m K J k,
      parityOriginalHistoricalUngatedActualKZRawPairMass434
        d L band slot δ ξ rho α signed Y e m K J k Z) ≤
    ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1‖ := by
  let S := parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
    d L band slot δ Y e m K J k
  let P : ℕ → Prop := fun Z => ∃q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0
  let W : (ℕ×ℕ) → ℝ := fun q =>
    ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
      d L band slot δ ξ rho α signed Y e q.2 m q.1‖
  let R : ℕ → ℝ := fun Z =>
    parityOriginalHistoricalUngatedActualKZRawPairMass434
      d L band slot δ ξ rho α signed Y e m K J k Z
  have hSub : (S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)).filter P ⊆
    S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m) :=
    Finset.filter_subset _ _
  have hPositive : ∀Z∈S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),0≤R Z := by
    intro Z hz
    unfold R parityOriginalHistoricalUngatedActualKZRawPairMass434
    exact Finset.sum_nonneg (fun q hq => norm_nonneg _)
  have hLe := Finset.sum_le_sum_of_subset_of_nonneg hSub
    (fun Z hz hnot => hPositive Z hz)
  change (∑Z∈(S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)).filter P,R Z) ≤
    ∑q∈S,W q
  have hReindex := parity_original_historical_ungated_full_odd_k_Z_real_mass_reindex434
    d L band slot δ Y e m K J k he W
  change (∑q∈S,W q) = ∑Z∈S.image (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m),R Z at hReindex
  exact hLe.trans (le_of_eq hReindex.symm)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFilteredRawShort -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Corrected original Parity4.16 new natural e|u B509 h=-2 source
full χ,Z mass on physically supported nonzero ηeηn cells at fixed
full-odd e,m: ≤ real raw Q/P physical pair source with k short.
Zero long-k physical cells removed BEFORE frequency truncation;
no φ(2|k|) or signed complex subset bound. -/
def parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) : ℝ :=
  ∑χ : DirichletCharacter ℂ (2*k.natAbs),
    ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
      (∑Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
        d L E V hL band slot δ Y e m K J k,
        parityOriginal3DPhysicalFiniteCoefficientMass434
          (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
            d L band slot δ Y e m K J k Z)
          (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
            d L band slot δ ξ rho α signed Y e m k χ))

/-- No SOURCE χ-character multiplicity and no binary Z-image loss:
for EVERY odd e and fixed m, a nonzero signed k has the ORIGINAL
cofactor mass on exactly attained smoothed Z cells bounded by the
true REAL positive pair norm over all Q/P physical (m',n) in its
canonical k-fibre. No false signed-subset comparison occurs. -/
theorem parity_original_historical_ungated_full_odd_k_filtered_mass_le_physical434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (he : Odd e) (hk : k≠0) :
    parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
      d L E V hL band slot δ ξ rho α signed Y e m K J k ≤
    ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1‖ := by
  let S := parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
    d L E V hL band slot δ Y e m K J k
  have hChi := parity_original_historical_ungated_full_odd_chi_k_z_raw_mass_no_phi434
    d L band slot δ ξ rho α signed Y e m K J k hk S
  have hZ := parity_original_historical_ungated_full_odd_nonzero_Z_raw_mass_le_all434
    d L E V hL band slot δ ξ rho α signed Y e m K J k he
  exact hChi.trans hZ

/-- SUM over real original full-odd-e k and χ/Z masks at fixed m:
all selected k beyond |k|>ceil(L^(K0+89)) have EMPTY nonzero
SOURCE eta_eη_n Z support (not merely tiny signed sums). The
original true positive B509 Q/P coefficient mass with all k,χ,Z
can therefore be enlarged only to the exact short-k physical
carrier, with NO false long-k source contribution and NO |K| or
χ-count loss. -/
theorem parity_original_historical_ungated_full_odd_k_chi_Z_mass_le_short_raw434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (he : Odd e) (hm : m∈K) (hU : 0<U)
    (hScale : E=U*L^(-K0))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    (∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
        d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
    ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
       (fun k=> k.natAbs≤Nat.ceil (L^(K0+89))),
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1‖ := by
  let N := Nat.ceil (L^(K0+89))
  let Sk := parityOriginalHistoricalNonzeroKSupport434 e m K
  let Bk := (parityOriginalHistoricalKSupport434 e m K).filter (fun k=> k.natAbs≤N)
  let mass : ℤ → ℝ := fun k =>
    parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
      d L E V hL band slot δ ξ rho α signed Y e m K J k
  let raw : ℤ → ℝ := fun k =>
    ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,
      ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e q.2 m q.1‖
  have hR : ∀k,0≤ raw k := by
    intro k
    exact Finset.sum_nonneg (fun q hq=>norm_nonneg _)
  have hS : (Sk.filter (fun k=> k.natAbs≤N)) ⊆ Bk := by
    intro k hk
    have hmem := Finset.mem_filter.mp hk
    have hSk := Finset.mem_filter.mp hmem.1
    exact Finset.mem_filter.mpr ⟨hSk.1,hmem.2⟩
  have hBound (k : ℤ) (hk : k∈Sk) :
      mass k ≤ if k.natAbs≤N then raw k else 0 := by
    have hkNonzero := (Finset.mem_filter.mp hk).2
    by_cases hShort : k.natAbs≤N
    · simp only [if_pos hShort]
      exact parity_original_historical_ungated_full_odd_k_filtered_mass_le_physical434
        d L E V hL band slot δ ξ rho α signed Y e m K J k he hkNonzero
    · have hLong : N < k.natAbs := by omega
      have hEmpty := parity_original_historical_ungated_full_odd_long_k_nonzero_Z_empty434
        d L U E V K0 hL band slot δ Y e m K J k he hU hScale
        hm hDyad hLong
      have hZero : mass k=0 := by
        unfold mass parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
        rw [hEmpty]
        simp
      simp only [if_neg hShort,hZero,le_refl]
  calc
    _ ≤ ∑k∈Sk,if k.natAbs≤N then raw k else 0 :=
      Finset.sum_le_sum (fun k hk=>hBound k hk)
    _ = ∑k∈Sk.filter (fun k=>k.natAbs≤N),raw k := by
      rw [Finset.sum_filter]
    _ ≤ ∑k∈Bk,raw k := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun k hk hnot=>hR k)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPhysicalPairMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Genuine original h=-2 natural UNGATED full-odd-e B509 pair,
including when e contains group P prime powers, has norm
exactly PRODUCT of its true alpha/Cauchy physical endpoint norms.
Arithmetic mean diagonal and original Dirichlet chi norm≤1 give
pointwise positive cofactor mass bound without spectral Parity4.17
assumptions or artificial source Pfree-e gate. -/
theorem parity_original_historical_ungated_real_physical_pair_norm_product434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) :
    ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp‖ =
    ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖ *
    ‖α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖ := by
  unfold parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
  rw [norm_mul,norm_star]

/-- Original complete physical signed m≠m' Cauchy cofactor pair is
bounded pointwise by the ARITHMETIC mean of the TWO positive actual
SOURCE diagonal summands. Unlike bounding the signed offdiagonal
by its unweighted value, this uses only a correct absolute-value
inequality 2ab<=a²+b², and no assumed Parity (4.17) cancellation. -/
theorem parity_original_historical_ungated_real_physical_pair_norm_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) :
    ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
       d L band slot δ ξ rho α signed Y e n m mp‖ ≤
    (‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖^2 +
     ‖α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖^2)/2 := by
  rw [parity_original_historical_ungated_real_physical_pair_norm_product434]
  let A : ℝ := ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖
  let B : ℝ := ‖α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖
  change A*B≤(A^2+B^2)/2
  nlinarith [sq_nonneg (A-B)]

/-- ORIGINAL historical real character source physical pair mass is
never larger than its genuine positive diagonal mean, since native
Dirichlet characters modulo 2|k| have norm at most one. This is
per-term and does NOT introduce a #characters bound. -/
theorem parity_original_historical_ungated_character_pair_norm_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) (k : ℤ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    ‖χ (mp : ZMod (2*k.natAbs)) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ ≤
    (‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n m‖^2 +
     ‖α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
       d L band slot δ ξ rho signed Y e n mp‖^2)/2 := by
  rw [norm_mul]
  have hχ : ‖χ (mp : ZMod (2*k.natAbs))‖≤1 :=
    DirichletCharacter.norm_le_one χ _
  have hNorm : 0≤‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ := norm_nonneg _
  calc
    _ ≤ 1*‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ :=
      mul_le_mul_of_nonneg_right hχ hNorm
    _ = ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
         d L band slot δ ξ rho α signed Y e n m mp‖ := one_mul _
    _ ≤ _ := parity_original_historical_ungated_real_physical_pair_norm_le_diagonal434
      d L band slot δ ξ rho α signed Y e n m mp
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPairMassDegree -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 26000000

/-- UNGATED actual original B509 r20 h=-2 source real k,m',n
physical pair norm with e arbitrary odd (including P-group primes),
reindexed canonically into one bounded-quotient mprime image.
Sums over |k|≤N have no hidden multiplicity or original Pfree-e
assumption. The original symmetric bounded-k graph and native
positive AMGM energy yield ONLY degree loss 2N+1 times one
positive e-fixed UNGATED diagonal, not exponential #cofactor. -/
theorem parity_original_historical_ungated_real_k_physical_events_fubini434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ)
    (W : ℕ → ℕ → ℝ) :
    (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k,W q.1 q.2) =
    ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
      ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m mp),W mp n := by
  unfold parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
  rw [Finset.sum_filter]
  calc
    _ = ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J,if parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp n then W mp n else 0 := by
          exact Finset.sum_product (parityOriginalHistoricalKPrimeFibre434 e m K k) J
            (fun q : ℕ×ℕ => if parityOriginalHistoricalUngatedPhysicalValidN434
              d L band slot δ Y e m q.1 q.2 then W q.1 q.2 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact (Finset.sum_filter (s:=J)
        (p:=parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp)
        (f:=W mp)).symm

/-- No physical k multiplicity is needed in the positive raw
absolute B509 pair mass, provided the k sum is restricted to the
ACTUAL bounded k interval. The full real k,m',n source double
sum equals one canonical bounded-quotient m' image and its genuine
Q/P n-fibre, at fixed e,m; no source term is dropped. -/
theorem parity_original_historical_ungated_bounded_k_raw_source_reindex434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (N : ℕ) :
    (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
      (fun k => k.natAbs≤N),
      ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1‖) =
    ∑mp∈(K.erase m).filter (fun mp=>
      (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N),
      ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m mp),
        ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp‖ := by
  have hFibre (k : ℤ) :
      (∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k,
        ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e q.2 m q.1‖) =
      ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ :=
    parity_original_historical_ungated_real_k_physical_events_fubini434
      d L band slot δ Y e m K J k (fun mp n =>
        ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp‖)
  calc
    _ = ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
      (fun k => k.natAbs≤N),
      ∑mp∈parityOriginalHistoricalKPrimeFibre434 e m K k,
        ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hFibre k
    _ = _ := parity_original_historical_bounded_k_real_cofactor_partition434
      e m K N (fun mp =>
        ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖)


theorem parity_original_historical_ungated_bounded_k_physical_row_energy434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m : ℕ) (K : Finset ℕ) (N : ℕ) (he : Odd e) :
    (∑mp∈((K.erase m).filter (fun mp =>
        (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)).filter
          (parityOriginalHistoricalUngatedPhysicalValidN434
            d L band slot δ Y e m · n),
      ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖) ≤
    ∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
      ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖ *
      ‖α mp*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n mp‖ := by
  let A : ℕ → ℝ := fun r =>
    ‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖
  let S := ((K.erase m).filter (fun mp =>
    (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)).filter
      (fun mp => parityOriginalHistoricalUngatedPhysicalValidN434
        d L band slot δ Y e m mp n)
  let B := K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m)
  have hSub : S ⊆ B := by
    intro mp hmp
    obtain ⟨hMP,hValid⟩ := Finset.mem_filter.mp hmp
    obtain ⟨hErase,hShort⟩ := Finset.mem_filter.mp hMP
    have hNe : m≠mp := (Finset.mem_erase.mp hErase).1.symm
    have hK := parity_original_historical_ungated_physical_k_exact_cofactor_shift434
      d L band slot δ Y e m mp n he hNe hValid
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_erase.mp hErase).2,
       ⟨parityOriginalHistoricalOffdiagK434 e m mp,hK,hShort⟩⟩
  have hPair (mp : ℕ) (hmp : mp∈S) :
      ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖ = A m * A mp := by
    exact parity_original_historical_ungated_real_physical_pair_norm_product434
      d L band slot δ ξ rho α signed Y e n m mp
  calc
    _ = ∑mp∈S,A m*A mp := by
      apply Finset.sum_congr rfl
      intro mp hmp
      exact hPair mp hmp
    _ ≤ ∑mp∈B,A m*A mp := Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun mp hmp hnot => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- SOURCE TRUE positive raw B509 h=-2 physical cofactor MASS,
where k is restricted to the actual polynomial window |k|≤N,
within one full odd selected e. The entire k,m',n source is
controlled by the original diagonal with ONLY (2N+1) loss:

 sum_{m,k short,m',n physical} |α_m A_e,n,m α_m' A_e,n,m'| ≤
    (2N+1) * sum_{n∈FullN,m∈K} |α_m A_e,n,m|².

Proved by exact signed k→m' finite reindex, actual physical n
filter, source Gram pair absolute product, positivity, and the
source-derived bounded-k symmetric cofactor graph degree lemma.
No assumption on #K, #χ or #Z; repeated prime multiplicities
remain inside the original H0/Q/P source. -/
theorem parity_original_historical_ungated_bounded_k_physical_mass_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e : ℕ) (K J : Finset ℕ) (N : ℕ) (he : Odd e) :
    (∑m∈K,
      ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤N),
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e q.2 m q.1‖) ≤
    (2*N+1:ℕ) *
      (∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
  let A (n : ℕ) (m : ℕ) : ℝ :=
    ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n m‖
  have hRow (m n : ℕ) :
      (∑mp∈((K.erase m).filter (fun mp=>
        (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)).filter
          (fun mp=>parityOriginalHistoricalUngatedPhysicalValidN434
            d L band slot δ Y e m mp n),
        ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
          d L band slot δ ξ rho α signed Y e n m mp‖) ≤
      ∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
        A n m*A n mp :=
    parity_original_historical_ungated_bounded_k_physical_row_energy434
      d L band slot δ ξ rho α signed Y e n m K N he
  have hReindex (m : ℕ) :
      (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤N),
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e q.2 m q.1‖) =
      ∑mp∈(K.erase m).filter (fun mp=>
        (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N),
        ∑n∈J.filter (parityOriginalHistoricalUngatedPhysicalValidN434
          d L band slot δ Y e m mp),
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ :=
    parity_original_historical_ungated_bounded_k_raw_source_reindex434
      d L band slot δ ξ rho α signed Y e m K J N
  have hAtM (m : ℕ) (hm : m∈K) :
      (∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤N),
        ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
          d L band slot δ Y e m K J k,
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e q.2 m q.1‖) ≤
      ∑n∈J,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
        A n m*A n mp := by
    rw [hReindex m]
    let S := (K.erase m).filter (fun mp=>
      (parityOriginalHistoricalOffdiagK434 e m mp).natAbs≤N)
    calc
      _ = ∑n∈J,∑mp∈S.filter (fun mp=>
          parityOriginalHistoricalUngatedPhysicalValidN434 d L band slot δ Y e m mp n),
          ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
            d L band slot δ ξ rho α signed Y e n m mp‖ := by
            simp only [Finset.sum_filter]
            rw [Finset.sum_comm]
            simp only [←Finset.sum_filter]
            rfl
      _ ≤ ∑n∈J,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
          A n m*A n mp := by
            apply Finset.sum_le_sum
            intro n hn
            exact hRow m n
  have hByN (n : ℕ) :
      (∑m∈K,∑mp∈K.filter (parityOriginalHistoricalBoundedKNeighbors434 e N m),
        A n m*A n mp) ≤
      (2*N+1:ℕ)*(∑m∈K,(A n m)^2) :=
    parity_original_historical_bounded_k_pair_energy434 e N he.pos K (A n)
  calc
    _ ≤ ∑m∈K,∑n∈J,∑mp∈K.filter
          (parityOriginalHistoricalBoundedKNeighbors434 e N m),
          A n m*A n mp := Finset.sum_le_sum hAtM
    _ = ∑n∈J,∑m∈K,∑mp∈K.filter
          (parityOriginalHistoricalBoundedKNeighbors434 e N m),
          A n m*A n mp := Finset.sum_comm
    _ ≤ ∑n∈J,(2*N+1:ℕ)*(∑m∈K,(A n m)^2) :=
      Finset.sum_le_sum (fun n hn=>hByN n)
    _ = (2*N+1:ℕ)*(∑n∈J,∑m∈K,(A n m)^2) := by
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedCharacterMassDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 27000000

/-- **GLOBAL CORRECTED ORIGINAL Parity(4.15) POSITIVE ℓ1 MASS**:
sum over ALL genuine full odd-e, m, nonzero signed k, Dirichlet χ
and ONLY real binary Z with nonzero original eta_eeta_n B509
natural u/e H0 source weight of |cχ|∑_{actual mprime,n}|χ(mprime)*α_mH0...| ≤
  (2*ceil(L^(K0+89))+1)*D_genuine_UNGATED.

Crucially D_genuine_UNGATED is the native ORIGINAL positive Cauchy
full odd-e/n diagonal with e including original P-group primes.
The result combines character mask l1≤1, real Z image without
multiplicity, short k from nonzero ηe, exact k→mprime reindex,
symmetric graph degree and true α/complex H0 pair norm. There is
NO exponential #m,#e,#n,#χ,#Z factor and NO signed subset
cancellation claim. This is genuinely NEW compared with old gated
original source. -/
def parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
    (d : ℕ) (L E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ) : ℝ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
          d L E V hL band slot δ ξ rho α signed Y e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k

/-- MAIN NEW TRUE ORIGINAL Parity (4.10)--(4.16) source positive
coefficient-mass bridge:

 sum_{all odd e≤2E,m∈K,k!=0,χ,Z with nonzero ηeηn}
      |cχ| sum_{physical m',n} |χ(m') A_source(e,m,m',n)|
 ≤ (2 ceil(L^(K0+89))+1) ×
       sum_{all odd e≤2E,n≤3V,m∈K} |α_m H0(e,n,m)|².

This is an ACTUAL positive diagonal estimate, not an unsupported
signed subset comparison or an artificial uniform Z-cell bound.

Proof chain: native original character ℓ1≤1, exact positive binary
Z image reindex, actual moving η_eη_n support forces short k,
real canonical k→m' quotient reindex, exact source Q/P physical
Gram pair norm, and symmetric bounded-quotient cofactor graph
with degree ≤2 ceil(L^(K0+89))+1. No factor #χ, #Z, #m, #n or #e.
Original r0=20 h=-2 signed ε=1/E, B509 H0, fine b629 α and
multiplicities of all P primes remain untouched. -/
theorem parity_original_historical_ungated_full_odd_filtered_coefficient_mass_le_diagonal434
    (d : ℕ) (L U E V K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y : ℕ) (K : Finset ℕ)
    (hU : 0<U) (hScale : E=U*L^(-K0))
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) :
    parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
      d L E V hL band slot δ ξ rho α signed Y K ≤
    (2*Nat.ceil (L^(K0+89))+1:ℕ) *
      parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
        d L band slot δ ξ rho K
        (parityOriginalHistoricalFullOddEEnvelope434 E)
        (parityOriginalHistoricalFullNEnvelope434 V) α signed Y := by
  let EFull := parityOriginalHistoricalFullOddEEnvelope434 E
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let C : ℝ := (2*Nat.ceil (L^(K0+89))+1:ℕ)
  have heBound (e : ℕ) (he : e∈EFull) :
    (∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
        d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
    C * (∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hStep (m : ℕ) (hm : m∈K) :
        (∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
            d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
        ∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
          (fun k => k.natAbs≤Nat.ceil (L^(K0+89))),
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot δ Y e m K J k,
            ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e q.2 m q.1‖ :=
      parity_original_historical_ungated_full_odd_k_chi_Z_mass_le_short_raw434
        d L U E V K0 hL band slot δ ξ rho α signed Y e m K J
        heOdd hm hU hScale hDyad
    have hAll :
      (∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
          d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
      ∑m∈K,∑k∈(parityOriginalHistoricalKSupport434 e m K).filter
        (fun k=>k.natAbs≤Nat.ceil (L^(K0+89))),
          ∑q∈parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
            d L band slot δ Y e m K J k,
            ‖parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
              d L band slot δ ξ rho α signed Y e q.2 m q.1‖ :=
      Finset.sum_le_sum hStep
    have hDegree := parity_original_historical_ungated_bounded_k_physical_mass_le_diagonal434
      d L band slot δ ξ rho α signed Y e K J (Nat.ceil (L^(K0+89))) heOdd
    exact hAll.trans hDegree
  unfold parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
    parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
  change (∑e∈EFull,
    ∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
      parityOriginalHistoricalUngatedFullOddKChiFilteredCoefficientMass434
        d L E V hL band slot δ ξ rho α signed Y e m K J k) ≤
    C*(∑e∈EFull,∑n∈J,∑m∈K,
      ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n m‖^2)
  calc
    _ ≤ ∑e∈EFull,C*(∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) :=
      Finset.sum_le_sum heBound
    _ = C*(∑e∈EFull,∑n∈J,∑m∈K,
        ‖α m*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
          d L band slot δ ξ rho signed Y e n m‖^2) := by
      rw [Finset.mul_sum]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedPhysicalKZMassDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Corrected original Parity(4.15) UNGATED B509/H0 actual
(e,m,k,Z,chi) source Fourier ℓ1 coefficient mass is bounded by
one e-fixed genuine positive Cauchy diagonal WITHOUT #mprime:
there is exactly at most one physical mprime for e,m,k, and
its n terms are ≤ Σ_{n,r∈K}|α_r a_v(u/e)|² by native χ and
AMGM, including original e with any group P-prime powers.
This is the physical coefficient cost, NOT an estimate of the
signed low-frequency Parity4.17 correlation. -/
theorem parity_original_historical_ungated_physical_character_pair_norm_le_en_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e n m mp : ℕ) (K : Finset ℕ) (hm : m∈K) (hmp : mp∈K)
    (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    ‖χ (mp : ZMod (2*k.natAbs)) *
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖ ≤
    ∑r∈K, ‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2 := by
  let F : ℕ → ℝ := fun r =>
    ‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2
  have hNonneg : ∀r∈K,0≤F r := by
    intro r hr
    exact sq_nonneg _
  have ha : F m ≤ ∑r∈K,F r := Finset.single_le_sum hNonneg hm
  have hb : F mp ≤ ∑r∈K,F r := Finset.single_le_sum hNonneg hmp
  have hPair := parity_original_historical_ungated_character_pair_norm_le_diagonal434
    d L band slot δ ξ rho α signed Y e n m mp k χ
  change ‖χ (mp : ZMod (2*k.natAbs))*
      parityOriginalHistoricalUngatedOffdiagPhysicalAtENMMp434
        d L band slot δ ξ rho α signed Y e n m mp‖ ≤ ∑r∈K,F r
  nlinarith [hPair,ha,hb]

/-- At fixed source selected e and actual canonical k/Z, the
complete TRUE original signed character Fourier cofactor l1 mass
has no extra #m' loss: physical m' is UNIQUE and the sum over
actual n is bounded by the genuine e-fixed original Cauchy
positive diagonal ∑_{n∈J,r∈K}|α_r A(e,n,r)|².

This is an exact structural bound, independent of the original
fine α, signed epsilon, k,Z size, or χ. It is NOT an estimate on
the Fourier-transformed 4.17 core; it bounds the genuine SOURCE
truncation coefficient cost before the main cancellation theorem. -/
theorem parity_original_historical_ungated_actual_k_z_physical_l1_mass_le_e_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hm : m∈K)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    ∑n∈J,∑r∈K,‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2 := by
  let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  let D : ℕ → ℝ := fun n =>
    ∑r∈K,‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
      d L band slot δ ξ rho signed Y e n r‖^2
  have hD : ∀n,0≤D n := by
    intro n
    apply Finset.sum_nonneg
    intro r hr
    exact sq_nonneg _
  change (∑q∈S,‖W q‖) ≤ ∑n∈J,D n
  by_cases hEmpty : S.Nonempty
  · obtain ⟨q0,hq0⟩ := hEmpty
    have h0Prod := Finset.mem_product.mp (Finset.mem_filter.mp hq0).1
    have h0Mp := (Finset.mem_filter.mp h0Prod.1)
    have h0K : q0.1∈K := (Finset.mem_erase.mp h0Mp.1).2
    have h0Ne : m≠q0.1 := (Finset.mem_erase.mp h0Mp.1).1.symm
    have h0Valid := (Finset.mem_filter.mp hq0).2.1
    let mp0 := q0.1
    let S0 : Finset (ℕ×ℕ) := ({mp0}:Finset ℕ).product J
    have hUnique (q : ℕ×ℕ) (hq : q∈S) : q.1=mp0 := by
      have hqProd := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
      have hqMp := Finset.mem_filter.mp hqProd.1
      have hqNe : m≠q.1 := (Finset.mem_erase.mp hqMp.1).1.symm
      exact parity_original_historical_ungated_physical_same_k_cofactor_unique434
        d L band slot δ Y e m q.1 mp0 q.2 q0.2 k he hqNe h0Ne
        (Finset.mem_filter.mp hq).2.1 h0Valid hqMp.2 h0Mp.2
    have hSub : S ⊆ S0 := by
      intro q hq
      have hqJ := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr (hUnique q hq),hqJ⟩
    have hSbound : (∑q∈S,‖W q‖) ≤ ∑q∈S0,‖W q‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hSub
        (fun q hq hnot => norm_nonneg _)
    have hS0 : (∑q∈S0,‖W q‖) = ∑n∈J,‖W (mp0,n)‖ := by
      dsimp [S0]
      rw [Finset.sum_product]
      simp
    have hPoint (n : ℕ) : ‖W (mp0,n)‖ ≤ D n := by
      exact parity_original_historical_ungated_physical_character_pair_norm_le_en_diagonal434
        d L band slot δ ξ rho α signed Y e n m mp0 K hm h0K k χ
    calc
      _ ≤ ∑q∈S0,‖W q‖ := hSbound
      _ = ∑n∈J,‖W (mp0,n)‖ := hS0
      _ ≤ ∑n∈J,D n := Finset.sum_le_sum (fun n hn => hPoint n)
  · have hSEmpty : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    rw [hSEmpty]
    simp only [Finset.sum_empty]
    exact Finset.sum_nonneg (fun n hn=> hD n)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFullOddKZMass -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- Corrected all-odd-e natural h=-2 r20 B509/H0 physical
per-cell Fourier ℓ1 mass is bounded by one positive full odd-e
Cauchy diagonal and hence by Acoef² exp(L)L^(2CW1+256).
No artificial original selected-Q/Pfree e restriction; e with
all prime powers allowed. This is a POSITIVE coefficient budget,
not a signed Parity(4.17) correlation saving. -/
theorem parity_original_historical_ungated_full_odd_e_fixed_diagonal_le_full434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e : ℕ) (he : e∈Eenv) :
    (∑n∈Nenv,∑r∈K,
      ‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e n r‖^2) ≤
    parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y := by
  let F : ℕ → ℝ := fun e0 =>
    ∑n∈Nenv,∑r∈K,
      ‖α r*parityOriginalHistoricalUngatedCauchyPhysicalAtENM434
        d L band slot δ ξ rho signed Y e0 n r‖^2
  have hF : ∀e0∈Eenv, 0≤F e0 := by
    intro e0 he0
    apply Finset.sum_nonneg
    intro n hn
    apply Finset.sum_nonneg
    intro r hr
    exact sq_nonneg _
  change F e≤∑e0∈Eenv,F e0
  exact Finset.single_le_sum hF he

/-- For ANY original h=-2 populated physical canonical k/Z cell
at e∈FULL ODD-E envelope, its exact source signed/chi cofactor ℓ1
mass is bounded by the FULL enlarged positive source diagonal.
This uses the actual Q/P/B509 two-ended source, χ norm≤1 and
unique physical m' per e,m,k, no alpha proxy and no #characters.
It works even when the eta_e,n smoothing weight is zero: the
coefficient mass itself is unweighted and always nonnegative. -/
theorem parity_original_historical_ungated_full_odd_k_z_mass_le_diagonal434
    (d : ℕ) (L : ℝ) (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (heFull : e∈Eenv) (hm : m∈K)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) :
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K Nenv k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) ≤
    parityOriginalHistoricalUngatedExtendedUnweightedDiagonal434
      d L band slot δ ξ rho K Eenv Nenv α signed Y := by
  exact (parity_original_historical_ungated_actual_k_z_physical_l1_mass_le_e_diagonal434
    d L band slot δ ξ rho α signed Y e m K Nenv k Z he hm χ).trans
    (parity_original_historical_ungated_full_odd_e_fixed_diagonal_le_full434
      d L band slot δ ξ rho K Eenv Nenv α signed Y e heFull)

/-- The entire full-odd-e original signed χ cofactor k/Z ℓ1
mass is SOURCE-unconditionally bounded by one FIXED power of L
times x=e^L, no matter which odd e from the enlarged positive
Cauchy support and which original physical k,Z. This uses the
true original eighth shifted divisor moment, not a stronger
unproved fourth divisor moment or a synthetic SourceComparisonData. -/
theorem parity_eventually_original_historical_ungated_full_odd_k_z_mass_X434 :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧
      ∀ (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho : ℝ) (K Eenv Nenv : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈Eenv → m∈K →
      ∀χ : DirichletCharacter ℂ (2*k.natAbs),
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K Nenv k Z)
        (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
          ⌊2*Real.exp L⌋₊ e m k χ) ≤
      Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := by
  filter_upwards [parity_eventually_original_historical_ungated_extended_diagonal_polylog434]
    with L hDiag
  refine ⟨hDiag.1,?_⟩
  intro band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hAlpha
    e m k Z he heFull hm χ
  exact (parity_original_historical_ungated_full_odd_k_z_mass_le_diagonal434
    (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho
    K Eenv Nenv α signed ⌊2*Real.exp L⌋₊ e m k Z
    he heFull hm χ).trans
    (hDiag.2 band slot δ ξ rho K Eenv Nenv α signed Acoef hAcoef hAlpha)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedZeroWeightFourier -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- All exact literal original Parity4.16 UNGATED B633 Fourier
UNTRUNCATED integrals of physical k/Z cells with zero source
eta_eeta_n weight vanish. This follows from original correct
source finite Fourier inversion and permits filtering the WHOLE
signed correlation BEFORE low-frequency Fourier truncation.
A truncated Fourier integral of such cell need NOT be zero. -/
theorem parity_original_historical_ungated_full_odd_zero_weight_B633_full_fourier434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (hZImage : Z∈(parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
        d L band slot δ Y e m K J k).image
        (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m))
    (hNot : Z∉parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    (∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalUngatedActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hBufSmooth hBufSupport ζ) = 0 := by
  obtain ⟨q,hq,hZscale⟩ := Finset.mem_image.mp hZImage
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMP := Finset.mem_filter.mp hProd.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hVal := hMem.2
  have hPos := parity_original_historical_ungated_physical_valid_k_z434
    d L band slot δ Y e m q.1 q.2 he hNe hVal
  dsimp only at hPos
  have hzpos := hPos.2.1
  have hdy := parity_original_historical_actual_z_in_own_dyad434
    (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hzpos
  have hZpos : 0<Z := by
    rw [←hZscale]
    exact hdy.1
  have hW := parity_original_historical_ungated_full_odd_nonselected_Z_source_zero434
    d L E V hL band slot δ ξ rho α signed Y e m K J k Z hNot χ
  have hFourier := parity_original_historical_ungated_true_k_Z_chi_B633_fourier_integral434
    d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ he
    hU hE hV hmLo hmHi hDyad buf a b hBufSmooth hBufSupport hBufOne hZpos
  rw [hW,mul_zero] at hFourier
  exact hFourier.symm
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFilteredFourierOuter -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22500000

/-- The CORRECTED original h=-2 all odd-e/n literal Parity4.16
B633 complex signed full 3D Fourier outer, now restricted to
only truly attained Z cells containing nonzero real source
eta_eeta_n weight, preserving each original H0, α,χ and ε
term exactly. This filtering occurs BEFORE frequency truncation,
not a fake signed subset dominance. -/
def parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            ∫ζ : EuclideanSpace ℝ (Fin 3),
              parityOriginalHistoricalUngatedActualB6333DFourierCell434
                d L U E V hL Z k band slot δ ξ rho α signed Y e m K
                (parityOriginalHistoricalFullNEnvelope434 V) χ
                buf a b hBufSmooth hBufSupport ζ)

/-- EXACT original FULL odd-e/n Parity(4.16) B633 Fourier sum may be
restricted to physically attained cells with SOME nonzero source
smoothing weight, because all excluded cells' COMPLETE Fourier
integrals vanish by the source-native true 3D Fourier inversion.

This is an exact complex identity on the full original signed
source; it does NOT claim a truncated Fourier integral vanishes
on a zero-weight cell. Thus subsequent low-frequency truncation
may be performed ONLY after this equality, avoiding a mathematically
invalid high-frequency tail omission or signed-subset inequality. -/
theorem parity_original_historical_ungated_full_odd_B633_outer_eq_nonzero_weight434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hBufSmooth : ContDiff ℝ ∞ buf)
    (hBufSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) :
    parityOriginalHistoricalUngatedFullOddB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hBufSmooth hBufSupport =
    parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hBufSmooth hBufSupport := by
  unfold parityOriginalHistoricalUngatedFullOddB633FourierOuter434
    parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
  apply Finset.sum_congr rfl
  intro e he
  have heOdd : Odd e := (Finset.mem_filter.mp he).2
  apply Finset.sum_congr rfl
  intro m hm
  have hmDyad := hDyad m hm
  have hDyad' : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
    intro mp hmp
    exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro χ hχ
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let S := (parityOriginalHistoricalUngatedFullOddKPhysicalEvents434
      d L band slot δ Y e m K J k).image
      (parityOriginalHistoricalPhysicalZScaleOfEvent434 e m)
  let P : ℕ → Prop := fun Z => ∃q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z,
      parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2 ≠ 0
  let F : ℕ → ℂ := fun Z =>
      ∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalUngatedActualB6333DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hBufSmooth hBufSupport ζ
  change (parityShiftTwoMaskCoefficient434 k.natAbs χ)*(∑Z∈S,F Z) =
    (parityShiftTwoMaskCoefficient434 k.natAbs χ)*(∑Z∈S.filter P,F Z)
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Z hZ
  change F Z = if P Z then F Z else 0
  by_cases hp : P Z
  · simp only [if_pos hp]
  · have hNot : Z∉parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hL band slot δ Y e m K J k := by
      intro hmem
      exact hp (Finset.mem_filter.mp hmem).2
    have hFullZero : F Z=0 :=
      parity_original_historical_ungated_full_odd_zero_weight_B633_full_fourier434
        d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ heOdd
        hU hE hV hmDyad.1 hmDyad.2.le hDyad' hZ hNot
        buf a b hBufSmooth hBufSupport hBufOne
    simp only [if_neg hp,hFullZero]
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedKZFourierTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- ACTUAL CORRECTED full odd-e natural B509 source Parity(4.15)
Fourier truncation error. The physical α/χ/ε H0 signed coefficient
and the original full source η_e(e/E)η_n(n/V) remain unchanged;
this is a norm of a TRUE original complex finite-signed difference,
not a surrogate 4.17 cancellation estimate. -/
def parityOriginalHistoricalUngatedActualKZ416FourierError434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℝ :=
  ‖parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ -
    (∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
      parityOriginalHistoricalUngatedActual3DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport ζ)‖

/-- FINITE CORRECTED original Parity (4.15)--(4.16) full 3D
Fourier truncation bound for the genuine UNGATED h=-2 physical
k/Z B509 two-prime-slot source, including group-P-bad e:

 ||Source_actual(e,m,k,Z,χ) - ∫_{||ζ||≤T} Fourier_actual||
  ≤ (Σ_(actual physical m',n) ||signed χ(m')H0 alpha pair||) *
       B_H(actual Euclidean 3D Schwartz eta_eeta_n) / T^H.

No source Pfree-e assumption, no unbounded spectral estimate,
no hypothetical large-Z extension and NO cost for the number of
Dirichlet characters. The full source Fourier inversion on the
NEW ungated physical carrier is used to justify termwise source
signal, then the ALREADY NATIVE-VERIFIED generic Schwartz
finite-sum Fourier tail applies exactly. -/
theorem parity_original_historical_ungated_actual_k_z_416_error_le_mass434
    (d : ℕ) (L : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (U E V : ℝ) (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    parityOriginalHistoricalUngatedActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport T ≤
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ) *
      (parityOriginal3DSourceMomentFiniteBudget434 H
        (parityOriginalHistoricalActualDyadicCutoffSchwartz434
          L hL U E V (Z:ℝ) k buf a b hSmooth hSupport)/T^H) := by
  let S := parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
    d L band slot δ Y e m K J k Z
  let W := parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
    d L band slot δ ξ rho α signed Y e m k χ
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hL U E V (Z:ℝ) k buf a b hSmooth hSupport
  let t := parityOriginalHistoricalPhysicalFourierEventTriple434
    U (Z:ℝ) e m (fun q : ℕ×ℕ=>q.1) (fun q : ℕ×ℕ=>q.2)
  have hOriginal := parity_original_historical_ungated_actual_k_z_physical_fourier434
    d L hL band slot δ ξ rho α signed Y e m K J k Z χ he
    U E V hU hE hV hmLo hmHi hDyad
    buf a b hSmooth hSupport hOne hZ
  have hFubini := parity_original_3d_physical_finite_source_fourier_fubini434
    S W t f
  have hSignal : parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ =
      parityOriginal3DPhysicalFiniteSignal434 S W t f :=
    hOriginal.trans hFubini.symm
  unfold parityOriginalHistoricalUngatedActualKZ416FourierError434
  rw [hSignal]
  exact parity_original_historical_actual_dyadic_finite_3d_truncation434
    S W t H L hL U E V (Z:ℝ) k
    buf a b hSmooth hSupport T hT
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedB633CellTail -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 21000000

/-- CORRECTED original Parity4.16 literal B633 full two-prime-slot
physical R³ Fourier integral at one actual ungated B509 e,m,k,Z,χ
minus the SAME literal B633 frequency-ball truncation, bounded by
the true original UNGATED source complex η_eη_n k/Z Fourier
error, via exact signed B633 integrand and original |χ(m)|≤1.
This theorem does not assume low-frequency Parity4.17 cancellation.
It holds for all odd e including original group P-prime powers. -/
def parityOriginalHistoricalUngatedActualB633FourierBall434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L) (Z : ℕ) (k : ℤ)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs))
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ, buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℂ :=
  ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _),
    parityOriginalHistoricalUngatedActualB6333DFourierCell434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport ζ

/-- A mathematically exact **per physical k/Z cell** B633 Fourier
truncation inequality. The FULL integral of the literal B633 two-core
kernel equals the actual source weighted h=-2 Cauchy pair times
original conjugate chi(m); the truncated integral has the SAME
pointwise integrand. Thus the cell truncation error is bounded by
the REAL source previously proved eta_e,L eta_n pre-Fourier error,
with factor ||chi(m)||<=1 and NO independent character count:

 ||int_{R^3} B633_cell - int_{||ζ||<=T} B633_cell||
   <= sourceOriginalActualKZ416FourierError.

This is not a Fourier tail estimate on the FULL unrestricted Parity
4.17 sum, only the exact physically supported B633 source cell. -/
theorem parity_original_historical_ungated_true_B633_fourier_ball_error_le_source434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (α : ℕ → ℂ) (signed : Bool)
    (Y e m : ℕ) (K J : Finset ℕ) (k : ℤ) (Z : ℕ)
    (χ : DirichletCharacter ℂ (2*k.natAbs)) (he : Odd e)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hmLo : U≤(m:ℝ)) (hmHi : (m:ℝ)≤2*U)
    (hDyad : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hBufOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (hZ : 0<Z) (H : ℕ) (T : ℝ) (hT : 0<T) :
    ‖(∫ζ : EuclideanSpace ℝ (Fin 3),
        parityOriginalHistoricalUngatedActualB6333DFourierCell434
          d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
          buf a b hSmooth hSupport ζ) -
      parityOriginalHistoricalUngatedActualB633FourierBall434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
        buf a b hSmooth hSupport T‖ ≤
    parityOriginalHistoricalUngatedActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport T := by
  let c : ℂ := star (χ (m : ZMod (2*k.natAbs)))
  let W : ℂ := parityOriginalHistoricalUngatedActualKZPhysicalWeightedSource434
      d L E V hL band slot δ ξ rho α signed Y e m K J k Z χ
  let f : EuclideanSpace ℝ (Fin 3) → ℂ := fun ζ =>
    parityOriginalHistoricalUngatedActual3DFourierCell434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport ζ
  have hFull := parity_original_historical_ungated_true_k_Z_chi_B633_fourier_integral434
    d L U E V hL band slot δ ξ rho α signed Y e m K J k Z χ he
    hU hE hV hmLo hmHi hDyad
    buf a b hSmooth hSupport hBufOne hZ
  have hBall : parityOriginalHistoricalUngatedActualB633FourierBall434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K J χ
      buf a b hSmooth hSupport T =
      c * ∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ := by
    unfold parityOriginalHistoricalUngatedActualB633FourierBall434
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ζ
    exact (parity_original_historical_ungated_actual_k_z_3d_fourier_eq_B633434
      d L U E V hL band slot δ ξ K J α Y e m he k Z χ rho signed
      hU hZ buf a b hSmooth hSupport ζ).symm
  have hC : ‖c‖≤1 := by
    change ‖star (χ (m : ZMod (2*k.natAbs)))‖ ≤ 1
    rw [norm_star]
    exact DirichletCharacter.norm_le_one χ _
  have hD : 0≤‖W-(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ :=
    norm_nonneg _
  have hCauchy : ‖c‖*‖W-(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ ≤
      ‖W-(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hC hD]
  rw [←hFull,hBall]
  change ‖c*W - c*(∫ζ in ({ζ : EuclideanSpace ℝ (Fin 3) | ‖ζ‖≤T}:Set _), f ζ)‖ ≤ _
  rw [←mul_sub,norm_mul]
  exact hCauchy
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedB633TailAggregate -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 24500000

/-- CORRECTED SOURCE original full odd-e h=-2 B509/H0 literal
Parity4.16 B633 complex Fourier outer minus its actual low-frequency
ball on source-filtered, genuinely nonzero η_eη_n Z cells, norm ≤
positive sum over ALL e,m,nonzero k,chi,Z of |cχ|×exact original
natural ungated source per-cell Fourier error. This uses only
triangle inequality and native |χ(m)|≤1, NEVER signed subset
comparison, no 4.17 spectral assumption, and no discarded
zero-weight cell after truncation. Original e P-primes allowed. -/
def parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℂ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          parityShiftTwoMaskCoefficient434 k.natAbs χ *
          (∑Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalUngatedActualB633FourierBall434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T)

/-- Literal nonnegative full-e,m,k,chi,Z source error budget for
the FILTERED original physically populated B633 outer. The actual
Parity(2.6) cchi is charged by its exact absolute norm; no invented
#characters factor and no bound on the full (4.17) correlation. -/
def parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (T : ℝ) : ℝ :=
  ∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
    ∑m∈K,
      ∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
              d L E V hL band slot δ Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) k,
            parityOriginalHistoricalUngatedActualKZ416FourierError434
              d L U E V hL Z k band slot δ ξ rho α signed Y e m K
              (parityOriginalHistoricalFullNEnvelope434 V) χ
              buf a b hSmooth hSupport T)

/-- EXACT FINITE ORIGINAL SOURCE PARITY(4.16) FOURIER TRUNCATION:

 ‖FullOddB633FilteredFourierOuter - FullOddB633FilteredBallOuter‖
 <= sum_(real full-odd e,m,k,chi,Z nonzero source cells)
      |cchi| * genuine source eta_e,L eta_n Fourier tail error.

All terms are literally the original B633 physical pair at z,z+2k
and original Q/P/B509 skipped-Q, b629 fine alpha and signed epsilon.
The only estimates applied are the triangle inequality and
‖chi(m)‖≤1; no independent correlation saving or unsupported
full 4.17 source mask is asserted. This is precisely the native
algebra needed to SUM the already PROVED source polynomial per-cell
B_H/T^H errors without discarding nonzero truncated integrals. -/
theorem parity_original_historical_ungated_full_odd_filtered_B633_ball_error_le_mass434
    (d : ℕ) (L U E V : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (ξ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → ℝ)
    (rho : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
    (signed : Bool) (Y : ℕ)
    (hU : 0<U) (hE : 0<E) (hV : 0<V)
    (hDyad : ∀m∈K,U≤(m:ℝ) ∧ (m:ℝ)<2*U)
    (buf : ℝ → ℂ) (a b : ℝ)
    (hSmooth : ContDiff ℝ ∞ buf)
    (hSupport : ∀t : ℝ,buf t≠0 → a≤t ∧ t≤b)
    (hOne : ∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1)
    (T : ℝ) (hT : 0<T) :
    ‖parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport -
      parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport T‖ ≤
    parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
      d L U E V hL band slot δ ξ rho K α signed Y
      buf a b hSmooth hSupport T := by
  unfold parityOriginalHistoricalUngatedFullOddFilteredB633FourierOuter434
    parityOriginalHistoricalUngatedFullOddFilteredB633BallOuter434
    parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro e he
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro m hm
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro k hk
  apply parity_original_historical_norm_sum_sub_le_finite_error434
  intro χ hχ
  let S := parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
    d L E V hL band slot δ Y e m K (parityOriginalHistoricalFullNEnvelope434 V) k
  let c := parityShiftTwoMaskCoefficient434 k.natAbs χ
  let F : ℕ → ℂ := fun Z =>
    ∫ζ : EuclideanSpace ℝ (Fin 3),
      parityOriginalHistoricalUngatedActualB6333DFourierCell434
        d L U E V hL Z k band slot δ ξ rho α signed Y e m K
        (parityOriginalHistoricalFullNEnvelope434 V) χ
        buf a b hSmooth hSupport ζ
  let G : ℕ → ℂ := fun Z =>
    parityOriginalHistoricalUngatedActualB633FourierBall434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) χ
      buf a b hSmooth hSupport T
  let Err : ℕ → ℝ := fun Z =>
    parityOriginalHistoricalUngatedActualKZ416FourierError434
      d L U E V hL Z k band slot δ ξ rho α signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) χ
      buf a b hSmooth hSupport T
  have hCell : ∀Z∈S, ‖F Z-G Z‖≤Err Z := by
    intro Z hZ
    have hData := (Finset.mem_filter.mp hZ).2
    obtain ⟨q,hq,hw⟩ := hData
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    have hqData := Finset.mem_filter.mp hq
    have hqProd := Finset.mem_product.mp hqData.1
    have hmPrime := Finset.mem_filter.mp hqProd.1
    have hNe : m≠q.1 := (Finset.mem_erase.mp hmPrime.1).1.symm
    have hValid := hqData.2.1
    have hPositive := parity_original_historical_ungated_physical_valid_k_z434
      d L band slot δ Y e m q.1 q.2 heOdd hNe hValid
    dsimp only at hPositive
    have hz : 0<parityOriginalHistoricalCanonicalZ434 e m q.1 q.2 := hPositive.2.1
    have hZscale := hqData.2.2.2
    have hZpos : 0<Z := by
      have hh := (parity_original_historical_actual_z_in_own_dyad434
        (parityOriginalHistoricalCanonicalZ434 e m q.1 q.2) hz).1
      rw [hZscale] at hh
      exact hh
    have hmD := hDyad m hm
    have hAllD : ∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)≤2*U := by
      intro mp hmp
      exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩
    exact parity_original_historical_ungated_true_B633_fourier_ball_error_le_source434
      d L U E V hL band slot δ ξ rho α signed Y e m K
      (parityOriginalHistoricalFullNEnvelope434 V) k Z χ heOdd
      hU hE hV hmD.1 hmD.2.le hAllD
      buf a b hSmooth hSupport hOne hZpos 0 T hT
  have hZsum : ‖(∑Z∈S,F Z)-(∑Z∈S,G Z)‖≤∑Z∈S,Err Z :=
    parity_original_historical_norm_sum_sub_le_finite_error434 S F G Err hCell
  change ‖c*(∑Z∈S,F Z)-c*(∑Z∈S,G Z)‖ ≤ ‖c‖*(∑Z∈S,Err Z)
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left hZsum (norm_nonneg c)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedSmoothedZDyadic -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19000000

/-- Original Parity4.15/4.17 true physically populated ungated
h=-2 B509/H0 k/Z cell has exactly the original wider η_eη_n
SOURCE smoothed dyadic height window:
 (exp L/16)L^K0 < Z < 8 exp L L^(K0+88),
including e with original group P prime divisors, without the
old e*vStar=ordinaryP(u) source shortcut. The proof derives
u=m*n-2>0, e|u and e*z=m'*u from the NEW source physical carrier
and uses source-independent true bump support and shifted-u dyad. -/
theorem parity_original_historical_ungated_full_odd_smoothed_actual_Z_window434
    (d : ℕ) (L U V E K0 : ℝ) (hL : 8≤L)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0) :
    (Real.exp L/16)*L^K0 < (Z:ℝ) ∧
    (Z:ℝ) < 8*Real.exp L*L^(K0+88) := by
  let z := parityOriginalHistoricalCanonicalZ434 e m q.1 q.2
  have hMem := Finset.mem_filter.mp hq
  have hProd := Finset.mem_product.mp hMem.1
  have hMp := Finset.mem_filter.mp hProd.1
  have hMpK : q.1∈K := (Finset.mem_erase.mp hMp.1).2
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMp.1).1.symm
  have hValid := hMem.2.1
  have hzPos : 0<z := hMem.2.2.1
  have hzScale : parityOriginalHistoricalActualZDyadicScale434 z=Z := hMem.2.2.2
  have hDy := parity_original_historical_actual_z_in_own_dyad434 z hzPos
  rw [hzScale] at hDy
  have hmD := hDyad m hm
  have hmpD := hDyad q.1 hMpK
  obtain ⟨u,hu,up,hup,hDiv,hDivp,hvs,hvps⟩ := hValid
  have hmn : m*q.2=u+2 := (Finset.mem_filter.mp hu).2.2.2
  have hUeq : u=e*(u/e) := (Nat.mul_div_cancel_left' hDiv).symm
  have hZexact : z=q.1*(u/e) := by
    dsimp [z,parityOriginalHistoricalCanonicalZ434,
      parityOriginalHistoricalCanonicalV434]
    have huN : m*q.2-2=u := by omega
    rw [huN]
  have hEz : e*z=q.1*u := by
    calc
      _ = e*(q.1*(u/e)) := by rw [hZexact]
      _ = q.1*(e*(u/e)) := by ring
      _ = q.1*u := by rw [←hUeq]
  have hZ := parity_original_historical_full_odd_smoothed_physical_z_scale434
    L U V E K0 e m q.1 q.2 u z hL hU hV hUV hE hw
    hmD.1 hmpD.1 hmpD.2 hu hEz
  have hzReal : (z:ℝ) < 2*(Z:ℝ) := by exact_mod_cast hDy.2.2
  have hZlo : (Real.exp L/16)*L^K0 < (Z:ℝ) := by
    have hLp : 0<L^K0 := Real.rpow_pos_of_pos (by linarith : 0<L) _
    nlinarith [hZ.1,hzReal,hLp]
  have hZR : (Z:ℝ)≤(z:ℝ) := by exact_mod_cast hDy.2.1
  exact ⟨hZlo,hZR.trans_lt hZ.2⟩
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedSmoothedZPolylog -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 16500000

/-- Fully original Parity4.17 z-window for TRUE corrected UNGATED
B509/H0 smooth odd e,n physical source, including e with P factors.
Reproved with real source u=m*n−2 and k≠0 rather than old selected-Q
e-gate; source physical Z satisfies exp(L)L^-(K0+90) ≤ Z ≤
exp(L)L^(K0+90) whenever actual eta_eeta_n nonzero. -/
theorem parity_original_historical_ungated_full_odd_smooth_Z_polylog_numeric434
    (L K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0) :
    16*L^(-(K0+90)) ≤ L^K0 ∧
    8*L^(K0+88) ≤ L^(K0+90) := by
  have hLp : 0<L := by linarith
  have hL1 : 1≤L := by linarith
  have hLsq : (16:ℝ)≤L^2 := by nlinarith [hL]
  have hp2 : 0<L^(K0-2) := Real.rpow_pos_of_pos hLp _
  have hsmall : L^(-(K0+90)) ≤ L^(K0-2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hpow : L^(K0-2)*L^2=L^K0 := by
    rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
    congr 1
    push_cast
    ring
  have hsmallA : 16*L^(-(K0+90)) ≤ 16*L^(K0-2) :=
    mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have hsmallB : 16*L^(K0-2)≤L^2*L^(K0-2) :=
    mul_le_mul_of_nonneg_right hLsq hp2.le
  have hUpper : 8*L^(K0+88)≤L^(K0+90) := by
    have hP : 0<L^(K0+88) := Real.rpow_pos_of_pos hLp _
    have h8 : (8:ℝ)≤L^2 := by linarith
    have hh : 8*L^(K0+88)≤L^2*L^(K0+88) :=
      mul_le_mul_of_nonneg_right h8 hP.le
    calc
      _ ≤ L^2*L^(K0+88) := hh
      _ = L^(K0+90) := by
        rw [←Real.rpow_natCast L 2,←Real.rpow_add hLp]
        congr 1
        ring
  constructor
  · calc
      _ ≤ 16*L^(K0-2) := hsmallA
      _ ≤ L^2*L^(K0-2) := hsmallB
      _ = L^K0 := by rw [mul_comm]; exact hpow
  · exact hUpper

/-- The source-correct ACTUAL full odd-e,n smoothed dyadic Z
window is LEGAL in the SAME Parity(4.17) polynomial height range
as the historical selected-Q proof, despite its wider cutoffs:

 exp L L^(-(K0+90)) ≤ Z ≤ exp L L^(K0+90).

No old E-window/n dyad premise is smuggled in: only the genuinely
proved smoother range and a sufficiently large L with K0≥0. -/
theorem parity_original_historical_ungated_full_odd_smooth_Z_Parity417_window434
    (L Z K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (hLo : (Real.exp L/16)*L^K0 < Z)
    (hHi : Z < 8*Real.exp L*L^(K0+88)) :
    Real.exp L*L^(-(K0+90))≤Z ∧
      Z≤Real.exp L*L^(K0+90) := by
  obtain ⟨hNumLo,hNumHi⟩ :=
    parity_original_historical_ungated_full_odd_smooth_Z_polylog_numeric434 L K0 hL hK0
  have hx : 0≤Real.exp L/16 := by positivity
  have hZlo : Real.exp L*L^(-(K0+90)) ≤ (Real.exp L/16)*L^K0 := by
    have hh := mul_le_mul_of_nonneg_left hNumLo hx
    calc
      _ = (Real.exp L/16)*(16*L^(-(K0+90))) := by ring
      _ ≤ (Real.exp L/16)*L^K0 := hh
  have hZhi : 8*Real.exp L*L^(K0+88) ≤ Real.exp L*L^(K0+90) := by
    have hh := mul_le_mul_of_nonneg_left hNumHi (Real.exp_pos L).le
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  exact ⟨(hZlo.trans_lt hLo).le,(hHi.trans_le hZhi).le⟩

/-- For an ACTUAL populated physical full odd-e,n source k/Z
cell, whenever its original smoothed η_eη_n weight is nonzero,
Parity(4.17)'s true height hypotheses hold with the same fixed
exponent CZ=K0+90 as in the original manuscript source:
 exp L L^(-CZ) ≤ (Z:ℝ) ≤ exp L L^CZ.
This is proved with the corrected factor-eight smoothing support
and exact binary dyadic Z, never by reusing the old sparse E-window. -/
theorem parity_original_historical_ungated_full_odd_actual_Z_Parity417_legal434
    (d : ℕ) (L U V E K0 : ℝ) (hL : 8≤L) (hK0 : 0≤K0)
    (band : Fin (d+1)) (slot : Fin 20)
    (δ : Fin (sourceOrderedLabels 20
      (sourceActualSortedScales 20 d L) band slot).length → Bool)
    (K J : Finset ℕ) (e m : ℕ) (k : ℤ) (Z : ℕ)
    (he : Odd e) (hU : 0<U) (hV : 0<V)
    (hUV : Real.exp L≤U*V) (hE : E=U*L^(-K0))
    (hm : m∈K) (hDyad : ∀mp∈K,
      U≤(mp:ℝ) ∧ (mp:ℝ)<2*U)
    (q : ℕ×ℕ)
    (hq : q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
      d L band slot δ ⌊2*Real.exp L⌋₊ e m K J k Z)
    (hw : parityOriginalHistoricalDyadicEtaWeight434 L E V hL e q.2≠0) :
    Real.exp L*L^(-(K0+90))≤(Z:ℝ) ∧
    (Z:ℝ)≤Real.exp L*L^(K0+90) := by
  obtain ⟨hZlo,hZhi⟩ :=
    parity_original_historical_ungated_full_odd_smoothed_actual_Z_window434
      d L U V E K0 hL band slot δ K J e m k Z he hU hV hUV
      hE hm hDyad q hq hw
  exact parity_original_historical_ungated_full_odd_smooth_Z_Parity417_window434
    L (Z:ℝ) K0 hL hK0 hZlo hZhi
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedFullOddKZMassZ -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 19500000

/-- Source-correct original Parity4.15 physically nonzero η_eη_n
ungated B509/H0 k,Z Fourier coefficient ℓ1 mass ≤
Acoef² Z L^(2CW1+256+K0+90), with REAL group-P-bad e allowed.
Proof via independent ungated true full positive diagonal and
true smoothed source Z≥expL L^-(K0+90), no spectrum or
arbitrary number of cofactor/character factors. -/
theorem parity_eventually_original_ungated_full_odd_k_z_l1_mass_Z434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool) (Acoef : ℝ),
      0≤Acoef → (∀m∈K,‖α m‖≤Acoef) →
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k Z →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 →
      ∀χ : DirichletCharacter ℂ (2*k.natAbs),
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k Z)
        (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α signed
          ⌊2*Real.exp L⌋₊ e m k χ) ≤
      Acoef^2*(Z:ℝ)*
        L^(2*parityOriginalW1PolylogExponent434+256+K0+90) := by
  filter_upwards [parity_eventually_original_historical_ungated_full_odd_k_z_mass_X434,
    eventually_ge_atTop (8:ℝ)] with L hMass hL8
  refine ⟨hMass.1,hL8,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed Acoef hA hα
    hU hV hUV hScale hDyad e m k Z he heMem hm q hq hw χ
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Eenv := parityOriginalHistoricalFullOddEEnvelope434 E
  have hLpos : 0<L := by linarith
  have hZ := parity_original_historical_ungated_full_odd_actual_Z_Parity417_legal434
    (sourceOriginalLiteralDepth 20 L) L U V E K0 hL8 hK0
    band slot δ K J e m k Z he hU hV hUV hScale hm hDyad q hq hw
  have hMassBound := hMass.2 band slot δ ξ rho K Eenv J α signed Acoef
    hA hα e m k Z he heMem hm χ
  have hConvert := parity_original_historical_source_X_to_Z_polylog434
    L (Z:ℝ) (2*parityOriginalW1PolylogExponent434+256) K0 hLpos hZ.1
  have hCoefSq : 0≤Acoef^2 := sq_nonneg _
  have hMult := mul_le_mul_of_nonneg_left hConvert hCoefSq
  calc
    _ ≤ Acoef^2*Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256) := hMassBound
    _ = Acoef^2*(Real.exp L*L^(2*parityOriginalW1PolylogExponent434+256)) := by ring
    _ ≤ Acoef^2*((Z:ℝ)*L^((2*parityOriginalW1PolylogExponent434+256)+K0+90)) := hMult
    _ = Acoef^2*(Z:ℝ)*L^(2*parityOriginalW1PolylogExponent434+256+K0+90) := by ring
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedKZTailUniform -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 22500000

/-- Corrected original Parity4.15 h=-2 true UNGATED k,Z,χ B509
source finite Fourier error ≤ exact physical source cofactor ℓ1
mass times ONE uniform native Euclidean 3D SOURCE Schwartz moment
C_H L^[5(K0+90)(H+P+1)]/T^H; no original selected-Q e Pfree
hypothesis. Source true nonzero η_eη_n physical event provides
k≠0 and Z within original Parity4.17 legal source window. The moment
bound is SOURCE-INDEPENDENT and its hypotheses are discharged using
new corrected ungated real physical e,m,k,Z carrier.
No analytic Parity4.17 saving assumed. -/
theorem parity_eventually_original_ungated_full_odd_k_z_416_tail_actual_mass_uniform434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool),
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (e m : ℕ) (k : ℤ) (Z : ℕ) (he : Odd e),
      e∈parityOriginalHistoricalFullOddEEnvelope434 E → m∈K →
      ∀ (q : ℕ×ℕ),
      q∈parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        (sourceOriginalLiteralDepth 20 L) L band slot δ
        ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) k Z →
      parityOriginalHistoricalDyadicEtaWeight434 L E V hLw e q.2≠0 →
      ∀ (χ : DirichletCharacter ℂ (2*k.natAbs))
        (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 →
          -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      parityOriginalHistoricalUngatedActualKZ416FourierError434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw Z k band slot δ ξ
        rho α signed ⌊2*Real.exp L⌋₊ e m K
        (parityOriginalHistoricalFullNEnvelope434 V) χ
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      parityOriginal3DPhysicalFiniteCoefficientMass434
        (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
          (sourceOriginalLiteralDepth 20 L) L band slot δ
          ⌊2*Real.exp L⌋₊ e m K
          (parityOriginalHistoricalFullNEnvelope434 V) k Z)
        (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
          (sourceOriginalLiteralDepth 20 L) L band slot δ ξ rho α
          signed ⌊2*Real.exp L⌋₊ e m k χ) *
        (parityOriginalHistoricalActual3DFourierMomentFixedK434
          A R buf hSmooth hSupport H *
          L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H) := by
  filter_upwards [eventually_ge_atTop (max ((3:ℝ)^256) (8:ℝ))] with L hLarge
  have hL : 8≤L := le_trans (le_max_right _ _) hLarge
  have hL3 : (3:ℝ)^256≤L := le_trans (le_max_left _ _) hLarge
  refine ⟨hL3,hL,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed hU hV hUV hScale hDyad
    e m k Z he heMem hm q hq hw χ A R hA hR buf hSmooth hSupport
    hOne hCube H hLargeE hLargeN T hT
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := ⌊2*Real.exp L⌋₊
  let f := parityOriginalHistoricalActualDyadicCutoffSchwartz434
    L hLw U E V (Z:ℝ) k buf (-Real.log A) (Real.log A) hSmooth hSupport
  let mass := parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Power : ℝ := L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))
  have hLp : 0<L := by linarith
  have hEpos : 0<E := by
    rw [hScale]
    exact mul_pos hU (Real.rpow_pos_of_pos hLp _)
  have hmDyad := hDyad m hm
  have hZrange := parity_original_historical_ungated_full_odd_smoothed_actual_Z_window434
    d L U V E K0 hLw band slot δ K J e m k Z he hU hV hUV hScale
    hm hDyad q hq hw
  have hZlegal := parity_original_historical_full_odd_smooth_Z_Parity417_window434
    L (Z:ℝ) K0 hLw hK0 hZrange.1 hZrange.2
  have hZreal : (0:ℝ)<(Z:ℝ) :=
    (mul_pos (Real.exp_pos L) (Real.rpow_pos_of_pos hLp (-(K0+90)))).trans_le hZlegal.1
  have hZ : 0<Z := by exact_mod_cast hZreal
  have hQ := Finset.mem_filter.mp hq
  have hQprod := Finset.mem_product.mp hQ.1
  have hMP := Finset.mem_filter.mp hQprod.1
  have hNe : m≠q.1 := (Finset.mem_erase.mp hMP.1).1.symm
  have hReal := parity_original_historical_ungated_physical_valid_k_z434
    d L band slot δ Y e m q.1 q.2 he hNe hQ.2.1
  dsimp only at hReal
  have hK : parityOriginalHistoricalOffdiagK434 e m q.1=k := hMP.2
  have hk : k≠0 := by
    rw [←hK]
    exact hReal.1
  have hBH := parity_original_historical_full_odd_source_BH_uniform_polylog434
    L U E V (Z:ℝ) K0 A hLw hK0 k hk hU hV hUV hScale
    (by exact_mod_cast (Nat.zero_le Z)) hZrange.2.le
    hA buf hSmooth hSupport H hLargeE hLargeN R hR hCube
  have hTbound : parityOriginalHistoricalUngatedActualKZ416FourierError434
    d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
    buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
    mass*(parityOriginal3DSourceMomentFiniteBudget434 H f/T^H) :=
    parity_original_historical_ungated_actual_k_z_416_error_le_mass434
      d L hLw band slot δ ξ rho α signed Y e m K J k Z χ he
      U E V hU hEpos hV hmDyad.1 hmDyad.2.le
      (by intro mp hmp; exact ⟨(hDyad mp hmp).1,(hDyad mp hmp).2.le⟩)
      buf (-Real.log A) (Real.log A) hSmooth hSupport hOne hZ H T hT
  have hDiv : parityOriginal3DSourceMomentFiniteBudget434 H f/T^H ≤
      C*Power/T^H :=
    div_le_div_of_nonneg_right hBH (pow_pos hT H).le
  have hM : 0 ≤ mass := parity_original_3d_physical_finite_coefficient_mass_nonneg434 _ _
  exact hTbound.trans (mul_le_mul_of_nonneg_left hDiv hM)
end Green64Analytic.Parity

end

end

/-! ## OriginalHistoricalUngatedTailToDiagonal -/

section

open Filter Real MeasureTheory
open scoped BigOperators Classical ContDiff RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace Green64Analytic.Parity
open Green64Analytic.SourceBlockSieve Green64Analytic.ShiftTwoTerminal
open Green64Analytic.CorrelationSquare Green64Analytic.CorrelationD
set_option autoImplicit false
set_option maxHeartbeats 29000000

/-- **GLOBAL TRUE CORRECTED UNGATED ORIGINAL SOURCE FOURIER TAIL**
for every physically populated all-odd e, m, k, Dirichlet χ and
actual nonzero-η_eη_n binary Z, the REAL sum of absolute B633
3D Fourier truncation errors ≤ one FIXED source C_H L^X/T^H
factor times total original natural a_v(u/e) physical χ-weighted
cofactor source ℓ1 mass. No #characters, #Z, #cofactors or #e.
Only true 3D source Schwartz H moment and positivity of finite
sums are used. This does NOT assert any Parity4.17 signed saving.
P-group-bad odd e are included correctly. -/
theorem parity_eventually_original_ungated_full_odd_filtered_tail_le_coefficient_mass434
    (K0 : ℝ) (hK0 : 0≤K0) :
    ∀ᶠ L : ℝ in atTop, (3:ℝ)^256≤L ∧ 8≤L ∧
      ∀ (hLw : 8≤L)
        (band : Fin (sourceOriginalLiteralDepth 20 L+1)) (slot : Fin 20)
        (δ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → Bool)
        (ξ : Fin (sourceOrderedLabels 20
          (sourceActualSortedScales 20 (sourceOriginalLiteralDepth 20 L) L)
          band slot).length → ℝ)
        (rho U V E : ℝ) (K : Finset ℕ) (α : ℕ → ℂ)
        (signed : Bool),
      0<U → 0<V → Real.exp L≤U*V → E=U*L^(-K0) →
      (∀mp∈K,U≤(mp:ℝ) ∧ (mp:ℝ)<2*U) →
      ∀ (A R : ℝ) (hA : 0<A) (hR : 1≤R)
        (buf : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ buf)
        (hSupport : ∀t : ℝ,buf t≠0 → -Real.log A≤t ∧ t≤Real.log A),
      (∀t∈Set.Icc (0:ℝ) (Real.log 2),buf t=1) →
      (∀t∈parityOriginalHistoricalEuclideanFixedLogCube434 A,‖t‖≤R) →
      ∀ (H : ℕ),
      2*A*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)≤L →
      (8*A^2*((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*
        (2:ℝ)^(H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower)+
        ((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower).factorial:ℝ)*A≤L) →
      ∀ (T : ℝ),0<T →
      let Q : ℝ :=
        parityOriginalHistoricalActual3DFourierMomentFixedK434 A R buf hSmooth hSupport H *
        L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
      parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
        (sourceOriginalLiteralDepth 20 L) L U E V hLw band slot δ ξ rho
        K α signed ⌊2*Real.exp L⌋₊
        buf (-Real.log A) (Real.log A) hSmooth hSupport T ≤
      Q * parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
        (sourceOriginalLiteralDepth 20 L) L E V hLw band slot δ ξ rho
        α signed ⌊2*Real.exp L⌋₊ K := by
  filter_upwards [parity_eventually_original_ungated_full_odd_k_z_416_tail_actual_mass_uniform434
    K0 hK0] with L hSource
  refine ⟨hSource.1,hSource.2.1,?_⟩
  intro hLw band slot δ ξ rho U V E K α signed hU hV hUV hScale hDyad
    A R hA hR buf hSmooth hSupport hOne hCube H hLargeE hLargeN T hT
  dsimp only
  let d := sourceOriginalLiteralDepth 20 L
  let J := parityOriginalHistoricalFullNEnvelope434 V
  let Y := ⌊2*Real.exp L⌋₊
  let C : ℝ := parityOriginalHistoricalActual3DFourierMomentFixedK434
    A R buf hSmooth hSupport H
  let Q : ℝ := C *
    L^((5*(K0+90))*(((H+(volume : Measure (EuclideanSpace ℝ (Fin 3))).integrablePower:ℕ):ℝ)+1))/T^H
  let S : ℕ → ℕ → ℤ → Finset ℕ := fun e m k =>
    parityOriginalHistoricalUngatedFullOddNonzeroWeightZCells434
      d L E V hLw band slot δ Y e m K J k
  let Mass (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (Z : ℕ) : ℝ :=
    parityOriginal3DPhysicalFiniteCoefficientMass434
      (parityOriginalHistoricalUngatedActualKZPhysicalEventCarrier434
        d L band slot δ Y e m K J k Z)
      (parityOriginalHistoricalUngatedActualKZPhysicalSignedCoefficient434
        d L band slot δ ξ rho α signed Y e m k χ)
  let Err (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (Z : ℕ) : ℝ :=
    parityOriginalHistoricalUngatedActualKZ416FourierError434
      d L U E V hLw Z k band slot δ ξ rho α signed Y e m K J χ
      buf (-Real.log A) (Real.log A) hSmooth hSupport T
  have hC : 0≤C := parity_original_historical_3d_fourier_fixed_moment_K_nonneg434
    A R buf hSmooth hSupport H hR
  have hLp : 0<L := by linarith [hSource.2.1]
  have hQ : 0≤Q := by
    dsimp [Q]
    positivity
  have hCell (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E)
      (hm : m∈K) (Z : ℕ) (hZ : Z∈S e m k) :
      Err e m k χ Z ≤ Mass e m k χ Z * Q := by
    have heOdd : Odd e := (Finset.mem_filter.mp he).2
    obtain ⟨q,hq,hw⟩ := (Finset.mem_filter.mp hZ).2
    have hStep := hSource.2.2 hLw band slot δ ξ rho U V E K α signed
      hU hV hUV hScale hDyad e m k Z heOdd he hm q hq hw χ
      A R hA hR buf hSmooth hSupport hOne hCube H hLargeE hLargeN T hT
    exact hStep
  have hZ (e m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ (2*k.natAbs))
      (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E) (hm : m∈K) :
      (∑Z∈S e m k, Err e m k χ Z) ≤
        Q*(∑Z∈S e m k,Mass e m k χ Z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Z hz
    have hh := hCell e m k χ he hm Z hz
    simpa only [mul_comm] using hh
  have hχ (e m : ℕ) (k : ℤ)
      (he : e∈parityOriginalHistoricalFullOddEEnvelope434 E) (hm : m∈K) :
      (∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Err e m k χ Z)) ≤
      Q*(∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Mass e m k χ Z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    have hh := mul_le_mul_of_nonneg_left
      (hZ e m k χ he hm)
      (norm_nonneg (parityShiftTwoMaskCoefficient434 k.natAbs χ))
    calc
      _ ≤ ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (Q*(∑Z∈S e m k,Mass e m k χ Z)) := hh
      _ = Q*(‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Mass e m k χ Z)) := by ring
  unfold parityOriginalHistoricalUngatedFullOddFilteredB633TailMass434
    parityOriginalHistoricalUngatedFullOddFilteredCoefficientMass434
  change (∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
      ∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
        ∑χ : DirichletCharacter ℂ (2*k.natAbs),
          ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
          (∑Z∈S e m k,Err e m k χ Z)) ≤
      Q*(∑e∈parityOriginalHistoricalFullOddEEnvelope434 E,
        ∑m∈K,∑k∈parityOriginalHistoricalNonzeroKSupport434 e m K,
          ∑χ : DirichletCharacter ℂ (2*k.natAbs),
            ‖parityShiftTwoMaskCoefficient434 k.natAbs χ‖ *
            (∑Z∈S e m k,Mass e m k χ Z))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hχ e m k he hm
end Green64Analytic.Parity

end

end

