module

public import Green64.Library.Weights.Part054
public import Green64.Library.Weights.Part023
public import Green64.Library.Weights.Part017

@[expose] public section

/-!
# Weights / Part055

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26AuxBanUniformSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exponential BIG-prime size absorbs the actual finite ban cost AFTER
all conductor/retention exponents are fixed. The eventual threshold is
before every moving slot count, auxiliary count, Q and xi. -/
theorem eventually_source_original_aux_ban_budget434
    (a v Cs Cslots D : ℝ) (Cq Cxi : ℕ)
    (ha : 0 < a) (hv : 0 < v) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      ∀ (A M Q : ℕ) (xi : ℝ),
        (A:ℝ) ≤ Cs*Real.log L → (M:ℝ) ≤ L^Cslots →
        (Q:ℝ) ≤ L^Cq → 0 < xi → xi⁻¹ ≤ L^Cxi →
        (A:ℝ)*(2*M:ℕ)/(Real.exp (L^a)*v)*((Q:ℝ)^4*(xi⁻¹)^2) ≤ L^(-D) := by
  let CB : ℝ := ((4*Cq+2*Cxi:ℕ):ℝ)
  let K : ℝ := 2*Cs/v
  filter_upwards [eventually_source_fixed_poly_exp_saving a K (1+Cslots+CB) D ha]
    with L hL
  have hLp : 0 < L := by linarith [hL.1]
  refine ⟨hL.1,?_⟩
  intro A M Q xi hA hM hQ hxi hXi
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have hAL : (A:ℝ) ≤ Cs*L :=
    hA.trans (mul_le_mul_of_nonneg_left hlog hCs)
  have hQ4 := pow_le_pow_left₀ (Nat.cast_nonneg Q : (0:ℝ) ≤ _) hQ 4
  have hXi2 := pow_le_pow_left₀ (inv_nonneg.mpr hxi.le) hXi 2
  have hB : (Q:ℝ)^4*(xi⁻¹)^2 ≤ L^CB := by
    calc
      _ ≤ (L^Cq)^4*(L^Cxi)^2 := mul_le_mul hQ4 hXi2 (sq_nonneg _) (by positivity)
      _ = L^CB := by
        dsimp only [CB]
        rw [Real.rpow_natCast,←pow_mul,←pow_mul,←pow_add]
        congr 1
        omega
  have hNum : (A:ℝ)*(2*M:ℕ) ≤ (Cs*L)*(2*L^Cslots) := by
    push_cast
    exact mul_le_mul hAL (mul_le_mul_of_nonneg_left hM (by norm_num))
      (by positivity) (mul_nonneg hCs hLp.le)
  have hden : 0 < Real.exp (L^a)*v := mul_pos (Real.exp_pos _) hv
  calc
    _ ≤ ((Cs*L)*(2*L^Cslots)/(Real.exp (L^a)*v))*L^CB :=
      mul_le_mul (div_le_div_of_nonneg_right hNum hden.le) hB
        (by positivity) (by positivity)
    _ = K*L^(1+Cslots+CB)*Real.exp (-(L^a)) := by
      rw [Real.rpow_add hLp,Real.rpow_add hLp,Real.rpow_one,Real.exp_neg]
      dsimp only [K]
      ring
    _ ≤ 1/L^D := hL.2
    _ = L^(-D) := by rw [Real.rpow_neg hLp.le,one_div]

/-- A genuine analytic saving for the literal original B26 auxiliary
ban error. In particular J, ell and all types/data are quantified AFTER
the threshold, subject to their displayed original growth bounds. -/
theorem eventually_source_original_B26_canonical_aux_ban_saving434
    (a v Cs Cslots D : ℝ) (Cq Cxi : ℕ)
    (ha : 0 < a) (hv : 0 < v) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
        (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
        (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
        (Q : ℕ) (hA hB xi : ℝ),
        0 < hA → 0 < hB → 0 < xi →
        (∀ g,V g = ∑ p ∈ P g,1/(p:ℝ)) →
        (∀ g,v ≤ V g) →
        (∀ g p,p ∈ P g → Real.exp (L^a) ≤ (p:ℝ)) →
        ((ν.1.card+ν.2.card:ℕ):ℝ) ≤ Cs*Real.log L →
        ((J+ell:ℕ):ℝ) ≤ L^Cslots →
        (Q:ℝ) ≤ L^Cq → xi⁻¹ ≤ L^Cxi →
        ∀ (dsmall : ℕ)
          (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
          (sigma tau : BigGroupPerm (BG := G) (J+ell))
          (ζ theta : ℝ) (o k : ℤ),
          o=1 ∨ o= -1 →
          ‖sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ ν
            Q hA hB xi dsmall s t sigma tau ζ theta o k‖ ≤ L^(-D) := by
  filter_upwards [eventually_source_original_aux_ban_budget434
    a v Cs Cslots D Cq Cxi ha hv hCs] with L hL
  intro G _ _ P _ V J ell m hmJ ν hDisj Q hA hB xi
    hhA hhB hxi hV hVmin hPmin hCard hSlots hQ hXi
    dsmall s t sigma tau ζ theta o k ho
  exact (source_original_B26_canonical_aux_ban_error_bound434
    P V J ell m hmJ ν hDisj Q hA hB xi hhA hhB hxi
    (Real.exp (L^a)) v (Real.exp_pos _) hv hV hVmin hPmin
    dsmall s t sigma tau ζ theta o k ho).trans
      (hL.2 (ν.1.card+ν.2.card) (J+ell) Q xi hCard hSlots hQ hxi hXi)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26AllNuAuxBanSaving -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- The actual B26 auxiliary-ban errors summed over the genuine moving
two-block family and all four original shared endpoint sign choices.
Every moving type, J, ell, m, prime support and endpoint array is AFTER
the threshold. Conductor exponents are fixed first and cause no cycle. -/
theorem eventually_source_original_B26_ALL_NU_aux_ban_saving434
    (a v C0 Cslots D : ℝ) (Cq Cxi tmax : ℕ)
    (ha : 0 < a) (hv : 0 < v) (hC0 : 0 ≤ C0) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type} [Fintype G] [DecidableEq G]
        (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
        (V : G → ℝ) (blockA blockB : Finset G)
        (hBlocks : Disjoint blockA blockB)
        (J ell m : ℕ) (hmJ : m ≤ J) (hm : m ≤ tmax)
        (Q : ℕ) (hA hB xi : ℝ),
        0 < hA → 0 < hB → 0 < xi →
        (∀ g,V g = ∑ p ∈ P g,1/(p:ℝ)) →
        (∀ g,v ≤ V g) →
        (∀ g p,p ∈ P g → Real.exp (L^a) ≤ (p:ℝ)) →
        ((blockA.card+blockB.card:ℕ):ℝ) ≤ C0*Real.log L →
        ((J+ell:ℕ):ℝ) ≤ L^Cslots →
        (Q:ℝ) ≤ L^Cq → xi⁻¹ ≤ L^Cxi →
        ∀ (dsmall : SourceOriginalProbePattern434 G m → ℕ)
          (s t : SourceOriginalProbePattern434 G m →
            (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g})
          (sigma tau : SourceOriginalProbePattern434 G m →
            BigGroupPerm (BG := G) (J+ell))
          (ζ theta : SourceOriginalProbePattern434 G m → ℝ)
          (o : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
          (ho : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
            o ν=1 ∨ o ν= -1)
          (nSmall : ℕ) (epsSrc epsTgt : Bool),
        let shared := fun ν : SourceOriginalProbePattern434 G m =>
          nSmall*J + ∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
        let sign := fun ν : SourceOriginalProbePattern434 G m =>
          (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
          (if epsTgt then (-1:ℂ)^(shared ν) else 1)
        ‖∑ ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m,
          sign ν * sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ ν
            Q hA hB xi (dsmall ν) (s ν) (t ν) (sigma ν) (tau ν)
              (ζ ν) (theta ν) (o ν) k‖ ≤ L^(-D) := by
  let E : ℝ := (tmax:ℝ)*C0*Real.log 2
  have hCs : 0 ≤ (tmax:ℝ)*C0 := mul_nonneg (Nat.cast_nonneg _) hC0
  filter_upwards [eventually_source_original_B26_canonical_aux_ban_saving434
    a v ((tmax:ℝ)*C0) Cslots (D+E) Cq Cxi ha hv hCs,
    eventually_ge_atTop (1:ℝ)] with L hSave hL
  intro G _ _ P _ V blockA blockB hBlocks J ell m hmJ hm Q hA hB xi
    hhA hhB hxi hV hVmin hPmin hGroups hSlots hQ hXi
    dsmall s t sigma tau ζ theta o k ho nSmall epsSrc epsTgt
  classical
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    nSmall*J + ∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1) *
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  let term := fun ν => sign ν * sourceOriginalB26CanonicalAuxBanError434
    P V J ell m hmJ ν Q hA hB xi (dsmall ν) (s ν) (t ν) (sigma ν) (tau ν)
      (ζ ν) (theta ν) (o ν) k
  have hLp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ‖term ν‖ ≤ L^(-(D+E)) := by
    have hmemb := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
    have hNA : ν.1.card ≤ blockA.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmemb.2.1
    have hNB : ν.2.card ≤ blockB.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmemb.2.2.2
    have hNat : ν.1.card+ν.2.card ≤ m*(blockA.card+blockB.card) := by nlinarith
    have hCard : ((ν.1.card+ν.2.card:ℕ):ℝ) ≤
        ((tmax:ℝ)*C0)*Real.log L := by
      calc
        _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by exact_mod_cast hNat
        _ ≤ (m:ℝ)*(C0*Real.log L) :=
          mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg _)
        _ ≤ (tmax:ℝ)*(C0*Real.log L) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (mul_nonneg hC0 hlog)
        _ = _ := by ring
    have hDisj := source_original_probe_memory_actual_pattern_disjoint434
      blockA blockB hBlocks m ν hν
    have hs := hSave P V J ell m hmJ ν hDisj Q hA hB xi
      hhA hhB hxi hV hVmin hPmin hCard hSlots hQ hXi
      (dsmall ν) (s ν) (t ν) (sigma ν) (tau ν) (ζ ν) (theta ν) (o ν) k (ho ν hν)
    have hn : ‖sign ν‖=1 := by
      dsimp only [sign]
      rw [norm_mul]
      split_ifs <;> simp
    dsimp only [term]
    rw [norm_mul,hn,one_mul]
    exact hs
  have hmE : (m:ℝ)*C0*Real.log 2 ≤ E := by
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hC0
    · exact Real.log_nonneg (by norm_num)
  have hCardF : (family.card:ℝ) ≤ L^E :=
    (source_original_probe_family_log_power_card434 blockA blockB m L C0 hL hGroups).trans
      (Real.rpow_le_rpow_of_exponent_le hL hmE)
  calc
    ‖∑ ν ∈ family,term ν‖ ≤ ∑ ν ∈ family,‖term ν‖ := norm_sum_le _ _
    _ ≤ ∑ ν ∈ family,L^(-(D+E)) := Finset.sum_le_sum hEach
    _ = (family.card:ℝ)*L^(-(D+E)) := by simp
    _ ≤ L^E*L^(-(D+E)) :=
      mul_le_mul_of_nonneg_right hCardF (Real.rpow_nonneg hLp.le _)
    _ = L^(-D) := by
      rw [←Real.rpow_add hLp]
      congr 1
      ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26AuxScalarComparison -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Actual frozen SMALL/shared source divisor; the endpoint permutation
is retained, and this value may be arbitrarily large. -/
noncomputable def sourceOriginalB26CanonicalSharedDivisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (dsmall : ℕ)
    (s : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma : BigGroupPerm (BG := G) (J+ell)) : ℕ :=
  dsmall * ∏ g : G,∏ i ∈ sourceOriginalProbeSharedSlots434 J ell m hmJ ν g,
    (s g (sigma g i)).val

theorem source_original_B26_canonical_shared_divisor_positive434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (dsmall : ℕ) (hdsmall : 0 < dsmall)
    (s : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma : BigGroupPerm (BG := G) (J+ell)) :
    0 < sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma := by
  apply Nat.mul_pos hdsmall
  apply Finset.prod_pos
  intro g hg
  apply Finset.prod_pos
  intro i hi
  exact Nat.pos_of_ne_zero (NeZero.ne _)

/-- B26's literal divisor becomes c*(D_A*D_B) under the actual
dependent assignment bijection, with no approximation. -/
theorem source_original_B26_memory_assignment_divisor434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (dsmall : ℕ)
    (aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν))
    (s : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma : BigGroupPerm (BG := G) (J+ell)) :
    sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s sigma =
    sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma *
      (sourceOriginalGramPrimeProduct434 (fun a : ν.1 => P a.val.1)
        (sourceOriginalProbeMemoryPrimeAssignmentEquiv434 P J m hmJ ν hDisj aux).1 *
       sourceOriginalGramPrimeProduct434 (fun b : ν.2 => P b.val.1)
        (sourceOriginalProbeMemoryPrimeAssignmentEquiv434 P J m hmJ ν hDisj aux).2) := by
  rw [source_original_probe_memory_frozen_divisor434]
  congr 1
  exact source_original_probe_memory_aux_product_transfer434 J m hmJ ν hDisj
    (fun z => (aux z.1 z.2).val)

/-- Exact full auxiliary expectation in the actual B26 carrier equals
the analytic oriented comparison plus its original signed RAW term.
Both physical endpoint permutations and all labels remain present. -/
theorem source_original_B26_unbanned_scalar_comparison434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      (sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux : ℂ) *
      originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        ζ theta
        (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s sigma) o k) -
    originalEdgeScalar (-((-1:ℂ)^(ν.1.card+ν.2.card))) ζ theta
      (sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma *
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
            (fun g i => t g (tau g i))) *
         sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
            (fun g i => s g (sigma g i))))) o k =
    sourceOriginalProbeOrientedDivisorError434 J ell m hmJ ν P V Q hA hB xi
      (sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma)
      ζ theta o k
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
        (fun g i => s g (sigma g i)))
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
        (fun g i => t g (tau g i))) := by
  classical
  unfold sourceOriginalProbeOrientedDivisorError434
  dsimp only
  congr 1
  rw [← source_original_probe_memory_weighted_assignment_sum434 P J m hmJ ν hDisj V]
  apply Finset.sum_congr rfl
  intro aux haux
  rw [source_original_B26_memory_assignment_divisor434 P J ell m hmJ ν hDisj]
  rfl

/-- Restoring the literal ban is an exact subtraction of the previously
estimated error, not an insertion of a joint factor into a GLOBAL norm. -/
theorem source_original_B26_banned_scalar_comparison434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
      (sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux : ℂ) *
      (if sourceOriginalB26FrozenAuxBan434 _ J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t then
       originalEdgeScalar
        (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν Q hA hB xi aux
          (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
        ζ theta
        (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s sigma) o k
       else 0)) -
    originalEdgeScalar (-((-1:ℂ)^(ν.1.card+ν.2.card))) ζ theta
      (sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma *
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
            (fun g i => t g (tau g i))) *
         sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
            (fun g i => s g (sigma g i))))) o k =
    sourceOriginalProbeOrientedDivisorError434 J ell m hmJ ν P V Q hA hB xi
      (sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma)
      ζ theta o k
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
        (fun g i => s g (sigma g i)))
      (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
        (fun g i => t g (tau g i))) -
    sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ ν
      Q hA hB xi dsmall s t sigma tau ζ theta o k := by
  rw [← source_original_B26_unbanned_scalar_comparison434
    P V J ell m hmJ ν hDisj Q hA hB xi dsmall s t sigma tau ζ theta o k]
  unfold sourceOriginalB26CanonicalAuxBanError434
  rw [sub_right_comm,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro aux haux
  by_cases hb : sourceOriginalB26FrozenAuxBan434 _ J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ ν) aux s t <;> simp [hb]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26LiteralCanonicalAuxSum -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000

noncomputable def sourceOriginalB26CanonicalRawValue434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (dsmall : ℕ)
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) : ℂ :=
  originalEdgeScalar (-((-1:ℂ)^(ν.1.card+ν.2.card))) ζ theta
    (sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma *
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
          (fun g i => t g (tau g i))) *
       sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
          (fun g i => s g (sigma g i))))) o k

noncomputable def sourceOriginalB26CanonicalComparisonValue434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ)
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ζ theta : ℝ) (o k : ℤ) : ℂ :=
  sourceOriginalProbeOrientedDivisorError434 J ell m hmJ ν P V Q hA hB xi
    (sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall s sigma)
    ζ theta o k
    (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
      (fun g i => s g (sigma g i)))
    (sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
      (fun g i => t g (tau g i)))

/-- Literal original B26 BigWeight, summed over ALL actual auxiliary
assignments, with its ban, normalized endpoint-pair mass and shared-copy
law unchanged. The original signed RAW contribution is explicit. -/
theorem source_original_B26_literal_big_weight_aux_sum434
    {G Nu : Type} [Fintype G] [DecidableEq G] [Fintype Nu]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (probes : Nu → SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB : Nu → ℝ) (xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (nu : Nu) (hDisj : Disjoint (probes nu).1 (probes nu).2)
    (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
    (s t : ∀ g,Fin (J+ell) → {p : ℕ // p ∈ P g})
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)),
      sourceOriginalB26FrozenBigWeight434 _ (fun _ p => p.val) J ell m
        (fun n => sourceOriginalProbeMemoryPattern434 J m hmJ (probes n)) mu V
        (fun n => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ (probes n)
          Q (hA n) (hB n) xi)
        dsmall ζ theta o k s ⟨nu,aux,sigma,tau⟩ t) =
    (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
      sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)) s t sigma tau *
      (sourceOriginalB26CanonicalRawValue434 P J ell m hmJ (probes nu)
          dsmall s t sigma tau ζ theta o k +
       sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ (probes nu)
          Q (hA nu) (hB nu) xi dsmall s t sigma tau ζ theta o k -
       sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ (probes nu)
          Q (hA nu) (hB nu) xi dsmall s t sigma tau ζ theta o k) := by
  classical
  have hb := source_original_B26_banned_scalar_comparison434 P V J ell m hmJ
    (probes nu) hDisj Q (hA nu) (hB nu) xi dsmall s t sigma tau ζ theta o k
  let C : ℂ := (bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
    sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)) s t sigma tau
  have hs :
    (∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
      (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)),
      (sourceAuxMass _ (fun _ p => p.val) J m V
        (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)) aux : ℂ) *
      (if sourceOriginalB26FrozenAuxBan434 _ J ell m
        (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)) aux s t then
        originalEdgeScalar
          (sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ (probes nu)
            Q (hA nu) (hB nu) xi aux (fun g i => s g (sigma g i)) (fun g i => t g (tau g i)))
          ζ theta (sourceOriginalB26FrozenD434 _ (fun _ p => p.val) J ell m dsmall
            (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)) aux s sigma) o k
        else 0)) =
      sourceOriginalB26CanonicalRawValue434 P J ell m hmJ (probes nu)
          dsmall s t sigma tau ζ theta o k +
      sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ (probes nu)
          Q (hA nu) (hB nu) xi dsmall s t sigma tau ζ theta o k -
      sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ (probes nu)
          Q (hA nu) (hB nu) xi dsmall s t sigma tau ζ theta o k := by
    unfold sourceOriginalB26CanonicalRawValue434 sourceOriginalB26CanonicalComparisonValue434
    linear_combination hb
  rw [← hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro aux haux
  unfold sourceOriginalB26FrozenBigWeight434
  dsimp only
  by_cases hban : sourceOriginalB26FrozenAuxBan434 _ J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ (probes nu)) aux s t
  · rw [if_pos ⟨ho,hk,hban⟩,if_pos hban]
    ring
  · rw [if_neg (by simp [hban]),if_neg hban]
    ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26CoherentRawComparisonBan -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Exact coherent decomposition of the literal frozen B26 BIG block.
The sums over nu, both permutations, and the full target remain inside
the operator. The genuine signed RAW term and auxiliary correction remain. -/
theorem source_original_B26_COHERENT_RAW_COMPARISON_BAN434
    {G Nu : Type} [Fintype G] [DecidableEq G] [Fintype Nu]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (probes : Nu → SourceOriginalProbePattern434 G m)
    (hDisj : ∀ n,Disjoint (probes n).1 (probes n).2)
    (Q : ℕ) (hA hB : Nu → ℝ) (xi : ℝ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1) (hk : k≠0)
    (f : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) :
    sourceOriginalB26FrozenBigBlock434 _ (fun _ p => p.val) J ell m
      (fun n => sourceOriginalProbeMemoryPattern434 J m hmJ (probes n)) mu V
      (fun n => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ (probes n)
        Q (hA n) (hB n) xi) dsmall ζ theta o k f s =
    ∑ n : Nu,∑ sigma : BigGroupPerm (BG := G) (J+ell),
      ∑ tau : BigGroupPerm (BG := G) (J+ell),
        ∑ t : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}),
          ((bigEndpointPairMass (BG := G) (J+ell) : ℂ) *
            sourceOriginalB26FrozenFreshLaw434 _ J ell m mu
              (sourceOriginalProbeMemoryPattern434 J m hmJ (probes n)) s t sigma tau *
            (sourceOriginalB26CanonicalRawValue434 P J ell m hmJ (probes n)
                dsmall s t sigma tau ζ theta o k +
             sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ (probes n)
                Q (hA n) (hB n) xi dsmall s t sigma tau ζ theta o k -
             sourceOriginalB26CanonicalAuxBanError434 P V J ell m hmJ (probes n)
                Q (hA n) (hB n) xi dsmall s t sigma tau ζ theta o k)) * f t := by
  classical
  unfold sourceOriginalB26FrozenBigBlock434
  simp only [SourceOriginalB26FrozenFrame434,Fintype.sum_sigma,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma hs
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tau ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t htt
  rw [← Finset.sum_mul]
  rw [source_original_B26_literal_big_weight_aux_sum434
    P V J ell m hmJ probes Q hA hB xi mu n (hDisj n) dsmall ζ theta o k ho hk]
end Green64Analytic.CorrelationSquare

end

