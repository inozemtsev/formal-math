module

public import Green64.Library.Correlation.Part042
public import Green64.Library.Weights.Part055
public import Green64.Library.Correlation.Part006
public import Green64.Library.Correlation.Part041
public import Green64.Library.Correlation.Part036
public import Green64.Library.Weights.Part053
public import Green64.Library.Weights.Part018
public import Green64.Library.Correlation.Part037
public import Green64.Library.Weights.Part015
public import Green64.Library.Weights.Part046
public import Green64.Library.Correlation.Part034
public import Green64.Library.Weights.Part051

@[expose] public section

/-!
# Weights / Part056

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalB26HomogeneousShared -/

section

open Filter
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 22000000

/-- Finite homogeneous integration. This is used only with the proved
arithmetic comparison bound and the literal shared harmonic measure. -/
theorem source_original_B26_homogeneous_shared_integration434
    {H : Type} [Fintype H]
    (w ES ET : H → ℝ) (z : H → ℂ) (eps : ℝ)
    (hw : ∀ h,0 ≤ w h) (hES : ∀ h,0 ≤ ES h) (hET : ∀ h,0 ≤ ET h)
    (heps : 0 ≤ eps)
    (hz : ∀ h,‖z h‖^2 ≤ eps*ES h*ET h) :
    ‖∑ h : H,(w h:ℂ)*z h‖^2 ≤
      eps*(∑ h : H,w h*ES h)*(∑ h : H,w h*ET h) := by
  classical
  let a := fun h => Real.sqrt (w h*ES h)
  let b := fun h => Real.sqrt (w h*ET h)
  have ha (h : H) : (a h)^2=w h*ES h := Real.sq_sqrt (mul_nonneg (hw h) (hES h))
  have hb (h : H) : (b h)^2=w h*ET h := Real.sq_sqrt (mul_nonneg (hw h) (hET h))
  have hab (h : H) : 0 ≤ a h*b h := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hp (h : H) : w h*‖z h‖ ≤ Real.sqrt eps*(a h*b h) := by
    have hsq : (w h*‖z h‖)^2 ≤ (Real.sqrt eps*(a h*b h))^2 := by
      rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt heps,ha,hb]
      have hh := mul_le_mul_of_nonneg_left (hz h) (sq_nonneg (w h))
      nlinarith [hh]
    exact (sq_le_sq₀ (mul_nonneg (hw h) (norm_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (hab h))).mp hsq
  have ht : ‖∑ h : H,(w h:ℂ)*z h‖ ≤ Real.sqrt eps*(∑ h : H,a h*b h) := by
    calc
      _ ≤ ∑ h : H,‖(w h:ℂ)*z h‖ := norm_sum_le _ _
      _ = ∑ h : H,w h*‖z h‖ := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw h)]
      _ ≤ ∑ h : H,Real.sqrt eps*(a h*b h) := Finset.sum_le_sum (fun h _ => hp h)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset H) a b
  simp_rw [ha,hb] at hc
  calc
    _ ≤ (Real.sqrt eps*(∑ h : H,a h*b h))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ = eps*(∑ h : H,a h*b h)^2 := by rw [mul_pow,Real.sq_sqrt heps]
    _ ≤ eps*((∑ h : H,w h*ES h)*(∑ h : H,w h*ET h)) :=
      mul_le_mul_of_nonneg_left hc heps
    _ = _ := by ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26LiteralComparisonPairing -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem source_original_B26_free_values_on_split434
    {G : Type} [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (h : (g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → {p : ℕ // p ∈ P g})
    (u : (g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) →
      {p : ℕ // p ∈ P g}) :
    sourceOriginalProbeMemoryFreeValues434 P J ell m hmJ ν
      ((sourceOriginalB26ActiveSplitEquiv434 (fun g => {p : ℕ // p ∈ P g})
        J ell m hmJ ν).symm (h,u)) = fun g i => (u g i).val := by
  have he := congrArg Prod.snd
    ((sourceOriginalB26ActiveSplitEquiv434 (fun g => {p : ℕ // p ∈ P g})
      J ell m hmJ ν).apply_symm_apply (h,u))
  funext g i
  exact congrArg Subtype.val (congrFun (congrFun he g) i)

theorem source_original_B26_shared_divisor_on_split434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (dsmall : ℕ)
    (h : (g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → {p : ℕ // p ∈ P g})
    (u : (g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) →
      {p : ℕ // p ∈ P g}) :
    sourceOriginalB26CanonicalSharedDivisor434 P J ell m hmJ ν dsmall
      ((sourceOriginalB26ActiveSplitEquiv434 (fun g => {p : ℕ // p ∈ P g})
        J ell m hmJ ν).symm (h,u)) (fun _ => Equiv.refl _) =
      dsmall * ∏ g : G,∏ i,(h g i).val := by
  classical
  let e := sourceOriginalB26ActiveSplitEquiv434 (fun g => {p : ℕ // p ∈ P g})
    J ell m hmJ ν
  have he := congrArg Prod.fst (e.apply_symm_apply (h,u))
  unfold sourceOriginalB26CanonicalSharedDivisor434
  congr 1
  apply Finset.prod_congr rfl
  intro g hg
  rw [← source_original_probe_memory_shared_slots434]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg Subtype.val (congrFun (congrFun he g) i)

/-- The literal B26 comparison value on a surviving shared fibre is
exactly the oriented two-GLOBAL residual with its full positive divisor. -/
theorem source_original_B26_comparison_on_split434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (h : (g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → {p : ℕ // p ∈ P g})
    (u v : (g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) →
      {p : ℕ // p ∈ P g}) :
    sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ ν Q hA hB xi dsmall
      ((sourceOriginalB26ActiveSplitEquiv434 (fun g => {p : ℕ // p ∈ P g})
        J ell m hmJ ν).symm (h,u))
      ((sourceOriginalB26ActiveSplitEquiv434 (fun g => {p : ℕ // p ∈ P g})
        J ell m hmJ ν).symm (h,v))
      (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) ζ theta o k =
    sourceOriginalProbeOrientedDivisorError434 J ell m hmJ ν P V Q hA hB xi
      (dsmall * ∏ g : G,∏ i,(h g i).val) ζ theta o k
      (fun g i => (u g i).val) (fun g i => (v g i).val) := by
  unfold sourceOriginalB26CanonicalComparisonValue434
  simp only [Equiv.refl_apply]
  rw [source_original_B26_shared_divisor_on_split434,
    source_original_B26_free_values_on_split434,
    source_original_B26_free_values_on_split434]

/-- Exact transfer of the literal CLEAN comparison pairing, including
its shared-copy law and full endpoint tests, to the proved fibre sum. -/
theorem source_original_B26_literal_comparison_pairing434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (F Gtest : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let X := SourceOriginalVariableBIGState434 BP t
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let Shared := ((g : G) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g)
    let wH := sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu
    let Active := ((g : G) → Fin (J+ell) → BP g)
    let e := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν
    (∑ s : Active,∑ v : Active,
      ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        (star (F s)*Gtest v*
          sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ ν
            Q hA hB xi dsmall s v (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
            ζ theta o k)) =
    ∑ h : Shared,(wH h:ℂ) *
      (∑ ab : X × X,((w ab.1*w ab.2:ℝ):ℂ) *
        star (F (e.symm (h,ab.1)))*Gtest (e.symm (h,ab.2))*
        sourceOriginalProbeOrientedDivisorError434 J ell m hmJ ν P V Q hA hB xi
          (dsmall * ∏ g : G,∏ i,(h g i).val) ζ theta o k
          (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)) := by
  classical
  dsimp only
  rw [source_original_B26_shared_free_pairing434]
  simp_rw [source_original_B26_comparison_on_split434]
  simp only [Fintype.sum_prod_type,Finset.mul_sum,Complex.ofReal_mul,
    sourceOriginalVariableBIGMass434]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26EndpointPermutation -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

noncomputable def sourceOriginalB26EndpointPermutationEquiv434
    {G : Type} (BP : G → Type) (M : ℕ) (sigma : BigGroupPerm (BG := G) M) :
    ((g : G) → Fin M → BP g) ≃ ((g : G) → Fin M → BP g) where
  toFun s g i := s g (sigma g i)
  invFun s g i := s g ((sigma g).symm i)
  left_inv s := by funext g i; simp only [Equiv.apply_symm_apply]
  right_inv s := by funext g i; simp only [Equiv.symm_apply_apply]

theorem source_original_B26_permutation_energy434
    {G : Type} [Fintype G] (BP : G → Type) [∀ g,Fintype (BP g)]
    (M : ℕ) (sigma : BigGroupPerm (BG := G) M)
    (mu : (g : G) → BP g → ℝ) (F : ((g : G) → Fin M → BP g) → ℂ) :
    (∑ s : ((g : G) → Fin M → BP g),
      (∏ g : G,∏ i : Fin M,mu g (s g i)) *
        ‖F ((sourceOriginalB26EndpointPermutationEquiv434 BP M sigma).symm s)‖^2) =
    ∑ s : ((g : G) → Fin M → BP g),
      (∏ g : G,∏ i : Fin M,mu g (s g i))*‖F s‖^2 := by
  classical
  apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP M sigma).symm
  intro s
  congr 1
  exact (source_original_B26_endpoint_permutation_mass434 BP M mu s
    (fun g => (sigma g).symm)).symm

/-- Exact reindexing of an arbitrary joint kernel, with the source's true
product law. This permits no factorization of the kernel. -/
theorem source_original_B26_permutation_pair_reindex434
    {G : Type} [Fintype G] (BP : G → Type) [∀ g,Fintype (BP g)]
    (M : ℕ) (sigma tau : BigGroupPerm (BG := G) M)
    (mu : (g : G) → BP g → ℝ)
    (K : ((g : G) → Fin M → BP g) → ((g : G) → Fin M → BP g) → ℂ) :
    (∑ s : ((g : G) → Fin M → BP g),∑ t : ((g : G) → Fin M → BP g),
      ((∏ g : G,∏ i : Fin M,mu g (s g i):ℝ):ℂ)*K s t) =
    ∑ s : ((g : G) → Fin M → BP g),∑ t : ((g : G) → Fin M → BP g),
      ((∏ g : G,∏ i : Fin M,mu g (s g i):ℝ):ℂ) *
      K ((sourceOriginalB26EndpointPermutationEquiv434 BP M sigma).symm s)
        ((sourceOriginalB26EndpointPermutationEquiv434 BP M tau).symm t) := by
  classical
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP M sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP M tau
  apply Fintype.sum_equiv eS
  intro s
  have hm := source_original_B26_endpoint_permutation_mass434 BP M mu s sigma
  change (∏ g : G,∏ i : Fin M,mu g (eS s g i)) =
    (∏ g : G,∏ i : Fin M,mu g (s g i)) at hm
  rw [Equiv.symm_apply_apply,hm]
  apply Fintype.sum_equiv eT
  intro t
  simp only [eT,sourceOriginalB26EndpointPermutationEquiv434,Equiv.symm_apply_apply]

/-- Both actual endpoint permutations are removed by exact changes of
variables, retaining the full CLEAN comparison and transformed full tests. -/
theorem source_original_B26_literal_comparison_permuted434
    {G : Type} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) (V : G → ℝ)
    (J ell m : ℕ) (hmJ : m ≤ J) (ν : SourceOriginalProbePattern434 G m)
    (Q : ℕ) (hA hB xi : ℝ) (dsmall : ℕ) (ζ theta : ℝ) (o k : ℤ)
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (F Gtest : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ P g}) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let Active := ((g : G) → Fin (J+ell) → BP g)
    let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
    let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
    (∑ s : Active,∑ v : Active,
      ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v sigma tau *
        (star (F s)*Gtest v*
          sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ ν
            Q hA hB xi dsmall s v sigma tau ζ theta o k)) =
    (∑ s : Active,∑ v : Active,
      ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        (star (F (eS.symm s))*Gtest (eT.symm v)*
          sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ ν
            Q hA hB xi dsmall s v (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
            ζ theta o k)) := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  have he := source_original_B26_permutation_pair_reindex434
    BP (J+ell) sigma tau mu
    (fun s v =>
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v sigma tau *
      (star (F s)*Gtest v*sourceOriginalB26CanonicalComparisonValue434 P V
        J ell m hmJ ν Q hA hB xi dsmall s v sigma tau ζ theta o k))
  simp only [mul_assoc] at he ⊢
  convert! he using 1
  · apply Finset.sum_congr (by ext s; simp)
    intro s hs
    apply Finset.sum_congr (by ext v; simp)
    intro v hv
    simp only [BP,sourceOriginalB26FrozenFreshLaw434]
  · apply Finset.sum_congr (by ext s; simp)
    intro s hs
    apply Finset.sum_congr (by ext v; simp)
    intro v hv
    have hS := eS.apply_symm_apply s
    have hT := eT.apply_symm_apply v
    change (fun g i => eS.symm s g (sigma g i))=s at hS
    change (fun g i => eT.symm v g (tau g i))=v at hT
    have hSp (g : G) (i : Fin (J+ell)) : eS.symm s g (sigma g i)=s g i :=
      congrFun (congrFun hS g) i
    have hTp (g : G) (i : Fin (J+ell)) : eT.symm v g (tau g i)=v g i :=
      congrFun (congrFun hT g) i
    have hfresh := source_original_B26_fresh_law_permuted434
      BP J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu
      (eS.symm s) (eT.symm v) sigma tau
    rw [hS,hT] at hfresh
    have hcomp :
      sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ ν Q hA hB xi
        dsmall (eS.symm s) (eT.symm v) sigma tau ζ theta o k =
      sourceOriginalB26CanonicalComparisonValue434 P V J ell m hmJ ν Q hA hB xi
        dsmall s v (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) ζ theta o k := by
      simp only [sourceOriginalB26CanonicalComparisonValue434,
        sourceOriginalB26CanonicalSharedDivisor434,Equiv.refl_apply,hSp,hTp]
    rw [hcomp,hfresh]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26PhysicalTiltDensity -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Exact endpoint density: shared slots carry r, free slots carry r^2.
The assignment uses the actual source/target permutations. -/
def sourceOriginalB26TiltEndpoint434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) (J ell m : ℕ) (pat : SourcePattern G J m)
    (r : (g : G) → BP g → ℝ)
    (sigma : BigGroupPerm (BG := G) (J+ell))
    (s : (g : G) → Fin (J+ell) → BP g) : ℝ :=
  ∏ g : G, ∏ i : Fin (J+ell),
    if i ∈ sourceBigShared J ell m pat g then r g (s g (sigma g i))
    else (r g (s g (sigma g i)))^2

/-- Pointwise factorization on the actual shared-copy support. It holds
for any joint multiplier subsequently attached to this law; no joint
kernel is assumed to factor. Shared density is charged exactly once. -/
theorem source_original_B26_TILT_SHARED_JOINT_DENSITY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (mu r : (g : G) → BP g → ℝ)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i)*(r g (s g i))^2:ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m
        (fun g p => mu g p*(r g p)^2) pat s t sigma tau =
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau *
      (sourceOriginalB26TiltEndpoint434 BP J ell m pat r sigma s:ℂ) *
      (sourceOriginalB26TiltEndpoint434 BP J ell m pat r tau t:ℂ) := by
  classical
  rw [source_original_B26_fresh_law_permuted434 BP J ell m pat
    (fun g p => mu g p*(r g p)^2) s t sigma tau,
    source_original_B26_fresh_law_permuted434 BP J ell m pat mu s t sigma tau]
  rw [← source_original_B26_endpoint_permutation_mass434 BP (J+ell)
    (fun g p => mu g p*(r g p)^2) s sigma,
    ← source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s sigma]
  unfold sourceOriginalB26FrozenFreshLaw434 sourceOriginalB26TiltEndpoint434
  simp only [Equiv.refl_symm,Equiv.refl_apply]
  push_cast
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ sourceBigShared J ell m pat g
  · by_cases he : t g (tau g i) = s g (sigma g i)
    · simp only [hi,if_pos,he]
      ring
    · simp [hi,he]
  · simp only [hi,if_false,Complex.ofReal_pow]
    ring

/-- The density factor is the literal baseline from all source visits,
including the two sqrt(q) boundary visits. -/
def sourceOriginalB26PhysicalTiltRoot434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (g : G) (p : BP g) : ℝ :=
  Real.sqrt ((physicalSourceBaseline BP modulus q N g p)⁻¹)

theorem source_original_B26_PHYSICAL_TILT_ATOM434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (g : G) (p : BP g)
    (hb : 0 < physicalSourceBaseline BP modulus q N g p) :
    physicalSourceMuTilde BP modulus q N V g p =
      sourceOriginalJointHarmonicMu434 BP modulus V g p *
      (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N g p)^2 := by
  rw [sourceOriginalB26PhysicalTiltRoot434,Real.sq_sqrt (inv_nonneg.mpr hb.le)]
  simp only [physicalSourceMuTilde,sourceOriginalJointHarmonicMu434,
    sourceOriginalHarmonicPrimeMu434,div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- Exact change of the actual physical tilted law to the harmonic joint
law with two explicit endpoint multipliers. Positivity of the source
baselines is explicit; quantitative bounds remain a separate obligation. -/
theorem source_original_B26_PHYSICAL_TILT_JOINT_DENSITY434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ)
    (hb : ∀ g p,0 < physicalSourceBaseline BP modulus q N g p)
    (J ell m : ℕ) (pat : SourcePattern G J m)
    (s t : (g : G) → Fin (J+ell) → BP g)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    let mu := sourceOriginalJointHarmonicMu434 BP modulus V
    let muTilt := physicalSourceMuTilde BP modulus q N V
    let r := sourceOriginalB26PhysicalTiltRoot434 BP modulus q N
    ((∏ g : G,∏ i : Fin (J+ell),muTilt g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m muTilt pat s t sigma tau =
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat s t sigma tau *
      (sourceOriginalB26TiltEndpoint434 BP J ell m pat r sigma s:ℂ) *
      (sourceOriginalB26TiltEndpoint434 BP J ell m pat r tau t:ℂ) := by
  classical
  have he : physicalSourceMuTilde BP modulus q N V =
      (fun g p => sourceOriginalJointHarmonicMu434 BP modulus V g p *
        (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N g p)^2) := by
    funext g p
    exact source_original_B26_PHYSICAL_TILT_ATOM434 BP modulus q N V g p (hb g p)
  dsimp only
  rw [he]
  exact source_original_B26_TILT_SHARED_JOINT_DENSITY434 BP J ell m pat
    (sourceOriginalJointHarmonicMu434 BP modulus V)
    (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N) s t sigma tau
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26SharedComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Proved arithmetic comparison on the exact shared fibres of the literal B26 CLEAN law. The original shared divisor is positive and unrestricted; the eventual threshold precedes all shared assignments, endpoint lengths and full-label tests. --/
theorem eventually_source_original_B26_SHARED_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (Cq Cxi Cs C4 Cfactor : ℕ)
    (gamma dscale D Bsave H Bgoal : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hD : 0 ≤ D) (hB : 0 < Bsave) (hH : 0 ≤ H)
    (hCs : D+dscale+2 ≤ (Cs:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hWidthBudget : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H)
    (hDropBudget : Bsave+H+dscale+4 ≤ (Cxi:ℝ))
    (hExponent : cfg.C0*
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ))
    (hMinorBudget : Bsave+2*(Cfactor:ℝ) ≤ D)
    (hSumBudget : Bgoal+(2*dscale+4)+2 ≤ Bsave) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (hMeshA : hA = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hMeshB : hB = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hXiExact : xi = L^(-(Cxi:ℝ)))
      (ζ theta : ℝ) (k : ℤ) (hZeta : |ζ| ≤ L^C4)
      (hQlower : L^D ≤ (Qchar:ℝ))
      (dsmall : ℕ) (hdsmall : 0 < dsmall) (o : ℤ) (ho : o=1 ∨ o= -1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let Shared := ((g : β) → sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g)
    let wH : Shared → ℝ := sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu
    let Active := ((g : β) → Fin (J+ell) → BP g)
    let e := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν
    let c : Shared → ℕ := fun h => dsmall * ∏ g : β,∏ i,(h g i).val
    ∀ (sourceTest targetTest : Active → ℂ),
    ‖∑ h : Shared,(wH h:ℂ) *
      (∑ ab : X × X,((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest (e.symm (h,ab.1))) * targetTest (e.symm (h,ab.2)) *
        sourceOriginalProbeOrientedDivisorError434
          J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi (c h) ζ theta o k
          (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val))‖^2 ≤
      L^(-Bgoal) *
        (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖sourceTest s‖^2) *
        (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖targetTest s‖^2) := by
  obtain ⟨Y0,hBase⟩ :=
    eventually_source_original_CANONICAL_GLOBAL_ORIENTED_DIVISOR_COMPARISON434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H Bgoal
      hgamma hd hD hB hH hCs hC4 hWidthBudget hDropBudget hExponent hMinorBudget hSumBudget
  refine ⟨Y0,?_⟩
  filter_upwards [hBase] with L hGlobal
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower dsmall hdsmall o ho
  intro sourceTest targetTest
  classical
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let Shared := ((g : β) → sourceBigShared J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g → BP g)
  let wH : Shared → ℝ := sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ ν mu
  let Active := ((g : β) → Fin (J+ell) → BP g)
  let e := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ ν
  let c : Shared → ℕ := fun h => dsmall * ∏ g : β,∏ i,(h g i).val
  let f : Shared → X → ℂ := fun h u => sourceTest (e.symm (h,u))
  let g : Shared → X → ℂ := fun h v => targetTest (e.symm (h,v))
  let ES : Shared → ℝ := fun h => ∑ u : X,w u*‖f h u‖^2
  let ET : Shared → ℝ := fun h => ∑ v : X,w v*‖g h v‖^2
  let z : Shared → ℂ := fun h => ∑ ab : X × X,((w ab.1*w ab.2:ℝ):ℂ) *
    star (f h ab.1)*g h ab.2*
    sourceOriginalProbeOrientedDivisorError434
      J ell m hmJ ν d.Tb d.Vbig Qchar hA hB xi (c h) ζ theta o k
      (fun g i => (ab.1 g i).val) (fun g i => (ab.2 g i).val)
  have hmu (b : β) (p : BP b) : 0 ≤ mu b p :=
    source_original_harmonic_prime_nonneg434 (fun p : BP b => p.val) (d.Vbig b)
      (lt_of_lt_of_le cfg.hv (d.hVbig b)) p
  have hw (u : X) : 0 ≤ w u :=
    Finset.prod_nonneg (fun b _ => Finset.prod_nonneg (fun i _ => hmu b (u b i)))
  have hwH (h : Shared) : 0 ≤ wH h :=
    Finset.prod_nonneg (fun b _ => Finset.prod_nonneg (fun i _ => hmu b (h b i)))
  have hES (h : Shared) : 0 ≤ ES h :=
    Finset.sum_nonneg (fun u _ => mul_nonneg (hw u) (sq_nonneg _))
  have hET (h : Shared) : 0 ≤ ET h :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (hw v) (sq_nonneg _))
  have hc (h : Shared) : 0 < c h := by
    apply Nat.mul_pos hdsmall
    apply Finset.prod_pos
    intro b hb
    apply Finset.prod_pos
    intro i hi
    exact (d.hTbPrime b (h b i).val (h b i).property).pos
  have hz (h : Shared) : ‖z h‖^2 ≤ L^(-Bgoal)*ES h*ET h :=
    @hGlobal ι β instI instDI instB instDB x Y Hprime d sep hVbig
      blockA blockB hDisjoint m hm ν hPattern Qchar
      hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
      hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower
      (c h) (hc h) o ho (f h) (g h)
  have hL : 0 ≤ L := by
    have hlog := Real.log_pos (show (1:ℝ)<2 by norm_num)
    have hinv : 0 < (Real.log (2:ℝ))⁻¹ := inv_pos.mpr hlog
    linarith
  have hbound := source_original_B26_homogeneous_shared_integration434
    wH ES ET z (L^(-Bgoal)) hwH hES hET (Real.rpow_nonneg hL _) hz
  have hEnergy (F : Active → ℂ) :
      (∑ s : Active,(∏ b : β,∏ i : Fin (J+ell),mu b (s b i))*‖F s‖^2) =
        ∑ h : Shared,wH h*(∑ u : X,w u*‖F (e.symm (h,u))‖^2) := by
    have hh := source_original_B26_active_split_weighted_sum434
      BP J ell m hmJ ν mu (fun s => ‖F s‖^2)
    simpa only [wH,w,sourceOriginalVariableBIGMass434,e,Finset.mul_sum,mul_assoc] using hh
  rw [hEnergy sourceTest,hEnergy targetTest]
  exact hbound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26LiteralComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Proved physical comparison saving on the literal B26 CLEAN copy law, with both complete active endpoint tests and the actual SMALL/shared divisor. --/
theorem eventually_source_original_B26_LITERAL_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (Cq Cxi Cs C4 Cfactor : ℕ)
    (gamma dscale D Bsave H Bgoal : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hD : 0 ≤ D) (hB : 0 < Bsave) (hH : 0 ≤ H)
    (hCs : D+dscale+2 ≤ (Cs:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hWidthBudget : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H)
    (hDropBudget : Bsave+H+dscale+4 ≤ (Cxi:ℝ))
    (hExponent : cfg.C0*
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ))
    (hMinorBudget : Bsave+2*(Cfactor:ℝ) ≤ D)
    (hSumBudget : Bgoal+(2*dscale+4)+2 ≤ Bsave) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (hMeshA : hA = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hMeshB : hB = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hXiExact : xi = L^(-(Cxi:ℝ)))
      (ζ theta : ℝ) (k : ℤ) (hZeta : |ζ| ≤ L^C4)
      (hQlower : L^D ≤ (Qchar:ℝ))
      (dsmall : ℕ) (hdsmall : 0 < dsmall) (o : ℤ) (ho : o=1 ∨ o= -1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let Active := ((g : β) → Fin (J+ell) → BP g)
    ∀ (sourceTest targetTest : Active → ℂ),
    ‖∑ s : Active,∑ v : Active,
      ((∏ g : β,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        (star (sourceTest s)*targetTest v*
          sourceOriginalB26CanonicalComparisonValue434 d.Tb d.Vbig J ell m hmJ ν
            Qchar hA hB xi dsmall s v (fun _ => Equiv.refl _) (fun _ => Equiv.refl _)
            ζ theta o k)‖^2 ≤
      L^(-Bgoal) *
        (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖sourceTest s‖^2) *
        (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖targetTest s‖^2) := by
  obtain ⟨Y0,hBase⟩ :=
    eventually_source_original_B26_SHARED_COMPARISON434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H Bgoal
      hgamma hd hD hB hH hCs hC4 hWidthBudget hDropBudget hExponent hMinorBudget hSumBudget
  refine ⟨Y0,?_⟩
  filter_upwards [hBase] with L hGlobal
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower dsmall hdsmall o ho
  intro sourceTest targetTest
  have hSaved := @hGlobal ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower
    dsmall hdsmall o ho sourceTest targetTest
  rw [source_original_B26_literal_comparison_pairing434]
  exact hSaved
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26PermutedComparison -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 20000000

/-- Proved physical B26 comparison with both original endpoint permutations, true harmonic law and complete active tests. No permutation-count loss occurs. --/
theorem eventually_source_original_B26_PERMUTED_COMPARISON434
    (cfg : SourceComparisonFixed434)
    (Cq Cxi Cs C4 Cfactor : ℕ)
    (gamma dscale D Bsave H Bgoal : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ dscale)
    (hD : 0 ≤ D) (hB : 0 < Bsave) (hH : 0 ≤ H)
    (hCs : D+dscale+2 ≤ (Cs:ℝ))
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hWidthBudget : Bsave+((4*Cq+C4:ℕ):ℝ) ≤ H)
    (hDropBudget : Bsave+H+dscale+4 ≤ (Cxi:ℝ))
    (hExponent : cfg.C0*
      Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
        (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (Cfactor:ℝ))
    (hMinorBudget : Bsave+2*(Cfactor:ℝ) ≤ D)
    (hSumBudget : Bgoal+(2*dscale+4)+2 ≤ Bsave) :
    ∃ Y0 : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
      (x Y Hprime : ℝ)
      (d : SourceComparisonData434 ι β cfg x L Y Hprime)
      (sep : SourceOriginalSource03GroupSeparation434 d)
      (hVbig : ∀ g : β, d.Vbig g = ∑ p ∈ d.Tb g, 1/(p:ℝ))
      (blockA blockB : Finset β) (hDisjoint : Disjoint blockA blockB)
      (m : ℕ) (hm : m ≤ cfg.tmax)
      (ν : SourceOriginalProbePattern434 β m)
      (hPattern : ν ∈ sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
      (Qchar : ℕ)
      (hA hB : ℝ) (hhA : 0 < hA) (hhB : 0 < hB)
      (xi : ℝ) (hxi : 0 < xi) (hXipoly : xi⁻¹ ≤ L^Cxi)
      (hQchar : (Qchar:ℝ) ≤ L^Cq)
      (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
      (hBIG : ∀ g : β, ∀ p ∈ d.Tb g, Qchar^2 < p)
      (J ell : ℕ) (hmJ : m ≤ J),
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ := fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    ∀ (iA : ν.1) (iB : ν.2)
      (uA vA uB vB : ℕ)
      (huA : 1 ≤ uA) (huB : 1 ≤ uB)
      (huvA : uA ≤ vA) (huvB : uB ≤ vB)
      (hvA : (vA:ℝ) ≤ Real.exp (L^dscale))
      (hvB : (vB:ℝ) ≤ Real.exp (L^dscale))
      (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
      (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
      (huBIGA : Qchar^2 ≤ uA) (huBIGB : Qchar^2 ≤ uB)
      (hYA : Y0 ≤ ((uA+1:ℕ):ℝ)) (hYB : Y0 ≤ ((uB+1:ℕ):ℝ))
      (hBandA : SA iA = sourceOriginalActualPrimeBand434 uA vA)
      (hBandB : SB iB = sourceOriginalActualPrimeBand434 uB vB)
      (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g, Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (hTbUpper : ∀ g : β, ∀ p ∈ d.Tb g, (p:ℝ) ≤ Real.exp (L^dscale))
      (hMeshA : hA = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hMeshB : hB = Real.log 2/((Nat.ceil (4*L^H):ℕ):ℝ))
      (hXiExact : xi = L^(-(Cxi:ℝ)))
      (ζ theta : ℝ) (k : ℤ) (hZeta : |ζ| ≤ L^C4)
      (hQlower : L^D ≤ (Qchar:ℝ))
      (dsmall : ℕ) (hdsmall : 0 < dsmall) (o : ℤ) (ho : o=1 ∨ o= -1),
    let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
    let Active := ((g : β) → Fin (J+ell) → BP g)
    ∀ (sigma tau : BigGroupPerm (BG := β) (J+ell))
      (sourceTest targetTest : Active → ℂ),
    ‖∑ s : Active,∑ v : Active,
      ((∏ g : β,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v sigma tau *
        (star (sourceTest s)*targetTest v*
          sourceOriginalB26CanonicalComparisonValue434 d.Tb d.Vbig J ell m hmJ ν
            Qchar hA hB xi dsmall s v sigma tau
            ζ theta o k)‖^2 ≤
      L^(-Bgoal) *
        (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖sourceTest s‖^2) *
        (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖targetTest s‖^2) := by
  obtain ⟨Y0,hBase⟩ :=
    eventually_source_original_B26_LITERAL_COMPARISON434
      cfg Cq Cxi Cs C4 Cfactor gamma dscale D Bsave H Bgoal
      hgamma hd hD hB hH hCs hC4 hWidthBudget hDropBudget hExponent hMinorBudget hSumBudget
  refine ⟨Y0,?_⟩
  filter_upwards [hBase] with L hGlobal
  intro ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
  dsimp only
  intro iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower dsmall hdsmall o ho
  intro sigma tau sourceTest targetTest
  let BP : β → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  let mu := sourceOriginalJointHarmonicMu434 BP (fun g p => p.val) d.Vbig
  let Active := ((g : β) → Fin (J+ell) → BP g)
  have hEnergy (pi : BigGroupPerm (BG := β) (J+ell)) (F : Active → ℂ) :
      (∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i)) *
        ‖F ((sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) pi).symm s)‖^2) =
      ∑ s : Active,(∏ g : β,∏ i : Fin (J+ell),mu g (s g i))*‖F s‖^2 := by
    apply Fintype.sum_equiv
      (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) pi).symm
    intro s
    congr 1
    exact (source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s
      (fun g => (pi g).symm)).symm
  have hSaved := @hGlobal ι β instI instDI instB instDB x Y Hprime d sep hVbig
    blockA blockB hDisjoint m hm ν hPattern Qchar
    hA hB hhA hhB xi hxi hXipoly hQchar hLdyad hBIG J ell hmJ
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB hBandA hBandB
    hTbLower hTbUpper hMeshA hMeshB hXiExact ζ theta k hZeta hQlower
    dsmall hdsmall o ho (fun s => sourceTest (eS.symm s))
      (fun v => targetTest (eT.symm v))
  dsimp only at hSaved
  rw [source_original_B26_literal_comparison_permuted434]
  dsimp only [eS,eT] at hSaved
  rw [hEnergy sigma sourceTest,hEnergy tau targetTest] at hSaved
  exact hSaved
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalProbeTrueSignedDiscardedGlobalL2 -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Genuine SOURCE03 signed physical rational+Mellin major error
on ALL discarded source-B/target-A GLOBAL log cells, across
ALL genuine free prime-mark states and with NO dyad cutoff.
Unlike per-dyad C196, the discarded contribution needs NO
major beta smallness, r<=Q or prime-band comparison.
This follows because the true primitive comparison Knu
vanishes on the discarded event, leaving a unit-modulus
signed original phase, combined with the REAL physical
rare-event mass and selected BIG group cell geometry. -/
theorem source_original_probe_true_signed_discarded_global_L2_sq434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hxi : 0 < xi)
    (r : ℕ) (hr : 0 < r) (u : ℤ) (ζ beta : ℝ)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
       (fun g : G => {p : ℕ // p ∈ P g})
       (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
        ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                  (SourceOriginalVariableBIGState434 BP t),
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if badSource ab.1 ∨ badTarget ab.2 then
            sourceOriginalProbeSignedMajorSlowError434
              J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤
      Cgeo *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let Cgeo : ℝ :=
    2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
      ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi r hr u ζ beta
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let HDrop : X × X → ℂ := fun ab =>
    if badSource ab.1 ∨ badTarget ab.2 then err ab else 0
  have hHDrop (ab : X × X) : ‖HDrop ab‖ ≤ 1 := by
    exact source_original_probe_true_dropped_phase_cutoff_norm434
      J ell m hmJ ν P V Q hA hB xi hhA hhB
      r hr u ζ beta ab.1 ab.2
  have hBound :=
    source_original_probe_true_physical_discarded_BIG_L2_sq434
      J ell m hmJ ν P V hV hVpos
      L d hL hPrimeA hPrimeB
      hA hB xi hhA hhB hxi
      sourceTest targetTest HDrop hHDrop
  have hIdempotent :
      (∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if badSource ab.1 ∨ badTarget ab.2 then
            HDrop ab else 0)) =
      (∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if badSource ab.1 ∨ badTarget ab.2 then
            err ab else 0)) := by
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases hb : badSource ab.1 ∨ badTarget ab.2
    · simp only [if_pos hb, HDrop]
    · simp only [if_neg hb, mul_zero]
  change
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        (if badSource ab.1 ∨ badTarget ab.2 then err ab else 0))‖^2 ≤
      Cgeo*(∑ s : X, w s*‖sourceTest s‖^2)*
        (∑ v : X, w v*‖targetTest v‖^2)
  dsimp only at hBound
  rw [hIdempotent] at hBound
  exact hBound
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedDiscardedFourierGlobal -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The EXACT original SOURCE03 discarded-GLOBAL-cell
RAW-minus-canonical-Knu error at PHYSICAL Fourier frequency
-k theta is small for EVERY theta, k and Mellin zeta.
No rational approximation, major-arc membership, physical
dyad cutoff, or product factorization of endpoint tests is
assumed: the canonical primitive comparison vanishes on the
true discarded event, while the original harmonic-law
rare-event estimate pays its cost exactly once. -/
theorem source_original_true_signed_discarded_fourier_global_L2_434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
        ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                  (SourceOriginalVariableBIGState434 BP t),
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if badSource ab.1 ∨ badTarget ab.2 then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ theta k
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤
      Cgeo *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let Cgeo : ℝ :=
    2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
      ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
  let errSlow : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorSlowError434
      J ell m hmJ ν P V Q hA hB xi 1 (by norm_num)
        0 ζ (-(k:ℝ)*theta)
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let errFourier : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  have hLift :
      -(k:ℝ)*theta = ((0:ℤ):ℝ)/((1:ℕ):ℝ) +
        (-(k:ℝ)*theta)-((0:ℤ):ℝ) := by norm_num
  have hPhase (ab : X × X) : errSlow ab = errFourier ab :=
    source_original_true_signed_major_fourier_error_eq434
      J ell m hmJ ν P V Q hA hB xi 1 (by norm_num)
      0 ζ (-(k:ℝ)*theta) theta k 0 hLift
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  have hSlow :=
    source_original_probe_true_signed_discarded_global_L2_sq434
      J ell m hmJ ν P V hV hVpos
      L d hL hPrimeA hPrimeB
      Q hA hB xi hhA hhB hxi
      1 (by norm_num) 0 ζ (-(k:ℝ)*theta)
      sourceTest targetTest
  have hSum :
      (∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if badSource ab.1 ∨ badTarget ab.2
           then errSlow ab else 0)) =
      (∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if badSource ab.1 ∨ badTarget ab.2
           then errFourier ab else 0)) := by
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases hBad : badSource ab.1 ∨ badTarget ab.2
    · simp only [if_pos hBad]
      rw [hPhase ab]
    · simp only [if_neg hBad]
  change
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2*
        (if badSource ab.1 ∨ badTarget ab.2
         then errFourier ab else 0))‖^2 ≤
       Cgeo*(∑ s : X,w s*‖sourceTest s‖^2)*
         (∑ v : X,w v*‖targetTest v‖^2)
  rw [←hSum]
  exact hSlow
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueNuExactPrimitiveMinusRaw -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- EXACT original ν-physical signed RAW-minus-canonical-Knu
error equals the sum of genuine primitive (jA,χA,jB,χB)
comparison terms MINUS ONE, and only one, raw term.
Both full independently labelled auxiliary prime laws,
source-B/target-A free-mark products and coupled Fourier/
Mellin phase remain literal source03 objects. No spectral,
circle approximation, or source-specific assumptions. -/
theorem source_original_true_nu_exact_primitive_MINUS_RAW434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (source target : ∀ g,
      Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν g) → ℕ) :
    let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let Char := sourceOriginalActualPrimitiveCharacters434 Q
    let Modes := ((JA.product Char).product (JB.product Char))
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k source target =
      (∑ t ∈ Modes,
        sourceOriginalTrueNuPrimitiveFourierTerm434
          J ell m hmJ ν P V Q hA hB xi ζ theta k
          t source target) -
      sourceOriginalTrueNuRawFourierTerm434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        source target := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z => sourcePrimeSharedAtom434 (V z.val.1)
  let XA := sourceOriginalProbeFreeTargetX434 J ell m hmJ ν target
  let XB := sourceOriginalProbeFreeSourceX434 J ell m hmJ ν source
  let JA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let JB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let Char := sourceOriginalActualPrimitiveCharacters434 Q
  let Modes := ((JA.product Char).product (JB.product Char))
  let massA := sourceOriginalProbeCellA434 m P V ν hA
  let massB := sourceOriginalProbeCellB434 m P V ν hB
  let Aux := SourceOriginalGramPrimeTuple434 SA ×
    SourceOriginalGramPrimeTuple434 SB
  let DA : Aux → ℕ := fun ab =>
    sourceOriginalGramPrimeProduct434 SA ab.1
  let DB : Aux → ℕ := fun ab =>
    sourceOriginalGramPrimeProduct434 SB ab.2
  let weight : Aux → ℂ := fun ab =>
    (sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
    (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    Complex.exp (Complex.I *((ζ*Real.log (n:ℝ)):ℂ))
  let σ : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  have hExpanded :=
    source_original_true_primitive_physical_expectation_expand434
      Q JA JB hA hB massA massB
      DA DB XA XB (ν.1.card+ν.2.card) weight phase
  have hExact :
    (∑ ab : Aux,
      weight ab *
        sourceOriginalActualPrimitiveComparisonKernel434
          Q JA JB hA hB massA massB
          (DA ab) XA (DB ab) XB (ν.1.card+ν.2.card) *
        phase (DA ab*DB ab)) =
    ∑ t ∈ Modes,
      sourceOriginalTrueNuPrimitiveFourierTerm434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        t source target := by
    simpa only [SA,SB,muA,muB,XA,XB,JA,JB,Char,Modes,
      massA,massB,Aux,DA,DB,weight,phase,σ,
      sourceOriginalTrueNuPrimitiveFourierTerm434]
      using hExpanded
  change
    (∑ ab : Aux,
      weight ab *
        sourceOriginalActualPrimitiveComparisonKernel434
          Q JA JB hA hB massA massB
          (DA ab) XA (DB ab) XB (ν.1.card+ν.2.card) *
        phase (DA ab*DB ab)) - σ*phase (XA*XB) =
    (∑ t ∈ Modes,
      sourceOriginalTrueNuPrimitiveFourierTerm434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        t source target) - σ*phase (XA*XB)
  rw [hExact]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueOwnMajorNoCellCountLoss -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- Original SOURCE03 global RETAINED MAJOR physical L² estimate
WITHOUT multiplying by the number of original GLOBAL cell pairs.
For each pair of genuine physical source-B and target-A prime-mark
states, the major test is membership of theta in THEIR OWN moving
rational arc at Hcell = exp(jA*hA)*exp(jB*hB). If the true signed
RAW-minus-canonical-Knu Fourier kernel has a UNIFORM pointwise
C191 bound on this actual major region, the full original marked
bilinear pairing obeys the SAME eps² weighted-L² bound.
The major pointwise C191 input remains an explicit premise.
Crucially: no h^-2 cell loss, no fake common major arc, no
product factorization of the arbitrary full-state endpoint tests. -/
theorem source_original_true_own_major_no_cell_count_loss434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (Q : ℕ) (hA hB xi ζ theta L D Carc : ℝ) (k : ℤ)
    (eps : ℝ) (hEps : 0 ≤ eps)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    let activeS := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let activeT := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let major : X × X → Prop := fun ab =>
      idxS ab.1 ∈ activeS ∧ idxT ab.2 ∈ activeT ∧
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^Carc/(Real.exp ((idxT ab.2:ℝ)*hA) *
                  Real.exp ((idxS ab.1:ℝ)*hB)))
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    (∀ ab : X × X, major ab → ‖err ab‖ ≤ eps) →
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2 *
        (if major ab then err ab else 0))‖^2 ≤
      eps^2 *
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest *
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let activeS := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let activeT := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let major : X × X → Prop := fun ab =>
    idxS ab.1 ∈ activeS ∧ idxT ab.2 ∈ activeT ∧
    (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^Carc/(Real.exp ((idxT ab.2:ℝ)*hA) *
                Real.exp ((idxS ab.1:ℝ)*hB)))
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  intro hPoint
  have hVEq (g : G) : V g = ∑ p : BP g, 1/(prime g p:ℝ) := by
    calc
      V g = ∑ p ∈ P g, 1/(p:ℝ) := hV g
      _ = ∑ p : BP g, 1/(prime g p:ℝ) := by
        simpa only [BP,prime] using
          (Finset.sum_coe_sort (P g) (fun p : ℕ => 1/(p:ℝ))).symm
  let masked : X × X → ℂ := fun ab => if major ab then err ab else 0
  have hMasked (s v : X) : ‖masked (s,v)‖ ≤ eps := by
    by_cases h : major (s,v)
    · simpa only [masked,if_pos h] using hPoint (s,v) h
    · simpa only [masked,if_neg h,norm_zero] using hEps
  have hPhysical :=
    source_original_true_variable_BIG_L2_error434
      BP t prime V hVpos hVEq
      sourceTest targetTest masked eps hEps hMasked
  exact hPhysical
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFullRetainedOwnArcMajor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 17000000

/-- TRUE ORIGINAL source03 retained PHYSICAL Fourier major on the
MOVING own rational arc of EACH source-B/target-A active cell.
UNLIKE separate-cell bounds, it retains NO factor counting pairs
of original GLOBAL cells: C191 major is pointwise for the actual
joint physical states at their OWN arc, and the original independent
harmonic prime law lifts this uniformly to arbitrary full-state L2
endpoint tests. All genuine prime-band, Q/xi, mesh, beta and
Mellin restrictions remain explicit, no ad hoc test factorization.
The complement off-own circle, true bad, B transference and
Green64 are NOT obtained by this theorem. -/
theorem source_original_true_full_retained_own_arc_major_L2_434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBsave : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g, Vmin ≤ V g)
    (Q : ℕ)
    (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (L : ℝ) (hL : 192 ≤ L)
    (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (iA : ν.1) (iB : ν.2)
    (uA vA uB vB : ℕ)
    (huA : 1 ≤ uA) (huB : 1 ≤ uB)
    (huvA : uA ≤ vA) (huvB : uB ≤ vB)
    (hvA : (vA:ℝ) ≤ Real.exp (L^d))
    (hvB : (vB:ℝ) ≤ Real.exp (L^d))
    (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
    (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
    (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
    (hYA : Y ≤ ((uA+1:ℕ):ℝ))
    (hYB : Y ≤ ((uB+1:ℕ):ℝ))
    (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
    (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
    (ζ theta : ℝ) (k : ℤ) (D Carc : ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Q)
    (hBudget :
      3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
        |(k:ℝ)| *L^Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
    (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hA+hB ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ),
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    let activeS := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let activeT := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let major : X × X → Prop := fun ab =>
      idxS ab.1 ∈ activeS ∧ idxT ab.2 ∈ activeT ∧
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^Carc/(Real.exp ((idxT ab.2:ℝ)*hA) *
                  Real.exp ((idxS ab.1:ℝ)*hB)))
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2 *
        (if major ab then err ab else 0))‖^2 ≤
      eps^2 *
        sourceOriginalVariableBIGEnergy434 BP t mu sourceTest *
        sourceOriginalVariableBIGEnergy434 BP t mu targetTest := by
  obtain ⟨K,Y,hK,hPointwise⟩ :=
    source_original_true_global_pair_retained_fourier_pointwise434
      Cq Cxi Cs C4 gamma d B hgamma hd hBsave
  refine ⟨K,Y,hK,?_⟩
  intro G instF instD J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi L hL
    hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k D Carc
    S hS hSscale hQchar hBudget
    hC4 hDeltaLe hWidth hWidth1 hZeta
    sourceTest targetTest
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let activeS := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let activeT := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let major : X × X → Prop := fun ab =>
    idxS ab.1 ∈ activeS ∧ idxT ab.2 ∈ activeT ∧
    (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^Carc/(Real.exp ((idxT ab.2:ℝ)*hA) *
                Real.exp ((idxS ab.1:ℝ)*hB)))
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
  have hEps : 0 ≤ eps := by
    dsimp only [eps]
    have hKV : 0 ≤ K/Vmin := div_nonneg hK hVmin.le
    exact mul_nonneg (by linarith)
      (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
  have hVpos : ∀ g, 0 < V g :=
    fun g => hVmin.trans_le (hMass g)
  have hPoint (ab : X × X)
      (hm : major ab) : ‖err ab‖ ≤ eps := by
    rcases hm with ⟨hjB,hjA,hOwn⟩
    let jA : ℤ := idxT ab.2
    let jB : ℤ := idxS ab.1
    let Uscale : ℝ := Real.exp (((jA:ℝ)+1)*hA)
    let Vscale : ℝ := Real.exp (((jB:ℝ)+1)*hB)
    have hU : 0 ≤ Uscale := (Real.exp_pos _).le
    have hVB : 0 ≤ Vscale := (Real.exp_pos _).le
    have hBound := hPointwise J ell m hmJ ν P V hV
      Vmin hVmin hMass Q jA jB hBIGA hBIGB
      hA hB xi hhA hhB hxi L hL
      hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
      iA iB uA vA uB vB huA huB huvA huvB hvA hvB
      huLargeA huLargeB huBIGA huBIGB hYA hYB
      hBandA hBandB ζ theta k D Carc
      Uscale Vscale S hU hVB hS hSscale
      hQchar hBudget hOwn rfl rfl
      hC4 hDeltaLe hWidth hWidth1 hZeta
      hjA hjB ab.1 ab.2 rfl rfl
    change ‖err ab‖ ≤ eps at hBound
    exact hBound
  have hResult :=
    source_original_true_own_major_no_cell_count_loss434
      J ell m hmJ ν P V hV hVpos
      Q hA hB xi ζ theta L D Carc k
      eps hEps sourceTest targetTest hPoint
  exact hResult
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedCellSignedFubini -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 14500000

/-- For ONE exact original SOURCE03 active output GLOBAL cell pair,
the true selected TWO-INTEGER signed Fourier/Mellin residual is
exactly the full primitive Knu auxiliary expectation minus the
signed physical RAW output expectation, with NO changes in
source prime labels, harmonic weights, primitive character
families, inclusion-exclusion sign or output coefficient tests.
The original selected Fourier kernel is used literally,
rather than replaced by an invented jointly dependent H.
No C6 saving is assumed by this identity. -/
theorem source_original_true_selected_cell_signed_fubini434
    {G : Type} [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (Q : ℕ) (hA hB xi ζ theta : ℝ) (k : ℤ)
    (jA jB : ℤ) (aCoeff bCoeff : ℕ → ℂ) :
    let SA : ν.1 → Finset ℕ := fun z => P z.val.1
    let SB : ν.2 → Finset ℕ := fun z => P z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(V z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(V z.val.1)
    let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
    let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
    let activeA : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 hA n=jA
    let activeB : ℕ → Prop := fun n =>
      sourceOriginalLiteralLogCellIndex434 hB n=jB
    let TA := TAfull.filter activeA
    let TB := TBfull.filter activeB
    let sigma : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
    let phase : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
        sourceOriginalPureMellinPhase434 ζ n
    let H : ℕ → ℕ → ℂ := fun nA nB =>
      ∑ ab : SourceOriginalGramPrimeTuple434 SA ×
             SourceOriginalGramPrimeTuple434 SB,
        ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
         (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
        sourceOriginalActualPrimitiveComparisonKernel434 Q
          (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
          (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
          hA hB
          (sourceOriginalProbeCellA434 m P V ν hA)
          (sourceOriginalProbeCellB434 m P V ν hB)
          (sourceOriginalGramPrimeProduct434 SA ab.1) nA
          (sourceOriginalGramPrimeProduct434 SB ab.2) nB
          (ν.1.card+ν.2.card) *
        phase (sourceOriginalGramPrimeProduct434 SA ab.1 *
          sourceOriginalGramPrimeProduct434 SB ab.2)
    (∑ nA ∈ TA, ∑ nB ∈ TB,
      aCoeff nA*bCoeff nB*
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB) =
      (∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*H nA nB) -
      sigma * (∑ nA ∈ TAfull, ∑ nB ∈ TBfull,
        (if activeA nA then aCoeff nA else 0) *
        (if activeB nB then bCoeff nB else 0) *
        phase (nA*nB)) := by
  classical
  dsimp only
  let SA : ν.1 → Finset ℕ := fun z => P z.val.1
  let SB : ν.2 → Finset ℕ := fun z => P z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(V z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(V z.val.1)
  let TAfull := sourceOriginalPhysicalProductAtomSupport434 SA
  let TBfull := sourceOriginalPhysicalProductAtomSupport434 SB
  let activeA : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 hA n=jA
  let activeB : ℕ → Prop := fun n =>
    sourceOriginalLiteralLogCellIndex434 hB n=jB
  let TA := TAfull.filter activeA
  let TB := TBfull.filter activeB
  let sigma : ℂ := -((-1:ℂ)^(ν.1.card+ν.2.card))
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
  let H : ℕ → ℕ → ℂ := fun nA nB =>
    ∑ ab : SourceOriginalGramPrimeTuple434 SA ×
           SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
       (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
      sourceOriginalActualPrimitiveComparisonKernel434 Q
        (sourceOriginalProbeActiveCellsA434 m P V ν hA xi)
        (sourceOriginalProbeActiveCellsB434 m P V ν hB xi)
        hA hB
        (sourceOriginalProbeCellA434 m P V ν hA)
        (sourceOriginalProbeCellB434 m P V ν hB)
        (sourceOriginalGramPrimeProduct434 SA ab.1) nA
        (sourceOriginalGramPrimeProduct434 SB ab.2) nB
        (ν.1.card+ν.2.card) *
      phase (sourceOriginalGramPrimeProduct434 SA ab.1 *
        sourceOriginalGramPrimeProduct434 SB ab.2)
  have hPoint (nA nB : ℕ) :
      sourceOriginalProbeSignedSelectedFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB =
      H nA nB - sigma * phase (nA*nB) := by
    have hEq := source_original_true_selected_RAW_Knu_real_masses434
      J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB
    change
      sourceOriginalProbeSignedSelectedFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB =
      H nA nB - sigma * phase (nA*nB) at hEq
    exact hEq
  have hMask :
      (∑ n ∈ TAfull, ∑ mm ∈ TBfull,
        (if activeA n then aCoeff n else 0) *
        (if activeB mm then bCoeff mm else 0) *
        phase (n*mm)) =
      (∑ n ∈ TA, ∑ mm ∈ TB,
        aCoeff n*bCoeff mm*phase (n*mm)) := by
    calc
      _ = ∑ n ∈ TAfull, if activeA n then
          (∑ mm ∈ TBfull, if activeB mm then
            aCoeff n*bCoeff mm*phase (n*mm) else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            by_cases ha : activeA n
            · simp only [if_pos ha]
              apply Finset.sum_congr rfl
              intro mm hmm
              by_cases hb : activeB mm <;> simp [hb]
            · simp [ha]
      _ = _ := by
        simp only [TA,TB,Finset.sum_filter]
  have hAlgebra :
      (∑ n ∈ TA, ∑ mm ∈ TB,
        aCoeff n*bCoeff mm*
          (H n mm-sigma*phase (n*mm))) =
      (∑ n ∈ TA, ∑ mm ∈ TB,
        aCoeff n*bCoeff mm*H n mm) -
      sigma*(∑ n ∈ TA, ∑ mm ∈ TB,
        aCoeff n*bCoeff mm*phase (n*mm)) := by
    calc
      _ = ∑ n ∈ TA, ∑ mm ∈ TB,
        (aCoeff n*bCoeff mm*H n mm -
          sigma*(aCoeff n*bCoeff mm*phase (n*mm))) := by
            apply Finset.sum_congr rfl
            intro n hn
            apply Finset.sum_congr rfl
            intro mm hmm
            ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  calc
    (∑ nA ∈ TA, ∑ nB ∈ TB,
      aCoeff nA*bCoeff nB*
        sourceOriginalProbeSignedSelectedFourierError434
          J ell m hmJ ν P V Q hA hB xi ζ theta k nA nB) =
      (∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*(H nA nB-sigma*phase (nA*nB))) := by
        apply Finset.sum_congr rfl
        intro nA hnA
        apply Finset.sum_congr rfl
        intro nB hnB
        rw [hPoint nA nB]
    _ = (∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*H nA nB) -
      sigma*(∑ nA ∈ TA, ∑ nB ∈ TB,
        aCoeff nA*bCoeff nB*phase (nA*nB)) := hAlgebra
    _ = _ := by rw [hMask]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSignedDiscardedGoodMask -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 15000000

/-- TRUE physical original signed RAW-minus-canonical-Knu discarded
GLOBAL Fourier estimate in exactly the GOOD/BAD event notation
needed for the moving-cell global operator. GOOD means BOTH
literal source-B and target-A selected GLOBAL prime-product cells
are ACTIVE under the authentic ν-dependent normalized prime law.
No theta, k, Mellin ζ, mode/rational arc or endpoint-test restriction.
The bad-event L2 budget is inherited directly from the fully verified
SOURCE03 physical rare-event estimate and hence paid ONCE. -/
theorem source_original_true_signed_discarded_good_mask_L2_434
    {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (hVpos : ∀ g, 0 < V g)
    (L d : ℝ) (hL : 1 ≤ L)
    (hPrimeA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
       p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (Q : ℕ) (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (ζ theta : ℝ) (k : ℤ)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ) :
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let w := sourceOriginalVariableBIGMass434 BP t mu
    let X := SourceOriginalVariableBIGState434 BP t
    let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
    let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
    let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let badSource : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun s => sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
    let badTarget : SourceOriginalVariableBIGState434 BP t → Prop :=
      fun v => sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
    let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
        ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
    let good : X × X → Prop := fun ab =>
      ¬badSource ab.1 ∧ ¬badTarget ab.2
    ‖(∑ ab : (SourceOriginalVariableBIGState434 BP t) ×
                  (SourceOriginalVariableBIGState434 BP t),
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2*
          (if ¬good ab then
            sourceOriginalProbeSignedMajorFourierError434
              J ell m hmJ ν P V Q hA hB xi ζ theta k
              (fun g i => (ab.1 g i).val)
              (fun g i => (ab.2 g i).val)
           else 0))‖^2 ≤
      Cgeo *
        (∑ s : SourceOriginalVariableBIGState434 BP t,
          w s*‖sourceTest s‖^2) *
        (∑ v : SourceOriginalVariableBIGState434 BP t,
          w v*‖targetTest v‖^2) := by
  classical
  dsimp only
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let eA := sourceOriginalProbeTargetAFreeEmbedding434 J ell m hmJ ν
  let eB := sourceOriginalProbeSourceBFreeEmbedding434 J ell m hmJ ν
  let activeA := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let activeB := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let badSource : X → Prop := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2, ((s (eB z).1 (eB z).2).val:ℕ)) ∉ activeB
  let badTarget : X → Prop := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1, ((v (eA z).1 (eA z).2).val:ℕ)) ∉ activeA
  let good : X × X → Prop := fun ab =>
    ¬badSource ab.1 ∧ ¬badTarget ab.2
  let Cgeo : ℝ := 2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
    ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
  have hOld := source_original_true_signed_discarded_fourier_global_L2_434
    J ell m hmJ ν P V hV hVpos L d hL hPrimeA hPrimeB
    Q hA hB xi hhA hhB hxi ζ theta k sourceTest targetTest
  simpa only [good, not_and_or, not_not] using hOld
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFullResidualFromOwnMinor -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The FULL TRUE original ν-physical signed RAW-minus-canonical
Knu Fourier/Mellin residual is reduced to EXACTLY ONE pending
analytic input: its weighted-L2 operator estimate on genuine
ACTIVE original GLOBAL states OUTSIDE EACH PAIR'S OWN moving
rational arc. The retained major branch is UNCONDITIONALLY
proved using original C191, and TRUE discarded free-mark
states are bounded ONCE by SOURCE03 rare-event arithmetic.
No artificial common arc, no factorization, no multiple cell
count loss or unverified extra arithmetic saving. Original
prime interval geometry, Q/xi/mesh and Mellin restrictions
remain explicit. This theorem alone does NOT prove its
off-own-minor hypothesis or the four-sign sh:correlation. -/
theorem source_original_true_full_signed_residual_from_own_minor_L2_434
    (Cq Cxi Cs C4 : ℕ) (gamma d B : ℝ)
    (hgamma : 0 < gamma) (hd : 0 ≤ d) (hBsave : 0 < B) :
    ∃ K Y : ℝ, 0 ≤ K ∧
    ∀ {G : Type} [Fintype G] [DecidableEq G]
    (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m)
    (P : G → Finset ℕ) (V : G → ℝ)
    (hV : ∀ g, V g = ∑ p ∈ P g, 1/(p:ℝ))
    (Vmin : ℝ) (hVmin : 0 < Vmin)
    (hMass : ∀ g, Vmin ≤ V g)
    (Q : ℕ)
    (hBIGA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (hBIGB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ Q^2 < p)
    (hA hB xi : ℝ)
    (hhA : 0 < hA) (hhB : 0 < hB) (hxi : 0 < xi)
    (L : ℝ) (hL : 192 ≤ L)
    (hPrimeUpperA : ∀ z : ν.1, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hPrimeUpperB : ∀ z : ν.2, ∀ p ∈ P z.val.1,
      p.Prime ∧ (p:ℝ) ≤ Real.exp (L^d))
    (hLdyad : ((Real.log (2:ℝ))⁻¹+1) ≤ L)
    (hQ : (Q:ℝ) ≤ L^Cq)
    (hXi : xi⁻¹ ≤ L^Cxi)
    (iA : ν.1) (iB : ν.2)
    (uA vA uB vB : ℕ)
    (huA : 1 ≤ uA) (huB : 1 ≤ uB)
    (huvA : uA ≤ vA) (huvB : uB ≤ vB)
    (hvA : (vA:ℝ) ≤ Real.exp (L^d))
    (hvB : (vB:ℝ) ≤ Real.exp (L^d))
    (huLargeA : Real.exp (L^gamma) ≤ ((uA+1:ℕ):ℝ))
    (huLargeB : Real.exp (L^gamma) ≤ ((uB+1:ℕ):ℝ))
    (huBIGA : Q^2 ≤ uA) (huBIGB : Q^2 ≤ uB)
    (hYA : Y ≤ ((uA+1:ℕ):ℝ))
    (hYB : Y ≤ ((uB+1:ℕ):ℝ))
    (hBandA : P iA.val.1 = sourceOriginalActualPrimeBand434 uA vA)
    (hBandB : P iB.val.1 = sourceOriginalActualPrimeBand434 uB vB)
    (ζ theta : ℝ) (k : ℤ) (D Carc : ℝ)
    (S : ℝ) (hS : 0 ≤ S) (hSscale : S ≤ L^Cs)
    (hQchar : k.natAbs*Nat.ceil (L^(D+1)) ≤ Q)
    (hBudget :
      3*(((k.natAbs*Nat.ceil (L^(D+1)):ℕ):ℝ)) *
        |(k:ℝ)| *L^Carc ≤ 2*S)
    (hC4 : (Cs:ℝ)+1 ≤ (C4:ℝ))
    (hDeltaLe : (K/Vmin)*L^(-(B+(Cq:ℝ))) ≤ 1)
    (hWidth : hA+hB ≤ L^(-(B+((4*Cq+C4:ℕ):ℝ))))
    (hWidth1 : hA+hB ≤ 1)
    (hZeta : |ζ| ≤ L^C4)
    (minorBudget : ℝ)
    (sourceTest targetTest : SourceOriginalVariableBIGState434
      (fun g : G => {p : ℕ // p ∈ P g})
      (sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν) → ℂ),
    let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
    let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
    let prime : (g : G) → BP g → ℕ := fun g p => p.val
    let mu := sourceOriginalJointHarmonicMu434 BP prime V
    let X := SourceOriginalVariableBIGState434 BP t
    let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
    let idxS : X → ℤ := fun s =>
      sourceOriginalLiteralLogCellIndex434 hB
        (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
          (fun g i => (s g i).val))
    let idxT : X → ℤ := fun v =>
      sourceOriginalLiteralLogCellIndex434 hA
        (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
          (fun g i => (v g i).val))
    let activeS := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
    let activeT := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
    let active : X × X → Prop := fun ab =>
      ¬(sourceOriginalLiteralLogCellIndex434 hB
        (∏ z : ν.2,
          ((ab.1 (sourceOriginalProbeSourceBFreeEmbedding434
            J ell m hmJ ν z).1
            (sourceOriginalProbeSourceBFreeEmbedding434
              J ell m hmJ ν z).2).val:ℕ)) ∉ activeS) ∧
      ¬(sourceOriginalLiteralLogCellIndex434 hA
        (∏ z : ν.1,
          ((ab.2 (sourceOriginalProbeTargetAFreeEmbedding434
            J ell m hmJ ν z).1
            (sourceOriginalProbeTargetAFreeEmbedding434
              J ell m hmJ ν z).2).val:ℕ)) ∉ activeT)
    let major : X × X → Prop := fun ab =>
      idxS ab.1 ∈ activeS ∧ idxT ab.2 ∈ activeT ∧
      (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^Carc/(Real.exp ((idxT ab.2:ℝ)*hA) *
                  Real.exp ((idxS ab.1:ℝ)*hB)))
    let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
    let Cgeo : ℝ :=
      2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
           ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
    let err : X × X → ℂ := fun ab =>
      sourceOriginalProbeSignedMajorFourierError434
        J ell m hmJ ν P V Q hA hB xi ζ theta k
        (fun g i => (ab.1 g i).val)
        (fun g i => (ab.2 g i).val)
    (‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2 *
        (if active ab ∧ ¬major ab then err ab else 0))‖^2 ≤
      minorBudget *
        (∑ s : X, w s*‖sourceTest s‖^2) *
        (∑ v : X, w v*‖targetTest v‖^2)) →
    ‖(∑ ab : X × X,
      ((w ab.1*w ab.2:ℝ):ℂ) *
        star (sourceTest ab.1)*targetTest ab.2 *
        err ab)‖^2 ≤
      2*(2*(eps^2+minorBudget)+Cgeo) *
        (∑ s : X,w s*‖sourceTest s‖^2) *
        (∑ v : X,w v*‖targetTest v‖^2) := by
  obtain ⟨K,Y,hK,hMajorBound⟩ :=
    source_original_true_full_retained_own_arc_major_L2_434
      Cq Cxi Cs C4 gamma d B hgamma hd hBsave
  refine ⟨K,Y,hK,?_⟩
  intro G instF instD J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi L hL
    hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k D Carc
    S hS hSscale hQchar hBudget
    hC4 hDeltaLe hWidth hWidth1 hZeta
    minorBudget sourceTest targetTest
  dsimp only
  intro hMinor
  classical
  let BP : G → Type := fun g => {p : ℕ // p ∈ P g}
  let t := sourceOriginalProbeFreeMarkCount434 J ell m hmJ ν
  let prime : (g : G) → BP g → ℕ := fun g p => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP prime V
  let X := SourceOriginalVariableBIGState434 BP t
  let w : X → ℝ := sourceOriginalVariableBIGMass434 BP t mu
  let idxS : X → ℤ := fun s =>
    sourceOriginalLiteralLogCellIndex434 hB
      (sourceOriginalProbeFreeSourceX434 J ell m hmJ ν
        (fun g i => (s g i).val))
  let idxT : X → ℤ := fun v =>
    sourceOriginalLiteralLogCellIndex434 hA
      (sourceOriginalProbeFreeTargetX434 J ell m hmJ ν
        (fun g i => (v g i).val))
  let activeS := sourceOriginalProbeActiveCellsB434 m P V ν hB xi
  let activeT := sourceOriginalProbeActiveCellsA434 m P V ν hA xi
  let active : X × X → Prop := fun ab =>
    ¬(sourceOriginalLiteralLogCellIndex434 hB
      (∏ z : ν.2,
        ((ab.1 (sourceOriginalProbeSourceBFreeEmbedding434
          J ell m hmJ ν z).1
          (sourceOriginalProbeSourceBFreeEmbedding434
            J ell m hmJ ν z).2).val:ℕ)) ∉ activeS) ∧
    ¬(sourceOriginalLiteralLogCellIndex434 hA
      (∏ z : ν.1,
        ((ab.2 (sourceOriginalProbeTargetAFreeEmbedding434
          J ell m hmJ ν z).1
          (sourceOriginalProbeTargetAFreeEmbedding434
            J ell m hmJ ν z).2).val:ℕ)) ∉ activeT)
  let major : X × X → Prop := fun ab =>
    idxS ab.1 ∈ activeS ∧ idxT ab.2 ∈ activeT ∧
    (theta : AddCircle (1:ℝ)) ∈ sourceCircleRationalArcs434
      (k.natAbs*Nat.ceil (L^(D+1)))
      (L^Carc/(Real.exp ((idxT ab.2:ℝ)*hA) *
                Real.exp ((idxS ab.1:ℝ)*hB)))
  let Cgeo : ℝ :=
    2*((((Fintype.card ν.1:ℝ)*L^d)/hA +
        ((Fintype.card ν.2:ℝ)*L^d)/hB)+4)*xi
  let err : X × X → ℂ := fun ab =>
    sourceOriginalProbeSignedMajorFourierError434
      J ell m hmJ ν P V Q hA hB xi ζ theta k
      (fun g i => (ab.1 g i).val)
      (fun g i => (ab.2 g i).val)
  let eps : ℝ := (3*(K/Vmin)+2)*L^(-B)
  have hVpos : ∀ g, 0 < V g :=
    fun g => hVmin.trans_le (hMass g)
  have hMajor' := hMajorBound J ell m hmJ ν P V hV
    Vmin hVmin hMass Q hBIGA hBIGB
    hA hB xi hhA hhB hxi L hL
    hPrimeUpperA hPrimeUpperB hLdyad hQ hXi
    iA iB uA vA uB vB huA huB huvA huvB hvA hvB
    huLargeA huLargeB huBIGA huBIGB hYA hYB
    hBandA hBandB ζ theta k D Carc
    S hS hSscale hQchar hBudget
    hC4 hDeltaLe hWidth hWidth1 hZeta
    sourceTest targetTest
  have hMajorNat :
      ‖(∑ ab : X × X,
         ((w ab.1*w ab.2:ℝ):ℂ) *
           star (sourceTest ab.1)*targetTest ab.2*
           (if major ab then err ab else 0))‖^2 ≤
        (eps^2)*(∑ s : X,w s*‖sourceTest s‖^2)*
          (∑ v : X,w v*‖targetTest v‖^2) := by
    dsimp only at hMajor'
    rw [source_original_true_variable_BIG_energy_norm434
      BP t mu sourceTest,
      source_original_true_variable_BIG_energy_norm434
      BP t mu targetTest] at hMajor'
    convert hMajor' using 1
  have hDiscarded' :=
    source_original_true_signed_discarded_good_mask_L2_434
      J ell m hmJ ν P V hV hVpos
      L d (by linarith : 1 ≤ L)
      hPrimeUpperA hPrimeUpperB
      Q hA hB xi hhA hhB hxi
      ζ theta k sourceTest targetTest
  have hBad :
      ‖(∑ ab : X × X,
        ((w ab.1*w ab.2:ℝ):ℂ) *
          star (sourceTest ab.1)*targetTest ab.2 *
          (if ¬active ab then err ab else 0))‖^2 ≤
        Cgeo*(∑ s : X,w s*‖sourceTest s‖^2)*
          (∑ v : X,w v*‖targetTest v‖^2) := by
    dsimp only at hDiscarded'
    simpa only [active,not_and_or,not_not] using hDiscarded'
  have hSubset (ab : X × X) (hm : major ab) : active ab := by
    change ¬(idxS ab.1 ∉ activeS) ∧
      ¬(idxT ab.2 ∉ activeT)
    exact ⟨fun h => h hm.1, fun h => h hm.2.1⟩
  apply source_original_finite_own_arc_major_minor_bad_combine434
    w w sourceTest targetTest err active major hSubset
    (eps^2) minorBudget Cgeo
  · convert hMajorNat using 1
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases hm : major ab <;> simp [hm]
  · simpa only [active,major,not_not,not_and] using hMinor
  · convert hBad using 1
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases ha : active ab <;> simp [ha]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTwoGlobalWindowInverseAtomPairing -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 11000000

/-- EXACT original source03 TWO independent BIG labelled-prime
products, each in its genuine dyadic window, are an isometric
representation of arbitrary INTEGER product-atom coefficient
vectors. The joint arithmetic Fourier/Mellin phase may be any
function of the true product nA*nB; this is not a factorization
assumption on the coefficient vectors. The proof uses true
harmonic laws and the sharp inverse-atom recovery, with no
factor of physical fibre cardinality and no synthetic
probability distribution. This is an algebraic bridge,
not by itself the C6 logarithmic minor-arc saving. -/
theorem source_original_true_two_global_window_inverse_atom_pairing434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (hmuA : ∀ i p, p ∈ SA i → 0 < muA i p)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (hmuB : ∀ i p, p ∈ SB i → 0 < muB i p)
    (WA WB : Finset ℕ)
    (a b : ℕ → ℂ)
    (F : ℕ → ℂ) :
    (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
              SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
       (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
        (sourceOriginalPhysicalProductAtomWindowInverseLift434
          SA muA WA a ab.1) *
        (sourceOriginalPhysicalProductAtomWindowInverseLift434
          SB muB WB b ab.2) *
        F (sourceOriginalGramPrimeProduct434 SA ab.1 *
           sourceOriginalGramPrimeProduct434 SB ab.2)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 SA,
      ∑ m ∈ sourceOriginalPhysicalProductAtomSupport434 SB,
        (if n ∈ WA then a n else 0) *
        (if m ∈ WB then b m else 0) * F (n*m) := by
  classical
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    sourceOriginalPhysicalProductAtomWindowInverseLift434 SA muA WA a
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    sourceOriginalPhysicalProductAtomWindowInverseLift434 SB muB WB b
  have hPush :=
    source_original_physical_two_global_atom_pushforward434
      SA muA SB muB fA fB F
  change
    (∑ ab : SourceOriginalGramPrimeTuple434 SA ×
              SourceOriginalGramPrimeTuple434 SB,
      ((sourceOriginalGramPrimeMass434 SA muA ab.1:ℂ) *
       (sourceOriginalGramPrimeMass434 SB muB ab.2:ℂ)) *
        fA ab.1 * fB ab.2 *
        F (sourceOriginalGramPrimeProduct434 SA ab.1 *
           sourceOriginalGramPrimeProduct434 SB ab.2)) =
    ∑ n ∈ sourceOriginalPhysicalProductAtomSupport434 SA,
      ∑ m ∈ sourceOriginalPhysicalProductAtomSupport434 SB,
        (if n ∈ WA then a n else 0) *
        (if m ∈ WB then b m else 0) * F (n*m)
  rw [hPush]
  apply Finset.sum_congr rfl
  intro n hn
  rw [source_original_physical_atom_window_inverse_recovers434
    SA muA hmuA WA a n hn]
  apply Finset.sum_congr rfl
  intro m hm
  rw [source_original_physical_atom_window_inverse_recovers434
    SB muB hmuB WB b m hm]
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTwoGlobalWindowInverseMask -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 13500000

/-- The ORIGINAL source03 dyadic mask is already carried by
the TRUE inverse-lift test itself. An actual labelled prime
tuple whose integer product lies outside W receives exactly
ZERO multiplier, without a fabricated support restriction. -/
theorem source_original_inverse_prime_test_zero_off_window434
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (mu : ι → ℕ → ℝ)
    (W : Finset ℕ) (a : ℕ → ℂ)
    (v : SourceOriginalGramPrimeTuple434 S)
    (hv : sourceOriginalGramPrimeProduct434 S v ∉ W) :
    sourceOriginalPhysicalProductAtomWindowInverseLift434
      S mu W a v = 0 := by
  classical
  simp [sourceOriginalPhysicalProductAtomWindowInverseLift434,
        sourceOriginalPhysicalProductAtomInverseLift434,hv]

/-- Exact equality of the two ORIGINAL separate C6 prime
dyadic window masks and the single true two-global physical
sum whose endpoint inverse-lift functions already vanish
off their windows. Independent real source/target harmonic
prime laws and an arbitrary JOINT complex F(nA*nB) remain
unchanged; no C6 saving is assumed here. -/
theorem source_original_true_two_global_window_inverse_mask_identity434
    {ιA ιB : Type}
      [Fintype ιA] [DecidableEq ιA]
      [Fintype ιB] [DecidableEq ιB]
    (SA : ιA → Finset ℕ) (muA : ιA → ℕ → ℝ)
    (SB : ιB → Finset ℕ) (muB : ιB → ℕ → ℝ)
    (WA WB : Finset ℕ)
    (a b : ℕ → ℂ)
    (F : ℕ → ℂ) :
    let XA := SourceOriginalGramPrimeTuple434 SA
    let XB := SourceOriginalGramPrimeTuple434 SB
    let pa := sourceOriginalGramPrimeProduct434 SA
    let pb := sourceOriginalGramPrimeProduct434 SB
    let fA := sourceOriginalPhysicalProductAtomWindowInverseLift434
      SA muA WA a
    let fB := sourceOriginalPhysicalProductAtomWindowInverseLift434
      SB muB WB b
    (∑ vA : XA, if pa vA ∈ WA then
      (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
      (∑ vB : XB, if pb vB ∈ WB then
        (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
        F (pa vA*pb vB) else 0)
      else 0) =
    (∑ v : XA × XB,
      ((sourceOriginalGramPrimeMass434 SA muA v.1:ℂ) *
        (sourceOriginalGramPrimeMass434 SB muB v.2:ℂ)) *
        fA v.1 * fB v.2 * F (pa v.1*pb v.2)) := by
  classical
  dsimp only
  let XA := SourceOriginalGramPrimeTuple434 SA
  let XB := SourceOriginalGramPrimeTuple434 SB
  let pa := sourceOriginalGramPrimeProduct434 SA
  let pb := sourceOriginalGramPrimeProduct434 SB
  let fA := sourceOriginalPhysicalProductAtomWindowInverseLift434
    SA muA WA a
  let fB := sourceOriginalPhysicalProductAtomWindowInverseLift434
    SB muB WB b
  let wA : XA → ℂ := fun v => (sourceOriginalGramPrimeMass434 SA muA v:ℂ)
  let wB : XB → ℂ := fun v => (sourceOriginalGramPrimeMass434 SB muB v:ℂ)
  have hOffA (vA : XA) (hv : pa vA ∉ WA) : fA vA=0 :=
    source_original_inverse_prime_test_zero_off_window434
      SA muA WA a vA hv
  have hOffB (vB : XB) (hv : pb vB ∉ WB) : fB vB=0 :=
    source_original_inverse_prime_test_zero_off_window434
      SB muB WB b vB hv
  have hPerA (vA : XA) :
      (if pa vA ∈ WA then wA vA*fA vA*
        (∑ vB : XB, if pb vB ∈ WB then
          wB vB*fB vB*F (pa vA*pb vB) else 0)
       else 0) =
      (∑ vB : XB,
        (wA vA*wB vB)*fA vA*fB vB*F (pa vA*pb vB)) := by
    by_cases ha : pa vA ∈ WA
    · simp only [if_pos ha]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro vB hvB
      by_cases hb : pb vB ∈ WB
      · simp only [if_pos hb]
        ring
      · simp only [if_neg hb]
        rw [hOffB vB hb]
        ring
    · simp only [if_neg ha]
      rw [hOffA vA ha]
      simp
  change (∑ vA : XA, if pa vA ∈ WA then
      wA vA*fA vA*
      (∑ vB : XB, if pb vB ∈ WB then
        wB vB*fB vB*F (pa vA*pb vB) else 0)
      else 0) =
    (∑ v : XA × XB,
      (wA v.1*wB v.2)*fA v.1*fB v.2*F (pa v.1*pb v.2))
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro vA hvA
  exact hPerA vA
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedTwoIntegerRawMellin -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 23000000

/-- ACTUAL source03 C6 logarithmic Fourier/Mellin minor saving for
ARBITRARY two-INTEGER selected coefficient vectors on the
attainable original BIG prime-product supports. Unlike older
pointwise/unit-bounded tests, coefficients are normalized by
their REAL harmonic product-atom mass, proven strictly positive
on the source prime intervals. Uses the independently certified
true ν selected arithmetic C6 weighted prime-tuple minor,
then the exact inverse-atom isometry and actual two-sided
labelled-prime Fourier/window pushforward. No new spectral
saving premise or fictional uniform prime product law.
This covers signed RAW of ONE true ν/two product dyads,
not the primitive Knu difference or original full correlation. -/
theorem source_original_true_selected_two_integer_raw_MELLIN_C6_minor434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (ν : SourceOriginalProbePattern434 β m)
    (hPattern : ν ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let AW := (Finset.range P).image (fun i => M+i)
    let BW := (Finset.range Q).image (fun j => N+j)
    let EA : ℝ := ∑ n ∈ TA, if n ∈ AW then
      ‖aCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SA muA n
      else 0
    let EB : ℝ := ∑ n ∈ TB, if n ∈ BW then
      ‖bCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SB muB n
      else 0
    let phase : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
       (∑ n ∈ TA, ∑ m ∈ TB,
         (if n ∈ AW then aCoeff n else 0) *
         (if m ∈ BW then bCoeff m else 0) *phase (n*m))‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  classical
  let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
  let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let AW := (Finset.range P).image (fun i => M+i)
  let BW := (Finset.range Q).image (fun j => N+j)
  let EA : ℝ := ∑ n ∈ TA, if n ∈ AW then
    ‖aCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SA muA n
    else 0
  let EB : ℝ := ∑ n ∈ TB, if n ∈ BW then
    ‖bCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SB muB n
    else 0
  let fA : SourceOriginalGramPrimeTuple434 SA → ℂ :=
    sourceOriginalPhysicalProductAtomWindowInverseLift434 SA muA AW aCoeff
  let fB : SourceOriginalGramPrimeTuple434 SB → ℂ :=
    sourceOriginalPhysicalProductAtomWindowInverseLift434 SB muB BW bCoeff
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
  have hmuA : ∀ z : ν.1, ∀ p ∈ SA z, 0 < muA z p := by
    intro z p hp
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hPrime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < (p:ℝ) := by
      exact_mod_cast hPrime.pos
    exact div_pos (div_pos zero_lt_one hpp) hVpos
  have hmuB : ∀ z : ν.2, ∀ p ∈ SB z, 0 < muB z p := by
    intro z p hp
    have hVpos : 0 < d.Vbig z.val.1 :=
      cfg.hv.trans_le (d.hVbig z.val.1)
    have hPrime := d.hTbPrime z.val.1 p hp
    have hpp : (0:ℝ) < (p:ℝ) := by
      exact_mod_cast hPrime.pos
    exact div_pos (div_pos zero_lt_one hpp) hVpos
  have hRaw := source_original_true_signed_raw_mellin_physical_minor434
    cfg x L Y Hprime d sep blockA blockB hDisjoint
    m hm ν hPattern ζ fA fB M N P Q hM hN
    a r beta0 theta k hApprox
    hr hcop hbeta hP hQ D Bsave hL hR hNlarge hMlarge hMNlarge
    C hExponent hSaving
  have hEFA := source_original_physical_atom_window_inverse_energy434
    SA muA hmuA AW aCoeff
  have hEFB := source_original_physical_atom_window_inverse_energy434
    SB muB hmuB BW bCoeff
  have hMask := source_original_true_two_global_window_inverse_mask_identity434
    SA muA SB muB AW BW aCoeff bCoeff phase
  have hAtom := source_original_true_two_global_window_inverse_atom_pairing434
    SA muA hmuA SB muB hmuB AW BW aCoeff bCoeff phase
  dsimp only at hRaw
  change
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
       (∑ vA : SourceOriginalGramPrimeTuple434 SA,
         if sourceOriginalGramPrimeProduct434 SA vA ∈ AW then
           (sourceOriginalGramPrimeMass434 SA muA vA:ℂ)*fA vA*
           (∑ vB : SourceOriginalGramPrimeTuple434 SB,
             if sourceOriginalGramPrimeProduct434 SB vB ∈ BW then
               (sourceOriginalGramPrimeMass434 SB muB vB:ℂ)*fB vB*
               Green64SourceC6.integerPhase (-(k:ℝ)*theta)
                 (((sourceOriginalGramPrimeProduct434 SA vA *
                     sourceOriginalGramPrimeProduct434 SB vB):ℕ):ℤ) *
               sourceOriginalPureMellinPhase434 ζ
                 (sourceOriginalGramPrimeProduct434 SA vA *
                  sourceOriginalGramPrimeProduct434 SB vB)
             else 0)
         else 0)‖^2 ≤
      125*((∑ v : SourceOriginalGramPrimeTuple434 SA,
          sourceOriginalGramPrimeMass434 SA muA v*‖fA v‖^2)*
           (∑ v : SourceOriginalGramPrimeTuple434 SB,
          sourceOriginalGramPrimeMass434 SB muB v*‖fB v‖^2))*
        L^(-Bsave) at hRaw
  simp only [mul_assoc] at hRaw hMask hAtom
  rw [hMask,hAtom] at hRaw
  rw [hEFA,hEFB] at hRaw
  simpa only [mul_assoc] using hRaw
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueSelectedCellRawMellinWindow -/

section

open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Actual ORIGINAL SOURCE03 signed RAW Fourier/Mellin C6 on
a TRUE selected output GLOBAL jA/jB pair, for an arbitrary
output dyadic window [M,2M)x[N,2N).
Original output coefficient vectors are precisely masked to
those cells; original harmonic atom laws, independently labelled
prime groups and -k theta and Mellin zeta unchanged.
This theorem directly derives the analytic saving from the
certified two-integer C6, no surrogate local spectral premise.
The output energies here cover ALL original attainable products,
so there is no hidden small-cell normalization assumption. -/
theorem source_original_true_selected_CELL_raw_MELLIN_C6_window434
    {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (cfg : SourceComparisonFixed434)
    (x L Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m : ℕ) (hm : m ≤ cfg.tmax)
    (ν : SourceOriginalProbePattern434 β m)
    (hPattern : ν ∈
      sourceOriginalTwoBlockProbePatterns434 blockA blockB m)
    (hA hB : ℝ) (jA jB : ℤ)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (M N P Q : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a : ℤ) (r : ℕ) (beta0 theta : ℝ) (k : ℤ)
    (hApprox : -(k:ℝ)*theta = (a:ℝ)/(r:ℝ)+beta0)
    (hr : 0 < r) (hcop : Int.gcd a (r:ℤ) = 1)
    (hbeta : |beta0| ≤ 1/((r:ℝ)^2))
    (hP : P ≤ M) (hQ : Q ≤ N)
    (D Bsave : ℝ) (hL : 1 ≤ L)
    (hR : L^D ≤ (r:ℝ))
    (hNlarge : L^D ≤ (N:ℝ))
    (hMlarge : L^D*Real.log (2*(r:ℝ)) ≤ (M:ℝ))
    (hMNlarge : L^D*(r:ℝ)*Real.log (2*(r:ℝ)) ≤
         (M:ℝ)*(N:ℝ))
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D) :
    let SA : ν.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : ν.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : ν.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : ν.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let AW := (Finset.range P).image (fun i => M+i)
    let BW := (Finset.range Q).image (fun j => N+j)
    let aCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 hA n=jA
      then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 hB n=jB
      then bCoeff n else 0
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SB muB n
    let phase : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
       (∑ n ∈ TA, ∑ m ∈ TB,
         (if n ∈ AW then aCell n else 0) *
         (if m ∈ BW then bCell m else 0) *phase (n*m))‖^2 ≤
       125*(EA*EB)*L^(-Bsave) := by
  classical
  let SA : ν.1 → Finset ℕ := fun t => d.Tb t.val.1
  let SB : ν.2 → Finset ℕ := fun t => d.Tb t.val.1
  let muA : ν.1 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let muB : ν.2 → ℕ → ℝ :=
    fun t p => (1/(p:ℝ))/(d.Vbig t.val.1)
  let TA := sourceOriginalPhysicalProductAtomSupport434 SA
  let TB := sourceOriginalPhysicalProductAtomSupport434 SB
  let AW := (Finset.range P).image (fun i => M+i)
  let BW := (Finset.range Q).image (fun j => N+j)
  let aCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 hA n=jA
    then aCoeff n else 0
  let bCell : ℕ → ℂ := fun n =>
    if sourceOriginalLiteralLogCellIndex434 hB n=jB
    then bCoeff n else 0
  let EA : ℝ := ∑ n ∈ TA,
    ‖aCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SA muA n
  let EB : ℝ := ∑ n ∈ TB,
    ‖bCoeff n‖^2 / sourceOriginalPhysicalProductAtom434 SB muB n
  let EAw : ℝ := ∑ n ∈ TA, if n ∈ AW then
    ‖aCell n‖^2 / sourceOriginalPhysicalProductAtom434 SA muA n
    else 0
  let EBw : ℝ := ∑ n ∈ TB, if n ∈ BW then
    ‖bCell n‖^2 / sourceOriginalPhysicalProductAtom434 SB muB n
    else 0
  let phase : ℕ → ℂ := fun n =>
    Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
    sourceOriginalPureMellinPhase434 ζ n
  have hC6 := source_original_true_selected_two_integer_raw_MELLIN_C6_minor434
    cfg x L Y Hprime d sep blockA blockB hDisjoint
    m hm ν hPattern ζ aCell bCell M N P Q hM hN
    a r beta0 theta k hApprox hr hcop hbeta
    hP hQ D Bsave hL hR hNlarge hMlarge hMNlarge
    C hExponent hSaving
  have hC6' :
    ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      (∑ n ∈ TA, ∑ mm ∈ TB,
        (if n ∈ AW then aCell n else 0) *
        (if mm ∈ BW then bCell mm else 0) *
        phase (n*mm))‖^2 ≤
      125*(EAw*EBw)*L^(-Bsave) := by
    simpa only [SA,SB,muA,muB,TA,TB,AW,BW,
      EAw,EBw,phase] using hC6
  have hMuA : ∀ i p, p∈SA i → 0 ≤ muA i p := by
    intro i p hp
    exact div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg p))
      (cfg.hv.trans_le (d.hVbig i.val.1)).le
  have hMuB : ∀ i p, p∈SB i → 0 ≤ muB i p := by
    intro i p hp
    exact div_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg p))
      (cfg.hv.trans_le (d.hVbig i.val.1)).le
  have hAtomA (n : ℕ) : 0 ≤ sourceOriginalPhysicalProductAtom434 SA muA n :=
    source_original_physical_product_atom_nonneg434 SA muA hMuA n
  have hAtomB (n : ℕ) : 0 ≤ sourceOriginalPhysicalProductAtom434 SB muB n :=
    source_original_physical_product_atom_nonneg434 SB muB hMuB n
  have hEAw : EAw ≤ EA := by
    dsimp only [EAw,EA]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hc : sourceOriginalLiteralLogCellIndex434 hA n=jA
    · by_cases hw : n∈AW
      · simp [aCell,hc,hw]
      · simp [aCell,hc,hw]
        exact div_nonneg (sq_nonneg _) (hAtomA n)
    · by_cases hw : n∈AW
      · simp [aCell,hc,hw]
        exact div_nonneg (sq_nonneg _) (hAtomA n)
      · simp [aCell,hc,hw]
        exact div_nonneg (sq_nonneg _) (hAtomA n)
  have hEBw : EBw ≤ EB := by
    dsimp only [EBw,EB]
    apply Finset.sum_le_sum
    intro n hn
    by_cases hc : sourceOriginalLiteralLogCellIndex434 hB n=jB
    · by_cases hw : n∈BW
      · simp [bCell,hc,hw]
      · simp [bCell,hc,hw]
        exact div_nonneg (sq_nonneg _) (hAtomB n)
    · by_cases hw : n∈BW
      · simp [bCell,hc,hw]
        exact div_nonneg (sq_nonneg _) (hAtomB n)
      · simp [bCell,hc,hw]
        exact div_nonneg (sq_nonneg _) (hAtomB n)
  have hEAn : 0 ≤ EA := by
    dsimp only [EA]
    exact Finset.sum_nonneg (fun n hn =>
      div_nonneg (sq_nonneg _) (hAtomA n))
  have hEBwn : 0 ≤ EBw := by
    dsimp only [EBw]
    apply Finset.sum_nonneg
    intro n hn
    by_cases hw : n ∈ BW
    · simp only [if_pos hw]
      exact div_nonneg (sq_nonneg _) (hAtomB n)
    · simp [hw]
  have hProd : EAw*EBw ≤ EA*EB := by
    calc
      _ ≤ EA*EBw := mul_le_mul_of_nonneg_right hEAw hEBwn
      _ ≤ EA*EB := mul_le_mul_of_nonneg_left hEBw hEAn
  dsimp only
  change ‖(-((-1:ℂ)^(ν.1.card+ν.2.card))) *
      (∑ n ∈ TA, ∑ mm ∈ TB,
        (if n ∈ AW then aCell n else 0) *
        (if mm ∈ BW then bCell mm else 0) *
        phase (n*mm))‖^2 ≤
      125*(EA*EB)*L^(-Bsave)
  calc
    _ ≤ 125*(EAw*EBw)*L^(-Bsave) := hC6'
    _ ≤ 125*(EA*EB)*L^(-Bsave) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
      exact mul_le_mul_of_nonneg_left hProd (by norm_num)
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalTrueFiveIndexRawCellMellin -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Original SOURCE03 signed RAW Fourier/Mellin C6 saving on
ANY one of two actual dyadic windows on each OUTPUT side of
a genuine five-index ν/jA/χA/jB/χB, off its OWN moving major
arc. Original selected GLOBAL cell masks, labelled prime
weights, Fourier -k theta and Mellin ζ are unchanged.
Large coprime Dirichlet denominator and scale conditions
derive from the real original moving-circle geometry.
The bound uses full authentic inverse product-atom energies.
Four-output-window union remains separate. -/
theorem eventually_source_original_true_five_index_RAW_selected_CELL_mellin_window434
    (cfg : SourceComparisonFixed434)
    (D Bsave : ℝ) (hD : 0 ≤ D)
    (C : ℕ)
    (hExponent : cfg.C0*
       Real.log (((cfg.tmax.factorial:ℕ):ℝ)*
         (max (1:ℝ) cfg.vmin⁻¹)^cfg.tmax) ≤ (C:ℝ))
    (hSaving : Bsave+2*(C:ℝ) ≤ D)
    (Aarc : ℝ) (hAarc : (1/2:ℝ) < Aarc)
    (hArc : Aarc+(D+1) ≤ cfg.Carc) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι β : Type} [Fintype ι] [DecidableEq ι]
      [Fintype β] [DecidableEq β]
    (x Y Hprime : ℝ)
    (d : SourceComparisonData434 ι β cfg x L Y Hprime)
    (sep : SourceOriginalSource03GroupSeparation434 d)
    (blockA blockB : Finset β)
    (hDisjoint : Disjoint blockA blockB)
    (m Qchar : ℕ) (hm : m ≤ cfg.tmax)
    (hTbLower : ∀ g : β, ∀ p ∈ d.Tb g,
      Real.exp (L^cfg.cexp) ≤ (p:ℝ))
    (hAvar hBvar : SourceOriginalProbePattern434 β m → ℝ)
    (hhA : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hAvar ν ∧ hAvar ν ≤ 1)
    (hhB : ∀ ν ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m, 0 < hBvar ν ∧ hBvar ν ≤ 1)
    (xi : ℝ) (hxi : 0 < xi)
    (z : SourceOriginalTrueFiveIndex434 β m Qchar)
    (hz : z ∈ sourceOriginalProbeExpandedFamily434
      blockA blockB m Qchar d.Tb d.Vbig hAvar hBvar xi)
    (ζ : ℝ) (aCoeff bCoeff : ℕ → ℂ)
    (M N : ℕ)
    (hMchoice :
      M = Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1)) ∨
      M = 2*Nat.ceil (Real.exp ((z.2.1.1:ℝ)*hAvar z.1)))
    (hNchoice :
      N = Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1)) ∨
      N = 2*Nat.ceil (Real.exp ((z.2.2.1:ℝ)*hBvar z.1)))
    (theta : ℝ) (k : ℤ) (hk : k ≠ 0)
    (hOutside : (theta:AddCircle (1:ℝ)) ∉
      sourceCircleRationalArcs434
        (k.natAbs*Nat.ceil (L^(D+1)))
        (L^cfg.Carc/
          sourceOriginalProbeTrueHprime434
            m Qchar hAvar hBvar z)),
    let SA : z.1.1 → Finset ℕ := fun z => d.Tb z.val.1
    let SB : z.1.2 → Finset ℕ := fun z => d.Tb z.val.1
    let muA : z.1.1 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let muB : z.1.2 → ℕ → ℝ :=
      fun z p => (1/(p:ℝ))/(d.Vbig z.val.1)
    let TA := sourceOriginalPhysicalProductAtomSupport434 SA
    let TB := sourceOriginalPhysicalProductAtomSupport434 SB
    let AW : Finset ℕ := (Finset.range M).image (fun i => M+i)
    let BW : Finset ℕ := (Finset.range N).image (fun j => N+j)
    let aCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 (hAvar z.1) n=z.2.1.1
      then aCoeff n else 0
    let bCell : ℕ → ℂ := fun n =>
      if sourceOriginalLiteralLogCellIndex434 (hBvar z.1) n=z.2.2.1
      then bCoeff n else 0
    let phase : ℕ → ℂ := fun n =>
      Green64SourceC6.integerPhase (-(k:ℝ)*theta) (n:ℤ) *
      sourceOriginalPureMellinPhase434 ζ n
    let EA : ℝ := ∑ n ∈ TA,
      ‖aCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SA muA n
    let EB : ℝ := ∑ n ∈ TB,
      ‖bCoeff n‖^2/sourceOriginalPhysicalProductAtom434 SB muB n
    ‖(-((-1:ℂ)^(z.1.1.card+z.1.2.card))) *
      (∑ n ∈ TA, ∑ mm ∈ TB,
        (if n ∈ AW then aCell n else 0) *
        (if mm ∈ BW then bCell mm else 0) *
        phase (n*mm))‖^2 ≤
      125*(EA*EB)*L^(-Bsave) := by
  let Chigh : ℝ := 2*(cfg.tmax:ℝ)*cfg.C0
  have hChigh : 0 ≤ Chigh := by
    dsimp [Chigh]
    exact mul_nonneg (by positivity) cfg.hC0
  have hc : 0 < cfg.cexp := by
    linarith [cfg.haexp,cfg.hab,cfg.hbc]
  have hCircle :=
    eventually_source_original_circle_physical_C6_scales434
      cfg.cexp (1/2:ℝ) Aarc D cfg.Carc 1 1 Chigh
      hc (by norm_num) hAarc hD hArc hChigh
  filter_upwards [hCircle,eventually_ge_atTop (4:ℝ)]
    with L hCircleL hL
  intro ι β instI instDI instB instDB
    x Y Hprime d sep
    blockA blockB hDisjoint
    m Qchar hm hTbLower hAvar hBvar hhA hhB xi hxi z hz
    ζ aCoeff bCoeff M N hMchoice hNchoice theta k hk hOutside
  let UA : ℝ := Real.exp ((z.2.1.1:ℝ)*hAvar z.1)
  let UB : ℝ := Real.exp ((z.2.2.1:ℝ)*hBvar z.1)
  let HC : ℝ := sourceOriginalProbeTrueHprime434
    m Qchar hAvar hBvar z
  have hν : z.1 ∈ sourceOriginalTwoBlockProbePatterns434
      blockA blockB m :=
    (Finset.mem_sigma.mp hz).1
  obtain ⟨hU1,hU2,hH,hHupper⟩ :=
    source_original_source03_true_five_index_circle_scales434
      cfg x L Y Hprime d (by linarith : 1 ≤ L)
      blockA blockB m Qchar hm hTbLower
      hAvar hBvar hhA hhB xi z hz
  have hM0 : 0 < Nat.ceil UA := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hN0 : 0 < Nat.ceil UB := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hMp : 0 < M := by
    rcases hMchoice with hm | hm
    · rw [hm];exact hM0
    · rw [hm]
      change 0 < 2 * Nat.ceil UA
      omega
  have hNp : 0 < N := by
    rcases hNchoice with hn | hn
    · rw [hn];exact hN0
    · rw [hn]
      change 0 < 2 * Nat.ceil UB
      omega
  have hMA : UA ≤ (M:ℝ) := by
    have hh : UA ≤ (Nat.ceil UA:ℝ) := Nat.le_ceil UA
    rcases hMchoice with hm | hm
    · rw [hm];exact hh
    · rw [hm]
      have hNN : (0:ℝ) ≤ (Nat.ceil UA:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
  have hNB : UB ≤ (N:ℝ) := by
    have hh : UB ≤ (Nat.ceil UB:ℝ) := Nat.le_ceil UB
    rcases hNchoice with hn | hn
    · rw [hn];exact hh
    · rw [hn]
      have hNN : (0:ℝ) ≤ (Nat.ceil UB:ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
  have hHp : 0 < HC := by
    change 0 < UA*UB
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  obtain ⟨a,r,hr,hcop,hNear,hR,hNlarge,hMlarge,hMNlarge⟩ :=
    hCircleL.2 UA UB HC hU1 hU2 hH hHp
      hHupper M N hMA hNB theta k hk hOutside
  let beta0 : ℝ := -(k:ℝ)*theta-(a:ℝ)/(r:ℝ)
  have hApprox : -(k:ℝ)*theta =
      (a:ℝ)/(r:ℝ)+beta0 := by
    dsimp [beta0]
    ring
  have hbeta : |beta0| ≤ 1/((r:ℝ)^2) := by
    simpa only [beta0] using hNear
  have hh := source_original_true_selected_CELL_raw_MELLIN_C6_window434
    cfg x L Y Hprime d sep blockA blockB hDisjoint
    m hm z.1 hν (hAvar z.1) (hBvar z.1)
    z.2.1.1 z.2.2.1 ζ aCoeff bCoeff
    M N M N hMp hNp a r beta0 theta k hApprox
    hr hcop hbeta (le_refl _) (le_refl _)
    D Bsave (by linarith [hL] : 1 ≤ L)
    hR hNlarge hMlarge hMNlarge C hExponent hSaving
  simpa only [UA,UB,HC] using hh
end Green64Analytic.CorrelationSquare

end

