module

public import Green64.Library.Weights.Part080
public import Green64.Library.Weights.Part057

@[expose] public section

/-!
# Weights / Part081

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## NonNormalizedFreshLawExact -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (J ell m : ℕ)

/-- TRUE non-normalized original BIG frozen fresh target law: a shared slot
copies one source prime with total mass exactly one, while every genuinely
free target slot contributes the actual total mass of μ_g. This is valid for
the physically tilted μ~; no artificial normalization Σ_p μ~=1 occurs. -/
theorem source_original_B405_fresh_law_real_exact_mass434
    (mu : (g : G) → BP g → ℝ)
    (pat : SourcePattern G J m)
    (a : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ b : SourceOriginalB26Active434 BP J ell,
      source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau) =
    ∏ g : G,∏ i : Fin (J+ell),
      if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
      else ∑ p : BP g, mu g p := by
  let e := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  have hr :
      (∑ b,source_original_B390_fresh_law_real434 BP J ell m
        mu pat a b sigma tau) =
      ∑ b : SourceOriginalB26Active434 BP J ell,∏ g,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then
          (if b g i=a g (sigma g i) then (1:ℝ) else 0)
        else mu g (b g i) := by
    apply Fintype.sum_equiv e
    intro b
    rfl
  rw [hr,← Fintype.prod_sum (fun (g : G) (b : Fin (J+ell) → BP g) =>
    ∏ i : Fin (J+ell),if i ∈ sourceBigShared J ell m pat g then
      (if b i=a g (sigma g i) then (1:ℝ) else 0) else mu g (b i))]
  apply Finset.prod_congr rfl
  intro g hg
  rw [← Fintype.prod_sum (fun (i : Fin (J+ell)) (p : BP g) =>
    if i ∈ sourceBigShared J ell m pat g then
      (if p=a g (sigma g i) then (1:ℝ) else 0) else mu g p)]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hs : i ∈ sourceBigShared J ell m pat g
  · simp [hs]
  · simp [hs]

/-- Norm of the genuine complex original B26 fresh law. In particular the
free-slot mass is NOT dropped for the actual tilted physical source. -/
theorem source_original_B405_original_fresh_law_norm_exact_mass434
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (pat : SourcePattern G J m)
    (a : SourceOriginalB26Active434 BP J ell)
    (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
    (∑ b : SourceOriginalB26Active434 BP J ell,
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖) =
    ∏ g : G,∏ i : Fin (J+ell),
      if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
      else ∑ p : BP g, mu g p := by
  have hnorm (b : SourceOriginalB26Active434 BP J ell) :
      ‖sourceOriginalB26FrozenFreshLaw434 BP J ell m mu pat a b sigma tau‖ =
        source_original_B390_fresh_law_real434 BP J ell m mu pat a b sigma tau := by
    rw [← source_original_B390_fresh_law_real_cast434]
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (source_original_B390_fresh_law_real_nonneg434
        BP J ell m mu hmu pat a b sigma tau)]
  simp only [hnorm]
  exact source_original_B405_fresh_law_real_exact_mass434
    BP J ell m mu pat a sigma tau
end Green64Analytic.CorrelationSquare

end

end

/-! ## NonNormalizedPhysicalTargetCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal marked B26 collision for arbitrary nonnegative actual BIG μ,
including the physically tilted μ~ which is NOT normalized. B405 supplies
the exact free-slot target mass; B399 preserves the AUX-dependent SMALL gate. -/
theorem source_original_B406_marked_collision_all_target_exact_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (ss tt : GroupPermFamily (G := SG) (J+ell)) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
    bigEndpointPairMass (BG := G) (J+ell) *
      (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (groupPermutationPairMass (G := SG) (J+ell) *
        (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B)) *
    (∏ g : G, ∏ i : Fin (J+ell),
      if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
      else ∑ p : BP g, mu g p) := by
  dsimp only
  let fac : ℝ := bigEndpointPairMass (BG := G) (J+ell) *
    (((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
       (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (groupPermutationPairMass (G := SG) (J+ell) *
        (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B))
  let mass : ℝ := ∏ g : G, ∏ i : Fin (J+ell),
    if i ∈ sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g
      then (1:ℝ) else ∑ p : {p : ℕ // p ∈ P g}, mu g p
  let T : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → ℂ :=
    fun b => ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell m cap sizes hsizes prime
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
          (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
            Q hA hC xi aux s t) q Vs zeta theta o k F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
            (fun g => {p : ℕ // p ∈ P g}) J ell m
            (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt
  let law : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell → ℂ :=
    fun b => sourceOriginalB26FrozenFreshLaw434
      (fun g => {p : ℕ // p ∈ P g}) J ell m mu
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) a b sigma tau
  have hbound (b : SourceOriginalB26Active434
      (fun g => {p : ℕ // p ∈ P g}) J ell) :
      ‖T b‖ ≤ ‖law b‖ * fac := by
    convert (source_original_B399_marked_collision_all_SMALL_bound434
      P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
      Pmin vmin hP hv hV hVmin hPmin mu SP sm cap sizes hsizes prime
      q Vs hq hq1 hVs zeta theta o k ho hk
      F B hB hF xs a b t S sigma tau ss tt) using 1 <;>
      dsimp [T,law,fac] <;> ring
  have hlaw : (∑ b : SourceOriginalB26Active434
      (fun g => {p : ℕ // p ∈ P g}) J ell, ‖law b‖) = mass := by
    dsimp [mass]
    exact source_original_B405_original_fresh_law_norm_exact_mass434
      (fun g => {p : ℕ // p ∈ P g}) J ell m mu hmu
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) a sigma tau
  change ‖∑ b : SourceOriginalB26Active434
      (fun g => {p : ℕ // p ∈ P g}) J ell, T b‖ ≤ fac * mass
  calc
    _ ≤ ∑ b : SourceOriginalB26Active434
        (fun g => {p : ℕ // p ∈ P g}) J ell, ‖T b‖ := norm_sum_le _ _
    _ ≤ ∑ b : SourceOriginalB26Active434
        (fun g => {p : ℕ // p ∈ P g}) J ell, ‖law b‖ * fac := by
      apply Finset.sum_le_sum
      intro b hb
      exact hbound b
    _ = (∑ b : SourceOriginalB26Active434
          (fun g => {p : ℕ // p ∈ P g}) J ell, ‖law b‖) * fac := by
      rw [Finset.sum_mul]
    _ = fac * mass := by rw [hlaw]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## NonNormalizedFullHaarCollision -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The literal marked collision under a NON-normalized positive BIG source law.
All BIG/SMALL target and four Haar-permutation sums are paid exactly, while
retaining the original source free-slot mass, not replacing it by one. -/
theorem source_original_B407_full_Haar_all_target_actual_mass434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ sigma : BigGroupPerm (BG := G) (J+ell),
      ∑ tau : BigGroupPerm (BG := G) (J+ell),
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ tt : GroupPermFamily (G := SG) (J+ell),
      ∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux BP J m pat,
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434 BP J ell m patterns)
          ss tt‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,mu g p) := by
  dsimp only
  let delta : ℝ :=
    (((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
      (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)
  let row : ℝ := ∏ g : SG, memorySmallRowConstant q (Vs g) ell
  let mass : ℝ := ∏ g : G, ∏ i : Fin (J+ell),
    if i ∈ sourceBigShared J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g
      then (1:ℝ) else ∑ p : {p : ℕ // p ∈ P g}, mu g p
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    apply Finset.prod_nonneg
    intro g hg
    apply Finset.prod_nonneg
    intro i hi
    by_cases hs : i ∈ sourceBigShared J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ ν) g
    · simp [hs]
    · simp only [if_neg hs]
      exact Finset.sum_nonneg (fun p hp => hmu g p)
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    have hpv : 0 ≤ Pmin*vmin := le_of_lt (mul_pos hP hv)
    positivity
  have hsqrt : Real.sqrt q < 1 := by
    have hsq := Real.sq_sqrt (le_of_lt hq)
    have hn := Real.sqrt_nonneg q
    nlinarith only [hsq,hn,hq1]
  have hden : 0 < 1 - Real.sqrt q := sub_pos.mpr hsqrt
  have hrow : 0 ≤ row := by
    dsimp [row]
    apply Finset.prod_nonneg
    intro g hg
    unfold memorySmallRowConstant
    have hvg := hVs g
    positivity
  have hM : 0 ≤ delta * row * B * mass :=
    mul_nonneg (mul_nonneg (mul_nonneg hdelta hrow) hB) hmass
  have h := source_original_B392_four_Haar_uniform_bound434
    (G := G) (SG := SG) (J+ell)
    (fun sigma tau ss tt =>
      ∑ b : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ aux : SourceBigAux (fun g => {p : ℕ // p ∈ P g}) J m
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell m cap sizes hsizes prime
          (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν) mu V
          (fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
            Q hA hC xi aux s t)
          q Vs zeta theta o k F xs ys a b t S
          (⟨(),aux,sigma,tau⟩ : SourceOriginalB26FrozenFrame434
            (fun g => {p : ℕ // p ∈ P g}) J ell m
            (fun _ => sourceOriginalProbeMemoryPattern434 J m hmJ ν)) ss tt)
    (delta*row*B*mass) hM (by
      intro sigma tau ss tt
      convert (source_original_B406_marked_collision_all_target_exact_mass434
        P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
        Pmin vmin hP hv hV hVmin hPmin mu hmu
        SP sm cap sizes hsizes prime q Vs hq hq1 hVs
        zeta theta o k ho hk F B hB hF xs a t S sigma tau ss tt) using 1 <;>
        dsimp [delta,row,mass] <;> ring)
  simpa only [delta,row,mass] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## ChronologicalActualMassCollisionBound -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Quantitative B26 correction for the original chronological Frame consumer
with the ACTUAL non-normalized positive BIG source law. Exact B405 mass paid. -/
theorem source_original_B408_chronological_actual_mass_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
      ∑ b : SourceOriginalB26Active434 BP J ell,
      ∑ ys : GroupState SP sm (J+ell),
      ∑ ss : GroupPermFamily (G := SG) (J+ell),
      ∑ tt : GroupPermFamily (G := SG) (J+ell),
        sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
          cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
          F xs ys a b t S h ss tt‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      (∏ g : G, ∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g, mu g p) := by
  dsimp only
  rw [source_original_B402_full_frame_to_Haar_reindex434]
  exact source_original_B407_full_Haar_all_target_actual_mass434
    P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
    Pmin vmin hP hv hV hVmin hPmin mu hmu
    SP sm cap sizes hsizes prime q Vs hq hq1 hVs
    zeta theta o k ho hk F B hB hF xs a t S
end Green64Analytic.CorrelationSquare

end

end

/-! ## OrbitActualMassCollisionConsumer -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The genuine Fock/OLD/seen orbit consumer differs from the only-ban-removed
chronological comparison by bounded B26 collision for arbitrary actual
positive, NON-normalized BIG source law, paying EXACT free-slot masses. -/
theorem source_original_B409_orbit_actual_tilted_mass_collision_bound434
    {G : Type} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) [∀ g (p : {p : ℕ // p ∈ P g}),NeZero p.val]
    (V : G → ℝ) (J ell m : ℕ) (hmJ : m ≤ J)
    (ν : SourceOriginalProbePattern434 G m) (hDisj : Disjoint ν.1 ν.2)
    (Q : ℕ) (hA hC xi : ℝ) (hhA : 0<hA) (hhC : 0<hC) (hxi : 0<xi)
    (Pmin vmin : ℝ) (hP : 0<Pmin) (hv : 0<vmin)
    (hV : ∀ g,V g=∑ p ∈ P g,1/(p:ℝ))
    (hVmin : ∀ g,vmin≤V g)
    (hPmin : ∀ g p,p∈P g → Pmin≤(p:ℝ))
    (mu : (g : G) → {p : ℕ // p ∈ P g} → ℝ)
    (hmu : ∀ g p, 0 ≤ mu g p)
    (hmu_pos : ∀ g p, 0 < mu g p)
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
    (cap sizes : G → ℕ) (hsizes : ∀ g,sizes g ≤ cap g)
    (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ P g})
    (q : ℝ) (Vs : SG → ℝ) (hq : 0<q) (hq1 : q<1)
    (hVs : ∀ g,0<Vs g) (zeta theta : ℝ) (o k : ℤ)
    (ho : o=1 ∨ o= -1) (hk : k≠0)
    (F : FullPhysicalOutput SP sm (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) (J+ell) → Finset ℕ → ℂ)
    (B : ℝ) (hB : 0≤B) (hF : ∀ Y seen, ‖F Y seen‖≤B)
    (xs : GroupState SP sm (J+ell))
    (a : SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ P g}) J ell)
    (t : SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ P g})
      (fun _ p => p.val) sizes prime) (S : Finset ℕ)
    (hr : sourceOriginalPhysicalReachable434 SP sm
      (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val) (J+ell)
      (physicalFockProjection SP sm (fun g => {p : ℕ // p ∈ P g})
        (fun _ p => p.val) (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434
          (fun g => {p : ℕ // p ∈ P g}) (fun _ p => p.val)
          J ell cap sizes hsizes prime a t)) S) :
    let BP := fun g => {p : ℕ // p ∈ P g}
    let bm : (g : G) → BP g → ℕ := fun _ p => p.val
    let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
    let patterns : Unit → SourcePattern G J m := fun _ => pat
    let K : SourcePatternK BP J ell m patterns :=
      fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
        Q hA hC xi aux s t
    ‖fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
      (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
        J ell m cap patterns
        (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
        q 1 Vs V mu K zeta theta o k st S F)
      (physicalFockProjection SP sm BP bm (J+ell) cap
        (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
          sizes hsizes prime a t)) -
      (∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
        ∑ b : SourceOriginalB26Active434 BP J ell,
        ∑ ys : GroupState SP sm (J+ell),
        ∑ ss : GroupPermFamily (G := SG) (J+ell),
        ∑ tt : GroupPermFamily (G := SG) (J+ell),
          sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
            cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
            F xs ys a b t S h ss tt)‖ ≤
      ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
        (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
      (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,mu g p) := by
  dsimp only
  let BP := fun g => {p : ℕ // p ∈ P g}
  let bm : (g : G) → BP g → ℕ := fun _ p => p.val
  let pat := sourceOriginalProbeMemoryPattern434 J m hmJ ν
  let patterns : Unit → SourcePattern G J m := fun _ => pat
  let K : SourcePatternK BP J ell m patterns :=
    fun _ aux s t => sourceOriginalProbeMemoryCanonicalK434 P V J ell m hmJ ν
      Q hA hC xi aux s t
  let O : ℂ := fullPhysicalOrbitAverage SP sm BP bm (J+ell) cap Vs mu
    (fun st => sourceOriginalMemoryMarkedFilteredE434 SP sm BP bm
      J ell m cap patterns
      (sourceOriginalCleanChoice434 SP sm BP bm J ell m cap patterns)
      q 1 Vs V mu K zeta theta o k st S F)
    (physicalFockProjection SP sm BP bm (J+ell) cap
      (xs,sourceOriginalB26FrozenBigState434 BP bm J ell cap
        sizes hsizes prime a t))
  let U : ℂ := ∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
    ∑ b : SourceOriginalB26Active434 BP J ell,
    ∑ ys : GroupState SP sm (J+ell),
    ∑ ss : GroupPermFamily (G := SG) (J+ell),
    ∑ tt : GroupPermFamily (G := SG) (J+ell),
      sourceOriginalMarkedUnbannedCleanIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        F xs ys a b t S h ss tt
  let E : ℂ := ∑ h : SourceOriginalB26FrozenFrame434 BP J ell m patterns,
    ∑ b : SourceOriginalB26Active434 BP J ell,
    ∑ ys : GroupState SP sm (J+ell),
    ∑ ss : GroupPermFamily (G := SG) (J+ell),
    ∑ tt : GroupPermFamily (G := SG) (J+ell),
      sourceOriginalMarkedAuxCollisionIndexedTerm434 SP sm BP bm J ell m
        cap sizes hsizes prime patterns mu V K q Vs zeta theta o k
        F xs ys a b t S h ss tt
  have hOrbit : O = U - E := by
    simpa only [O,U,E] using
      (source_original_B389_orbit_MARKED_CLEAN_eq_unbanned_MINUS_collision434
        SP sm BP bm J ell m cap sizes hsizes prime patterns
        mu V K q Vs zeta theta o k hVs hmu_pos F xs a t S hr)
  have hCollision :
      ‖E‖ ≤
        ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
          (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
          (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,mu g p) := by
    simpa only [E] using
      (source_original_B408_chronological_actual_mass_collision_bound434
        P V J ell m hmJ ν hDisj Q hA hC xi hhA hhC hxi
        Pmin vmin hP hv hV hVmin hPmin mu hmu
        SP sm cap sizes hsizes prime q Vs hq hq1 hVs
        zeta theta o k ho hk F B hB hF xs a t S)
  have hFinal :
      ‖O - U‖ ≤
        ((((ν.1.card + ν.2.card : ℕ):ℝ) * (2*(J+ell : ℕ):ℕ) /
          (Pmin*vmin)) * ((Q:ℝ)^4*(xi⁻¹)^2)) *
          (∏ g : SG, memorySmallRowConstant q (Vs g) ell) * B *
      (∏ g : G,∏ i : Fin (J+ell),
        if i ∈ sourceBigShared J ell m pat g then (1:ℝ)
        else ∑ p : BP g,mu g p) := by
    rw [hOrbit, show (U-E)-U = -E by abel, norm_neg]
    exact hCollision
  simpa only [O,U] using hFinal
end Green64Analytic.CorrelationSquare

end

end

/-! ## PhysicalTiltedSourceMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- The genuine original physical μ~ is positive, and at most twice its
untilted harmonic reference, provided the ACTUAL source visit count fits
inside the BIG prime size. No normalization of μ~ is postulated. -/
theorem source_original_B410_physical_mu_tilde_positive_bound434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hsize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ))
    (g : G) (p : BP g) :
    0 < physicalSourceMuTilde BP bm q N V g p ∧
    physicalSourceMuTilde BP bm q N V g p ≤ 2/(V g * (bm g p:ℝ)) := by
  have hp : 0 < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hbase := (source_original_B26_physical_baseline_half434
    BP bm q hq hq1 N g p (hsize g p)).1
  let bb := physicalSourceBaseline BP bm q N g p
  have hb : 0 < bb := by dsimp [bb]; linarith only [hbase]
  have hprod : 0 < V g * (bm g p:ℝ) := mul_pos (hV g) hp
  have hdiv : (1:ℝ)/bb ≤ 2 := (div_le_iff₀ hb).mpr (by
    change (1:ℝ)/2 ≤ bb at hbase
    linarith only [hbase])
  have heq : physicalSourceMuTilde BP bm q N V g p =
      (1/(V g * (bm g p:ℝ))) * (1/bb) := by
    dsimp [physicalSourceMuTilde,bb]
    simp only [one_div, mul_inv_rev]
    ring
  constructor
  · rw [heq]
    positivity
  · rw [heq]
    have ht := mul_le_mul_of_nonneg_left hdiv (div_nonneg zero_le_one hprod.le)
    convert ht using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## OriginalTiltedGroupRowMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- The harmonic reference IS normalized, but the genuine physically tilted
µ~ is not: we prove only the legitimate bound 2. It is enough to keep the
true mass multiplicatively, without replacing it by 1. -/
theorem source_original_B411_physical_tilt_group_mass_le_two434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : G → ℝ) (hV : ∀ g, V g = ∑ p : BP g, 1/(bm g p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (hsize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ))
    (g : G) :
    (∑ p : BP g, physicalSourceMuTilde BP bm q N V g p) ≤ 2 := by
  have hnorm : (∑ p : BP g, 1/(V g*(bm g p:ℝ))) = 1 := by
    calc
      _ = (∑ p : BP g, 1/(bm g p:ℝ))/V g := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p hp
        simp only [one_div, mul_inv_rev]
        ring
      _ = 1 := by rw [← hV g,div_self (ne_of_gt (hVpos g))]
  calc
    (∑ p : BP g, physicalSourceMuTilde BP bm q N V g p) ≤
      ∑ p : BP g, 2/(V g*(bm g p:ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (source_original_B410_physical_mu_tilde_positive_bound434
          BP bm q hq hq1 N V hVpos hsize g p).2
    _ = 2*(∑ p : BP g, 1/(V g*(bm g p:ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = 2 := by rw [hnorm]; ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SharpPhysicalTiltBaseline -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 6000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- Genuine original N+1 visit baseline gives a near-one tilted correction,
not merely the crude bound two. All boundary eta terms are included. -/
theorem source_original_B412_physical_baseline_sharp_inv434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (N : ℕ) (g : G) (p : BP g)
    (hsize : 2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ)) :
    (physicalSourceBaseline BP bm q N g p)⁻¹ ≤
      1+2*((N+1:ℕ):ℝ)/(bm g p:ℝ) := by
  let S : ℝ := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
  let pp : ℝ := (bm g p:ℝ)
  let t : ℝ := S/pp
  have hp : 0 < pp := Nat.cast_pos.mpr (NeZero.pos _)
  have hS := source_original_B26_visit_sum_unit434 q hq hq1 N
  have hS0 : 0 ≤ S := hS.1
  have hSA : S ≤ ((N+1:ℕ):ℝ) := hS.2
  have ht0 : 0 ≤ t := div_nonneg hS0 hp.le
  have hbt : physicalSourceBaseline BP bm q N g p = 1-t := rfl
  have hhalf := (source_original_B26_physical_baseline_half434
    BP bm q hq hq1 N g p hsize).1
  rw [hbt] at hhalf
  have hthalf : t ≤ 1/2 := by linarith only [hhalf]
  have htA : t ≤ ((N+1:ℕ):ℝ)/pp := by
    dsimp [t]
    exact (div_le_div_iff_of_pos_right hp).mpr hSA
  have hden : 0 < 1-t := by linarith only [hthalf]
  have hcore : (1:ℝ)/(1-t) ≤ 1+2*t :=
    (div_le_iff₀ hden).mpr (by
      have hmul : 0 ≤ t*(1-2*t) :=
        mul_nonneg ht0 (by linarith only [hthalf])
      nlinarith only [hmul])
  have hcore' : (1-t)⁻¹ ≤ 1+2*t := by
    simpa only [one_div] using hcore
  rw [hbt]
  change (1-t)⁻¹ ≤ 1+2*((N+1:ℕ):ℝ)/pp
  calc
    _ ≤ 1+2*t := hcore'
    _ ≤ _ := by
      have hmul := mul_le_mul_of_nonneg_left htA
        (show (0:ℝ) ≤ 2 by norm_num)
      have hmul' : 2*t ≤ 2*((N+1:ℕ):ℝ)/pp := by
        convert hmul using 1 <;> ring
      simpa only [add_comm] using (add_le_add_left hmul' 1)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SharpTiltedPrimeMass -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- The actual tilted BIG source law is pointwise within
1+2(N+1)/Pmin of the UNTILTED harmonic source. No cap on the number of
primes, groups or BIG/SMALL histories is used here. -/
theorem source_original_B413_physical_tilted_mu_sharp_pointwise434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : G → ℝ) (hV : ∀ g,0 < V g)
    (Pmin : ℝ) (hPmin : 0 < Pmin)
    (hpmin : ∀ g p,Pmin ≤ (bm g p:ℝ))
    (hsize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ))
    (g : G) (p : BP g) :
    physicalSourceMuTilde BP bm q N V g p ≤
      (1+2*((N+1:ℕ):ℝ)/Pmin) * (1/(V g * (bm g p:ℝ))) := by
  have hp : 0 < (bm g p:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  have hpV : 0 < V g*(bm g p:ℝ) := mul_pos (hV g) hp
  have hrecip : ((N+1:ℕ):ℝ)/(bm g p:ℝ) ≤
      ((N+1:ℕ):ℝ)/Pmin := by
    apply (div_le_div_iff₀ hp hPmin).mpr
    exact mul_le_mul_of_nonneg_left (hpmin g p) (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hrecip
    (show (0:ℝ) ≤ 2 by norm_num)
  have hmul' : 2*((N+1:ℕ):ℝ)/(bm g p:ℝ) ≤
      2*((N+1:ℕ):ℝ)/Pmin := by convert hmul using 1 <;> ring
  have hInv : (physicalSourceBaseline BP bm q N g p)⁻¹ ≤
      1+2*((N+1:ℕ):ℝ)/Pmin := by
    calc
      _ ≤ 1+2*((N+1:ℕ):ℝ)/(bm g p:ℝ) :=
        source_original_B412_physical_baseline_sharp_inv434
          BP bm q hq hq1 N g p (hsize g p)
      _ ≤ _ := by simpa only [add_comm] using (add_le_add_left hmul' 1)
  have heq : physicalSourceMuTilde BP bm q N V g p =
      (1/(V g*(bm g p:ℝ))) *
      (physicalSourceBaseline BP bm q N g p)⁻¹ := by
    dsimp [physicalSourceMuTilde]
    simp only [one_div,mul_inv_rev]
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hInv (div_nonneg zero_le_one hpV.le)
  convert h using 1 <;> ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SharpTiltedGroupTotal -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 8000000

variable {G : Type} [Fintype G] [DecidableEq G]
variable (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

/-- The genuine physical tilted BIG group mass is near ONE, not 1 and not
necessarily as large as 2. Original boundary visits N+1 and the true prime
minimum Pmin give a multiplicative factor 1+2(N+1)/Pmin uniformly in g. -/
theorem source_original_B414_physical_tilted_group_mass_sharp434
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (V : G → ℝ) (hV : ∀ g, V g = ∑ p : BP g, 1/(bm g p:ℝ))
    (hVpos : ∀ g,0 < V g)
    (Pmin : ℝ) (hPmin : 0 < Pmin)
    (hpmin : ∀ g p, Pmin ≤ (bm g p:ℝ))
    (hsize : ∀ g p,2*((N+1:ℕ):ℝ) ≤ (bm g p:ℝ))
    (g : G) :
    (∑ p : BP g, physicalSourceMuTilde BP bm q N V g p) ≤
      1+2*((N+1:ℕ):ℝ)/Pmin := by
  let c : ℝ := 1+2*((N+1:ℕ):ℝ)/Pmin
  have hnorm : (∑ p : BP g, 1/(V g*(bm g p:ℝ))) = 1 := by
    calc
      _ = (∑ p : BP g, 1/(bm g p:ℝ))/V g := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p hp
        simp only [one_div,mul_inv_rev]
        ring
      _ = 1 := by rw [←hV g,div_self (ne_of_gt (hVpos g))]
  calc
    (∑ p : BP g, physicalSourceMuTilde BP bm q N V g p) ≤
      ∑ p : BP g, c*(1/(V g*(bm g p:ℝ))) := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [c] using
          (source_original_B413_physical_tilted_mu_sharp_pointwise434
            BP bm q hq hq1 N V hVpos Pmin hPmin hpmin hsize g p)
    _ = c*(∑ p : BP g, 1/(V g*(bm g p:ℝ))) := by rw [Finset.mul_sum]
    _ = c := by rw [hnorm]; ring
    _ = _ := rfl
end Green64Analytic.CorrelationSquare

end

end

