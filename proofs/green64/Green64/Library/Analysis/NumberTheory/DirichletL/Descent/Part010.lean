module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part006
public import Green64.Library.OAI.NumberTheory.DirichletL.Descent.FirstProfileUniform
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part007
public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part010

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstBalancedSource -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open JointLogSeparation MeasureTheory
noncomputable section

theorem first_fresh_physical_profile
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (s q : Fin 9 → ℝ) (hspos : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (normalization : ℂ)
    (he : ∀ y : Fin 9 → ℝ, normalization * firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → ω₁ (q 7/s 7) = 1)
    (hω₂ : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → ω₂ (q 8/s 8) = 1)
    (hcut : ω₁ (q 7/s 7) ≠ 0 → ω₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) :
    normalization * firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
    (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
  by_cases hw₁ : ω₁ (q 7/s 7) = 0
  · have hh : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0 := by
      by_contra hn
      have := hω₁ hn
      simp only [hw₁,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 8/s 8) = 0
  · have hh : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0 := by
      by_contra hn
      have := hω₂ hn
      simp only [hw₂,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₂,mul_zero,zero_mul,zero_div]
  have hcut' := hcut hw₁ hw₂
  have hnom := firstNormProfile_nominal W₁ W₂ Φ (fun _ _ => 1) s q hspos hq K
  have hfull : normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    have hp := firstPoissonProfile_log W₁ W₂ Φ V
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)
      (fun i => div_pos (hq i) (hspos i))
    have hc : firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) =
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) := by
      unfold firstRelativeLog
      rw [hp]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]
    rw [← hc]
    exact he (firstRelativeLog q s)
  have hm : firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
      (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q := by
    by_cases h1 : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0
    · simp only [firstNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0
    · simp only [firstNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  calc
    _ = (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
        (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)) := by
      conv_lhs => rw [hm,hnom]
      ring
    _ = _ := by rw [hfull]

theorem first_balanced_density_integrable (g : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseMomentFirstProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

open ActualEisensteinCubic FirstPassCubeLabels
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem firstCommonNorms_pos (A₁ A₂ C R : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hC : 0 < C) (hR : 0 < R) (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0)
    (j : FirstCommonIndex ι) : ∀ i,0 < firstCommonNorms p A₁ A₂ C R d h j i := by
  intro i
  fin_cases i <;> simp only [firstCommonNorms]
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hd))
  · exact hR
  · exact primeProductNorm_pos p hp _
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh))
  · exact primeProductNorm_pos p hp _
  · exact primeProductNorm_pos p hp _

include hp in

theorem actual_first_balanced_block (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (A₁ A₂ C R K L : ℝ)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hC : 0 < C) (hR : 0 < R)
    (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0) (s : Fin 9 → ℝ) (hs : ∀ i,0 < s i)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F selector C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  apply first_block_normalized_density p hg F selector C₁ C₂ _ _ ω₁ ω₂ Φ A₁ A₂ C R K d h s density hDensity
  intro j hj hn
  exact first_fresh_physical_profile W₁ W₂ ω₁ ω₂ Φ V s
    (firstCommonNorms p A₁ A₂ C R d h j) hs
    (firstCommonNorms_pos p hp A₁ A₂ C R hA₁ hA₂ hC hR d h hd hh j) K density
    (Real.exp (-(9/2:ℝ)*L):ℂ) hsep
    (by simpa [firstCommonNorms] using hω₁ j hj hn)
    (by simpa [firstCommonNorms] using hω₂ j hj hn)
    (by simpa [firstCommonNorms] using hcut j hj hn)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstFamilySource -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem integrable_first_block_density (F : Finset ι) (selector C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    Integrable (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z) := by
  let coef (j : FirstCommonIndex ι) :=
    (selector j.2.1*firstCommonWeight p hg C₁ C₂ h j)*
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8))
  have he : (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z) =
      fun z => ∑ j∈firstCommonIndices F,coef j*(density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) := by
    funext z
    rw [←first_block_modes_eq_columns]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [coef]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j hj => (integrable_density_mode density hDensity
    firstLeftSlope firstRightSlope firstKernelSlope
    (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s)).const_mul (coef j))

theorem first_family_density_sum (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    (∑ x∈source,w x*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x) ω₁ ω₂
        (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z) =
    ∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [←integral_const_mul]
  rw [←integral_finsetSum source (fun x hx =>
    (integrable_first_block_density p hg F (selector x) (C₁ x) (C₂ x) ω₁ ω₂
      (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s density hDensity).const_mul (w x))]
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstFamilySeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def firstFamilyPhysicalRows (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ → ℝ) (K : ℝ)
    (d h : κ → Eis) (s : Fin 9 → ℝ) : ℂ :=
  ∑ x∈source,w x*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
    (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
    Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)

theorem actual_first_balanced_family (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstFamilyPhysicalRows p hg source F selector C₁ C₂ w
      W₁ W₂ Φ A₁ A₂ C R K d h s =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
  have hb (x : κ) (hx : x∈source) := actual_first_balanced_block p hp hg F (selector x) (C₁ x) (C₂ x)
    W₁ W₂ ω₁ ω₂ Φ V (A₁ x) (A₂ x) (C x) (R x) K L
    (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2.1 (hpos x hx).2.2.2.1
    (d x) (h x) (hpos x hx).2.2.2.2.1 (hpos x hx).2.2.2.2.2 s hs density hDensity hsep
    (hω₁ x hx) (hω₂ x hx) (hcut x hx)
  rw [←first_family_density_sum p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s density hDensity]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    _ = w x*((Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
      (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
      Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)) := by ring
    _ = _ := by rw [hb x hx]; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstPhysicalFamily -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalCoefficient (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) : Finset ι→ℂ :=
  firstBareCubeCoefficient p hp hg hcop b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative
    (canonicalCubeResidual p hg b C negative Ψ m (ConcretePrimeRowBridge.idealGenerator x.1) H) d

theorem firstCanonicalCoefficient_old (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) :
    firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x =
      firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := rfl

lemma first_unblocked_physical (F : Finset ι) (C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstBlockedPhysicalRows p hg F (fun _=>1) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  simp only [firstBlockedPhysicalRows,one_mul]

theorem retained_first_physical_family (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (source : Finset (Ideal O×O)) (a : Ideal O×O→ℂ)
    (s : Fin 9→ℝ) (hs : ∀ i,0<s i) :
    (∑ x∈source,a x*canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)*
      firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)
        H₁ H₂ W₁ W₂ Φ K d x.2) =
    (K:ℂ)*firstFamilyPhysicalRows p hg source (pool\(b.support∪C)) (fun _ _=>1)
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂)
      (retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a)
      (fun x=>star (W₁ ((s 0*s 2*s 5*s 7)*x)))
      (fun x=>W₂ ((s 1*s 2*s 5*s 8)*x)) Φ
      (fun _=>‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (fun _=>‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (fun _=>primeProductNorm p C)
      (fun _=>primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
      K (fun _=>d) Prod.snd s := by
  have hscale₁ : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 0).ne' (hs 2).ne') (hs 5).ne') (hs 7).ne'
  have hscale₂ : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 1).ne' (hs 2).ne') (hs 5).ne') (hs 8).ne'
  have hw₁ : (fun y=>star (W₁ ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7))))) =
      fun y=>star (W₁ y) := by
    funext y
    rw [mul_div_cancel₀ _ hscale₁]
  have hw₂ : (fun y=>W₂ ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8)))) = W₂ := by
    funext y
    rw [mul_div_cancel₀ _ hscale₂]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical p hg]
  simp only [firstCubePhysicalMode,retainedCubeWeight,firstCanonicalCoefficient,
    firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceSupport -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma first_squarefree_row_zero_mem (U : Finset ι) (i : ι) (hi : i∈U) (n : O)
    (hn : n∈Ideal.span {p i}) : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg U n=0 := by
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_zero hi
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma canonicalCubeResidual_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (hn : ¬Disjoint U (b.support∪C)) : canonicalCubeResidual p hg b C negative Ψ m f H U=0 := by
  obtain ⟨i,hi,hib⟩ := Finset.not_disjoint_iff.mp hn
  rcases Finset.mem_union.mp hib with hib|hiC
  · have hm : cubeRadical p b.support∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hib)
    have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) U (cubeRadical p b.support)=0 := by
      simp only [rowCoprimeMask,ite_eq_left_iff]
      intro hh
      exact False.elim (hh ⟨i,hi,hm⟩)
    simp only [canonicalCubeResidual,originalLabelColumn,hz,mul_zero,zero_mul]
  · have hm : aLabel p b.support (if negative then b.rightBit else b.leftBit)*(∏j∈C,p j)∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiC) _)
    have hz := first_squarefree_row_zero_mem p hg U i hi _ hm
    simp only [canonicalCubeResidual,originalLabelColumn,hz,zero_pow (by norm_num : 4≠0),mul_zero,zero_mul]

lemma firstCanonicalCoefficient_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O)
    (hn : ¬Disjoint U (b.support∪C)) : firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x U=0 := by
  have hz := canonicalCubeResidual_zero_overlap p hg b C U negative Ψ m
    (ConcretePrimeRowBridge.idealGenerator x.1) H hn
  cases negative <;>
    simp only [firstCanonicalCoefficient,firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true,
      cubeMinusCoefficient,cubePlusCoefficient,firstPassColumnMinus,firstPassColumnPlus,hz,mul_zero]

lemma firstCommonIndices_membership (F : Finset ι) (j : FirstCommonIndex ι) :
    j∈firstCommonIndices F ↔ j.2.1⊆F ∧ j.2.2.1⊆F\j.2.1 ∧ j.2.2.2⊆F\j.2.1 := by
  simp [firstCommonIndices]

lemma firstCommonIndices_mono {F G : Finset ι} (h : F⊆G) : firstCommonIndices F⊆firstCommonIndices G := by
  intro j hj
  rcases (firstCommonIndices_membership F j).mp hj with ⟨hd,hu,hv⟩
  exact (firstCommonIndices_membership G j).mpr ⟨hd.trans h,
    hu.trans (Finset.sdiff_subset_sdiff h le_rfl),hv.trans (Finset.sdiff_subset_sdiff h le_rfl)⟩

lemma firstCommonWeight_zero_outside (F G : Finset ι) (C₁ C₂ : Finset ι→ℂ) (h : O)
    (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0) (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices G) (hjF : j∉firstCommonIndices F) :
    firstCommonWeight p hg C₁ C₂ h j=0 := by
  rcases (firstCommonIndices_membership G j).mp hj with ⟨hd,hu,hv⟩
  by_cases hleft : j.2.1∪j.2.2.1⊆F
  · have hright : ¬j.2.1∪j.2.2.2⊆F := by
      intro hr
      apply hjF
      apply (firstCommonIndices_membership F j).mpr
      refine ⟨Finset.Subset.trans Finset.subset_union_left hleft,?_,?_⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hleft (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hu hi)).2⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hr (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hv hi)).2⟩
    have hz := hC₂ _ (Finset.union_subset hd (hv.trans Finset.sdiff_subset)) hright
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul]
  · have hz := hC₁ _ (Finset.union_subset hd (hu.trans Finset.sdiff_subset)) hleft
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul,star_zero]

theorem firstPhysicalCommonRows_fixed_pool (F G : Finset ι) (hFG : F⊆G)
    (C₁ C₂ : Finset ι→ℂ) (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0)
    (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstPhysicalCommonRows p hg G C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed,firstPhysicalCommonRows_indexed]
  exact Finset.sum_subset (firstCommonIndices_mono hFG) (fun j hj hn=>by
    rw [firstCommonWeight_zero_outside p hg F G C₁ C₂ h hC₁ hC₂ j hj hn,zero_mul])

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) :
    Finset (Ideal O×O) :=
  labels.biUnion (fun f=> (nonzeroChildFrequencyBall
    (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y).image
      (fun h=>(f,h)))

theorem mem_firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ)
    (x : Ideal O×O) :
    x∈firstRetainedSource p labels b Y ↔ x.1∈labels ∧ x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y := by
  rcases x with ⟨f,h⟩
  simp [firstRetainedSource]

theorem sum_firstRetainedSource {A : Type*} [AddCommMonoid A]
    (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) (H : Ideal O×O→A) :
    ∑ x∈firstRetainedSource p labels b Y,H x =
    ∑ f∈labels,∑ h∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y,H (f,h) := by
  unfold firstRetainedSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro f hf
    exact Finset.sum_image (fun h hh k hk he=>congrArg Prod.snd he)
  · intro f hf g hg hfg
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hy
    exact hfg (congrArg Prod.fst he).symm

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_retained_label_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (labels : Finset (Ideal O)) (a : Ideal O→ℂ) (R : Finset ι→ℝ) :
    (∑ f∈labels,a f*canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator f)
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K
      (fun D=>childFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D))) =
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
      ∑ x∈firstRetainedSource p labels b (R D),a x.1*
        canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)*
        firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)
          H₁ H₂ W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) x.2 := by
  simp_rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  simp only [Finset.mul_sum,sum_firstRetainedSource,nonzeroChildFrequencyBall]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro h hh
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstActualSecondEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalSecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  (32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
        (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)) ω X (∏i∈C,p i) d core t Y).re

theorem firstCanonicalSecondEnergy_nonneg (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    0≤firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d H selector ω X t Y := by
  unfold firstCanonicalSecondEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro core hcore
  apply mul_nonneg (norm_nonneg _)
  rw [first_fresh_real_energy p hp hg hinj hc F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m _ ω X (∏i∈C,p i) d core t Y hY]
  exact Finset.sum_nonneg (fun z hz=>mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _))

theorem first_retained_actual_second_energy (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (labels : Finset (Ideal O)) (a : Ideal O×O→ℂ) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ f∈labels,Squarefree f) → (∀ f∈labels,f≠0) → (∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ) →
      ∀ (negative : Bool) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t : ℝ),0<X →
      firstFamilyEnergy p hg (firstRetainedSource p labels b Y) F (fun _=>selector)
        (firstCanonicalCoefficient p hp hcop hg b C negative
          (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H)
        (retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a) negative ω X t Prod.snd ≤
      Γ*K*Y^ε * firstCanonicalSecondEnergy p hp hg hinj F b C negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H selector ω X t Y := by
  obtain ⟨K,hK,hstep⟩ := retained_cube_energy_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d labels a Γ Y hΓ hY
    hlabels hn ha negative H selector ω X t hX
  have he := hstep p hp hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a
    (firstRetainedSource p labels b Y) Γ Y hΓ hY
    (fun x hx=>hlabels x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1)
    (fun x hx=>hn x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1) ha
    (fun x hx=>((mem_firstRetainedSource p labels b Y x).mp hx).2)
    negative H selector ω X t hX
  have hcoef : firstCanonicalCoefficient p hp hcop hg b C negative
      (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H =
      fun x=>firstOldLabelCoefficient p hp hcop hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂)
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := by
    funext x
    exact firstCanonicalCoefficient_old p hp hcop hg b C negative _ _ d H x
  rw [hcoef]
  exact he

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstActualPriorityEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstPrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := (if negative then b.rightDivisor else b.leftDivisor)∪C
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_prime_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (primeMark slots lists a) selector ω X t Y ≤
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m d slots lists a selector ω X t Y := by
  let A := (if negative then b.rightDivisor else b.leftDivisor)∪C
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      ω X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstPrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤(32*512:ℝ)*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from by positivity)
  convert h using 1
  · dsimp only [A]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstGlobalPush -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→Eis) (outer:Finset κ)
    (labels:κ→Finset (Ideal Eis)) (cube:κ→CubeCoordinates ι) (Y:ℝ):
    Finset (Σ _ : κ,Ideal Eis×Eis):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)

omit [DecidableEq κ] in
theorem first_global_retained_push (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(ω:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative ω X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) ω X t Y := by
  obtain ⟨K,hK,hpush⟩:=first_retained_actual_second_energy ε hε
  refine ⟨K,hK,?_⟩
  intro p hp _ hinj hcop hg hc hpr F outer cube common Ψ₁ Ψ₂ m₁ m₂ d labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hs hn ha negative H selector ω X t hX
  simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hpush p hp hinj hcop hg hc hpr F (cube k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
    (d k) (labels k) (a k) Γ Y hΓ hY (hs k hk) (hn k hk) (ha k hk)
    negative (H k) (selector k) ω X t hX

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceIndex -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

abbrev FirstOriginalOuter (ι : Type*) := Σ _ : CubeCoordinates ι,Σ _ : Finset ι,Finset ι

def firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (FirstOriginalOuter ι) :=
  (reopenedCubeFamily Q).sigma (fun b=>(pool\b.support).powerset.sigma
    (fun C=>(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset))

lemma mem_firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : FirstOriginalOuter ι) :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

lemma retained_cutoff_enlargement (E : O) (hE : E≠0) (R Y : ℝ) (hRY : R≤Y) (f : O→ℂ) :
    (∑h∈(childFrequencyBall E R).erase 0,f h)=
      ∑h∈nonzeroChildFrequencyBall E Y,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
  have hsub : (childFrequencyBall E R).erase 0⊆nonzeroChildFrequencyBall E Y := by
    intro h hh
    rcases Finset.mem_erase.mp hh with ⟨hn,hm⟩
    exact Finset.mem_erase.mpr ⟨hn,(mem_childFrequencyBall E hE Y h).mpr
      (((mem_childFrequencyBall E hE R h).mp hm).trans hRY)⟩
  calc
    _=∑h∈(childFrequencyBall E R).erase 0,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [(Finset.mem_erase.mp hh).2]
    _=_ := Finset.sum_subset hsub (by
      intro h hh hn
      have hne := (Finset.mem_erase.mp hh).1
      have hout : h∉childFrequencyBall E R := fun hm=>hn (Finset.mem_erase.mpr ⟨hne,hm⟩)
      simp [hout])

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstOriginalWeight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) : ℂ :=
  reopenedPairCoefficient β k.1 k.2.1 x.1 *
    (UniqueFactorizationMonoid.moebius (∏i∈k.2.2,Ideal.span {p i}):ℂ) *
    (if x.2∈reopenedPhysicalCutoff p k.1 x.1 (R k.1 k.2.1 x.1) k.2.2 then 1 else 0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma firstOriginalWeight_norm_le (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) :
    ‖firstOriginalWeight p β R k x‖≤‖reopenedPairCoefficient β k.1 k.2.1 x.1‖ := by
  unfold firstOriginalWeight
  split_ifs
  · simp only [mul_one,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (CubicEisenstein.norm_ideal_moebius_le_one _)
  · simp

theorem original_retained_global_index
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      firstOriginalWeight p β R x.1 x.2 *
      canonicalCubeOuter p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator x.2.1)*
      firstCubePhysicalMode p hp hcop hg pool x.1.1 x.1.2.1 Ψ Ψ m m
        (ConcretePrimeRowBridge.idealGenerator x.2.1) (mark x.1.1.rightExponent) (mark x.1.1.leftExponent)
        W W Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 := by
  simp only [firstGlobalRetainedSource,firstOriginalOuter,Finset.sum_sigma,sum_firstRetainedSource]
  unfold reopenedPhysicalSourceSum reopenedPhysicalRetained
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  have hE := firstPhysicalMultiplier_ne_zero p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit f (hlabels f hf)
  have hRY' := hRY ⟨b,⟨C,D⟩⟩ ((mem_firstOriginalOuter pool Q _).mpr ⟨hb,hC,hD⟩) f hf
  rw [show reopenedPhysicalCutoff p b f (R b C f) D=
    childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R b C f D) from rfl]
  rw [retained_cutoff_enlargement _ hE _ Y hRY']
  apply Finset.sum_congr rfl
  intro h hh
  simp only [firstOriginalWeight,reopenedPhysicalCutoff]
  ac_rfl

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourcePhysical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem firstCubePhysicalMode_fixed_pool (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (x : Ideal O×O) :
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator x.1) H₁ H₂ W₁ W₂ Φ K d x.2=
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2 *
      firstPhysicalCommonRows p hg pool
        (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
        (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x)
        (fun y=>star (W₁ y)) W₂ Φ
        (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
        (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
        (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d x.2 := by
  change _*firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x) _ _ _ _ _ _ _ _ _ _ = _
  apply congrArg (fun z : ℂ =>
    (K : ℂ) * cubeBaseFactor p hp hg b.support
      (fun i => b.leftExponent i + b.rightExponent i) b.leftBit b.rightBit d x.2 * z)
  apply firstPhysicalCommonRows_fixed_pool p hg _ pool Finset.sdiff_subset
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩

theorem original_retained_global_family
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    (K:ℂ)*firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s := by
  rw [original_retained_global_index p hp hcop hg pool Q labels hlabels β Ψ m mark W Φ K Y R hRY]
  have hleft : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 0)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 1)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 8))
  have hw₁ : (fun y=>star (W ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7)))))=fun y=>star (W y) := by
    funext y
    rw [mul_div_cancel₀ _ hleft]
  have hw₂ : (fun y=>W ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8))))=W := by
    funext y
    rw [mul_div_cancel₀ _ hright]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical,firstCubePhysicalMode_fixed_pool p hp hcop hg]
  unfold retainedCubeWeight
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def originalRetainedFamily
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s

theorem original_global_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (K Y : ℝ) (hK : 0<K)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    K*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant K Y R s‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  have he := original_reopened_physical_energy p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m (fun _=>mark) W K hK R hR
  rw [original_retained_global_family p hp hcop hg pool Q labels hlabels β Ψ m mark W rowMajorant K Y R hRY s hs] at he
  simpa only [originalRetainedFamily,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK] using he

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstUnequalPhysicalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_first_family_two_energies (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hWeighted : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
  have he := actual_first_balanced_family p hg hp source F selector C₁ C₂ w
    W₁ W₂ ω₁ ω₂ Φ V A₁ A₂ C R K L d h s hpos hs density hDensity hsep hω₁ hω₂ hcut
  have hb := first_family_integral_of_two_energies p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s
    density J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (firstRootScale_pos s hs)]
  have hexp : Real.exp ((9/2:ℝ)*L)*Real.exp (-(9/2:ℝ)*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn' := congrArg (fun a : ℝ => Real.exp ((9/2:ℝ)*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc,←div_eq_mul_inv] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by have := firstRootScale_pos s hs; positivity)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileUniform -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_moving_family_two_energies_uniform
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ {ι κ : Type*} [DecidableEq ι] (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro ι κ _ p hp _ hg source F selector C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep hω₁ hω₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

theorem first_global_retained_push_uniform (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ {ι κ:Type*} [DecidableEq ι] [DecidableEq κ] (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(ω:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative ω X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) ω X t Y := by
  obtain ⟨K,hK,hpush⟩:=first_retained_actual_second_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι κ _ _ p hp _ hinj hcop hg hc hpr F outer cube common Ψ₁ Ψ₂ m₁ m₂ d labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hs hn ha negative H selector ω X t hX
  simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hpush p hp hinj hcop hg hc hpr F (cube k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
    (d k) (labels k) (a k) Γ Y hΓ hY (hs k hk) (hn k hk) (ha k hk)
    negative (H k) (selector k) ω X t hX

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileFiltered -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hcop hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies_uniform
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_global_retained_push_uniform ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun x=>selector x.1) C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun x=>dd x.1) (fun x=>x.2.2) s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha true H₁ selector ω₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    simp only [ite_true,] at he
    have hm1 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm1.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha false H₂ selector ω₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    simp only [ite_false,Bool.false_eq_true] at he
    have hm2 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm2.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstUnequalMovingEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι κ : Type*} [DecidableEq ι]
theorem actual_first_moving_family_two_energies
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro p hp _ hg source F selector C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep hω₁ hω₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstUnequalRetainedEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι : Type*} [DecidableEq ι]
theorem actual_first_retained_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (b : SecondPassArithmetic.CubeCoordinates ι) (common : Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright dd : Eis) (H₁ H₂ selector : Finset ι→ℂ)
    (labels : Finset (Ideal Eis)) (a : Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀ f∈labels,Squarefree f) (_hn : ∀ f∈labels,f≠0)
    (_ha : ∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : Ideal Eis×Eis → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i),
    let source := firstRetainedSource p labels b Y
    let C₁ := firstCanonicalCoefficient p hp hcop hg b common true Ψ₁ mleft dd H₁
    let C₂ := firstCanonicalCoefficient p hp hcop hg b common false Ψ₂ mright dd H₂
    let w := retainedCubeWeight p hp hcop hg b common Ψ₁ Ψ₂ mleft mright dd a
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd≠0 ∧ x.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) dd x.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstCanonicalSecondEnergy p hp hg hinj F b common true Ψ₁ mleft dd H₁ selector ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstCanonicalSecondEnergy p hp hg hinj F b common false Ψ₂ mright dd H₂ selector ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun _=>selector) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun _=>dd) Prod.snd s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies (ι := ι) (κ := Ideal Eis×Eis)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_retained_actual_second_energy ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro p hp _ hg hinj hcop hc hpr F b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun _=>selector) C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun _=>dd) Prod.snd s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F b common Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright dd
      labels a Γ Y hΓ hY hlabels hn ha true H₁ selector ω₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    apply he.trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F b common Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright dd
      labels a Γ Y hΓ hY hlabels hn ha false H₂ selector ω₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    apply he.trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstHeightBudget -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open JointLogSeparation InverseAmbientProfileTower

theorem first_left_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 7 p‖) (inheritedLeft_bound 7 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_right_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 8 p‖) (inheritedRight_bound 8 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_right_eq,norm_neg,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_unequal_prefactor (Z:ℝ)(hZ:0<Z)
    (M r ell V delta A₁ A₂ B R t h eta:ℝ):
    (Z^(-r-2*ell-V)*Z^M/firstRootScale
      (fun i=>Z^(![A₁,A₂,B,delta,R,t,h,r-A₁-B-t,r-A₂-B-t] i)))*
      Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.sqrt ((Z^(firstKappa M r ell V delta A₁ B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))⁻¹)*
       Real.sqrt ((Z^(firstKappa M r ell V delta A₂ B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))⁻¹))=1:=by
  rw [first_physical_scalar Z hZ]
  have he:Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta):=by
    rw [Real.rpow_def_of_pos hZ];congr 1;ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  rw [←Real.rpow_neg hZ.le,←Real.rpow_neg hZ.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  convert Real.rpow_zero Z using 1
  congr 1
  ring
end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfilePhysical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_physical_budget (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hcop hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (Benergy : ℝ) (_hBenergy : 0 ≤ Benergy)
    (Z M r ell V delta aa₁ aa₂ bb rr tq hh eta:ℝ) (_hZ:0<Z)
    (_hscale:s=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
    (_hLe:L=eta*Real.log Z)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
    (Z^(-r-2*ell-V)*Z^M)*‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,Kpush,hCprofile,hKpush,he⟩:=actual_first_original_subset_two_energies ε hε
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut Benergy hBenergy
    Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe hleft hright
  let P₁:=Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let P₂:=Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hp₁:0<P₁:=by dsimp [P₁];positivity
  have hp₂:0<P₂:=by dsimp [P₂];positivity
  have hb:=he p hp hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut (Benergy/P₁) (Benergy/P₂) (by positivity) (by positivity)
    (by intro z;rw [div_mul_eq_mul_div];apply (le_div_iff₀ hp₁).mpr;convert hleft z using 1 ; dsimp only [P₁] ; ring)
    (by intro z;rw [div_mul_eq_mul_div];apply (le_div_iff₀ hp₂).mpr;convert hright z using 1 ; dsimp only [P₂] ; ring)
  have hroot:Real.sqrt (Benergy/P₁)*Real.sqrt (Benergy/P₂)=Benergy*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹):=by
    simp only [div_eq_mul_inv,Real.sqrt_mul hBenergy]
    calc
      _=(Real.sqrt Benergy)^2*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹):=by ring
      _= _:=by rw [Real.sq_sqrt hBenergy]
  rw [hroot] at hb
  have hcancel:(Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹)=1:=by
    rw [hscale,hLe]
    exact first_unequal_prefactor Z hZ M r ell V delta aa₁ aa₂ bb rr tq hh eta
  have hnorm:0≤Z^(-r-2*ell-V)*Z^M:=by positivity
  apply (mul_le_mul_of_nonneg_left hb hnorm).trans_eq
  calc
    _=((Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹))*
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)):=by ring
    _= _:=by rw [hcancel,one_mul]
end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstWholeCubePriority -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstWholePrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_whole_cube_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (fun U=>primeMark slots lists a (extra∪U)) selector ω X t Y ≤
    firstWholePrioritySecondEnergy p hp hg hinj F b C extra negative Ψ m d slots lists a selector ω X t Y := by
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      ω X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤(32*512:ℝ)*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from by positivity)
  convert h using 1
  · dsimp only [A]
    simp only [Finset.union_assoc]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem balanced_density_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

theorem balanced_density_weighted_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun t : Frequency × (Fin 6 → ℝ) => tripleHeight J t.1*coordinateHeight J t.2*
      ‖InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L t‖) :=
  InverseSecondProfileUniform.density_weighted_integrable g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L J

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_source (source : Finset κ) (F : Finset ι)
    (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6 → ℝ → ℂ)
    (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 6 → ℝ,
      (Real.exp (-6*L):ℂ) * secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ V
        (Y*K₀/(E₀*V₀^2*X₀^2)) y =
      ∫ t : Frequency × (Fin 6 → ℝ), density t *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2)
    (hn : ∀ j ∈ source,(x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0)
    (hω₁ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₁ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₁ (primeProductNorm p N/X₀) = 1)
    (hω₂ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₂ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₂ (primeProductNorm p N/X₀) = 1)
    (hcut : ∀ j ∈ secondProfileIndices source F x,
      ω₁ (primeProductNorm p j.2.1/X₀) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L):ℂ) * (∑ j ∈ source,w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
    ((E₀*V₀*X₀:ℝ):ℂ)⁻¹ * ∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ j ∈ source,w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t := by
  apply actualSecondFreshRows_normalized_density p hp hcop hg source F x w
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ Y G₀ E₀ V₀ K₀ X₀ density hDensity
  intro j hj
  obtain ⟨hjS,hN,hM⟩ := (mem_secondProfileIndices source F x j).mp hj
  have h1 : star (W₁ (primeProductNorm p (x j.1).common*primeProductNorm p (x j.1).overlap*
      primeProductNorm p j.2.1/(G₀*V₀*X₀))) ≠ 0 → star (ω₁ (primeProductNorm p j.2.1/X₀)) = 1 := by
    intro hh
    rw [hω₁ j.1 hjS j.2.1 hN (star_ne_zero.mp hh),star_one]
  have h2 := hω₂ j.1 hjS j.2.2 hM
  have h3 : star (ω₁ (primeProductNorm p j.2.1/X₀)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1 :=
    fun ha hb => hcut j hj (star_ne_zero.mp ha) hb
  have he := InverseSecondProfileUniform.fresh_physical_profile
    (fun x => star (W₁ x)) W₂ Φ V G₀ E₀ V₀ K₀ X₀ Y L hG hE hV hK hX
    (fun x => star (ω₁ x)) ω₂ (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hjS).1 (hn j.1 hjS).2 j.2.1 j.2.2)
    (by simpa [secondActualNorms] using h1)
    (by simpa [secondActualNorms] using h2)
    (by simpa [secondActualNorms] using h3)
  rw [hsep] at he
  simpa [secondActualNorms] using he

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondBalancedPhysical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondBalancedPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_profile_children
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (Real.exp (-6*L):ℂ) * ((Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
                ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := actual_second_modes_common_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hn : ∀ x ∈ source,(secondInheritedProfile p x Ψ m z).divisor ≠ 0 ∧
      (secondInheritedProfile p x Ψ m z).frequency ≠ 0 := by
    intro x hx
    refine ⟨primeSubsetGenerator_ne_zero _ _,?_⟩
    have hh := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) R _).mp (hrows x hx)
    intro he
    change x.second.frequency = 0 at he
    simp only [he,mul_zero,map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),lt_self_iff_false] at hh
    exact hh.1
  have he := actual_second_balanced_source p hp hcop hg source pool
    (fun x : MarkedSecondSource ι Jo 0 => secondInheritedProfile p x Ψ m z)
    (fun x : MarkedSecondSource ι Jo 0 => w x*actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ U G E V B X Y L
    hG hE hV hB hX density hDensity hsep hn hω₁ hω₂ hcut
  calc
    _ = ((Y:ℂ)*secondRayCoefficient z) * ((Real.exp (-6*L):ℂ)*
        ∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X)) := by ring
    _ = _ := by
      rw [he]
      rw [←mul_assoc]
      apply congrArg (fun a : ℂ => ((Y:ℂ)*secondRayCoefficient z*((E*V*X:ℝ):ℂ)⁻¹)*a)
      apply integral_congr_ae
      filter_upwards with t
      apply congrArg (fun a : ℂ => density t*a)
      exact hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t _

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondPhysicalEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_physical_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  obtain ⟨sector,hsector⟩ := actual_second_balanced_profile_children p hp hcop hg hpr (σ:=σ) source hs
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w labels K J A hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he := hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hb := actual_second_all_modes_integral p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R labels hlabels hrows
    K ho hslots₁ hslots₂ w hw A hA J density hWeighted hleft hright
  have hi : (∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
        (w x*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t) =
      ∫ t : Frequency × (Fin 6 → ℝ),density t*secondFullModeSum p hp hcop hg source sector pool Ψ m z
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X w t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [secondFullModeSum_physical]
  rw [hi] at he
  have hexp : Real.exp (6*L)*Real.exp (-6*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul]
  have hn' := congrArg (fun a : ℝ => Real.exp (6*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRecursive -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalRecursiveUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_physical_recursive
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*(Z^N)^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B Y R L Z N Vlabel εchild
    U density w labels K J A hZ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he (H : ℝ) : Z^(max 0 N+Vlabel)*(A*Z^(max 0 N+Vlabel+εchild)*H) =
      (A*Z^(2*(max 0 N+Vlabel)+εchild))*H := by
    calc
      _ = A*(Z^(max 0 N+Vlabel)*Z^(max 0 N+Vlabel+εchild))*H := by ring
      _ = _ := by rw [←Real.rpow_add hZ]; congr 2; ring_nf
  apply actual_second_balanced_physical_energy p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B (Z^N) Y R L
    U density w labels K J (A*Z^(2*(max 0 N+Vlabel)+εchild))
    hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels
    ho hslots₁ hslots₂ (mul_nonneg hA (Real.rpow_pos_of_pos hZ _).le) hWeighted
  · intro t J₁ hJ₁ γ hγ
    rw [second_left_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      (nonzeroChildFrequencyBall 1 R) γ pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayMinus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hleft t J₁ hJ₁ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)
  · intro t J₂ hJ₂ γ hγ
    rw [second_right_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      R γ pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayPlus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hright t J₂ hJ₂ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

@[ext] structure SecondParentSource (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

def attachSecondExpansion {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : MarkedSecondSource ι Jo 0 where
  cube := parent.cube
  firstCommon := parent.firstCommon
  firstDivisor := parent.firstDivisor
  second := x
  quotient := parent.quotient
  oldAssigned := parent.oldAssigned
  newAssigned := Fin.elim0

def secondParentOf {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := x.oldAssigned

omit [DecidableEq ι] in
theorem attachSecondExpansion_injective {Jo : ℕ} (parent : SecondParentSource ι Jo) :
    Function.Injective (attachSecondExpansion parent) := by
  intro x y h
  exact congrArg MarkedSecondSource.second h

omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def secondSourceParentEquiv {Jo : ℕ} :
    SecondParentSource ι Jo × SecondExpansionData ι ≃ MarkedSecondSource ι Jo 0 where
  toFun x := attachSecondExpansion x.1 x.2
  invFun x := (secondParentOf x,x.second)
  left_inv x := by cases x; rfl
  right_inv := attachSecondExpansion_recover

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondParentLabel {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  (∏ i∈parent.firstCommon,p i)*jLabel p parent.cube.support
    (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit

def secondParentDivisor {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) parent.firstDivisor

def secondParentPuncture {Jo : ℕ} (m : Eis) (parent : SecondParentSource ι Jo) : Eis :=
  (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*
    b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit*secondParentDivisor p parent

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_source_conditions {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι))
    (ha : parent.cube.Admissible) (hC : Disjoint parent.firstCommon parent.cube.support)
    (hD : parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (source.image (attachSecondExpansion parent)) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ha
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hC
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hD
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hE y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hold
  · intro x hx i
    exact Fin.elim0 i
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hq

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_inherited_profile {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    secondInheritedProfile p (attachSecondExpansion parent x) Ψ m z =
      expansionProfileData p Ψ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) z ∅ ∅ x := rfl

theorem attached_signed_weight {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator (attachSecondExpansion parent x).quotient) z
      (attachSecondExpansion parent x) =
    secondSignedSourceWeight p hp hcop hg Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z x := rfl

theorem secondExpansionSource_attached
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z source
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈source.image (attachSecondExpansion parent),
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  have he := secondExpansionSource_signed_profile p hp hcop hg hinj hpr pool Ψ
    (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    z source hE ∅ ∅ slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ X Y
  simp only [Finset.empty_union] at he
  rw [he]
  congr 1
  rw [Finset.sum_image (fun x hx y hy h => attachSecondExpansion_injective parent h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [attached_inherited_profile,attached_signed_weight]

end
end SevenEighths.InverseMoment

end OAI

end

