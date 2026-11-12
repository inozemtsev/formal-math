module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Eisenstein.Part005
public import Green64.Library.OAI.NumberTheory.DirichletL.CubicSieve.ReopeningSeparation

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / CubicSieve / Part014

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.LogSeparation -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CanonicalCubeSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation

lemma cube_log_bin (B n : ℝ) (hB : 0 < B) (hn : B ≤ n)
    (hn' : n ≤ Real.exp 1 * B) : Real.log (n/B) ∈ Set.Icc (0:ℝ) 1 := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  constructor
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hn))
  · have hh : n/B ≤ Real.exp 1 := (div_le_iff₀ hB).mpr hn'
    have := Real.log_le_log (div_pos hn0 hB) hh
    simpa only [Real.log_exp] using this

lemma cube_log_argument (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp

lemma cube_half_normalization (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp

lemma cube_half_normalization_complex (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell) : ℂ)⁻¹ * (Real.sqrt n : ℂ) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * (Real.exp (Real.log (n/B)/2) : ℂ) := by
  exact_mod_cast cube_half_normalization B ell n hB hell hn

theorem reopening_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) * W (q*n^3/X) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hn0 : 0 < n := lt_of_lt_of_le hB hn
  have hsep := reopening_separation_with_window W a b ha hs hW V hV
    (Real.log (n/B)) (Real.log (q/ell)) (cube_log_bin B n hB hn hn')
  rw [cube_log_argument B ell n q hB hell hn0 hq] at hsep
  rw [hX, cube_half_normalization_complex B ell n hB hell hn0, mul_assoc, hsep]

lemma completed_cube_half_weight (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt (X/n^3))⁻¹ = (Real.sqrt X)⁻¹ * Real.sqrt n := by
  have hs : Real.sqrt (n^3) = n*Real.sqrt n := by
    rw [show n^3=n^2*n by ring, Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  rw [Real.sqrt_div hX.le, hs, inv_div]
  field_simp

lemma completed_cube_half_weight_complex (X n : ℝ) (hX : 0 < X) (hn : 0 < n) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ =
      (Real.sqrt X : ℂ)⁻¹ * (Real.sqrt n : ℂ) := by
  exact_mod_cast completed_cube_half_weight X n hX hn

theorem completed_cube_norm_separation (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X n q : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : B ≤ n) (hn' : n ≤ Real.exp 1*B) (hq : 0 < q) :
    (n : ℂ)⁻¹ * (Real.sqrt (X/n^3) : ℂ)⁻¹ * W (q/(X/n^3)) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          cubeFrequencyFactor (Real.log (n/B)) ξ * frequencyTwist V ξ (Real.log (q/ell)) := by
  have hXp : 0 < X := hX ▸ mul_pos (pow_pos hB _) hell
  rw [completed_cube_half_weight_complex X n hXp (lt_of_lt_of_le hB hn), div_div_eq_mul_div]
  exact reopening_norm_separation W a b ha hs hW V hV B ell X n q hB hell hX hn hn' hq

def separatedCubeCoefficient {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ : ℝ) (v : κ) : ℂ := β v * cubeFrequencyFactor (Real.log (n v/B)) ξ

lemma separatedCubeCoefficient_bound {κ : Type*} (β : κ → ℂ) (n : κ → ℝ)
    (B ξ Γ : ℝ) (hB : 0 < B) (hΓ : 0 ≤ Γ) (v : κ)
    (hn : B ≤ n v) (hn' : n v ≤ Real.exp 1*B) (hβ : ‖β v‖ ≤ Γ) :
    ‖separatedCubeCoefficient β n B ξ v‖ ≤ Γ*Real.exp (1/2) := by
  unfold separatedCubeCoefficient
  rw [norm_mul]
  exact mul_le_mul hβ (cubeFrequencyFactor_bound _ ξ (cube_log_bin B _ hB hn hn').2)
    (norm_nonneg _) hΓ

theorem reopening_finite_sum_integrable {κ τ : Type*}
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell : ℝ) (b V : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => b ξ * ∑v∈Q,∑j∈S,
      separatedCubeCoefficient β n B ξ v * A v j * frequencyTwist V ξ (Real.log (q j/ell))) := by
  have hi : Integrable (fun ξ : ℝ => ∑v∈Q,∑j∈S,
      (β v*A v j)*(b ξ*cubeFrequencyFactor (Real.log (n v/B)) ξ*
        frequencyTwist V ξ (Real.log (q j/ell)))) := by
    apply integrable_finsetSum
    intro v hv
    apply integrable_finsetSum
    intro j hj
    exact (reopening_integrable b V _ _).const_mul _
  convert hi using 1
  funext ξ
  simp only [Finset.mul_sum, separatedCubeCoefficient]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem reopening_finite_sum {κ τ : Type*}
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Q : Finset κ) (S : Finset τ) (β : κ → ℂ) (A : κ → τ → ℂ)
    (n : κ → ℝ) (q : τ → ℝ) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀v∈Q,B ≤ n v) (hn' : ∀v∈Q,n v ≤ Real.exp 1*B)
    (hq : ∀j∈S,0 < q j) :
    (∑v∈Q,∑j∈S, (β v*A v j)*
      ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3)))) =
    ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ * ∑v∈Q,∑j∈S,
        separatedCubeCoefficient β n B ξ v * A v j *
          frequencyTwist V ξ (Real.log (q j/ell)) := by
  let G : ℝ → κ → τ → ℂ := fun ξ v j => (β v*A v j)*
    (reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
      frequencyTwist V ξ (Real.log (q j/ell)))
  have hi (v : κ) (j : τ) : Integrable (fun ξ => G ξ v j) :=
    (reopening_integrable _ V _ _).const_mul _
  have hterm (v : κ) (hv : v∈Q) (j : τ) (hj : j∈S) :
      (β v*A v j)*((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ * W (q j/(X/(n v)^3))) =
        ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,G ξ v j := by
    rw [completed_cube_norm_separation W a b ha hs hW V hV B ell X (n v) (q j)
      hB hell hX (hn v hv) (hn' v hv) (hq j hj)]
    rw [show (∫ ξ : ℝ,G ξ v j) = (β v*A v j)*∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ * cubeFrequencyFactor (Real.log (n v/B)) ξ *
          frequencyTwist V ξ (Real.log (q j/ell)) from integral_const_mul _ _]
    ring
  calc
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∑v∈Q,∑j∈S,∫ ξ : ℝ,G ξ v j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hterm v hv j hj)
    _ = ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,∑v∈Q,∑j∈S,G ξ v j := by
      congr 1
      rw [integral_finsetSum _ (fun v hv => integrable_finsetSum _ (fun j hj => hi v j))]
      apply Finset.sum_congr rfl
      intro v hv
      exact (integral_finsetSum _ (fun j hj => hi v j)).symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [Finset.mul_sum, separatedCubeCoefficient]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [G]
      ring

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight

theorem rowTwist_primary_zero_of_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:ActualEisensteinCubic.O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal ActualEisensteinCubic.O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryGenerator B) * idealRowHom _ (Ideal.span {primaryGenerator B}) = 0
    rw [(primaryGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) {P B : Ideal ActualEisensteinCubic.O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
  cubeWeight_zero_of_mask _ B (rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm)

theorem summand_cube_support (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D)
    (I B : Ideal ActualEisensteinCubic.O) (hn : summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [summand,hz,mul_zero,zero_mul])

theorem large_cube_sum_comm (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B) =
      ∑'B:Ideal ActualEisensteinCubic.O,∑'I:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand Ψ W X I B := by
  let a : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*summand Ψ W X p.1 p.2
  have hf : (Function.support a).Finite :=
    (completedT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal ActualEisensteinCubic.O) (Ideal ActualEisensteinCubic.O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem large_cube_sum_finite (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (∑'I:Ideal ActualEisensteinCubic.O,∑'B:Ideal ActualEisensteinCubic.O,largeCubeCoefficient H₀ B*summand (rowTwist Ψ m f z) W X I B) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B := by
  rw [large_cube_sum_comm _ W hWc X H₀ hX]
  simp only [tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal ActualEisensteinCubic.O,summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero]

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem inner_completed_sum (Ψ : ActualEisensteinCubic.O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal ActualEisensteinCubic.O) (hB : B≠0) :
    (∑'I:Ideal ActualEisensteinCubic.O,summand Ψ W X I B) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal ActualEisensteinCubic.O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3)) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal ActualEisensteinCubic.O) : summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  exact tsum_mul_left

theorem outsideCanonicalRow_reopened (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B * cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) B *
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) * idealRowHom z B^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm B:ℝ)^3) := by
  rw [outsideCanonicalRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hB0 : B≠0 := outsideIdealsUpTo_ne_bot S D B hB
  have hN := norm_at_least_one B hB0
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := by positivity
  have hYX : X/(Ideal.absNorm B:ℝ)^3 ≤ X :=
    div_le_self hX.le (one_le_pow₀ hN)
  have hDY : b*(X/(Ideal.absNorm B:ℝ)^3) ≤ D :=
    (mul_le_mul_of_nonneg_left hYX hb).trans hD
  rw [inner_completed_sum _ W X hX B hB0]
  rw [←outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b
    (X/(Ideal.absNorm B:ℝ)^3) hY hW hDY]
  rw [cubeWeight_row_factor]
  ring

theorem outsideCanonicalRow_reopened_exponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0 ≤ b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t≤b) (hD : b*X ≤ D) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex F),
        (largeCubeCoefficient H₀ (cubeIdeal F v) *
          cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
          (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹) *
          idealRowHom z (cubeIdeal F v)^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3) := by
  dsimp only
  rw [outsideCanonicalRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD]
  rw [sum_outside_cubeIndex S D]

end

open ActualEisensteinCubic
open CompletedGauss hiding O

theorem cubeWeight_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ B‖ ≤ 1/(Ideal.absNorm B:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator B)‖ ≤ 1 := by
    by_cases hz : primaryGenerator B=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator B))^3*
    Ψ (primaryGenerator B)^3/(Ideal.absNorm B:ℂ)‖ ≤ _
  rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) hang)).trans (pow_le_one₀ (norm_nonneg _) (hΨ _))

def cubePhase (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  (Ideal.absNorm B:ℂ)*cubeWeight Ψ B

theorem cubePhase_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (B : Ideal ActualEisensteinCubic.O) :
    ‖cubePhase Ψ B‖ ≤ 1 := by
  by_cases hB : B=0
  · simp [hB,cubePhase]
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  rw [cubePhase,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (Ideal.absNorm B:ℝ)*(1/(Ideal.absNorm B:ℝ)) :=
      mul_le_mul_of_nonneg_left (cubeWeight_norm_le Ψ hΨ B) hN.le
    _ = 1 := by field_simp

theorem cube_weight_scale (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) (hB : B≠0)
    (X : ℝ) (hX : 0<X) :
    cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹ =
      cubePhase Ψ B * (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)/(Real.sqrt X:ℂ) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hs3 : Real.sqrt ((Ideal.absNorm B:ℝ)^3) =
      (Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ) := by
    rw [show (Ideal.absNorm B:ℝ)^3=(Ideal.absNorm B:ℝ)^2*(Ideal.absNorm B:ℝ) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hN]
  have hs : Real.sqrt (X/(Ideal.absNorm B:ℝ)^3) =
      Real.sqrt X/((Ideal.absNorm B:ℝ)*Real.sqrt (Ideal.absNorm B:ℝ)) := by
    rw [Real.sqrt_div hX.le,hs3]
  rw [hs,Complex.ofReal_div,Complex.ofReal_mul,cubePhase]
  push_cast
  have hNc : (Ideal.absNorm B:ℂ)≠0 := by exact_mod_cast hN.ne'
  have hsN : (Real.sqrt (Ideal.absNorm B:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  have hsX : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  field_simp

def reopenedCubeCoefficient (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (B : Ideal ActualEisensteinCubic.O) : ℂ :=
  largeCubeCoefficient H₀ B * cubePhase Ψ B

theorem reopenedCubeCoefficient_small_power (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀(H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ), (∀z,‖Ψ z‖≤1) →
      ∀B:Ideal ActualEisensteinCubic.O,B≠0 → ‖reopenedCubeCoefficient H₀ Ψ B‖ ≤ C*(Ideal.absNorm B:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := largeCubeCoefficient_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro H₀ Ψ hΨ B hB
  rw [reopenedCubeCoefficient,norm_mul]
  calc
    _ ≤ ‖largeCubeCoefficient H₀ B‖*1 :=
      mul_le_mul_of_nonneg_left (cubePhase_norm_le Ψ hΨ B) (norm_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hbound H₀ B hB

theorem reopenedCubeCoefficient_support (H₀:ℝ) (Ψ:ActualEisensteinCubic.O →* ℂ) (B:Ideal ActualEisensteinCubic.O)
    (h:reopenedCubeCoefficient H₀ Ψ B≠0) : B≠0 ∧ H₀ ≤ (Ideal.absNorm B:ℝ) := by
  exact largeCubeCoefficient_support H₀ B (fun hz=>h (by simp only [reopenedCubeCoefficient,hz,zero_mul]))

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

def childLabelRotation (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O :=
  (z.1,(u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2))

theorem childLabelRotation_injective (u : ActualEisensteinCubic.Oˣ) (negative : Bool) :
    Function.Injective (childLabelRotation u negative) := by
  intro z w he
  have hf := congrArg Prod.fst he
  change z.1=w.1 at hf
  have hs := congrArg Prod.snd he
  change (u : ActualEisensteinCubic.O)^4*(if negative then -z.2 else z.2)=
    (u : ActualEisensteinCubic.O)^4*(if negative then -w.2 else w.2) at hs
  have hz := mul_left_cancel₀ (pow_ne_zero 4 u.ne_zero) hs
  apply Prod.ext hf
  cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,neg_inj] using hz

theorem childLabelRotation_norm (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    ‖eisEmbedding (childLabelRotation u negative z).2‖^2=‖eisEmbedding z.2‖^2 := by
  cases negative <;> simp only [childLabelRotation,Bool.false_eq_true,ite_false,ite_true,
    map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_pow,one_mul,map_neg,norm_neg]

theorem childLabelRotation_ne_zero (u : ActualEisensteinCubic.Oˣ) (negative : Bool) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)
    (hz : z.2≠0) : (childLabelRotation u negative z).2≠0 := by
  apply mul_ne_zero (pow_ne_zero 4 u.ne_zero)
  cases negative <;> simpa using hz

section
variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_label_mul (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (u f z : ActualEisensteinCubic.O) :
    fixedChildRow p hp hcop hg pool Ψ m H (u*f) z=
      fixedChildRow p hp hcop hg pool Ψ m H f (u^4*z) := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,finiteSquarefreeRow_mul,row_pow,mul_pow]
  ring

theorem idealChildRow_eq_rotated (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ) (z : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) :
    idealChildRow p hp hcop hg pool Ψ m H negative u z=
      fixedChildRow p hp hcop hg pool Ψ m H
        (ConcretePrimeRowBridge.idealGenerator (childLabelRotation u negative z).1)
        (childLabelRotation u negative z).2 := by
  exact fixedChildRow_label_mul p hp hcop hg pool Ψ m H (u : ActualEisensteinCubic.O) _ _

def canonicalSmoothedEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) : ℝ :=
  (∑I∈labels,nonzeroRowMajorantSum
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re

theorem canonicalSmoothedEnergy_nonneg (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    0≤ canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  unfold canonicalSmoothedEnergy
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro I hI
  have he := finite_nonzero_row_energy_le_majorant
    (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) ∅ K hK
    (by simp) (by simp)
  simpa using he

theorem canonicalSmoothedEnergy_zero_correction (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (K : ℝ) (hK : 0<K) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K=
      (∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
        (‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) z‖^2:ℝ)).re-
      ∑I∈labels,‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I) 0‖^2 := by
  unfold canonicalSmoothedEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
    Complex.re_sum,Complex.ofReal_re]

theorem idealChildRow_energy_le_canonical (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (H : Finset ι → ℂ) (negative : Bool) (u : ActualEisensteinCubic.Oˣ)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (K : ℝ) (hK : 0<K)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    (∑z∈T,‖idealChildRow p hp hcop hg pool Ψ m H negative u z‖^2)≤
      canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K := by
  let f : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O → ℝ := fun z=>
    ‖fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator z.1) z.2‖^2
  let R := (firstFrequencyDisk K).erase 0
  have hsub : T.image (childLabelRotation u negative)⊆labels.product R := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    apply Finset.mem_product.mpr
    refine ⟨hlabels z hz,Finset.mem_erase.mpr ⟨childLabelRotation_ne_zero u negative z (hzero z hz),?_⟩⟩
    apply (mem_firstFrequencyDisk K _).mpr
    rw [childLabelRotation_norm]
    exact hrows z hz
  calc
    _ = ∑w∈T.image (childLabelRotation u negative),f w := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        rw [idealChildRow_eq_rotated]
      · exact fun _ _ _ _ he=>childLabelRotation_injective u negative he
    _ ≤ ∑w∈labels.product R,f w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>sq_nonneg _)
    _ = ∑I∈labels,∑z∈R,f (I,z) := by rw [Finset.product_eq_sprod,Finset.sum_product]
    _ ≤ ∑I∈labels,(nonzeroRowMajorantSum
        (fixedChildRow p hp hcop hg pool Ψ m H (ConcretePrimeRowBridge.idealGenerator I)) K).re := by
      apply Finset.sum_le_sum
      intro I hI
      apply finite_nonzero_row_energy_le_majorant _ R K hK
      · intro z hz
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        exact (mem_firstFrequencyDisk K z).mp (Finset.mem_erase.mp hz).2
      · exact fun z hz=>(Finset.mem_erase.mp hz).1
    _ = _ := by unfold canonicalSmoothedEnergy; rw [Complex.re_sum]

def canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K : ℝ) : ℝ :=
  canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels (fun S=>V (columnLog p X S)) K

end

def orientedLogProfile (negative : Bool) (V : ℝ → ℂ) : ℝ → ℂ :=
  if negative then fun s=>star (V s) else V

theorem fixedSecondTest_zero_profile {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) :
    fixedSecondTest p V X 0 0 negative=(fun S=>orientedLogProfile negative V (columnLog p X S)) := by
  funext S
  cases negative <;> simp [fixedSecondTest,orientedLogProfile,JointLogSeparation.fixedColumnTest,FourierBridge.logPhase]

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.CanonicalLogEnergy -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_le_canonicalSmoothed (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels
        (fixedSecondTest p V X a b testNegative) K := by
  apply idealChildRow_unit_energy_le
  intro u
  exact idealChildRow_energy_le_canonical p hp hcop hg pool Ψ m _ rowNegative u
    T labels K hK hlabels hrows hzero

theorem childEnergy_le_canonicalLogEnergy (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalLogEnergy p hp hcop hg pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m labels
        (orientedLogProfile testNegative V) X K := by
  rw [childEnergy_normHeight p hp hcop hg pool Ψ m T V X a b hX testNegative rowNegative]
  simpa only [canonicalLogEnergy,fixedSecondTest_zero_profile] using
    childEnergy_le_canonicalSmoothed p hp hcop hg pool
      (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m T labels V X K 0 0 hK
      testNegative rowNegative hlabels hrows hzero

theorem childEnergy_le_canonicalLogEnergy_actual_labels (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ)
    (X K a b : ℝ) (hX : 0<X) (hK : 0<K) (testNegative rowNegative : Bool)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b≤
      6*canonicalLogEnergy p hp hcop hg pool
        (normHeightTwist Ψ (secondSignedHeight testNegative a b)) m (T.image Prod.fst)
        (orientedLogProfile testNegative V) X K :=
  childEnergy_le_canonicalLogEnergy p hp hcop hg pool Ψ m T (T.image Prod.fst) V X K a b hX hK
    testNegative rowNegative (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hrows hzero

end SecondPassIntegration

namespace CanonicalRowCompletion

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

variable {ι : Type*} [DecidableEq ι]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildRow_coefficient_expansion
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    fixedChildRow p hp hcop hg pool Ψ m H f z =
      ∑ T ∈ pool.powerset,
        canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z * H T := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  simp only [secondChildColumn, canonicalSourceCoefficient]
  ring

theorem reopenedCanonicalRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (H : Finset ι → ℂ) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
          canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) * H T := by
  unfold reopenedCanonicalRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

theorem canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      fixedChildRow p hp hcop hg pool Ψ m
        (fun T => W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow p hp hcop hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z
  have hsep := reopening_finite_sum W a b ha hs hW V hV Q pool.powerset β A n
    (primeProductNorm p) B ell X hB hell hX hn hn'
    (fun T _ => primeProductNorm_pos p hp T)
  calc
    _ = ∑ v ∈ Q, ∑ T ∈ pool.powerset, (β v * A v T) *
        ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ *
          W (primeProductNorm p T/(X/(n v)^3))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [fixedChildRow_coefficient_expansion p hp hcop hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [A]
      ring
    _ = _ := by
      rw [hsep]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [reopenedCanonicalRow_integrand p hp hcop hg]
      rfl

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O
open CanonicalCubeSeparation JointLogSeparation

theorem cube_coefficient_restore (H₀ : ℝ) (Ψ : ActualEisensteinCubic.O →* ℂ) (I : Ideal ActualEisensteinCubic.O)
    (hI : I ≠ 0) :
    reopenedCubeCoefficient H₀ Ψ I * (Ideal.absNorm I : ℂ)⁻¹ =
      largeCubeCoefficient H₀ I * cubeWeight Ψ I := by
  have hN : (Ideal.absNorm I : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)))
  unfold reopenedCubeCoefficient cubePhase
  field_simp

theorem cubeIdeal_row (F : Finset (Ideal ActualEisensteinCubic.O)) (hF : ∀ I ∈ F, Admissible I)
    (v : primePool F →₀ ℕ) (z : ActualEisensteinCubic.O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowHom z (cubeIdeal F v) =
      multiplicityRow (fun i => Ideal.span {poolPrimary F i}) (poolPrimary_good F hF)
        Finset.univ v z := by
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hprod : cubeIdeal F v = ∏ i : primePool F, (Ideal.span {poolPrimary F i}) ^ v i := by
    unfold cubeIdeal
    exact Finset.prod_congr rfl (fun i _ => by rw [poolPrimary_span F hF i])
  rw [hprod, idealRowHom_prime_powers]

def outsideCanonicalBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ∑ v ∈ Q,
    (largeCubeCoefficient H₀ (cubeIdeal F v) *
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3) : ℂ)⁻¹) *
      idealRowHom z (cubeIdeal F v)^3 *
      outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3)

theorem outsideCanonicalBin_separated
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀ =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  rw [← canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n Ψ m f z B ell X hB hell hX hn hn']
  unfold outsideCanonicalBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  change _ = (β v * (n v : ℂ)⁻¹ * _) * _ * _
  have hc' : β v * (n v : ℂ)⁻¹ =
      largeCubeCoefficient H₀ (cubeIdeal F v) *
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  rfl

end

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem fixedChildRow_zero_of_subunit {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    fixedChildRow p hp hcop hg pool Ψ m
      (fun T => W (primeProductNorm p T/X)) f z = 0 := by
  unfold fixedChildRow
  apply Finset.sum_eq_zero
  intro T hT
  have hw : W (primeProductNorm p T/X) = 0 := by
    by_contra hne
    have hh := (div_le_iff₀ hX).mp (hW _ hne)
    have hone := primeProductNorm_ge_one p hp T
    linarith
  simp only [secondChildColumn,hw,mul_zero]

theorem outsideCanonicalRow_zero_of_subunit
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hsub : b*X < 1) :
    outsideCanonicalRow S D hbad Ψ m f z W X = 0 := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold outsideCanonicalRow
  dsimp only
  exact fixedChildRow_zero_of_subunit _ _ _ _ _ Ψ m f z W b X hX hW hsub

def activeCubeExponents (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  ((outsideIdealsUpTo S D).image (cubeIndex F)).filter
    (fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)^3 ≤ b*X)

theorem outsideCanonicalBin_eq_active
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X H₀ : ℝ)
    (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) :
    outsideCanonicalBin S D hbad
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ =
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X < (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)^3 := by
    exact lt_of_not_ge (fun hh => hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0 < (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)^3) < 1 := by
    rw [← mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [outsideCanonicalRow_zero_of_subunit S D hbad Ψ m f z W b _
    (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem outsideCanonicalRow_reopened_active
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  have hh := outsideCanonicalRow_reopened_exponents S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD
  change _ = _ + outsideCanonicalBin S D hbad
    ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    Ψ m f z W X H₀ at hh
  rwa [outsideCanonicalBin_eq_active S D hbad Ψ m f z W b X H₀ hX hW] at hh

theorem activeCubeExponents_norm_bound
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) :
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ max 1 (b*X) := by
  have hcube := (Finset.mem_filter.mp hv).2
  have hN := norm_at_least_one _ (cubeIdeal_ne_zero (InitialMeanSquare.outsideSquarefreeIdeals S D) v)
  let n := (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
  have hone : 1 ≤ n := hN
  have hnn : n ≤ n^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (show 0 ≤ n^2+n by positivity)]
  exact (hnn.trans hcube).trans (le_max_right _ _)

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

def cubeLogIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) : ℕ :=
  normLogBin (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)

def cubeLogRange (b X : ℝ) : Finset ℕ :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)

def activeCubeLogBin (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ) :
    Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) :=
  (activeCubeExponents S D b X).filter (fun v => cubeLogIndex S D v = j)

theorem activeCubeLogIndex_mem (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) : cubeLogIndex S D v ∈ cubeLogRange b X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact normLogBin_mono
    (lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v)))
    (activeCubeExponents_norm_bound S D b X v hv)

theorem activeCubeLogBin_norms (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeLogBin S D b X j) :
    normLogScale j ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ∧
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*normLogScale j := by
  have hj := (Finset.mem_filter.mp hv).2
  rw [← hj]
  have hh := normLogBin_scale_bounds
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
    (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  exact ⟨hh.1,by simpa only [mul_comm,cubeLogIndex] using hh.2⟩

theorem cubeLogRange_card (b X : ℝ) :
    (cubeLogRange b X).card = normLogBin (max 1 (b*X)) + 1 := by
  exact Finset.card_range _

theorem sum_activeCubeLogBins {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ)
    (a : (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ) → M) :
    (∑ v ∈ activeCubeExponents S D b X, a v) =
      ∑ j ∈ cubeLogRange b X, ∑ v ∈ activeCubeLogBin S D b X j, a v := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun v hv => activeCubeLogIndex_mem S D b X v hv) a

theorem outsideCanonicalBin_log_bins
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (W : ℝ → ℂ) (b X H₀ : ℝ) :
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ =
      ∑ j ∈ cubeLogRange b X,
        outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

theorem outsideCanonicalRow_reopened_binned
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        ∑ j ∈ cubeLogRange b X,
          outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  rw [outsideCanonicalRow_reopened_active S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD,
    outsideCanonicalBin_log_bins]

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels

theorem nonzeroRowMajorantSum_exact_disk (P : ActualEisensteinCubic.O → ℂ) (K : ℝ) (hK : 0<K) :
    nonzeroRowMajorantSum P K=
      ∑z∈(firstFrequencyDisk (2*K)).erase 0,
        rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ) := by
  unfold nonzeroRowMajorantSum
  have hz (z : ActualEisensteinCubic.O) (hz : z∉(firstFrequencyDisk (2*K)).erase 0) :
      (if z=0 then 0 else rowMajorant (‖eisEmbedding z‖^2/K)*(‖P z‖^2:ℝ))=0 := by
    by_cases hzero : z=0
    · simp [hzero]
    have hn : z∉firstFrequencyDisk (2*K) := by
      intro hm
      exact hz (Finset.mem_erase.mpr ⟨hzero,hm⟩)
    have hlarge : 2<‖eisEmbedding z‖^2/K :=
      (lt_div_iff₀ hK).mpr (outside_firstFrequencyDisk (2*K) z hn)
    rw [ite_eq_right hzero,rowMajorant_zero _ hlarge,zero_mul]
  rw [tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro z hz
  rw [ite_eq_right (Finset.mem_erase.mp hz).1]

def canonicalTerminalConstant (A M : ℝ) : ℝ :=
  2*128^4*SchwartzMap.seminorm ℝ 0 0 rowMajorant*(Real.exp A*M)^2

theorem canonicalTerminalConstant_nonneg (A M : ℝ) : 0≤ canonicalTerminalConstant A M := by
  unfold canonicalTerminalConstant
  positivity

theorem fixedDepthRank_zero_iff (Z K : ℝ) (hZ : 1<Z) (hK : 0<K) :
    fixedDepthRank Z K=0 ↔ K≤1 := by
  rw [fixedDepthRank,Nat.ceil_eq_zero]
  constructor
  · intro h
    have hm := (div_le_iff₀ (Real.log_pos hZ)).mp h
    apply (Real.log_nonpos_iff hK.le).mp
    nlinarith
  · intro h
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hm := (Real.log_nonpos_iff hK.le).mpr h
    nlinarith

theorem smallColumn_row_le_label (m : ActualEisensteinCubic.O) (hm : m≠0) (X F K : ℝ)
    (hX : X≤1) (hF : 0≤F) (hK : 0≤K)
    (hinv : K*‖eisEmbedding m‖^2≤X*F) : K≤F := by
  have hn := element_norm_ge_one m hm
  have h1 := mul_le_mul_of_nonneg_left hn hK
  have h2 := mul_le_mul_of_nonneg_right hX hF
  nlinarith

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSmoothedEnergy_uniform_row_bound (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (H : Finset ι → ℂ) (F K D : ℝ)
    (hF : 1≤F) (hK : 1≤K) (_hD : 0≤D)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F)
    (hrow : ∀I∈labels,∀z,‖fixedChildRow p hp hcop hg pool Ψ m H
      (ConcretePrimeRowBridge.idealGenerator I) z‖≤D) :
    canonicalSmoothedEnergy p hp hcop hg pool Ψ m labels H K≤
      2*128^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*D^2 := by
  have hK0 : 0<K := zero_lt_one.trans_le hK
  let R := (firstFrequencyDisk (2*K)).erase 0
  have hR : (R.card:ℝ)≤128*(2*K) := by
    apply DescentFiberCost.finite_element_count_real R (2*K) (by linarith)
    exact fun z hz=>(mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hI : (labels.card:ℝ)≤128*F := DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hm : 0≤SchwartzMap.seminorm ℝ 0 0 rowMajorant := by positivity
  unfold canonicalSmoothedEnergy
  simp_rw [nonzeroRowMajorantSum_exact_disk _ K hK0]
  rw [Complex.re_sum]
  calc
    _ ≤ ∑I∈labels,∑z∈R,SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2 := by
      apply Finset.sum_le_sum
      intro I hIL
      rw [Complex.re_sum]
      apply Finset.sum_le_sum
      intro z hz
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      exact mul_le_mul
        ((Complex.re_le_norm _).trans (rowMajorant.norm_le_seminorm ℝ _))
        (pow_le_pow_left₀ (norm_nonneg _) (hrow I hIL z) 2) (sq_nonneg _) hm
    _ = (labels.card:ℝ)*R.card*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) := by simp; ring
    _ ≤ (128*F)*(128*(2*K))*(SchwartzMap.seminorm ℝ 0 0 rowMajorant*D^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hI hR (Nat.cast_nonneg _) (by linarith)) (by positivity)
    _ = _ := by ring

theorem canonicalLogEnergy_subunit (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X K A : ℝ) (hX : 0<X)
    (hV : ∀s,V s≠0→|s|≤A) (hsmall : X*Real.exp A<1) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K=0 := by
  have hcol (S : Finset ι) : V (columnLog p X S)=0 := by
    by_contra hn
    have hupper := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have hlower := primeProductNorm_ge_one p hp S
    linarith
  have hrow (f y : ActualEisensteinCubic.O) : fixedChildRow p hp hcop hg pool Ψ m
      (fun S=>V (columnLog p X S)) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,hcol,mul_zero]
  simp only [canonicalLogEnergy,canonicalSmoothedEnergy,nonzeroRowMajorantSum,hrow,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,
    Finset.sum_const_zero,Complex.zero_re]

theorem canonicalLogEnergy_terminal
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X F K A M : ℝ)
    (hX : 0<X) (hF : 1≤F) (hK : 1≤K) (hKF : K≤F) (hM : 0≤M)
    (hV : ∀s,‖V s‖≤M) (hVs : ∀s,V s≠0→|s|≤A)
    (hI0 : ∀I∈labels,I≠⊥) (hIF : ∀I∈labels,(Ideal.absNorm I:ℝ)≤F) :
    canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K≤ canonicalTerminalConstant A M*(X*F)^2 := by
  by_cases hscale : 1≤X*Real.exp A
  · have hcol : ∀S,V (columnLog p X S)≠0→primeProductNorm p S≤X*Real.exp A :=
      fun S hn=>columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hVs _ hn))
    have hrow (I : Ideal ActualEisensteinCubic.O) (hI : I∈labels) (z : ActualEisensteinCubic.O) :
        ‖fixedChildRow p hp hcop hg pool Ψ m (fun S=>V (columnLog p X S))
          (ConcretePrimeRowBridge.idealGenerator I) z‖≤128*(X*Real.exp A)*M :=
      fixedChildRow_elementary p hp hcop hg hc hinj pool Ψ hΨ m _ z _ (X*Real.exp A) M hscale hM
        (fun S=>hV _) hcol
    have hb := canonicalSmoothedEnergy_uniform_row_bound p hp hcop hg pool Ψ m labels
      (fun S=>V (columnLog p X S)) F K (128*(X*Real.exp A)*M) hF hK (by positivity) hI0 hIF hrow
    change canonicalLogEnergy p hp hcop hg pool Ψ m labels V X K≤_ at hb
    calc
      _ ≤ 2*128^2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*F*K*(128*(X*Real.exp A)*M)^2 := hb
      _ = canonicalTerminalConstant A M*X^2*F*K := by unfold canonicalTerminalConstant; ring
      _ ≤ canonicalTerminalConstant A M*X^2*F*F :=
        mul_le_mul_of_nonneg_left hKF (by have := canonicalTerminalConstant_nonneg A M; positivity)
      _ = _ := by ring
  · rw [canonicalLogEnergy_subunit p hp hcop hg pool Ψ m labels V X K A hX hVs (lt_of_not_ge hscale)]
    exact mul_nonneg (canonicalTerminalConstant_nonneg A M) (sq_nonneg _)

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian -/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

def kernelCoordinateLaplacian (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,
    fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j))+
    (p 2:ℂ)*fderiv ℝ (kernelTestField f) p (euclideanCoordinateVector 2)

lemma kernelCoreLift_laplacian (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∈kernelChartCore χ) :
    upperPositiveLaplacian (kernelCoreLift χ f) p=kernelCoordinateLaplacian f p := by
  have he := kernelCoreLift_eventually_eq χ f p hp
  have hd (j : Fin 3) : (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  have hdd (j : Fin 3) :
      (∂_{euclideanCoordinateVector j} (∂_{euclideanCoordinateVector j} (kernelCoreLift χ f))) p=
        fderiv ℝ (fun q => fderiv ℝ (kernelTestField f) q (euclideanCoordinateVector j)) p
          (euclideanCoordinateVector j) := by
    change fderiv ℝ (fun q => fderiv ℝ (kernelCoreLift χ f) q (euclideanCoordinateVector j)) p
      (euclideanCoordinateVector j)=_
    rw [(hd j).fderiv_eq]
  simp only [upperPositiveLaplacian,kernelCoordinateLaplacian,hdd,
    SchwartzMap.lineDerivOp_apply_eq_fderiv,he.fderiv_eq]

lemma kernelDirichletForm_coordinate_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp)]
        rfl
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

lemma kernelDirichletForm_sum_right {ι : Type*} (f : kernelSmoothTests)
    (t : Finset ι) (g : ι→kernelSmoothTests) :
    kernelDirichletForm f (∑i∈t,g i)=∑i∈t,kernelDirichletForm f (g i) := by
  induction t using Finset.induction_on with
  | empty =>
    have hz := kernelDirichletForm_smul_right 0 f (0 : kernelSmoothTests)
    simpa only [Finset.sum_empty,zero_smul,zero_mul] using hz
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi,kernelDirichletForm_add_right,ih]

theorem kernelDirichletForm_coordinate_equation (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (g : kernelSmoothTests) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_coordinate_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i) A hA heq
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

lemma kernelL2_inner_toLp_smooth (A : KernelQuotient→ℂ)
    (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel)) (g : kernelSmoothTests) :
    inner ℂ (hA.toLp A) (kernelSmoothTestsToL2 g)=
      ∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  calc
    _ = ∫q,inner ℂ ((hA.toLp A) q) (kernelSmoothTestsToL2 g q)
        ∂integralQuotientVolume globalKubotaKernel := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp,(kernelSmoothTests_memLp g).coeFn_toLp] with q hq hg
      change inner ℂ ((hA.toLp A) q) (((kernelSmoothTests_memLp g).toLp g.1) q)=_
      rw [hq,hg,RCLike.inner_apply]
      simp only [RCLike.star_def,mul_comm]

lemma kernelCoordinateLaplacian_form (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient v)=
      inner ℂ (hA.toLp A) (kernelEnergyMass v) := by
  exact kernelEnergyGraphCore_dense.induction_on v
    (isClosed_eq (by fun_prop : Continuous (fun u : KernelEnergyGraph =>
      inner ℂ (kernelEnergyGradient (kernelEnergyGraphCore f)) (kernelEnergyGradient u)))
      (by fun_prop : Continuous (fun u : KernelEnergyGraph => inner ℂ (hA.toLp A) (kernelEnergyMass u))))
    (fun g => by
      rw [kernelEnergyGradient_core,kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelGradientToL2_inner,kernelL2_inner_toLp_smooth]
      exact kernelDirichletForm_coordinate_equation f A hA heq g)

theorem kernelEnergyLaplacian_graph_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    (kernelSmoothTestsToL2 f,hA.toLp A)∈kernelEnergyLaplacian.graph := by
  have hu : kernelEnergyGraphCore f=
      kernelVariationalSolution (kernelSmoothTestsToL2 f+hA.toLp A) := by
    apply kernelVariationalSolution_unique
    intro v
    rw [kernelEnergyMass_core,kernelCoordinateLaplacian_form f A hA heq,inner_add_left]
  have hm := congrArg kernelEnergyMass hu
  rw [kernelEnergyMass_core] at hm
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  exact hm.symm

lemma kernelEnergyLaplacian_domain_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelSmoothTestsToL2 f∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_graph_of_coordinate f A hA heq)

lemma kernelEnergyLaplacian_apply_of_coordinate (f : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelEnergyLaplacian ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩=
      hA.toLp A :=
  kernelEnergyLaplacian.mem_graph_snd_inj
    (kernelEnergyLaplacian.mem_graph ⟨kernelSmoothTestsToL2 f,kernelEnergyLaplacian_domain_of_coordinate f A hA heq⟩)
    (kernelEnergyLaplacian_graph_of_coordinate f A hA heq) rfl

end CubicEisenstein

section

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem densityChildEnergy_from_canonical_state
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X F K E t₁ t₂ : ℝ) (J : ℕ) (hX : 0<X) (hK : 0<K) (hE : 0≤E)
    (hlabels : ∀z∈T,z.1∈labels)
    (hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K) (hzero : ∀z∈T,z.2≠0)
    (h₁ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m labels
      (orientedLogProfile true V₁) X K≤E*(X*F)^2*(1+‖t‖)^(2*J))
    (h₂ : ∀t,canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m labels
      (orientedLogProfile false V₂) X K≤E*(X*F)^2*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X X (2*J)≤
      6*E*(X*F)^2*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have hleft (t : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m T V₁ X true false 0 0≤
      (6*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m
      T labels V₁ X K 0 0 hX hK true false hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,ite_true,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₁ t) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hright (t : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m T V₂ X false true 0 0≤
      (6*E*(X*F)^2)*(1+‖t‖)^(2*J) := by
    have hh := childEnergy_le_canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m
      T labels V₂ X K 0 0 hX hK false true hlabels hrows hzero
    simp only [normHeightTwist_twice,secondSignedHeight,Bool.false_eq_true,ite_false,sub_self,add_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (h₂ t) (by norm_num : (0:ℝ)≤6)).trans_eq (by ring))
  have hb : 0≤6*E*(X*F)^2 := by positivity
  have hd := densityChildEnergy_normHeight_polynomial p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂
    X X t₁ t₂ (6*E*(X*F)^2) (6*E*(X*F)^2) J hX hX hb hb hleft hright
  rw [Real.mul_self_sqrt hb] at hd
  exact hd

end SecondPassIntegration

namespace SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels ConcreteTraceCRT

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

def globalCanonicalLabels (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) : Finset (Ideal ActualEisensteinCubic.O) :=
  (globalArithmeticTargets p source side q j).image Prod.fst

include hp in
theorem globalCanonicalLabels_bounds (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hk : ∀x∈source,x.source.frequency≠0) :
    ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  have hb := globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨hb.1,globalArithmeticTargets_squarefree p source side q j z hz,hb.2.1⟩

end SecondPassArithmetic
end

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct jLabel)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O)

omit [DecidableEq ι] in
theorem actualSecondLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    IsCoprime (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂) bad := by
  have hprod (S : Finset ι) : IsCoprime (∏i∈S,Ideal.span {p i}) bad :=
    IsCoprime.prod_left (fun i _=>hbad i)
  have hJ : IsCoprime (Ideal.span {jLabel p B (fun i=>v₁ i+v₂ i) ε₁ ε₂}) bad := by
    simp only [jLabel,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
    exact IsCoprime.prod_left (fun i _=>(hbad i).pow_left)
  exact ((hJ.mul_left (hprod C)).mul_left (hprod E)).mul_left (hprod V)

theorem globalNewLabel_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad) (x : GlobalSecondData ι) :
    IsCoprime (SecondPassFiber.newLabel (globalSecondTuple p x)) bad := by
  exact actualSecondLabel_coprime p bad hbad x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

theorem globalCanonicalLabels_coprime (bad : Ideal ActualEisensteinCubic.O)
    (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O × Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex) :
    ∀I∈globalCanonicalLabels p source side q j,IsCoprime I bad := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact globalNewLabel_coprime p bad hbad x

end SecondPassArithmetic

namespace CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O

theorem finite_integral_energy_polynomial {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ k, Integrable (fun t => b t*φ k t))
    (hbound : ∀ t, (∑ k, ‖φ k t‖^2) ≤ E*(1+|t|)^(2*d)) :
    (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖ ≤ (‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖b t*φ k t‖^2) ≤ _
    simp only [norm_mul,mul_pow,← Finset.mul_sum,Real.sq_sqrt hE]
    have hp : (1+|t|)^(2*d) = ((1+|t|)^d)^2 := by
      rw [← pow_mul,Nat.mul_comm d 2]
    calc
      _ ≤ ‖b t‖^2 * (E*(1+|t|)^(2*d)) :=
        mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
      _ = _ := by rw [hp]; ring
  have he : (∫ t : ℝ, F t) = e.symm (fun k => ∫ t : ℝ, b t*φ k t) := by
    rw [show F = (fun t => e.symm (fun k => b t*φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t : ℝ, b t*φ k t)‖ ≤
      (∫ t : ℝ, ‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    rw [← he,← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _)
      (Filter.Eventually.of_forall hF)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hh
  change (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2) ≤
    (∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 * E at hh
  simpa only [mul_comm] using hh

theorem norm_add_sum_sq_le {κ : Type*} (s : Finset κ) (a : ℂ) (b : κ → ℂ) :
    ‖a + ∑ k ∈ s, b k‖^2 ≤ 2*(‖a‖^2 + s.card*∑ k ∈ s, ‖b k‖^2) := by
  have hs : ‖∑ k ∈ s, b k‖^2 ≤ (s.card : ℝ)*∑ k ∈ s, ‖b k‖^2 := by
    calc
      _ ≤ (∑ k ∈ s, ‖b k‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by
        simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
          using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖b k‖)
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (∑ k ∈ s, b k)) 2
  nlinarith [sq_nonneg (‖a‖ - ‖∑ k ∈ s, b k‖)]

theorem outsideCanonicalRow_binned_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 ≤
      2*X*(‖shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀‖^2 +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          ‖outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀)
    (fun j => outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀)
  rw [← outsideCanonicalRow_reopened_binned S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD] at hs
  have hn : ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 =
      X*‖(Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

def IsBaseRayTwist (base Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  Ψ=base ∨ ∃χ : RayCharacter, Ψ=rayMonoid χ*base

def baseRayOrbit (base : ActualEisensteinCubic.O→*ℂ) : Finset (ActualEisensteinCubic.O→*ℂ) :=
  insert base (Finset.univ.image (fun χ : RayCharacter => rayMonoid χ*base))

lemma mem_baseRayOrbit (base Ψ : ActualEisensteinCubic.O→*ℂ) : Ψ∈baseRayOrbit base ↔ IsBaseRayTwist base Ψ := by
  simp only [baseRayOrbit,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and,IsBaseRayTwist]
  constructor
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩
  · rintro (h|⟨χ,h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨χ,h.symm⟩

lemma baseRayOrbit_card (base : ActualEisensteinCubic.O→*ℂ) : (baseRayOrbit base).card≤17 := by
  have h1 := Finset.card_insert_le base (Finset.univ.image (fun χ : RayCharacter => rayMonoid χ*base))
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset RayCharacter))
    (f := fun χ : RayCharacter => rayMonoid χ*base)
  have h3 := RayFourExpansion.rayCharacter_card_le
  simp only [Finset.card_univ] at h2
  unfold baseRayOrbit
  omega

lemma rayMonoid_mul (χ η : RayCharacter) : rayMonoid (χ*η)=rayMonoid χ*rayMonoid η := by
  ext x
  simp only [rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.mul_apply,MonoidHom.mul_apply]

lemma conjugateRayMonoid_eq (χ : RayCharacter) : conjugateRayMonoid χ=rayMonoid (star χ) := by
  ext x
  simp only [conjugateRayMonoid_apply,rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.star_apply]

lemma IsBaseRayTwist.mul_ray {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ) (χ : RayCharacter) :
    IsBaseRayTwist base (rayMonoid χ*Ψ) := by
  rcases hΨ with h|⟨η,h⟩
  · exact Or.inr ⟨χ,by rw [h]⟩
  · exact Or.inr ⟨χ*η,by rw [h,rayMonoid_mul,mul_assoc]⟩

lemma firstCoreTwist_single_ray (side : Bool) (χ : RayCharacter) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (r : FirstCoreIndex) :
    firstCoreTwist side χ Ψ r =
      rayMonoid ((if side then star χ else χ)*FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2)*Ψ := by
  rw [rayMonoid_mul]
  have hcore : FirstPassCubeLabels.coreRayTwist side r.1 r.2.2 =
      rayMonoid (FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2) := rfl
  unfold firstCoreTwist sideRayMonoid
  rw [hcore]
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,conjugateRayMonoid_eq] <;> ac_rfl

lemma IsBaseRayTwist.firstCore {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) :
    IsBaseRayTwist base (firstCoreTwist side χ Ψ r) := by
  rw [firstCoreTwist_single_ray]
  exact hΨ.mul_ray _

lemma secondRayMinus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayMinus Ψ r=rayMonoid (star r.2.2*star r.1.2)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayMinus,conjugateRayMonoid_eq,mul_assoc]

lemma secondRayPlus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayPlus Ψ r=rayMonoid (r.2.1*star r.1.1)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayPlus,conjugateRayMonoid_eq,mul_assoc]

lemma IsBaseRayTwist.secondMinus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayMinus Ψ r) := by
  rw [secondRayMinus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.secondPlus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayPlus Ψ r) := by
  rw [secondRayPlus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.norm_le {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (hbase : ∀x,‖base x‖≤1) (x : ActualEisensteinCubic.O) : ‖Ψ x‖≤1 := by
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x
  · rw [MonoidHom.mul_apply,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (FiniteRayExpansion.norm_char_le_one χ _)).trans (hbase x)

def FactorsModulo (Q : Ideal ActualEisensteinCubic.O) (Ψ : ActualEisensteinCubic.O→*ℂ) : Prop :=
  ∀x y : ActualEisensteinCubic.O,x-y∈Q → Ψ x=Ψ y

lemma IsBaseRayTwist.factorsModulo {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (Q : Ideal ActualEisensteinCubic.O) (hbase : FactorsModulo Q base) :
    FactorsModulo (Q*Ideal.span {(4:ActualEisensteinCubic.O)}) Ψ := by
  intro x y hxy
  have hb := hbase x y (Ideal.mul_le_left hxy)
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hb
  · simp only [MonoidHom.mul_apply]
    rw [hb]
    congr 1
    exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
      (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))

def initialBase {q : ℕ} (χ : DirichletCharacter ℂ q) : ActualEisensteinCubic.O→*ℂ :=
  InitialMeanSquare.conjugateMonoid (InitialMeanSquare.normCharacter χ)

lemma initialBase_norm {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ActualEisensteinCubic.O) :
    ‖initialBase χ x‖≤1 := by
  change ‖star (InitialMeanSquare.normCharacter χ x)‖≤1
  rw [norm_star]
  exact InitialMeanSquare.normCharacter_norm_le_one χ x

lemma initial_minus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayMinus (initialBase χ) r) :=
  IsBaseRayTwist.secondMinus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

lemma initial_plus_member {q : ℕ} (χ : DirichletCharacter ℂ q) (r : SecondRayIndex) :
    IsBaseRayTwist (initialBase χ) (secondRayPlus (initialBase χ) r) :=
  IsBaseRayTwist.secondPlus (Or.inl rfl : IsBaseRayTwist (initialBase χ) (initialBase χ)) r

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

lemma norm_eval_mod (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

theorem normCharacter_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (InitialMeanSquare.normCharacter χ) := by
  intro x y hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c := (coords y).1
  let d := (coords y).2
  let e := (coords z).1
  let f := (coords z).2
  have hy : y=eval c d := (eval_coords y).symm
  have hx : x=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
    calc
      x=y+(m : ActualEisensteinCubic.O)*z := by linear_combination hz
      _=eval (c+(m : ℤ)*e) (d+(m : ℤ)*f) := by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  change χ (Ideal.absNorm (Ideal.span {x}))=χ (Ideal.absNorm (Ideal.span {y}))
  congr 1
  rw [hx,hy,norm_eval_mod,norm_eval_mod]
  simp

theorem initialBase_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) :
    FactorsModulo (Ideal.span {(m : ActualEisensteinCubic.O)}) (initialBase χ) := by
  intro x y hxy
  change star (InitialMeanSquare.normCharacter χ x)=star (InitialMeanSquare.normCharacter χ y)
  rw [normCharacter_factorsModulo χ x y hxy]

def fixedBaseConductor (m : ℕ) : Ideal ActualEisensteinCubic.O := Ideal.span {(m : ActualEisensteinCubic.O)}*Ideal.span {(4 : ActualEisensteinCubic.O)}

theorem initialOrbit_factorsModulo {m : ℕ} (χ : DirichletCharacter ℂ m) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : IsBaseRayTwist (initialBase χ) Ψ) : FactorsModulo (fixedBaseConductor m) Ψ :=
  hΨ.factorsModulo _ (initialBase_factorsModulo χ)

lemma fixedBaseConductor_principal (m : ℕ) :
    fixedBaseConductor m=Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)} := by
  rw [fixedBaseConductor,Ideal.span_singleton_mul_span_singleton]
  congr 1
  push_cast
  ring_nf

lemma fixedBaseConductor_ne_zero (m : ℕ) (hm : m≠0) : fixedBaseConductor m≠0 := by
  rw [fixedBaseConductor_principal]
  change Ideal.span {((4*m : ℕ) : ActualEisensteinCubic.O)}≠⊥
  rw [ne_eq,Ideal.span_singleton_eq_bot]
  exact_mod_cast Nat.mul_ne_zero (by decide : (4:ℕ)≠0) hm

lemma fixedBaseConductor_norm (m : ℕ) (hm : m≠0) :
    Ideal.absNorm (fixedBaseConductor m)=16*m^2 := by
  rw [fixedBaseConductor_principal]
  have h := rational_modulus_card (4*m) (Nat.mul_ne_zero (by decide) hm)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  rw [h]
  ring

end CanonicalCoefficientClass

end

end OAI

end

