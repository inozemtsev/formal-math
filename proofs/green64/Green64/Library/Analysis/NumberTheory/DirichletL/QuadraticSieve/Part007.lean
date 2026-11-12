module

public import Green64.Library.OAI.NumberTheory.DirichletL.CubicSieve.ScaleCaps

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / QuadraticSieve / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison -/

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

namespace CanonicalQuadraticSieve

section

theorem hasSieveExponent_one_of_approximation
    (happrox : ∀ η : ℝ, 0<η → ∃ α : ℝ, α≤1+η ∧ HasSieveExponent α) :
    HasSieveExponent 1 := by
  intro ε hε
  have he : 0<ε/2 := by positivity
  obtain ⟨α,hα,h⟩ := happrox (ε/2) he
  obtain ⟨C,hC,hbound⟩ := h (ε/2) he
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  have hM0 : 0≤M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hNmn : N≤M*N := by nlinarith
  have hQ : 1≤(M*N)^(ε/2) := Real.one_le_rpow hMN he.le
  have hnα : N^α ≤ (M*N)^(ε/2)*N := by
    calc
      _ ≤ N^(1+ε/2) := Real.rpow_le_rpow_of_exponent_le hN hα
      _ = N*N^(ε/2) := by rw [Real.rpow_add hN0,Real.rpow_one]
      _ ≤ N*(M*N)^(ε/2) := by gcongr
      _ = _ := mul_comm _ _
  have hsum : M+N^α ≤ (M*N)^(ε/2)*(M+N) := by
    nlinarith [mul_le_mul_of_nonneg_right hQ hM0]
  calc
    _ ≤ C*(M*N)^(ε/2)*(M+N^α) := hbound M N hM hN
    _ ≤ C*(M*N)^(ε/2)*((M*N)^(ε/2)*(M+N)) := by gcongr
    _ = C*(M*N)^ε*(M+N^(1:ℝ)) := by
      rw [Real.rpow_one]
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2) = (M*N)^ε := by
        rw [← Real.rpow_add (by positivity : 0<M*N)]
        congr 1
        ring
      calc
        _ = C*((M*N)^(ε/2)*(M*N)^(ε/2))*(M+N) := by ring
        _ = _ := by rw [hp]

def bootstrapExponent (n : ℕ) : ℝ := 1+1/((n:ℝ)+1)

theorem bootstrapExponent_gt_one (n : ℕ) : 1<bootstrapExponent n := by
  unfold bootstrapExponent
  have h : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  linarith

theorem bootstrapExponent_le_two (n : ℕ) : bootstrapExponent n≤2 := by
  have h : 1/((n:ℝ)+1)≤(1:ℝ) := by
    apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  unfold bootstrapExponent
  linarith

theorem bootstrapExponent_step (n : ℕ) :
    bootstrapExponent (n+1) = 2-1/bootstrapExponent n := by
  unfold bootstrapExponent
  push_cast
  field_simp
  ring

theorem hasSieveExponent_one_of_improvement
    (himprove : ∀ α : ℝ, 1<α → α≤2 → HasSieveExponent α → HasSieveExponent (2-1/α)) :
    HasSieveExponent 1 := by
  have hn : ∀ n : ℕ, HasSieveExponent (bootstrapExponent n) := by
    intro n
    induction n with
    | zero => norm_num [bootstrapExponent]; exact hasSieveExponent_two
    | succ n ih =>
      rw [bootstrapExponent_step]
      exact himprove _ (bootstrapExponent_gt_one n) (bootstrapExponent_le_two n) ih
  apply hasSieveExponent_one_of_approximation
  intro η hη
  obtain ⟨n,hnη⟩ := exists_nat_one_div_lt hη
  refine ⟨bootstrapExponent n,?_,hn n⟩
  unfold bootstrapExponent
  linarith

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def divisorTwist {n : Type} (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) : n → ℂ :=
  fun j => a j*quadraticRow (cols j) (idealGenerator q)

def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (6:ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealRange K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))

def centeredMaskedSource {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum G (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeRange G K => I.val) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M

def maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily G cols a W M - (6:ℂ)⁻¹ *
    maskedPrincipalSourceSum G (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeRange G K => I.val) cols a M

lemma finite_centering_identity {ι : Type*} (S : Finset ι) (w R D : ι → ℂ) (c h : ℂ) :
    (∑ q∈S, w q*(c*R q-h*D q)) = c*(∑ q∈S,w q*R q)-h*(∑ q∈S,w q*D q) := by
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem maskedPoissonDifference_centered {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (6:ℂ)*maskedPoissonDifference G W cols a M K =
      (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
      (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K +
      paperRadialFourier (quadraticSquareProfile W) 0 *
        ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K) := by
  rw [←actual_source_dual_density_cancellation cols a G hG M K hM.le hcols hray hGc hbad]
  unfold maskedPoissonDifference centeredRetainedDual centeredMaskedSource divisorTwist
  rw [maskedDualFamily_retained G hG cols a W M K hM hcols hray]
  simp only [quadraticSquareProfile_principal_equal]
  rw [finite_centering_identity]
  ring

theorem maskedPoissonDifference_norm_le {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
      (∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) +
      6*‖maskedDualTailFamily G cols a W M K‖ + ‖centeredMaskedSource G W cols a M K‖ +
      ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
        ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ := by
  rw [maskedPoissonDifference_centered G hG W cols a M K hM hcols hray hGc hbad]
  have hs : ‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ ≤
      ∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one q)
  calc
    _ ≤ (‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ +
        ‖(6:ℂ)*maskedDualTailFamily G cols a W M K‖) + ‖centeredMaskedSource G W cols a M K‖ +
        ‖paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K)‖ := by
      have h1 := norm_add_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K)
        (paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K))
      have h2 := norm_sub_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K) (centeredMaskedSource G W cols a M K)
      have h3 := norm_add_le
        (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q)
        ((6:ℂ)*maskedDualTailFamily G cols a W M K)
      linarith
    _ ≤ _ := by
      simp only [norm_mul]
      norm_num
      gcongr

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

theorem divisorTwist_norm_le {n : Type} (cols : n → Ideal O) (a : n → ℂ)
    (q : Ideal O) (j : n) : ‖divisorTwist cols a q j‖≤‖a j‖ := by
  rw [divisorTwist,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem retainedDualMajorant_coefficient_scale_le {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a a' : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0<N) (hM : 0≤M) (hF : 1≤F) (hT : 0≤T)
    (ha : ∀j, ‖a' j‖≤‖a j‖) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a' W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M 1 T a W := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' a a' ha ha
  have he0 := divisorEnergyFactor_nonneg ε hε N a' a'
  have he1 := divisorEnergyFactor_nonneg ε hε N a a
  have hea : (∑j, ‖a' j‖^2)≤∑j, ‖a j‖^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
  have hs := (supportConstant_pos ε hε).le
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have hF0 : 0<F := by linarith
  have hMF : M/F≤M := div_le_self hM hF
  have hNF : N≤F*N := by nlinarith
  have hMN : 2*M/(F*N)≤2*M/N :=
    div_le_div_of_nonneg_left (by positivity) hN hNF
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  simp only [div_one,one_mul]
  gcongr

theorem centeredRetainedDual_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_global l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT cols hc hcols hray a W
  classical
  have hqbound (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖centeredRetainedDual W cols a M K q‖ ≤
        (columnDyadicLength K+1:ℕ)*
          retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
    have hqd := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqd; exact hG hqd
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hh := hbound hexp hα deltaLoss hδ ε hε K N M (Ideal.absNorm q:ℝ) T hK hN hM
      (by linarith) hT cols hc hcols hray (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact retainedDualMajorant_coefficient_scale_le s C hC.le l hexp deltaLoss hδ ε hε
      (2*K) N M (Ideal.absNorm q:ℝ) T a (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
      (by linarith) (by linarith) hM.le hq1 (by linarith) (divisorTwist_norm_le cols a q)
  calc
    _ ≤ ∑_q∈idealDivisors G, (columnDyadicLength K+1:ℕ)*
        retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) :=
      Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  6*(256*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)

theorem HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by
  obtain ⟨sD,CD,hCD,hdual⟩ := centeredRetainedDual_sum_bound l
  obtain ⟨sS,CS,hCS,hsource⟩ := masked_source_principal_global l
  obtain ⟨sT,CT,hCT,htail⟩ := maskedDualTailFamily_bound A
  obtain ⟨CP,hCP,hprincipal⟩ := hexp.actual_principal_difference deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro n _ _ ε hε G hG hbad K N M T hK hN hM hT cols hc hcols hray hGc a W hW
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hcols0 : ∀j, Admissible (cols j) := fun j => (hcols j).1
  have hcolsu : ∀j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N :=
    fun j => ⟨(hcols j).1,(hcols j).2.2⟩
  have hd := hdual hexp hα deltaLoss hδ ε hε G hG.ne_zero K N M T hK hN hM0 hT cols hc hcols hray a W
  have hs := hsource hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM0 hT
    (coprimeSquarefreeRange G K)
    (fun I hI => mem_idealRange.mp (coprimeSquarefreeRange_subset_idealRange G hbad K hI))
    cols hc hcolsu hGc a (quadraticSquareProfile W)
    (by simpa only [quadraticSquareProfile_apply,zero_pow (by decide : 2≠0)] using hW)
  have ht := htail G cols a W M N K hG.ne_zero hc hM0 hN (by linarith)
    (fun j => ⟨(hcols j).1.1,(hcols j).2⟩)
  have hp := hprincipal cols hc M N K hM hN hK hcolsu hray
    (densityColumn cols a) G hG hbad ε hε
  have he := densityColumn_energy_le cols a (fun j => (hcols j).1.1)
  have hsupp := (supportConstant_pos ε hε).le
  have hp' : ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ ≤
      ((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2 := by
    apply hp.trans
    gcongr
  have hmain := maskedPoissonDifference_norm_le G hG.ne_zero W cols a M K hM0 hcols0 hray hGc hbad
  apply hmain.trans
  change _ ≤ _+_+_+_
  have hs' : ‖centeredMaskedSource G W cols a M K‖ ≤
      (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a
        (quadraticSquareProfile W) := hs
  exact add_le_add (add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left ht (by norm_num))) hs')
    (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))

end
section

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open DivisorBlockCauchy

theorem gcdRaySupport_energy_eq {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    (∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, if D∣cols j ∧ columnRay (cols j)=c then ‖a j‖^2 else 0 := by
  classical
  rw [Finset.sum_coe_sort (gcdRaySupport cols a D c) (fun j => ‖a j‖^2)]
  simp only [gcdRaySupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,ne_eq,not_true_eq_false,and_false,ite_self,zero_pow (by decide : 2≠0)]
  · simp only [hz,ne_eq,not_false_eq_true,and_true]

theorem gcdRaySupport_energy_ray_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (D : Ideal O) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) =
      ∑j, ‖if D∣cols j then a j else 0‖^2 := by
  classical
  simp_rw [gcdRaySupport_energy_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : D∣cols j
  · simp only [hd,true_and,ite_true]
    rw [Finset.sum_eq_single (columnRay (cols j))]
    · simp only [ite_true]
    · intro c hc hne
      exact ite_eq_right (Ne.symm hne)
    · simp
  · simp only [hd,false_and,ite_false,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem gcdRaySupport_energy_divisor_sum {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X : ℝ)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
      ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) ≤
      (divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [gcdRaySupport_energy_ray_sum]
  apply (divisor_mask_energy S cols hcols a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 (cols j) (hcols j)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hX j hz) hε.le) (divisorConstant_pos ε hε).le

theorem gcdRaySupport_weighted_sum_bound {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (S : Finset (Ideal O)) (cols : n → Ideal O)
    (hcols : ∀j, cols j≠0) (a : n → ℂ) (X C : ℝ) (hC : 0≤C)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j):ℝ)≤X)
    (F : Ideal O → EisensteinEPrimaryPhase.Coord → ℝ)
    (hF : ∀D∈S, ∀c, F D c≤C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) :
    (∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S, F D c) ≤
      C*(divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2 := by
  calc
    _ ≤ ∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        C*∑j : gcdRaySupport cols a D c, ‖a j.val‖^2 :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun D hD => hF D hD c))
    _ = C*(∑c : EisensteinEPrimaryPhase.Coord, ∑D∈S,
        ∑j : gcdRaySupport cols a D c, ‖a j.val‖^2) := by simp only [Finset.mul_sum]
    _ ≤ C*((divisorConstant ε hε*X^ε)*∑j, ‖a j‖^2) :=
      mul_le_mul_of_nonneg_left (gcdRaySupport_energy_divisor_sum ε hε S cols hcols a X hX) hC
    _ = _ := by ring

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

theorem divisorEnergyFactor_diagonal {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0<ε) (N : ℝ) (a : n → ℂ) :
    divisorEnergyFactor ε hε N a a =
      (256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑j, ‖a j‖^2 := by
  unfold divisorEnergyFactor
  have hs : 0≤∑j, ‖a j‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _),Real.mul_self_sqrt hs]

theorem poissonComparisonMajorant_energy_factor {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W =
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
        (fun _ : Unit => (1:ℂ)) W * ∑j, ‖a j‖^2 := by
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,mul_one]
  ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondOuterWeight (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    (secondNormalizedExpansionWeight p hp hcop hg Ψ (m*b0) c d z X Y x.source *
      (secondExpansionScale p X r (expansionSupportData x.common x.firstDivisor x.source) : ℂ)⁻¹)

theorem globalSecondOuterWeight_squarefree
    (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex) (ell Y : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (h : globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x ≠ 0) :
    Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x)) := by
  apply actualSecondLabel_squarefree_of_weight p hp hcop hg x.cube.support x.common
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit hx.2.2.1 Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor) z x.source hx.2.1
  intro hw
  unfold secondArithmeticWeight at hw
  rcases mul_eq_zero.mp hw with hA|hB
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hA,mul_zero,zero_mul]
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hB,mul_zero,zero_mul]

theorem globalSecondOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      (Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
        (globalFirstColumnScale p ell x side)^2)*‖secondRayCoefficient z‖ := by
  have ht := FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon
  have hX := globalFirstColumnScale_pos p hp ell hell x side
  have hh := secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc x.common x.firstDivisor
    Ψ (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
    z (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y (div_pos hX ht) hY x.source (hΨ _) (hΨ _)
  rw [primeSubsetGenerator_norm_eq_productNorm] at hh
  unfold globalSecondOuterWeight
  dsimp only
  rw [norm_mul,norm_inv,Complex.norm_of_nonneg ht.le]
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq
  field_simp

def globalPooledOuterBound (z : SecondRayIndex) (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  (Y*(Real.exp 1)^6*globalLogRep j 2*globalLogRep j 3*(globalLogRep j 0)^2*(globalLogRep j 1)^2/ell^2)*
    ‖secondRayCoefficient z‖

theorem globalSecondOuterWeight_bin_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      globalPooledOuterBound z ell Y (globalScaleIndex p side x) := by
  apply (globalSecondOuterWeight_norm_le p hp hcop hg hinj hc Ψ hΨ m z ell Y hell hY side x).trans
  let j := globalScaleIndex p side x
  have ha := (globalScaleIndex_bounds p hp side x hk 0).2
  have hc' := (globalScaleIndex_bounds p hp side x hk 1).2
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p (x.cube.sideDivisor side) ≤ globalLogRep j 0*Real.exp 1 at ha
  change primeProductNorm p x.common ≤ globalLogRep j 1*Real.exp 1 at hc'
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have hn : Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
      (globalFirstColumnScale p ell x side)^2 =
      Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*
        (primeProductNorm p (x.cube.sideDivisor side))^2*(primeProductNorm p x.common)^2/ell^2 := by
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    unfold globalFirstColumnScale
    field_simp

  rw [hn]
  have h0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).le
  have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).le
  have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have h3 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hr0 := (globalLogRep_pos j 0).le
  have hr1 := (globalLogRep_pos j 1).le
  have hr2 := (globalLogRep_pos j 2).le
  have hr3 := (globalLogRep_pos j 3).le
  calc
    _ ≤ (Y*(globalLogRep j 2*Real.exp 1)*(globalLogRep j 3*Real.exp 1)*
      (globalLogRep j 0*Real.exp 1)^2*(globalLogRep j 1*Real.exp 1)^2/ell^2)*‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by unfold globalPooledOuterBound;ring

end SecondPassArithmetic

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins -/

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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalArithmeticBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j)

def globalSquarefreeBin (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  (globalArithmeticBin p s side q j).filter (fun x => Squarefree (newLabel (globalSecondTuple p x)))

def globalArithmeticTargets (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) : Finset (Ideal O × O) :=
  (globalSquarefreeBin p s side q j).image (fun x => (newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalArithmeticTargets_squarefree (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex) :
    ∀ z∈globalArithmeticTargets p s side q j,Squarefree z.1 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  exact (Finset.mem_filter.mp hx).2

include hp in
theorem globalArithmeticTargets_bounds (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0) :
    ∀ z∈globalArithmeticTargets p s side q j,z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ globalPooledLabelScale j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ globalLogRep j 8*Real.exp 1 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hx',hsf⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxs,hq,hj⟩ := Finset.mem_filter.mp hx'
  have hb := globalPooled_target_bounds p hp side x (hk x hxs)
  rw [hj] at hb
  refine ⟨?_,hb⟩
  exact secondSupportNewLabel_ne_bot p hp x.cube.support x.common x.firstDivisor
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.source

def globalBinZ (ell : ℝ) (side : Bool) (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j)
    (expansionSupportData x.common x.firstDivisor x.source)

def globalBinUd (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUd p (globalLogRep j 5) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinUe (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUe p (globalLogRep j 6) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinUv (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorUv p (globalLogRep j 7) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinKap (j : GlobalLogIndex) (x : GlobalSecondData ι) : ℝ :=
  secondSectorKap p (globalLogRep j 8) (expansionSupportData x.common x.firstDivisor x.source)

def globalBinRadial (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  Y*globalLogRep j 8/(globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2)

theorem globalBinRadial_pos (ell Y : ℝ) (hell : 0 < ell) (hY : 0 < Y) (j : GlobalLogIndex) :
    0 < globalBinRadial ell Y j := by
  have h5 := globalLogRep_pos j 5
  have h6 := globalLogRep_pos j 6
  have h7 := globalLogRep_pos j 7
  have h8 := globalLogRep_pos j 8
  have hX := globalPooledColumnScale_pos ell hell j
  unfold globalBinRadial
  positivity

def globalArithmeticBinSource (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) : ℂ :=
  globalSecondRawSource p hp hcop hg (globalArithmeticBin p s side q j)
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side)
    F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j)

theorem globalArithmeticBinSource_squarefree (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hs : ∀ x∈s,GlobalSecondAdmissible x)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) :
    globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray A₁ A₂ W V ell Y =
    globalSecondRawSource p hp hcop hg (globalSquarefreeBin p s side q j)
      (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side)
      F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
      (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
      (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  unfold globalArithmeticBinSource globalSecondRawSource globalSquarefreeBin
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hsf : Squarefree (newLabel (globalSecondTuple p x))
  · rw [ite_eq_left hsf]
  · rw [ite_eq_right hsf]
    have hz : globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x=0 := by
      by_contra hn
      exact hsf (globalSecondOuterWeight_squarefree p hp hcop hg Ψ m ray ell Y side x
        (hs x (Finset.mem_filter.mp hx).1) hn)
    rw [hz,zero_mul]

theorem globalArithmeticBin_transfer
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray A₁ A₂ W V ell Y‖ ≤
      C*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := globalSecondRawSource_uniform_transfer p hp hcop hg hinj ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro s side q j F Ψ m ray ell Y hell hY hq hΨ hs hk
  rw [globalArithmeticBinSource_squarefree p hp hcop hg s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s side q j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x∈t,‖globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x‖*
      ‖JointLogSeparation.outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤ globalPooledOuterBound ray ell Y j*Cw := by
    intro x hx
    have hh := globalSecondOuterWeight_bin_bound p hp hcop hg hinj hc Ψ hΨ m ray ell Y hell hY.le side x (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    exact mul_le_mul hh (hwglobal _ _ _ _ _) (norm_nonneg _) hB
  have hh := htrans (globalBinRadial ell Y j) (globalBinRadial_pos ell Y hell hY j) t T q
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side) (globalPooledOuterBound ray ell Y j*Cw)
    (globalPooledLabelScale j) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg hB hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => hs x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun a ha => (hbound a ha).1) (fun a ha => (hbound a ha).2.1) hw
  convert hh using 1 ; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def fixedDepthRank (Z K : ℝ) : ℕ := ⌈1000*Real.log K/Real.log Z⌉₊

theorem fixedDepthRank_initial (Z K : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hstart : K ≤ Z^3) : fixedDepthRank Z K ≤ 3000 := by
  have hz := Real.log_pos hZ
  have hl := Real.log_le_log hK hstart
  rw [Real.log_pow] at hl
  apply Nat.ceil_le.mpr
  change 1000*Real.log K/Real.log Z ≤ (3000:ℝ)
  apply (div_le_iff₀ hz).mpr
  norm_num at hl
  linarith

theorem fixedDepthRank_step (Z K K' : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hK' : 1 ≤ K') (hstep : K' ≤ K/Z^((1:ℝ)/1000)) :
    fixedDepthRank Z K'+1 ≤ fixedDepthRank Z K := by
  have hz0 : 0 < Z := lt_trans zero_lt_one hZ
  have hz := Real.log_pos hZ
  have hk0 : 0 < K' := lt_of_lt_of_le zero_lt_one hK'
  have hl := Real.log_le_log hk0 hstep
  rw [Real.log_div hK.ne' (Real.rpow_pos_of_pos hz0 _).ne',Real.log_rpow hz0] at hl
  have ha : 0 ≤ 1000*Real.log K'/Real.log Z := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hK')) hz.le
  have hb : 1000*Real.log K'/Real.log Z+1 ≤ 1000*Real.log K/Real.log Z := by
    apply (le_div_iff₀ hz).mpr
    field_simp
    nlinarith
  have hn := Nat.ceil_mono hb
  rw [Nat.ceil_add_one ha] at hn
  exact hn

theorem fixedDepthRank_path (Z : ℝ) (hZ : 1 < Z) (K : ℕ → ℝ) (n : ℕ)
    (hK : ∀ i,i ≤ n → 1 ≤ K i) (hstart : K 0 ≤ Z^3)
    (hstep : ∀ i,i < n → K (i+1) ≤ K i/Z^((1:ℝ)/1000)) : n+1 ≤ 3001 := by
  have hiter : ∀ i,i ≤ n → fixedDepthRank Z (K i)+i ≤ fixedDepthRank Z (K 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i hi =>
      intro hin
      have hip : i ≤ n := by omega
      have hil : i < n := by omega
      have hprev := hi hip
      have hs := fixedDepthRank_step Z (K i) (K (i+1)) hZ
        (lt_of_lt_of_le zero_lt_one (hK i hip)) (hK (i+1) hin) (hstep i hil)
      omega
  have ht := hiter n le_rfl
  have hb := fixedDepthRank_initial Z (K 0) hZ
    (lt_of_lt_of_le zero_lt_one (hK 0 (Nat.zero_le _))) hstart
  omega

theorem globalPooledDelta_pos (B F : ℝ) (hB : 0 < B) (hF : 0 < F)
    (j : GlobalLogIndex) : 0 < globalPooledDelta B F j := by
  unfold globalPooledDelta
  exact mul_pos (mul_pos (mul_pos (mul_pos hB hF) (globalLogRep_pos j 0))
    (globalLogRep_pos j 2)) (globalLogRep_pos j 3)

theorem globalPooledDelta_ge (B F : ℝ) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (j : GlobalLogIndex) : B*F ≤ globalPooledDelta B F j := by
  have h0 := globalLogRep_ge_one j 0
  have h2 := globalLogRep_ge_one j 2
  have h3 := globalLogRep_ge_one j 3
  unfold globalPooledDelta
  calc
    B*F = B*F*1*1*1 := by ring
    _ ≤ _ := by gcongr

theorem globalPooledNaturalRow_pos (K B F : ℝ) (hK : 0 < K) (hB : 0 < B)
    (hF : 0 < F) (j : GlobalLogIndex) : 0 < globalPooledNaturalRow K B F j := by
  unfold globalPooledNaturalRow
  exact div_pos (mul_pos hK (globalLogRep_pos j 4))
    (mul_pos (sq_pos_of_pos (globalPooledDelta_pos B F hB hF j)) (sq_pos_of_pos hB))

theorem globalPooledNaturalRow_bound (K B F : ℝ) (hK : 0 < K) (hB : 0 < B)
    (hF : 0 < F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2) :
    globalPooledNaturalRow K B F j ≤ K/(globalPooledDelta B F j)^2 := by
  have hD := globalPooledDelta_pos B F hB hF j
  unfold globalPooledNaturalRow
  calc
    K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2) ≤
      K*B^2/((globalPooledDelta B F j)^2*B^2) := by gcongr
    _ = _ := by field_simp

theorem globalPooledRow_contraction (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2)
    (hretained : globalBinRadial ell (globalPooledRowScale K ell B F j) j ≤ globalPooledDelta B F j) :
    globalLogRep j 8*Real.exp 1 ≤ K/globalPooledDelta B F j := by
  have hD := globalPooledDelta_pos B F hB hF j
  have hN := globalPooledNaturalRow_pos K B F hK hB hF j
  have hn := globalPooledNaturalRow_bound K B F hK hB hF j hJ
  have hr := hretained
  rw [globalBinRadial,globalPooled_radial_ratio K ell B F hK hell hB hF] at hr
  have hr' : globalLogRep j 8*Real.exp 1 ≤ globalPooledDelta B F j*globalPooledNaturalRow K B F j := by
    apply (div_le_iff₀ hN).mp
    convert hr using 1 ; ring
  calc
    _ ≤ globalPooledDelta B F j*globalPooledNaturalRow K B F j := hr'
    _ ≤ globalPooledDelta B F j*(K/(globalPooledDelta B F j)^2) := by gcongr
    _ = _ := by field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalPooled_J_bound (B : ℝ) (hB : 0 < B) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalLogRep (globalScaleIndex p side x) 4 ≤ B^2 := by
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).1
  exact (globalScaleIndex_bounds p hp side x hk 4).1.trans hJ

include hp in

theorem globalActualBin_fixed_depth (Z K ell B F : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (hprogress : Z^((1:ℝ)/1000) ≤ B*F)
    (hstart : K ≤ Z^3) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x) ≤ globalPooledDelta B F (globalScaleIndex p side x)) :
    let K' := globalLogRep (globalScaleIndex p side x) 8*Real.exp 1
    K' ≤ K/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z K'+1 ≤ fixedDepthRank Z K ∧
      fixedDepthRank Z K ≤ 3000 := by
  dsimp only
  have hrow := globalPooledRow_contraction K ell B F hK hell hB hF (globalScaleIndex p side x)
    (globalPooled_J_bound p hp B hB side x hk hb₁ hb₂) hretained
  have hD := hprogress.trans (globalPooledDelta_ge B F hB.le hF.le (globalScaleIndex p side x))
  have hz0 : 0 < Z := lt_trans zero_lt_one hZ
  have hsmall : globalLogRep (globalScaleIndex p side x) 8*Real.exp 1 ≤ K/Z^((1:ℝ)/1000) :=
    hrow.trans (div_le_div_of_nonneg_left hK.le (Real.rpow_pos_of_pos hz0 _) hD)
  have hchild : 1 ≤ globalLogRep (globalScaleIndex p side x) 8*Real.exp 1 :=
    one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one _ _) (Real.one_le_exp (by norm_num))
  exact ⟨hsmall,fixedDepthRank_step Z K _ hZ hK hchild hsmall,
    fixedDepthRank_initial Z K hZ hK hstart⟩

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

def activeGcdColumns (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → Ideal O :=
  fun j => idealQuotient D j.val.val

def activeGcdCoefficient (N : ℝ) (a : idealRange N → ℂ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    gcdRaySupport (fun I : idealRange N => I.val) a D c → ℂ := fun j => a j.val

theorem originalHigh_gcd_eq_maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (D : Ideal O) (hD : D≠0) (cols : n → Ideal O) (hcols : ∀j, Admissible (cols j))
    (hdiv : ∀j, D∣cols j) (hproper : ∀j, cols j≠D)
    (hray : ∀j k, columnRay (cols j)=columnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0<M) :
    (∑j, ∑k, if gcd (cols j) (cols k)=D then
      star (a j)*a k*(∑' lengthScale : Ideal O, originalPairHigh (cols j) (cols k) W M K lengthScale) else 0) =
    maskedPoissonDifference (commonMaskIdeal D) W (fun j => idealQuotient D (cols j)) a M K := by
  rw [originalHigh_gcd_principal_assembly D hD cols hcols hdiv hproper hray a W M K hM,
    maskedPoissonDifference,
    maskedDualFamily_retained _ (commonMaskIdeal_squarefree D).ne_zero _ a W M K hM
      (fun j => admissible_idealQuotient (hcols j) (hdiv j))
      (fun j k => columnRay_idealQuotient_eq D (cols j) (cols k) (hcols j) (hcols k)
        (hdiv j) (hdiv k) (hray j k))]

theorem annularRayGcdBlock_eq_active_difference (M N X K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (ha : CoefficientOnShell N X a)
    (D : Ideal O) (hD : D≠0) (hsmall : (Ideal.absNorm D:ℝ)≤X/2)
    (c : EisensteinEPrimaryPhase.Coord) :
    annularRayGcdBlock M N K D c a =
      maskedPoissonDifference (commonMaskIdeal D) QuadraticInitialBound.annularSieveCutoff
        (activeGcdColumns N a D c) (activeGcdCoefficient N a D c) M K := by
  classical
  rw [annularRayGcdBlock_eq_pair_high M N K hM D c a]
  simp only [rayPairCoefficient,ite_mul,zero_mul]
  rw [gcd_ray_pair_sum_restrict]
  let S := gcdRaySupport (fun I : idealRange N => I.val) a D c
  have hdiv (j : S) : D∣j.val.val :=
    ((mem_gcdRaySupport _ a D c j.val).mp j.property).1
  have hray (j k : S) : columnRay j.val.val=columnRay k.val.val := by
    have hj := ((mem_gcdRaySupport _ a D c j.val).mp j.property).2.1
    have hk := ((mem_gcdRaySupport _ a D c k.val).mp k.property).2.1
    exact hj.trans hk.symm
  exact originalHigh_gcd_eq_maskedPoissonDifference D hD
    (fun j : S => j.val.val) (fun j => (mem_idealRange.mp j.val.property).1) hdiv
    (gcdRaySupport_proper N X a ha D c hsmall) hray (fun j : S => a j.val)
    QuadraticInitialBound.annularSieveCutoff M K hM

theorem HasSieveExponent.annular_small_gcd_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N X K T : ℝ), 1≤M → 1≤K → 4≤T →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N X a →
      ∀ (D : Ideal O), D≠0 → (Ideal.absNorm D:ℝ)≤X/2 →
      ∀ (c : EisensteinEPrimaryPhase.Coord),
        ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
            (commonMaskIdeal D) K (X/(Ideal.absNorm D:ℝ)) M T
            (activeGcdCoefficient N a D c) QuadraticInitialBound.annularSieveCutoff := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hbound⟩ :=
    hexp.masked_poisson_complete hα deltaLoss hδ l A
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro ε hε M N X K T hM hK hT a ha D hD hsmall c
  classical
  have hDn : 0<(Ideal.absNorm D:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤X/(Ideal.absNorm D:ℝ) := (le_div_iff₀ hDn).mpr (by linarith)
  have hp := gcdRaySupport_quotient_properties N X a ha D hD c
  rw [annularRayGcdBlock_eq_active_difference M N X K (by linarith) a ha D hD hsmall c]
  apply hbound ε hε (commonMaskIdeal D) (commonMaskIdeal_squarefree D)
    (fun P hP => fixedBadPrimes_dvd_commonMaskIdeal D P hP)
    K (X/(Ideal.absNorm D:ℝ)) M T hK hscale hM hT
    (activeGcdColumns N a D c) hp.1
    (fun j => ⟨(hp.2.1 j).1,(hp.2.1 j).2.1,(hp.2.1 j).2.2.1⟩)
    hp.2.2 (fun j => (hp.2.1 j).2.2.2) (activeGcdCoefficient N a D c)
    QuadraticInitialBound.annularSieveCutoff QuadraticInitialBound.annularSieveCutoff_zero

end

def selectedPoissonT (C M X η : ℝ) : ℝ := C*(M*X)^η
def selectedPoissonK (C M X η : ℝ) : ℝ := selectedPoissonT C M X η*X^2/M

theorem selectedPoisson_bounds (C M X η : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hMX : M≤X^2) (hη : 0≤η) :
    4≤ selectedPoissonT C M X η ∧ 1≤ selectedPoissonK C M X η ∧
      selectedPoissonK C M X η≤C*(M*X)^(η+2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hprod : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hprod hη
  have hT : 4≤ selectedPoissonT C M X η := by
    unfold selectedPoissonT
    nlinarith
  have hfrac : 1≤X^2/M := (le_div_iff₀ hM0).mpr (by simpa using hMX)
  have hK : 1≤ selectedPoissonK C M X η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    nlinarith
  refine ⟨hT,hK,?_⟩
  have hXprod : X≤M*X := by nlinarith
  have hfracup : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg X) hM).trans (pow_le_pow_left₀ hX0.le hXprod 2)
  unfold selectedPoissonK selectedPoissonT
  rw [mul_div_assoc,Real.rpow_add (by positivity : 0<M*X),Real.rpow_two]
  calc
    _ ≤ (C*(M*X)^η)*(M*X)^2 := mul_le_mul_of_nonneg_left hfracup (by positivity)
    _ = _ := by ring

theorem selectedPoisson_radial_identity (C B M X q η : ℝ)
    (hM : 0<M) (hX : 0<X) (hq : 0<q) (hB : 0<B) :
    (M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η =
      selectedPoissonT C M X η*q/B := by
  unfold selectedPoissonK
  field_simp

theorem cutoff_middle_identity (M X T α : ℝ) (hM : 0<M) (hX : 0<X) (hT : 0<T) :
    T*Real.sqrt M*(T*X^2/M)^(α-1/2) =
      T^(α+1/2)*X^(2*α-1)*M^(1-α) := by
  rw [Real.div_rpow (by positivity : 0≤T*X^2) hM.le,
    Real.mul_rpow hT.le (sq_nonneg X),←Real.rpow_two,←Real.rpow_mul hX.le]
  have hx : 2*(α-1/2)=2*α-1 := by ring
  have hm : 1-α=1/2-(α-1/2) := by ring
  have ht : α+1/2=1+(α-1/2) := by ring
  have hmPow : M^(1-α)=M^(1/2:ℝ)/M^(α-1/2) := by
    calc
      _ = M^((1/2:ℝ)-(α-1/2)) := by rw [hm]
      _ = _ := Real.rpow_sub hM _ _
  have htPow : T^(α+1/2)=T*T^(α-1/2) := by
    calc
      _ = T^(1+(α-1/2)) := by rw [ht]
      _ = _ := by rw [Real.rpow_add hT,Real.rpow_one]
  rw [hx,hmPow,htPow,Real.sqrt_eq_rpow]
  ring

theorem selectedPoisson_middle_bound (C M X η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hη : 0≤η) (hα : α≤2) :
    selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C^3*(M*X)^(3*η)*(X^(2*α-1)*M^(1-α)) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 0<M*X := by positivity
  have hP1 : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP1 hη
  have hT : 1≤ selectedPoissonT C M X η := by unfold selectedPoissonT; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have htwo : (2:ℝ)^(α-1/2)≤4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : ((M*X)^η)^3 = (M*X)^(3*η) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP.le]
    congr 1
    ring
  have hT3 : (selectedPoissonT C M X η)^(α+1/2)≤C^3*(M*X)^(3*η) := by
    calc
      _ ≤ (selectedPoissonT C M X η)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = C^3*(M*X)^(3*η) := by norm_num only [selectedPoissonT,Real.rpow_ofNat,mul_pow,hp3]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hK0.le]
  calc
    _ ≤ 4*(selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)) := by
      have hh := mul_le_mul_of_nonneg_right htwo
        (show 0≤ selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) by positivity)
      nlinarith [hh]
    _ = 4*((selectedPoissonT C M X η)^(α+1/2)*X^(2*α-1)*M^(1-α)) := by
      rw [selectedPoissonK,cutoff_middle_identity M X _ α hM0 hX0 hT0]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hT3
        (show 0≤X^(2*α-1)*M^(1-α) by positivity)
      nlinarith [hh]

end CanonicalQuadraticSieve

open Filter MeasureTheory EuclideanGeometry
open scoped BigOperators Classical Topology InnerProductSpace ENNReal

namespace CubicEisenstein

abbrev EuclideanSpatial := EuclideanSpace ℝ (Fin 3)

def euclideanUpperHalf : Set EuclideanSpatial := {p | 0<p 2}
def hyperbolicDensity (p : EuclideanSpatial) : ℝ≥0∞ := ENNReal.ofReal ((p 2)^3)⁻¹

def hyperbolicEuclideanVolume : Measure EuclideanSpatial :=
  (volume.restrict euclideanUpperHalf).withDensity hyperbolicDensity

lemma euclideanUpperHalf_measurable : MeasurableSet euclideanUpperHalf := by
  exact measurableSet_lt measurable_const (by fun_prop)

lemma hyperbolicDensity_measurable : Measurable hyperbolicDensity := by
  unfold hyperbolicDensity
  fun_prop

lemma hyperbolic_volume_map_of_jacobian
    (f : EuclideanSpatial → EuclideanSpatial)
    (df : EuclideanSpatial → EuclideanSpatial →L[ℝ] EuclideanSpatial)
    (hf : Measurable f) (hderiv : ∀p∈euclideanUpperHalf,HasFDerivAt f (df p) p)
    (hinj : Set.InjOn f euclideanUpperHalf) (himage : f '' euclideanUpperHalf=euclideanUpperHalf)
    (hjac : ∀p∈euclideanUpperHalf,
      ENNReal.ofReal |(df p).det| *hyperbolicDensity (f p)=hyperbolicDensity p) :
    Measure.map f hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs]
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (hs.preimage hf),withDensity_apply _ hs]
  rw [←lintegral_indicator (hs.preimage hf),←lintegral_indicator hs]
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    euclideanUpperHalf_measurable (fun p hp => (hderiv p hp).hasFDerivWithinAt) hinj
    (s.indicator hyperbolicDensity)
  rw [himage] at hc
  rw [hc]
  apply setLIntegral_congr_fun euclideanUpperHalf_measurable
  intro p hp
  by_cases hsfp : f p∈s
  · simp only [Set.indicator_of_mem hsfp,Set.mem_preimage,hsfp,Set.indicator_of_mem]
    exact (hjac p hp).symm
  · simp only [Set.indicator_of_notMem hsfp,mul_zero]
    have hpnot : p∉f ⁻¹' s := hsfp
    exact Set.indicator_of_notMem hpnot hyperbolicDensity

def euclideanInversion : EuclideanSpatial → EuclideanSpatial := inversion 0 1

def euclideanInversionDeriv (p : EuclideanSpatial) : EuclideanSpatial →L[ℝ] EuclideanSpatial :=
  (1/‖p‖)^2 • (((ℝ ∙ p)ᗮ).reflection : EuclideanSpatial →L[ℝ] EuclideanSpatial)

lemma euclideanInversion_apply (p : EuclideanSpatial) (j : Fin 3) :
    euclideanInversion p j=(1/‖p‖)^2*p j := by
  simp [euclideanInversion,inversion,dist_zero_right]

lemma euclideanInversion_measurable : Measurable euclideanInversion := by
  simp +unfoldPartialApp only [euclideanInversion,inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero]
  fun_prop

lemma euclideanUpperHalf_ne_zero (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) : p≠0 := by
  intro he
  simp [euclideanUpperHalf,he] at hp

lemma euclideanInversion_mem (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    euclideanInversion p∈euclideanUpperHalf := by
  change 0<euclideanInversion p 2
  rw [euclideanInversion_apply]
  exact mul_pos (sq_pos_of_pos (one_div_pos.mpr (norm_pos_iff.mpr (euclideanUpperHalf_ne_zero p hp)))) hp

lemma euclideanInversion_image : euclideanInversion '' euclideanUpperHalf=euclideanUpperHalf := by
  apply Set.Subset.antisymm
  · rintro p ⟨q,hq,rfl⟩
    exact euclideanInversion_mem q hq
  · intro p hp
    exact ⟨euclideanInversion p,euclideanInversion_mem p hp,
      inversion_inversion 0 (by norm_num) p⟩

lemma euclideanInversion_hasFDerivAt (p : EuclideanSpatial) (hp : p≠0) :
    HasFDerivAt euclideanInversion (euclideanInversionDeriv p) p := by
  simpa [euclideanInversion,euclideanInversionDeriv,dist_zero_right] using
    (hasFDerivAt_inversion (R := (1:ℝ)) hp)

lemma euclideanInversion_abs_det (p : EuclideanSpatial) :
    |(euclideanInversionDeriv p).det|=((1/‖p‖)^2)^3 := by
  unfold euclideanInversionDeriv
  change |LinearMap.det ((1/‖p‖)^2 • ((ℝ ∙ p)ᗮ).reflection.toLinearMap)|=_
  rw [LinearMap.det_smul]
  rw [Submodule.det_reflection]
  simp only [finrank_euclideanSpace,Fintype.card_fin,abs_mul,abs_pow,abs_neg,abs_one,
    one_pow,mul_one]
  rw [abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg p))]

lemma euclideanInversion_jacobian_density (p : EuclideanSpatial) (hp : p∈euclideanUpperHalf) :
    ENNReal.ofReal |(euclideanInversionDeriv p).det| *
      hyperbolicDensity (euclideanInversion p)=hyperbolicDensity p := by
  rw [euclideanInversion_abs_det,hyperbolicDensity,hyperbolicDensity,euclideanInversion_apply]
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  field_simp

theorem euclideanInversion_preserves_hyperbolicVolume :
    Measure.map euclideanInversion hyperbolicEuclideanVolume=hyperbolicEuclideanVolume := by
  apply hyperbolic_volume_map_of_jacobian euclideanInversion euclideanInversionDeriv
    euclideanInversion_measurable
  · exact fun p hp => euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp)
  · exact (inversion_injective 0 (by norm_num : (1:ℝ)≠0)).injOn
  · exact euclideanInversion_image
  · exact euclideanInversion_jacobian_density

end CubicEisenstein

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.CubicSieve.UniformTransfer -/

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

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem full_uniform_labeled_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hp hcop hg F Ψ m H (label x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p hp _ hcop hg
    s t b0 w B lengthScale label F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw hlabel
  let sel : OldTuple → Oˣ := fun x => if hx : x ∈ s then
    Classical.choose (exists_label_unit (label x) (newLabel x) (hlabel x hx)) else 1
  have hsel (x : OldTuple) (hx : x ∈ s) : label x = (sel x : O) * idealGenerator (newLabel x) := by
    simp only [sel, dite_eq_left hx]
    exact Classical.choose_spec (exists_label_unit (label x) (newLabel x) (hlabel x hx))
  have hh := hb s t b0 w B lengthScale (idealChildRow p hp hcop hg F Ψ m H negative)
    sel hb0 hB hL hvalid hmap ht hnorm hw
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [hsel x hx]
  rfl

theorem full_uniform_fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖fixedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2) := by
  obtain ⟨C, hC, hpush⟩ := full_uniform_labeled_child_second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p hp _ hcop hg
  have hpush := hpush p hp hcop hg
  intro s t b0 w B lengthScale label F Ψ₁ Ψ₂ m H₁ H₂ hb0 hB hL hv hm ht hn hw hl
  let P₁ := fun x => fixedChildRow p hp hcop hg F Ψ₁ m H₁ (label x) (newRow x)
  let P₂ := fun x => fixedChildRow p hp hcop hg F Ψ₂ m H₂ (label x) (-newRow x)
  have h₁ := hpush s t b0 w B lengthScale label F Ψ₁ m H₁ false hb0 hB hL hv hm ht hn hw hl
  have h₂ := hpush s t b0 w B lengthScale label F Ψ₂ m H₂ true hb0 hB hL hv hm ht hn hw hl
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  let D : ℝ := B * C * (lengthScale * Ideal.absNorm b0)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have hmode : fixedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x ∈ s, w x * P₂ x * star (P₁ x) := by
    unfold fixedSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁, P₂]
    ring
  rw [hmode]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2)) *
      Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD, Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2) *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end SecondPassArithmetic
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem full_uniform_integrated_fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O))
      (b0 : Ideal O) (w : Frequency → OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ q, ∀ x ∈ s, ‖w q x‖ ≤ B) → (∀ x ∈ s, Continuous (fun q => w q x)) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖integratedSecondMode p hp hcop hg b₁ b₂ b₃ s w label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C, hC, hb⟩ := full_uniform_fixed_second_mode_transfer ε hε
  refine ⟨C, hC, ?_⟩
  intro ι _ p hp _ hcop hg
  have hb := hb p hp hcop hg
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hb0 hB hL hv hm ht hn hw hwc hl
  let f : Frequency → ℂ := fun q => fixedSecondMode p hp hcop hg s (w q) label F Ψ₁ Ψ₂ m
    (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f fixedSecondMode
    apply continuous_finsetSum
    intro x hx
    have hwx := hwc x hx
    have hc₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (label x) (newRow x) V₁ X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have hc₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (label x) (-newRow x) V₂ X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hwx.mul hc₁.star).mul hc₂
  have hpoint : ∀ q, ‖f q‖ ≤ (B * C * (lengthScale * Ideal.absNorm b0)^ε) * G q := by
    intro q
    have hh := hb s T b0 (w q) B lengthScale label F Ψ₁ Ψ₂ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      hb0 hB hL hv hm ht hn (hw q) hl
    simpa only [f, G, childGeometricMean, childEnergy, mul_assoc] using hh
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0
    (B * C * (lengthScale * Ideal.absNorm b0)^ε) M (by positivity) hM hpoint

end SecondPassIntegration

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)

theorem full_uniform_postCommonSmoothPair_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_separation A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p hp _ hcop hg
    F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
    z ud ue uv kap X₁ X₂ R b (hb z ud ue uv kap)

end SecondPassArithmetic
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem full_uniform_tupleSource_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
          FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O)) (b0 : Ideal O)
        (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ : ℝ),
        b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
        (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
        ‖tupleSourceSum p hp hcop hg s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := full_uniform_integrated_fixed_second_mode_transfer ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hpoint, hid⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro ι _ p hp _ hcop hg
  have htrans := htrans p hp hcop hg
  have hid := hid p hp hcop hg
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hsource := tupleSource_eq_integratedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T b0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hb0 hB hL hv hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)

theorem full_uniform_globalSecondSource_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i})), ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htransfer⟩ := SecondPassIntegration.full_uniform_tupleSource_transfer
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro ι _ p hp _ hcop hg hinj
    R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  obtain ⟨b,hb,htrans⟩ := htransfer R hR
  have htrans := htrans p hp hcop hg
  let r := globalSecondRecover p s
  have hr (x : GlobalSecondData ι) (hx : x∈s) : r (globalSecondTuple p x)=x :=
    globalSecondRecover_apply p hinj s q hs hfixed x hx
  have hvalid : ∀ y∈s.image (globalSecondTuple p),
      SecondPassFiber.Valid y (newLabel y) q.1 (newRow y) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hv := globalSecondTuple_valid p x (hs x hx)
    simpa only [hfixed x hx] using hv
  have hmap' : ∀ y∈s.image (globalSecondTuple p),(newLabel y,newRow y)∈T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hmap x hx
  have hw' : ∀ y∈s.image (globalSecondTuple p),
      ‖(w ∘ r) y‖*‖outerWindow V ((z ∘ r) y) ((ud ∘ r) y) ((ue ∘ r) y) ((uv ∘ r) y) ((kap ∘ r) y)‖ ≤ B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using hw x hx
  have hlabel : ∀ y∈s.image (globalSecondTuple p),Ideal.span {(globalSecondLabel p ∘ r) y}=newLabel y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using globalSecondLabel_span p x
  have hh := htrans (s.image (globalSecondTuple p)) T q.1 (w ∘ r) B lengthScale (globalSecondLabel p ∘ r)
    F Ψ₁ Ψ₂ (fixedTripleMask m q) (z ∘ r) (ud ∘ r) (ue ∘ r) (uv ∘ r) (kap ∘ r) X₁ X₂
    hq hB hL hvalid hmap' ht hn hw' hlabel
  rw [← globalSecondSource_eq_tupleSource p hp hcop hg hinj s q hs hfixed] at hh
  apply hh.trans
  have hd := SecondPassIntegration.child_coefficient_density_bound p hp hcop hg F Ψ₁ Ψ₂
    (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b J ((1+R)^A) Cₛ hb
  have hpow : 0 < (1+R)^A := pow_pos (by linarith) _
  have hi := (le_div_iff₀' hpow).mpr hd
  have hnn : 0 ≤ B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε := by positivity
  have hbnd := mul_le_mul_of_nonneg_left hi hnn
  convert hbnd using 1 ; ring

theorem full_uniform_globalSecondRawSource_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i})), ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondSource_transfer
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro ι _ p hp _ hcop hg hinj
  have htrans := htrans p hp hcop hg hinj
  intro R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  rw [globalSecondRawSource_eq p hp hcop hg hinj A₁ A₂ W V M hM hV s w q hfixed
    F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ R hR]
  exact htrans R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw

theorem full_uniform_globalArithmeticBin_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2), ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray A₁ A₂ W V ell Y‖ ≤
      C*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondRawSource_transfer ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc
  have htrans := htrans p hp hcop hg hinj
  intro s side q j F Ψ m ray ell Y hell hY hq hΨ hs hk
  rw [globalArithmeticBinSource_squarefree p hp hcop hg s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s side q j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x∈t,‖globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x‖*
      ‖JointLogSeparation.outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤ globalPooledOuterBound ray ell Y j*Cw := by
    intro x hx
    have hh := globalSecondOuterWeight_bin_bound p hp hcop hg hinj hc Ψ hΨ m ray ell Y hell hY.le side x (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    exact mul_le_mul hh (hwglobal _ _ _ _ _) (norm_nonneg _) hB
  have hh := htrans (globalBinRadial ell Y j) (globalBinRadial_pos ell Y hell hY j) t T q
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side) (globalPooledOuterBound ray ell Y j*Cw)
    (globalPooledLabelScale j) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg hB hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => hs x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun a ha => (hbound a ha).1) (fun a ha => (hbound a ha).2.1) hw
  convert hh using 1 ; ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)

theorem full_uniform_postCommonSmoothPair_twisted_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) t₁ * (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        C * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_twisted_profiles A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hid, hpoint, hint⟩ := hb θ₁ θ₂
  refine ⟨hpoint, ?_⟩
  intro ι _ p hp _ hcop hg
    F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V
    z ud ue uv kap X₁ X₂ R b (hid z ud ue uv kap)

end SecondPassArithmetic
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem full_uniform_tupleSource_twisted_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ), ∀ θ₁ θ₂ : ℝ,
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) t₁ * (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) t₂ * b t₃‖ ≤
        Cₛ * (1+‖θ₁‖)^(J+2) * (1+‖θ₂‖)^(J+2) * FirstPassCubeLabels.firstLogDensity J t₁ *
          FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O)) (b0 : Ideal O)
        (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ : ℝ),
        b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
        (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
        ‖tupleSourceSum p hp hcop hg s w label F Ψ₁ Ψ₂ m (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := full_uniform_integrated_fixed_second_mode_transfer ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := full_uniform_postCommonSmoothPair_twisted_fixed_tests A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hb⟩ := hsep R hR
  refine ⟨b, ?_⟩
  intro θ₁ θ₂
  obtain ⟨hpoint, hid⟩ := hb θ₁ θ₂
  refine ⟨hpoint, ?_⟩
  intro ι _ p hp _ hcop hg
  have htrans := htrans p hp hcop hg
  have hid := hid p hp hcop hg
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hsource := tupleSource_eq_integratedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T b0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) b hb0 hB hL hv hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)

theorem full_uniform_globalSecondSource_twisted_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i})), ∀ (R : ℝ),0 < R → ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondSource p hp hcop hg s w F Ψ₁ Ψ₂ (fixedTripleMask m q)
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htransfer⟩ := SecondPassIntegration.full_uniform_tupleSource_twisted_transfer
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro ι _ p hp _ hcop hg hinj
    R hR θ₁ θ₂ s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  obtain ⟨b,hsep⟩ := htransfer R hR
  obtain ⟨hb,htrans⟩ := hsep θ₁ θ₂
  have htrans := htrans p hp hcop hg
  let r := globalSecondRecover p s
  have hr (x : GlobalSecondData ι) (hx : x∈s) : r (globalSecondTuple p x)=x :=
    globalSecondRecover_apply p hinj s q hs hfixed x hx
  have hvalid : ∀ y∈s.image (globalSecondTuple p),
      SecondPassFiber.Valid y (newLabel y) q.1 (newRow y) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hv := globalSecondTuple_valid p x (hs x hx)
    simpa only [hfixed x hx] using hv
  have hmap' : ∀ y∈s.image (globalSecondTuple p),(newLabel y,newRow y)∈T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hmap x hx
  have hw' : ∀ y∈s.image (globalSecondTuple p),
      ‖(w ∘ r) y‖*‖outerWindow V ((z ∘ r) y) ((ud ∘ r) y) ((ue ∘ r) y) ((uv ∘ r) y) ((kap ∘ r) y)‖ ≤ B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using hw x hx
  have hlabel : ∀ y∈s.image (globalSecondTuple p),Ideal.span {(globalSecondLabel p ∘ r) y}=newLabel y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    simpa only [Function.comp_apply,hr x hx] using globalSecondLabel_span p x
  have hh := htrans (s.image (globalSecondTuple p)) T q.1 (w ∘ r) B lengthScale (globalSecondLabel p ∘ r)
    F Ψ₁ Ψ₂ (fixedTripleMask m q) (z ∘ r) (ud ∘ r) (ue ∘ r) (uv ∘ r) (kap ∘ r) X₁ X₂
    hq hB hL hvalid hmap' ht hn hw' hlabel
  rw [← globalSecondSource_eq_tupleSource p hp hcop hg hinj s q hs hfixed] at hh
  apply hh.trans
  have hd := SecondPassIntegration.child_coefficient_density_bound p hp hcop hg F Ψ₁ Ψ₂
    (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ (𝓕 (JointLogSeparation.frequencyTwist A₁ θ₁)) (𝓕 (JointLogSeparation.frequencyTwist A₂ θ₂)) b J ((1+R)^A)
    (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)) hb
  have hpow : 0 < (1+R)^A := pow_pos (by linarith) _
  have hi := (le_div_iff₀' hpow).mpr hd
  have hnn : 0 ≤ B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε := by positivity
  have hbnd := mul_le_mul_of_nonneg_left hi hnn
  convert hbnd using 1 ; ring

theorem full_uniform_globalSecondRawSource_twisted_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i})), ∀ (R : ℝ),0 < R → ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondSource_twisted_transfer
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro ι _ p hp _ hcop hg hinj
  have htrans := htrans p hp hcop hg hinj
  intro R hR θ₁ θ₂ s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  rw [globalSecondRawSource_eq p hp hcop hg hinj (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V M hM hV s w q hfixed
    F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ R hR]
  exact htrans R hR θ₁ θ₂ s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw

theorem full_uniform_globalArithmeticBin_twisted_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2), ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V ell Y‖ ≤
      C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondRawSource_twisted_transfer ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc
  have htrans := htrans p hp hcop hg hinj
  intro θ₁ θ₂ s side q j F Ψ m ray ell Y hell hY hq hΨ hs hk
  rw [globalArithmeticBinSource_squarefree p hp hcop hg s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s side q j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x∈t,‖globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x‖*
      ‖JointLogSeparation.outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤ globalPooledOuterBound ray ell Y j*Cw := by
    intro x hx
    have hh := globalSecondOuterWeight_bin_bound p hp hcop hg hinj hc Ψ hΨ m ray ell Y hell hY.le side x (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    exact mul_le_mul hh (hwglobal _ _ _ _ _) (norm_nonneg _) hB
  have hh := htrans (globalBinRadial ell Y j) (globalBinRadial_pos ell Y hell hY j) θ₁ θ₂ t T q
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side) (globalPooledOuterBound ray ell Y j*Cw)
    (globalPooledLabelScale j) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg hB hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => hs x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun a ha => (hbound a ha).1) (fun a ha => (hbound a ha).2.1) hw
  convert hh using 1 ; ring

end SecondPassArithmetic

end

end OAI

end

