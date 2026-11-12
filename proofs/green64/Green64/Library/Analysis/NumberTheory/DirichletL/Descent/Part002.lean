module

public import Green64.Library.OAI.NumberTheory.DirichletL.Descent.CuspCongruence
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.RowCompletion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part016
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part002

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.ActiveCusp -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance activeQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

variable {ι : Type*} [Fintype ι]

def localInactiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (A : Finset ι) : ℂ :=
  ∏ i ∈ (Finset.univ : Finset ι) \ A,
    finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) 0

def localActiveWeight (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) : ℂ :=
  ∏ i : A, finiteAdditiveFourierCoeff (quotientTrace (p i.val) (hp i.val)) (F i.val) (v i)

theorem primeFunction_fourier_by_active
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (n : Eis) :
    (∏ i, F i (Ideal.Quotient.mk _ n)) =
      ∑ A : Finset ι, localInactiveWeight p hp F A *
        ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
          localActiveWeight p hp F A v *
            ∏ i : A, quotientTrace (p i.val) (hp i.val)
              ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) := by
  let (i : ι) : Field (Eis ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by
    ext A
    simp
  simpa only [hpow, localInactiveWeight, localActiveWeight] using
    FixedRayActiveSet.fourier_inversion_by_active_set (fun i => Eis ⧸ Ideal.span {p i})
      (fun i => quotientTrace (p i) (hp i))
      (fun i => GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) F
      (fun i => Ideal.Quotient.mk _ n)

theorem activeStratum_function_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    {N a0 c0 : Eis} {mode : Bool}
    (D : ∀ A : Finset ι, ControlledStratumArithmetic (fun i : A => p i.val) N a0 c0 mode)
    (hN : (9 : Eis) * c0 ∣ N) (hc0 : c0 ≠ 0)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n : Eis) :
    (∑ A : Finset ι, localInactiveWeight p hp F A *
      ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
        localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i, F i (Ideal.Quotient.mk _ n) := by
  have hlocal (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n *
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i : A, quotientTrace (p i.val) (hp i.val)
          ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i : A => p i.val) (fun i _ => hprimary i.val))
      hbase s (fun i => hp i.val) hc0 v n
  simp_rw [hlocal]
  rw [primeFunction_fourier_by_active p hp F n]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro v hv
  ring

def fixedActiveFunctionWeight
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (φ : Eis →* ℂ) (t : FixedActiveCuspIndex c p) : ℂ :=
  fixedThetaRowCoeff c hc φ t.1 * localInactiveWeight p hp F t.2.1 *
    localActiveWeight p hp F t.2.1 t.2.2

theorem fixedActiveFunction_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (Q : Ideal Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (φ : Eis →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ) (n : Eis) :
    (∑ t : FixedActiveCuspIndex c p, fixedActiveFunctionWeight p hp F c hc φ t *
      ShortDraftTrace.breveE (-cuspFrequency n *
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
      fixedThetaTwist φ n * ∏ i, F i (Ideal.Quotient.mk _ n) := by
  simp only [FixedActiveCuspIndex, Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum]
  have hf : (∑ h : Eis ⧸ Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ShortDraftTrace.breveE (-cuspFrequency n * thetaFourierTranslation c h)) = fixedThetaTwist φ n := by
    simp only [fixedThetaRowCoeff]
    rw [thetaFourierTranslation_inversion c hc,
      fixedThetaQuotient_mk φ Q hφ c hcQ]
  rw [← hf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _ = fixedThetaRowCoeff c hc φ h *
        (∑ A : Finset ι, localInactiveWeight p hp F A *
          ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
            localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [activeStratum_function_multiplier p hp hprimary F (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n, (G h).point]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MixedRow -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance mixedQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι]

def unmarkedSexticTwist (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) : Eis →* ℂ where
  toFun n := ∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

def mixedPrimeFunction (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (i : ι) (x : Eis ⧸ Ideal.span {p i}) : ℂ :=
  if i ∈ S then zeroMark x else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) x

theorem unmarkedSexticTwist_norm (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    ‖unmarkedSexticTwist p hg j S n‖ ≤ 1 := by
  change ‖∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i hi => norm_nonneg _)
    (fun i hi => FiniteRayExpansion.norm_char_le_one _ _)

theorem unmarkedSexticTwist_periodic (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i, p i}) (unmarkedSexticTwist p hg j S) := by
  intro x y hxy
  change (∏ i ∈ (Finset.univ : Finset ι) \ S, _) = ∏ i ∈ (Finset.univ : Finset ι) \ S, _
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ideal.Quotient.mk (Ideal.span {p i}) x = Ideal.Quotient.mk _ y := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans (Ideal.mem_span_singleton.mp hxy)
  rw [he]

theorem mixedPrimeFunction_product (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    (∏ i, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      unmarkedSexticTwist p hg j S n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have hS : (∏ i ∈ S, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      ∏ i ∈ S, if p i ∣ n then (1 : ℂ) else 0 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mixedPrimeFunction, hi, ite_true, zeroMark,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hS]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mixedPrimeFunction, (Finset.mem_sdiff.mp hi).2, ite_false]

omit [Fintype ι] in
theorem markedThetaQuotient_mk (p : ι → Eis) (S : Finset ι)
    (Ψ : Eis →* ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (n : Eis) :
    markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n) =
      fixedThetaTwist Ψ n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  unfold markedThetaQuotient
  have hcbase : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q :=
    hcQ.trans (Ideal.mul_mono_right Ideal.mul_le_left)
  rw [fixedThetaQuotient_mk Ψ Q hΨ c hcbase]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hxy : Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n ∈ Ideal.span {c} :=
    Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) n))
  have hp : p i ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n :=
    (Finset.dvd_prod_of_mem p hi).trans (Ideal.mem_span_singleton.mp
      (Ideal.mul_le_right (Ideal.mul_le_right (hcQ hxy))))
  simp only [dvd_iff_dvd_of_dvd_sub hp]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActiveReflection -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CubicEisenstein CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance activeReflectionQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem markedCompletedT_fixed_active_strata {ι : Type*} [Fintype ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : Eis →* ℂ) (hφnorm : ∀ n, ‖φ n‖ ≤ 1)
    (Q : Ideal Eis) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : Eis) (hcall : call ≠ 0) [Fintype (Eis ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : Eis)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (φ * unmarkedSexticTwist p hg j S) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).smoothedKernel W X := by
  have hnorm (n : Eis) : ‖(φ * unmarkedSexticTwist p hg j S) n‖ ≤ 1 := by
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n)).trans
      (unmarkedSexticTwist_norm p hg j S n)
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_left hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_right hxy)]
  apply markedCompletedT_of_cusp_multiplier p S (fun i _ => hprime i) _ hnorm _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ControlledMultiplier -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance controlledField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis ⧸ P) := Ideal.Quotient.field _
noncomputable local instance controlledFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_phase_product (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) (x : Eis) :
    star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) (v i) := by
  have hbad : A4BadPhase c0 hc0 (D.matrix v 1 1) D.U x =
      A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x := by
    apply A4BadPhase_eq_of_residue
    convert dvd_mul_of_dvd_left (D.inverse_fixed hN v) D.U using 1 ; ring
  have hlocal := A3_A4_frequency_product p hp hcop hg (D.matrix v 0 0) (D.matrix v 0 1)
    c0 (D.matrix v 1 1) D.U D.w x hc0 (D.determinant v) D.bezout D.sigma D.epsilon
    (fun i => (v i : Eis ⧸ Ideal.span {p i})) (D.frequency_congruence v) D.epsilon_value
  rw [D.relative_character hN hr hbase v, star_mul]
  calc
    _ = star D.fixedFactor * (star (eisEmbedding (symbol (D.matrix v 0 0) (∏ i, p i))) *
        ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
          (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) := by ring
    _ = _ := by rw [hlocal, hbad]; ring

def fullLocalFourierWeight [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) : ℂ :=
  ∏ i, finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) (v i)

theorem controlled_local_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ, fullLocalFourierWeight hp F v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, ∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
        finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (F i) v *
          frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
            (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [mul_assoc, controlled_phase_product D hN hr hbase hp hc0 hcop hg v x]
  simp only [fullLocalFourierWeight, Finset.prod_mul_distrib]
  ring

def mixedActiveBracket [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) : ℂ :=
  if i ∈ S then
    (rootCard (Eis ⧸ Ideal.span {p i}) : ℂ)⁻¹ *
      tau (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 2 *
        (((actualSextic (Ideal.span {p i}) (hg i)) ^ 2)⁻¹)
          ((D.sigma i : Eis ⧸ Ideal.span {p i}) * (D.epsilon i : Eis ⧸ Ideal.span {p i}) *
            Ideal.Quotient.mk _ x)
  else (((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i) *
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x)

theorem mixedActiveBracket_eq_units [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (D : ControlledStratumArithmetic p N a0 c0 mode) (i : ι) (x : Eis) :
    (∑ v : (Eis ⧸ Ideal.span {p i})ˣ,
      finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i)) (mixedPrimeFunction p hg j S i) v *
        frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
          (quotientTrace (p i) (hp i)) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x) v) =
      mixedActiveBracket hp hg j S D i x := by
  have hh := actual_mixed_frequency_units (Ideal.span {p i}) (hg i) (hc i)
    (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i))
    (decide (i ∈ S)) (j i) (hj i) (D.sigma i) (D.epsilon i) (Ideal.Quotient.mk _ x)
  have hfun : mixedPrimeFunction p hg j S i = fun t =>
      if i ∈ S then zeroMark t else (actualSextic (Ideal.span {p i}) (hg i) ^ j i) t := rfl
  rw [hfun]
  by_cases hi : i ∈ S
  · simpa only [hi, decide_true, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      ite_true, markedFrequencyRow] using hh
  · simpa only [hi, decide_false, mixedFrequencyRow, mixedPrimeFunction, mixedActiveBracket,
      Bool.false_eq_true, ite_false, frequencyRow] using hh

theorem controlled_mixed_multiplier (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (x : Eis) :
    (∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
      fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      star (complexCharacter (D.relativeGamma hN hr hbase v)) *
      ShortDraftTrace.breveE (-(eisEmbedding (D.matrix v 1 1) * (eisEmbedding x / eisLam ^ 4)) /
        (eisEmbedding c0 * eisEmbedding (∏ i, p i)))) =
    (star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U x) *
      ∏ i, mixedActiveBracket hp hg j S D i x := by
  rw [controlled_local_multiplier D hN hr hbase hp hc0 hcop hg]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact mixedActiveBracket_eq_units hp hg hc j hj S D i x

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PoissonTails -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondOuterBall (Y E X₁ X₂ H : ℝ) : Finset Eis :=
  secondFrequencyCutoff (Y / (E * X₁ * X₂)) H

theorem secondOuterBall_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (Y E X₁ X₂ H : ℝ)
    (hY : 0 < Y) (hE : 0 < E) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (e : Eis) (he : e ≠ 0) (heE : ‖eisEmbedding e‖^2 ≤ E)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : primeProductNorm p S ≤ X₁) (hT : primeProductNorm p T ≤ X₂)
    (k : Eis) (hk : k ∉ secondOuterBall Y E X₁ X₂ H) :
    H ≤ (Y / (‖eisEmbedding e‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have hs : 0 < Y/(E*X₁*X₂) := by positivity
  have hn : 0 < ‖eisEmbedding e‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  have hprod : ‖eisEmbedding e‖^2 * primeProductNorm p S * primeProductNorm p T ≤ E*X₁*X₂ := by
    exact mul_le_mul (mul_le_mul heE hS (primeProductNorm_pos p hp S).le hE.le)
      hT (primeProductNorm_pos p hp T).le (mul_pos hE hX₁).le
  have hb : Y/(E*X₁*X₂) ≤
      Y/(‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2) := by
    rw [active_norm_sq_disjoint p S T hd]
    apply div_le_div_of_nonneg_left hY.le
    · exact mul_pos hn (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T))
    · simpa only [mul_assoc] using hprod
  exact (outside_secondFrequencyCutoff _ H hs k hk).le.trans
    (mul_le_mul_of_nonneg_right hb (sq_nonneg _))

theorem secondOuterBall_remainder {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y E X₁ X₂ H : ℝ),
      0 < Y → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (e : Eis), e ≠ 0 → ‖eisEmbedding e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      ‖∑' k : {k : Eis // k ∉ secondOuterBall Y E X₁ X₂ H},
        secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc A
  refine ⟨s,C,hC,?_⟩
  intro W Y E X₁ X₂ H hY hE hX₁ hX₂ hH e he heE S T hd hS hT
  exact hb S T e he W Y H hY hH (secondOuterBall Y E X₁ X₂ H)
    (fun k hk => secondOuterBall_raw_tail p hp Y E X₁ X₂ H hY hE hX₁ hX₂ e he heE S T hd hS hT k hk)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ChildCutoff -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def childFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (secondFrequencyCutoff (‖eisEmbedding a‖^2) R).filter
    (fun k => ‖eisEmbedding (a*k)‖^2 ≤ R)

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma outside_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis)
    (hk : k ∉ childFrequencyBall a R) : R < ‖eisEmbedding (a*k)‖^2 :=
  lt_of_not_ge (fun h => hk ((mem_childFrequencyBall a ha R k).mpr h))

def nonzeroChildFrequencyBall (a : Eis) (R : ℝ) : Finset Eis :=
  (childFrequencyBall a R).erase 0

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

lemma nonzeroChildFrequencyBall_empty (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : R < 1) :
    nonzeroChildFrequencyBall a R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hm := (mem_nonzeroChildFrequencyBall a ha R k).mp hk
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm
  exact (not_le_of_gt hR) ((EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq
    (a*k) (mul_ne_zero ha hk0)).trans hm.2)

def childOuterRadius (Y A E X₁ X₂ H : ℝ) : ℝ := A*E*X₁*X₂*H/Y

theorem childFrequencyBall_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) (Y A E X₁ X₂ H : ℝ)
    (hY : 0 < Y) (hA : 0 < A) (hE : 0 < E)
    (hX₁ : 0 < X₁) (_hX₂ : 0 < X₂) (hH : 0 ≤ H)
    (a e : Eis) (ha : a ≠ 0) (he : e ≠ 0)
    (haA : ‖eisEmbedding a‖^2 ≤ A) (heE : ‖eisEmbedding e‖^2 ≤ E)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : primeProductNorm p S ≤ X₁) (hT : primeProductNorm p T ≤ X₂)
    (k : Eis) (hk : k ∉ childFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)) :
    H ≤ (Y / (‖eisEmbedding e‖^2 *
      ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
  have haN : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  have heN : 0 < ‖eisEmbedding e‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  have hden : ‖eisEmbedding a‖^2 * ‖eisEmbedding e‖^2 *
      primeProductNorm p S * primeProductNorm p T ≤ A*E*X₁*X₂ := by
    exact mul_le_mul (mul_le_mul (mul_le_mul haA heE heN.le hA.le)
      hS (primeProductNorm_pos p hp S).le (mul_pos hA hE).le)
      hT (primeProductNorm_pos p hp T).le (by positivity)
  have hchild := (outside_childFrequencyBall a ha _ k hk).le
  simp only [map_mul,norm_mul,mul_pow,childOuterRadius] at hchild
  have hbound : H * (‖eisEmbedding a‖^2 * ‖eisEmbedding e‖^2 *
      primeProductNorm p S * primeProductNorm p T) ≤
      Y * (‖eisEmbedding a‖^2 * ‖eisEmbedding k‖^2) := by
    calc
      _ ≤ H*(A*E*X₁*X₂) := mul_le_mul_of_nonneg_left hden hH
      _ ≤ _ := by nlinarith [(div_le_iff₀ hY).mp hchild]
  have hcancel : H * (‖eisEmbedding e‖^2 * primeProductNorm p S *
      primeProductNorm p T) ≤ Y * ‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ haN).mp
    nlinarith [hbound]
  rw [active_norm_sq_disjoint p S T hd]
  have hdpos : 0 < ‖eisEmbedding e‖^2 * (primeProductNorm p S * primeProductNorm p T) :=
    mul_pos heN (mul_pos (primeProductNorm_pos p hp S) (primeProductNorm_pos p hp T))
  rw [div_mul_eq_mul_div, le_div_iff₀ hdpos]
  simpa only [mul_assoc] using hcancel

theorem childFrequencyBall_remainder {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y A E X₁ X₂ H : ℝ),
      0 < Y → 0 < A → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (a e : Eis), a ≠ 0 → e ≠ 0 →
      ‖eisEmbedding a‖^2 ≤ A → ‖eisEmbedding e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      ‖∑' k : {k : Eis // k ∉ childFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)},
        secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^order)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_remainder p hp hg hinj hc order
  refine ⟨s,C,hC,?_⟩
  intro W Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH a e ha he haA heE S T hd hS hT
  exact hb S T e he W Y H hY hH _
    (fun k hk => childFrequencyBall_raw_tail p hp Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH
      a e ha he haA heE S T hd hS hT k hk)

theorem nonzeroChildFrequencyBall_absolute_tail {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y A E X₁ X₂ H : ℝ),
      0 < Y → 0 < A → 0 < E → 0 < X₁ → 0 < X₂ → 0 ≤ H →
      ∀ (a e : Eis), a ≠ 0 → e ≠ 0 →
      ‖eisEmbedding a‖^2 ≤ A → ‖eisEmbedding e‖^2 ≤ E →
      ∀ (S T : Finset ι), Disjoint S T →
      primeProductNorm p S ≤ X₁ → primeProductNorm p T ≤ X₂ →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : Eis // k ≠ 0 ∧ k ∉ nonzeroChildFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^order)) := by
  obtain ⟨s,C,hC,hb⟩ := secondPairRadialMode_tail p hp hg hinj hc order
  refine ⟨s,C,hC,?_⟩
  intro W Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH a e ha he haA heE S T hd hS hT
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set Eis := {k | k ≠ 0 ∧ k ∉ nonzeroChildFrequencyBall a (childOuterRadius Y A E X₁ X₂ H)}
  let large : Set Eis := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  have hmap : ∀ k : small, k.val ∈ large := by
    intro k
    apply childFrequencyBall_raw_tail p hp Y A E X₁ X₂ H hY hA hE hX₁ hX₂ hH
      a e ha he haA heE S T hd hS hT k.val
    intro hk
    exact k.property.2 (Finset.mem_erase.mpr ⟨k.property.1,hk⟩)
  let f : small → large := fun k => ⟨k.val,hmap k⟩
  have hi : Function.Injective f := by
    intro x y h; exact Subtype.ext (congrArg (fun z : large => z.val) h)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkedTails -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def markedColumn {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a (A ∪ U) * C U

lemma markedColumn_source_support {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (C : Finset ι → ℂ) (U : Finset ι)
    (h : markedColumn slots lists a A C U ≠ 0) : C U ≠ 0 :=
  (mul_ne_zero_iff.mp h).2

theorem markedColumn_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A F : Finset ι) (C : Finset ι → ℂ) (G X M : ℝ),
      0 ≤ G → 0 < X →
      (∀ U ∈ F.powerset, ‖C U‖ ≤ G) →
      (∀ U ∈ F.powerset, C U ≠ 0 → columnLog p X U ≤ M) →
      ∀ U ∈ F.powerset, ‖markedColumn slots lists a A C U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A F C G X M hG hX hC hsupport U hU
  by_cases hz : C U = 0
  · simp only [markedColumn,hz,mul_zero,norm_zero]
    positivity
  · have hn := columnLog_norm_upper p hp X M hX U (hsupport U hU hz)
    rw [markedColumn,norm_mul]
    have hm := hmark p hp hcop slots lists a hslots ha A U
    have hnorm : 0 < primeProductNorm p U := primeProductNorm_pos p hp U
    apply (mul_le_mul hm (hC U hU) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem marked_first_kernel_remainder (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
      (F B A₁ A₂ : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), Disjoint F B →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
        (a₁ a₂ : σ → ι → ℂ),
      (slots₁ : Set σ).PairwiseDisjoint lists₁ → (slots₂ : Set σ).PairwiseDisjoint lists₂ →
      (∀ i ∈ slots₁, ∀ k ∈ lists₁ i, ‖a₁ i k‖ ≤ 1) →
      (∀ i ∈ slots₂, ∀ k ∈ lists₂ i, ‖a₂ i k‖ ≤ 1) →
      ∀ (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0 ≤ G₁ → 0 ≤ G₂ → 0 < X₁ → 0 < X₂ → 0 < K → 0 ≤ P →
      (∀ U ∈ F.powerset, ‖C₁ U‖ ≤ G₁) → (∀ U ∈ F.powerset, ‖C₂ U‖ ≤ G₂) →
      (∀ U ∈ F.powerset, C₁ U ≠ 0 → columnLog p X₁ U ≤ M₁) →
      (∀ U ∈ F.powerset, C₂ U ≠ 0 → columnLog p X₂ U ≤ M₂) →
      ∀ d : Eis, d ≠ 0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let G₁' := (2:ℝ)^A₁.card * Cm * U₁^ε * G₁
      let G₂' := (2:ℝ)^A₂.card * Cm * U₂^ε * G₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑' h : {h : Eis // h ∉ T}, actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (markedColumn slots₁ lists₁ a₁ A₁ C₁) (markedColumn slots₂ lists₂ a₂ A₂ C₂)
        W (fun _ => 1) (fun _ => 1) X₁ X₂ K d h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*K) *
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_actualFirstKernel_disk_remainder order
  obtain ⟨Cm,hCm,hmark⟩ := markedColumn_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc F B A₁ A₂ v ε₁ ε₂ hFB
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ hl₁ hl₂ ha₁ ha₂ C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂
    hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hs₁ hs₂ d hd
  apply htail p hp hinj hcop hg hc F B v ε₁ ε₂ hFB _ _ W _ _ X₁ X₂ K P M₁ M₂
    (by positivity) (by positivity) hX₁ hX₂ hK hP
  · exact hmark p hp hcop slots₁ lists₁ a₁ hl₁ ha₁ A₁ F C₁ G₁ X₁ M₁ hG₁ hX₁ hC₁ hs₁
  · exact hmark p hp hcop slots₂ lists₂ a₂ hl₂ ha₂ A₂ F C₂ G₂ X₂ M₂ hG₂ hX₂ hC₂ hs₂
  · intro U hU hn
    exact hs₁ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · intro U hU hn
    exact hs₂ U hU (markedColumn_source_support _ _ _ _ _ _ hn)
  · exact hd

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstWholeTail -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_supported_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 → ∀ T : Finset O,
      (∀ N∈F.powerset,∀ Q∈F.powerset,Disjoint N Q → C₁ N≠0 → C₂ Q≠0 →
        ∀ h : O,h∉T → P≤(K/(‖eisEmbedding d‖^2*
          primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2) →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P)^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd T hT
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P)^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P:=hP
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P)^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P hK hP d hd T (hT N hNF R hRF hNR hn hr)
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [ite_eq_left hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,ite_eq_right hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Quadratic -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_family_quadratic_hybrid_orientation :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal Eis) (cols : n → Ideal Eis),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (rows i) (primaryGenerator (cols j)) * a j‖ ^ 2) ≤
        C * (M * N) ^ ε * (M + N) * ∑ j, ‖a j‖ ^ 2 := by
  intro ε hε
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  let B : Matrix n m ℂ := fun j i => quadraticRow (rows i) (primaryGenerator (cols j))
  have hB : ‖FiniteSieveOperator.operator B‖ ^ 2 ≤ sieveNorm N M :=
    family_squared_norm_le cols rows hc hr N M hcols hrows
  have hBT : B.conjTranspose =
      (fun i j => quadraticRow (rows i) (primaryGenerator (cols j))) := by
    ext i j
    exact canonical_quadraticRow_star (rows i) (hrows i).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose a
  rw [FiniteSieveOperator.operator_conjTranspose_norm, hBT] at he
  have henergy : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply he.trans
  calc
    _ ≤ sieveNorm N M * ∑ j, ‖a j‖ ^ 2 := mul_le_mul_of_nonneg_right hB henergy
    _ ≤ (C * (N * M) ^ ε * (N + M)) * ∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hsharp N M hN hM) henergy
    _ = _ := by rw [mul_comm N M, add_comm N M]

theorem finite_squarefree_quadratic_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows cols : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ J ∈ cols, Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X) →
    ∀ a : Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
        C * (K * X) ^ ε * (K + X) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
  obtain ⟨C, hC, hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  intro K X hK hX rows cols hrows hcols a
  have hf := squarefree_all_column_energy (fun J : cols => J.val) Subtype.val_injective X K
    (fun J => hcols J.val J.property) (fun J => a J.val)
  have hi (k : idealRange K) :
      (∑ J : cols, quadraticRow k.val (primaryGenerator J.val) * a J.val) =
        ∑ J ∈ cols, quadraticRow k.val (primaryGenerator J) * a J :=
    Finset.sum_coe_sort cols (fun J => quadraticRow k.val (primaryGenerator J) * a J)
  simp_rw [hi] at hf
  rw [Finset.sum_coe_sort (idealRange K)
    (fun k => ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2),
    Finset.sum_coe_sort cols (fun J => ‖a J‖ ^ 2)] at hf
  have hr : rows ⊆ idealRange K := fun k hk => mem_idealRange.mpr (hrows k hk)
  have he : (∑ k ∈ rows, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2) ≤
      ∑ k ∈ idealRange K, ‖∑ J ∈ cols, quadraticRow k (primaryGenerator J) * a J‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hr (by intro k _ _; exact sq_nonneg _)
  apply (he.trans hf).trans
  calc
    _ ≤ 4 * (C * (X * K) ^ ε * (X + K)) * ∑ J ∈ cols, ‖a J‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (hsharp X K hX hK) (by norm_num)
    _ = _ := by rw [mul_comm X K, add_comm X K]; ring

theorem quadratic_squarefree_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquad⟩ := finite_squarefree_quadratic_energy (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (product_fiber_card pairs J (ht J hJ).1.ne_zero)).trans
    exact (hdiv J (ht J hJ).1.ne_zero).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber
    (hquad K X hK hX rows target hrows ht)
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Admissible (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal Eis × Ideal Eis → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquadratic⟩ := finite_family_quadratic_hybrid_orientation (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal Eis) (hJ : J ∈ target) :
      Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hquad (f : Ideal Eis → ℂ) :
      (∑ k ∈ rows, ‖∑ J ∈ target, quadraticRow k (primaryGenerator J) * f J‖ ^ 2) ≤
        (Cq * (K * X) ^ (ε / 2) * (K + X)) * ∑ J ∈ target, ‖f J‖ ^ 2 := by
    have he := hquadratic K X hK hX
      (fun k : rows => k.val) (fun J : target => J.val)
      Subtype.val_injective Subtype.val_injective
      (fun k => hrows k.val k.property) (fun J => ht J.val J.property)
      (fun J => f J.val)
    have hi (k : rows) :
        (∑ J : target, quadraticRow k.val (primaryGenerator J.val) * f J.val) =
        ∑ J ∈ target, quadraticRow k.val (primaryGenerator J) * f J :=
      Finset.sum_coe_sort target (fun J => quadraticRow k.val (primaryGenerator J) * f J)
    simp_rw [hi] at he
    rw [Finset.sum_coe_sort rows
      (fun k => ‖∑ J ∈ target, quadraticRow k (primaryGenerator J) * f J‖ ^ 2),
      Finset.sum_coe_sort target (fun J => ‖f J‖ ^ 2)] at he
    exact he
  have hfiber (J : Ideal Eis) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (CanonicalQuadraticSieve.product_fiber_card pairs J (ht J hJ).1.1)).trans
    exact (hdiv J (ht J hJ).1.1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => quadraticRow k (primaryGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber hquad
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy
    (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
    (hrows : ∀ k ∈ rows, Admissible k) (B : Ideal Eis)
    (a : Ideal Eis × Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (p.1 * p.2)) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs,
      quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p) =
      quadraticRow k (primaryGenerator B) * ∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (p.1 * p.2)) * a p := by
    simp only [primaryGenerator_mul,
      canonical_quadraticRow_argument_mul k (hrows k hk), Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one k _)

theorem quadratic_product_column_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Admissible (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

theorem quadratic_squarefree_product_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal Eis) (a : Ideal Eis × Ideal Eis → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_squarefree_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs (fun k hk => (hrows k hk).1) B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.HybridReduction -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_inverse_cubic_energy
    (Jset Pset : Finset (Ideal Eis)) (N L : ℝ)
    (hJ : ∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N)
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L)
    (a : Ideal Eis → ℂ) :
    (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
      CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  let A : Matrix Jset Pset ℂ := fun J P => CubicSieve.idealKernel P.val J.val
  have hnorm : CubicSieve.squaredNorm (fun J P => star (A J P)) =
      CubicSieve.squaredNorm A :=
    congrArg (fun z : ℝ => z ^ 2) (CubicSieve.operator_conjugate_norm A)
  have hfamily : CubicSieve.squaredNorm A ≤ CubicSieve.sieveNorm N L :=
    CubicSieve.family_squared_norm_le
      (fun J : Jset => J.val) (fun P : Pset => P.val)
      Subtype.val_injective Subtype.val_injective N L
      (fun J => hJ J.val J.property) (fun P => hP P.val P.property)
  have he := CubicSieve.energy_le_squaredNorm (fun J P => star (A J P)) (fun P => a P.val)
  rw [hnorm] at he
  have he' := he.trans (mul_le_mul_of_nonneg_right hfamily
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hinner (J : Jset) :
      (∑ P : Pset, star (A J P) * a P.val) =
        ∑ P ∈ Pset, a P * inverseCubicKernel P J.val := by
    simp only [A, inverseCubicKernel, CubicSieve.idealKernel, mul_comm]
    exact Finset.sum_coe_sort Pset
      (fun P => a P * star (ConcreteTraceCRT.eisEmbedding
        (CubicJacobiGlobal.idealSymbol P (primaryGenerator J.val))))
  simp_rw [hinner] at he'
  rw [Finset.sum_coe_sort Jset
    (fun J => ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2),
    Finset.sum_coe_sort Pset (fun P => ‖a P‖ ^ 2)] at he'
  exact he'

theorem hybrid_quadratic_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (Pset : Finset (Ideal Eis)) (coef : Ideal Eis → Ideal Eis → ℂ)
      (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (Cbound : ℝ),
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * Cbound *
        ∑ p ∈ pairs, ∑ c ∈ cset p.1,
          ‖∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))‖ ^ 2 := by
  obtain ⟨C, hC, hquadratic⟩ := quadratic_squarefree_product_energy_fixed_factor ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta Cbound hcount hbeta
  let F (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :=
    ∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))
  have he := hquadratic K X hK hX rows pairs hrows hpairs B
    (fun p => ∑ c ∈ cset p.1, beta c p.1 p.2 * F p c)
  apply he.trans
  have hlocal (p : Ideal Eis × Ideal Eis) (hp : p ∈ pairs) :
      ‖∑ c ∈ cset p.1, beta c p.1 p.2 * F p c‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
    exact (bounded_finset_coefficient_sum_sq (cset p.1)
      (fun c => beta c p.1 p.2) (F p) (hbeta p hp)).trans
        (mul_le_mul_of_nonneg_right (hcount p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ C * (K * X) ^ ε * (K + X) *
        ∑ p ∈ pairs, Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; simp only [F]; ring

theorem cubic_product_row_bound_of_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis) (S : ℝ),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ a : Ideal Eis → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
          S * ∑ P ∈ Pset, ‖a P‖ ^ 2) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * S * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro N hN pairs Jset Pset mBad S hmap hJset hcubic a
  let E (J : Ideal Eis) := ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2
  have hfiber (J : Ideal Eis) (hJ : J ∈ Jset) :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤ D * N ^ ε := by
    have hJ0 := (hJset J hJ).1.1.ne_zero
    have hc : ((pairs.filter (fun p => p.2 * (mBad * p.1) = J)).card : ℝ) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ) :=
      Nat.cast_le.mpr (scaled_product_fiber_card pairs mBad J hJ0)
    have hd := (hdiv J hJ0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hJset J hJ).2 hε.le) hD.le)
    exact (by simpa using hc :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ)).trans hd
  have hf := fiber_energy_bound pairs Jset (fun p => p.2 * (mBad * p.1))
    (fun _ => 1) (fun _ => D * N ^ ε) E hmap (fun _ _ => sq_nonneg _) hfiber
  simp only [one_mul, ← Finset.mul_sum] at hf
  apply hf.trans
  calc
    _ ≤ (D * N ^ ε) * (S * ∑ P ∈ Pset, ‖a P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hcubic a) (by positivity)
    _ = _ := by ring

theorem cubic_product_row_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hb⟩ := cubic_product_row_bound_of_sieve ε hε
  refine ⟨D, hD, ?_⟩
  intro N L hN pairs Jset Pset mBad hmap hJ hP a
  exact hb N hN pairs Jset Pset mBad (CubicSieve.sieveNorm N L) hmap hJ
    (finite_inverse_cubic_energy Jset Pset N L hJ hP) a

theorem hybrid_fixed_block_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L : ℝ, 1 ≤ K → 1 ≤ X → 1 ≤ N →
    ∀ (rows : Finset (Ideal Eis)) (pairs cubicPairs : Finset (Ideal Eis × Ideal Eis))
      (Hset Jset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (coef : Ideal Eis → Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
      (Cbound Ebound : ℝ), 0 ≤ Cbound →
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∀ p ∈ pairs, p.2 ∈ Hset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ cubicPairs) →
      (∀ u ∈ cubicPairs, u.2 * (mBad * u.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      (∀ h ∈ Hset, (∑ P ∈ Pset, ‖coef h P‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * Cbound * (Hset.card : ℝ) *
        CubicSieve.sieveNorm N L * Ebound := by
  obtain ⟨Cq, hCq, hquad⟩ := hybrid_quadratic_reduction ε hε
  obtain ⟨D, hD, hcube⟩ := cubic_product_row_sieve_norm ε hε
  refine ⟨Cq * D, mul_pos hCq hD, ?_⟩
  intro K X N L hK hX hN rows pairs cubicPairs Hset Jset Pset hrows hpairs
    B mBad cset coef beta Cbound Ebound hCbound hcount hbeta hH hmc hmap hJ hP hcoef
  let E (h m c : Ideal Eis) := ‖∑ P ∈ Pset,
    coef h P * inverseCubicKernel P (c * (mBad * m))‖ ^ 2
  have hnorm : 0 ≤ CubicSieve.sieveNorm N L := sq_nonneg _
  have he := hquad K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta
    Cbound hcount hbeta
  have hpos := positive_triple_enlarge pairs cset Hset cubicPairs E hH hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      (Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound) := by
    apply hpos.trans
    calc
      _ ≤ ∑ _h ∈ Hset, D * N ^ ε * CubicSieve.sieveNorm N L * Ebound := by
        apply Finset.sum_le_sum
        intro h hh
        apply (hcube N L hN cubicPairs Jset Pset mBad hmap hJ hP (coef h)).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hh)
          (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)) hnorm)
      _ = _ := by simp
  apply he.trans
  calc
    _ ≤ (Cq * (K * X) ^ ε * (K + X) * Cbound) *
        ((Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound)) := by
      apply mul_le_mul_of_nonneg_left htotal
      positivity
    _ = _ := by
      rw [Real.mul_rpow (show 0 ≤ K * X by positivity) (show 0 ≤ N by linarith)]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Quotients -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def quotientSupport (D : Ideal Eis) (S : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  (S.filter (fun I => D ∣ I)).image (idealQuotient D)

@[simp] theorem mem_quotientSupport (D J : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) :
    J ∈ quotientSupport D S ↔ D * J ∈ S := by
  constructor
  · intro hJ
    obtain ⟨I, hI, he⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIS, hDI⟩ := Finset.mem_filter.mp hI
    rw [← he, idealQuotient_mul hDI]
    exact hIS
  · intro hJ
    refine Finset.mem_image.mpr ⟨D * J, Finset.mem_filter.mpr ⟨hJ, dvd_mul_right _ _⟩, ?_⟩
    exact mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D J))

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal Eis) (S : Finset (Ideal Eis)) (f : Ideal Eis → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact idealQuotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

theorem quotientSupport_nonzero (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, I ≠ 0)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) : J ≠ 0 := by
  have h := hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)
  exact (mul_ne_zero_iff.mp h).2

theorem quotientSupport_quadratic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CanonicalQuadraticSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CanonicalQuadraticSieve.Admissible J :=
  admissible_of_dvd (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ))
    (dvd_mul_left _ _)

theorem quotientSupport_cubic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CubicSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

theorem quotientSupport_norm_le (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (N : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0) (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ N)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J : ℝ) ≤ N := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hn : Ideal.absNorm J ≤ Ideal.absNorm (D * J) := by
    apply Nat.le_of_dvd
    · exact Nat.pos_of_ne_zero (fun hz => hS0 _ hDJ (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact map_dvd Ideal.absNorm (dvd_mul_left J D)
  exact (Nat.cast_le.mpr hn).trans (hS _ hDJ)

theorem quotientSupport_shell (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    max 1 (L / (Ideal.absNorm D : ℝ)) ≤ (Ideal.absNorm J : ℝ) ∧
      (Ideal.absNorm J : ℝ) ≤ 2 * max 1 (L / (Ideal.absNorm D : ℝ)) := by
  have hDJ := (mem_quotientSupport D J hD S).mp hJ
  have hnD : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hJ0 := quotientSupport_nonzero D hD S hS0 J hJ
  have hnJ : 1 ≤ (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hJ0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs := hS (D * J) hDJ
  simp only [map_mul, Nat.cast_mul] at hs
  constructor
  · refine max_le hnJ ((div_le_iff₀ hnD).mpr ?_)
    simpa only [mul_comm] using hs.1
  · have hj : (Ideal.absNorm J : ℝ) ≤ 2 * (L / (Ideal.absNorm D : ℝ)) := by
      have hj := (le_div_iff₀ hnD).mpr (show
          (Ideal.absNorm J : ℝ) * (Ideal.absNorm D : ℝ) ≤ 2 * L by
        simpa only [mul_comm] using hs.2)
      simpa only [mul_div_assoc] using hj
    exact hj.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

theorem quotient_hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (hR : R ≠ 0) (S : Finset (Ideal Eis)) (L : ℝ)
    (hS0 : ∀ I ∈ S, I ≠ 0)
    (hS : ∀ I ∈ S, L ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ I ∈ S, ‖a I‖ ≤ 1) :
    (∑ P ∈ quotientSupport R S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply hybridCubicCoefficient_energy R r h t (quotientSupport R S)
    (max 1 (L / (Ideal.absNorm R : ℝ))) (le_max_left _ _)
  · exact quotientSupport_shell R hR S L hS0 hS
  · intro P hP
    exact ha (R * P) ((mem_quotientSupport R P hR S).mp hP)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.DivisorExtraction -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_divisor_overlap_zero (R r P c m : Ideal Eis)
    (hP : primaryGenerator P ≠ 0) (hcm : primaryGenerator (c * m) ≠ 0)
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    inverseCubicKernel P (c * m) = 0 := by
  apply inverseCubicKernel_eq_zero_of_not_coprime P (c * m) hP hcm
  intro hcop
  have hPc := hcop.of_isCoprime_of_dvd_right (dvd_mul_right c m)
  exact hRr ((hPc.of_isCoprime_of_dvd_left hRP).of_isCoprime_of_dvd_right hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal Eis)) (hrows : ∀ k ∈ rows, k ≠ 0)
    (R r : Ideal Eis) (hRr : IsCoprime R r) (F : Ideal Eis → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal Eis) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F

theorem double_column_divisor_reindex {A : Type*} [AddCommMonoid A]
    (Pset cset : Finset (Ideal Eis)) (R r : Ideal Eis)
    (F : Ideal Eis → Ideal Eis → A) :
    (∑ P ∈ Pset, ∑ c ∈ cset, if R ∣ P ∧ r ∣ c then F P c else 0) =
      ∑ P ∈ quotientSupport R Pset, ∑ c ∈ quotientSupport r cset, F (R * P) (r * c) := by
  calc
    _ = ∑ P ∈ Pset with R ∣ P, ∑ c ∈ cset with r ∣ c, F P c := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : R ∣ P
      · simp only [hd, true_and, ite_true]
      · simp [hd]
    _ = ∑ P ∈ quotientSupport R Pset, ∑ c ∈ cset with r ∣ c, F (R * P) c :=
      sum_quotientSupport R Pset (fun P => ∑ c ∈ cset with r ∣ c, F P c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_quotientSupport r cset (F (R * P))

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.DivisorSum -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridDivisorPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis × Ideal Eis) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

theorem hybridDivisorPool_bounds (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K)
    (D : Ideal Eis) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ 0 ∧ (Ideal.absNorm D : ℝ) ≤ K := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (hrows k hk).1 hdiv,
    (QuadraticMainBoundary.norm_le_of_dvd (hrows k hk).1 hdiv).trans (hrows k hk).2⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal Eis)) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).1⟩,
      Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).2⟩⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows K hrows
  have hsum := finite_inverse_norm_sum (hybridDivisorPool rows) K
    (fun D hD => (hb D hD).1) (fun D hD => (hb D hD).2)
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum 2

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.OriginalBlock -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_original_quotient_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L A H : ℝ,
      1 ≤ K → 1 ≤ X → 1 ≤ N → 1 ≤ A → 1 ≤ H →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (cset : Ideal Eis → Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧
        L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
      (∀ p ∈ pairs, p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1,
        c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta (r * c) p.1 p.2‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
          (∑ p ∈ pairs, quadraticRow k (primaryGenerator (p.1 * p.2)) *
            (∑ c ∈ cset p.1, hybridColumnCoefficient R r beta c p.1 p.2 *
              (∑ P ∈ quotientSupport R Pset,
                hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, hblock⟩ := hybrid_fixed_block_sieve_norm ε hε
  refine ⟨C * (128 * 128 * 256), by positivity, ?_⟩
  intro K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset pairs cset a beta
    hrows hn hP ha hpairs hhs hcs hbeta
  let Hset := pairs.image Prod.snd
  let mc := (pairs.image Prod.fst).biUnion fun m => (cset m).image fun c => (m, c)
  have hRr : R * r ≠ 0 := mul_ne_zero hR hr
  have hn0 : ∀ n ∈ nset, n ≠ 0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hP0 : ∀ P ∈ Pset, P ≠ 0 := fun P hP' => (hP P hP').1.1.ne_zero
  have hHcount : (Hset.card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real Hset H hH
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).1
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).2
  have hcCount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ 128 * A := by
    intro p hp
    exact DescentFiberCost.finite_ideal_count_real (cset p.1) A hA
      (fun c hc => (hcs p hp c hc).1) (fun c hc => (hcs p hp c hc).2.1)
  have hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc := by
    intro p hp c hc
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  have hmap : ∀ u ∈ mc, u.2 * (1 * u.1) ∈ quotientSupport r nset := by
    intro u hu
    obtain ⟨m, hm, cu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp cu
    apply (mem_quotientSupport r (c * (1 * p.1)) hr nset).mpr
    simpa only [one_mul, mul_assoc] using (hcs p hp c hc).2.2
  have he := hblock K X N (2 * L) hK hX hN
    (quotientSupport (R * r) rows) pairs mc Hset (quotientSupport r nset)
    (quotientSupport R Pset)
    (fun k hk => ⟨quotientSupport_quadratic_admissible (R * r) hRr rows
        (fun k hk => (hrows k hk).1) k hk,
      quotientSupport_norm_le (R * r) hRr rows K
        (fun k hk => (hrows k hk).1.1) (fun k hk => (hrows k hk).2) k hk⟩)
    hpairs 1 1 cset (fun h => hybridCubicCoefficient R r h t a)
    (hybridColumnCoefficient R r beta) (128 * A) 256 (by positivity) hcCount
    (fun p hp c hc => hybridColumnCoefficient_norm_le_one R r c p.1 p.2 beta (hbeta p hp c hc))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hmc hmap
    (fun J hJ => ⟨quotientSupport_cubic_admissible r hr nset (fun n hn' => (hn n hn').1) J hJ,
      quotientSupport_norm_le r hr nset N hn0 (fun n hn' => (hn n hn').2) J hJ⟩)
    (fun P hP' => ⟨quotientSupport_cubic_admissible R hR Pset (fun P hP' => (hP P hP').1) P hP',
      quotientSupport_norm_le R hR Pset (2 * L) hP0 (fun P hP' => (hP P hP').2.2) P hP'⟩)
    (fun h _ => quotient_hybridCubicCoefficient_energy R r h t hR Pset L hP0
      (fun P hP' => (hP P hP').2) a ha)
  simp only [one_mul] at he
  have hsqrt : ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (Ideal.absNorm R : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [norm_mul, mul_pow, hsqrt]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
  calc
    _ ≤ (Ideal.absNorm R : ℝ)⁻¹ *
      (C * (K * X * N) ^ ε * (K + X) * (128 * A) * (128 * H) *
        CubicSieve.sieveNorm N (2 * L) * 256) := by
      gcongr
      exact sq_nonneg _
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Reconstruction -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def supportedHybridRow (S : Finset (Ideal Eis × Ideal Eis)) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ p ∈ S, ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta p.1 p.2 *
    (quadraticRow k (primaryGenerator (p.1 * p.2)) * inverseCubicKernel P p.1 *
      (if IsCoprime P p.2 then 1 else 0) * (if IsCoprime k P then 1 else 0))

theorem supportedHybridRow_product (nset bset Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    supportedHybridRow (nset ×ˢ bset) Pset a beta k = hybridRow Pset nset bset a beta k := by
  simp only [supportedHybridRow, hybridRow, hybridInner, Finset.sum_product,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

def reconstructedHybridTerm (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) (P : Ideal Eis)
    (d : HybridColumnData) : ℂ :=
  a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) *
    ((if IsCoprime k d.square then 1 else 0) *
      (if IsCoprime k (P * d.common) then 1 else 0) *
      quadraticRow k (primaryGenerator (d.residualN * d.residualB)) *
      inverseCubicKernel P (d.common * d.residualN) *
      (if IsCoprime P (d.residualB * d.square) then 1 else 0))

theorem supportedHybridRow_reconstruct
    (S : Finset (Ideal Eis × Ideal Eis)) (Pset : Finset (Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0 ∧
      primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k : Ideal Eis) (hk : Admissible k) :
    supportedHybridRow S Pset a beta k =
      ∑ d ∈ hybridColumnSupport S, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d := by
  unfold supportedHybridRow
  rw [hybrid_finite_column_reindex S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdS := (mem_hybridColumnSupport S d).mp hd
  have hdprim := hS d.reconstruct hdS
  have hct := (d.primary_factors hdprim.2.2.1 hdprim.2.2.2).2.2.2.2
  apply Finset.sum_congr rfl
  intro P hPP
  unfold reconstructedHybridTerm
  exact congrArg
    (fun z : ℂ => a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) * z)
    (hybrid_original_kernel_decomposition k P
    (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2)
    d.common d.residualN d.residualB d.square hk (hP P hPP) hdprim.2.2.1 rfl rfl hct)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Dyadic -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridSquarePool (S : Finset (Ideal Eis × Ideal Eis)) : Finset (Ideal Eis) :=
  (hybridColumnSupport S).image HybridColumnData.square

def hybridCommonBlock (S : Finset (Ideal Eis × Ideal Eis)) (N : ℝ)
    (i : Fin (columnDyadicLength N + 1)) (t : Ideal Eis) : Finset HybridColumnData :=
  (hybridColumnSupport S).filter fun d =>
    d.square = t ∧ divisorDyadicLabel N d.common = i

theorem hybrid_dyadic_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (f : HybridColumnData → A) :
    (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ j : Fin (columnDyadicLength B + 1),
        ∑ i : Fin (columnDyadicLength N + 1),
          ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
            ∑ d ∈ hybridCommonBlock S N i t, f d := by
  have ht : (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ t ∈ hybridSquarePool S, ∑ d ∈ hybridColumnSupport S with d.square = t, f d := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f
  rw [ht, sum_divisorDyadicBins (hybridSquarePool S) B]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hi := Finset.sum_fiberwise
    ((hybridColumnSupport S).filter fun d => d.square = t)
    (fun d => divisorDyadicLabel N d.common) f
  simpa only [Finset.filter_filter, hybridCommonBlock] using hi.symm

theorem hybridSquarePool_bounds (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (t : Ideal Eis) (ht : t ∈ hybridSquarePool S) :
    1 ≤ (Ideal.absNorm t : ℝ) ∧ (Ideal.absNorm t : ℝ) ≤ B := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
  have hb0 : (d.common * d.residualB) * d.square ^ 2 ≠ 0 :=
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero _ d.square_ne_zero)
  refine ⟨QuadraticMainBoundary.norm_one_le d.square_ne_zero, ?_⟩
  apply (QuadraticMainBoundary.norm_le_of_dvd hb0 ?_).trans
    (hS d.reconstruct ((mem_hybridColumnSupport S d).mp hd))
  exact dvd_mul_of_dvd_right (dvd_pow_self d.square (by norm_num : 2 ≠ 0)) _

theorem hybridSquarePool_bin_count (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) :
    ((divisorDyadicBin (hybridSquarePool S) B j).card : ℝ) ≤
      256 * divisorDyadicScale j.val := by
  have hscale := divisorDyadicScale_ge_one j.val
  have hb := divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B hS) j
  have hc := DescentFiberCost.finite_ideal_count_real
    (divisorDyadicBin (hybridSquarePool S) B j) (2 * divisorDyadicScale j.val)
    (by linarith) (fun t ht hz => by
      have hp := (hb t ht).1
      simp [hz] at hp
      linarith) (fun t ht => (hb t ht).2)
  linarith

theorem hybridCommonBlock_bounds
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B)
    (i : Fin (columnDyadicLength N + 1)) (j : Fin (columnDyadicLength B + 1))
    (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j)
    (d : HybridColumnData) (hd : d ∈ hybridCommonBlock S N i t) :
    let C := divisorDyadicScale i.val
    let T := divisorDyadicScale j.val
    C ≤ (Ideal.absNorm d.common : ℝ) ∧ (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
  have hs := hS d.reconstruct ((mem_hybridColumnSupport S d).mp hdS)
  have hc1 := QuadraticMainBoundary.norm_one_le d.common_ne_zero
  have hcn : (Ideal.absNorm d.common : ℝ) ≤ N :=
    (QuadraticMainBoundary.norm_le_of_dvd d.n_squarefree.ne_zero (dvd_mul_right _ _)).trans hs.1
  have hcb := divisorDyadicLabel_bounds N d.common hc1 hcn
  rw [hdi] at hcb
  have hcLow : divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) :=
    max_le hc1 hcb.1.le
  have hcHigh : (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val := by
    have hh : (2 : ℝ) ^ i.val / 2 ≤ divisorDyadicScale i.val := le_max_right _ _
    linarith [hcb.2]
  have htLow := (divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B (fun p hp => (hS p hp).2)) j t ht).1
  rw [← hdt] at htLow
  refine ⟨hcLow, hcHigh, ?_⟩
  exact d.residual_norm_bounds N B (divisorDyadicScale i.val) (divisorDyadicScale j.val)
    hN hB (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val]) hs.1 hs.2 hcLow htLow

theorem hybrid_square_dyad_energy
    (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) (rows : Finset (Ideal Eis))
    (F : Ideal Eis → Ideal Eis → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      (∑ k ∈ rows, ‖F t k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j, F t k‖ ^ 2) ≤
      (256 * divisorDyadicScale j.val) ^ 2 * E := by
  let Tset := divisorDyadicBin (hybridSquarePool S) B j
  have hc := hybridSquarePool_bin_count S B hS j
  calc
    _ ≤ (Tset.card : ℝ) * ∑ t ∈ Tset, ∑ k ∈ rows, ‖F t k‖ ^ 2 := by
      calc
        _ ≤ ∑ k ∈ rows, (Tset.card : ℝ) * ∑ t ∈ Tset, ‖F t k‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          simpa using bounded_finset_coefficient_sum_sq Tset (fun _ => 1) (fun t => F t k)
            (by simp)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Tset.card : ℝ) * ∑ _t ∈ Tset, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (Nat.cast_nonneg _)
    _ = (Tset.card : ℝ) ^ 2 * E := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) hE

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.Grid -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section FiniteGrid
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]

def gridCommonSupport (T : Finset ((M × H) × C)) (m : M) : Finset C :=
  (T.filter fun u => u.1.1 = m).image Prod.snd

theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨hpc, rfl⟩, rfl⟩
  · intro u hu
    have hup := (Finset.mem_filter.mp hu).2
    simp only [← hup, Prod.eta]

end FiniteGrid

def HybridColumnData.gridIndex (d : HybridColumnData) :
    (Ideal Eis × Ideal Eis) × Ideal Eis := ((d.residualN, d.residualB), d.common)

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht : d.square = e.square := hd.trans he.symm
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

def hybridGridSupport (D : Finset HybridColumnData) :
    Finset ((Ideal Eis × Ideal Eis) × Ideal Eis) := D.image HybridColumnData.gridIndex

theorem hybrid_grid_reindex (D : Finset HybridColumnData) (t : Ideal Eis)
    (hD : ∀ d ∈ D, d.square = t) (f : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ p ∈ (hybridGridSupport D).image Prod.fst,
        ∑ c ∈ gridCommonSupport (hybridGridSupport D) p.1,
          if (p, c) ∈ hybridGridSupport D then f c p.1 p.2 else 0 := by
  have he : (∑ d ∈ D, f d.common d.residualN d.residualB) =
      ∑ u ∈ hybridGridSupport D, f u.2 u.1.1 u.1.2 := by
    symm
    apply Finset.sum_image
    intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg
  rw [he]
  exact finite_triple_support_reindex (hybridGridSupport D) _

theorem gridCommonSupport_origin (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (hybridGridSupport D) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = c := by
  obtain ⟨u, hu, huc⟩ := Finset.mem_image.mp hc
  obtain ⟨huT, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp huT
  exact ⟨d, hd, hum, huc⟩

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ExtractedGrid -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def quotientGridSupport (r : Ideal Eis) (T : Grid) : Grid :=
  (T.filter fun u => r ∣ u.2).image fun u => (u.1, idealQuotient r u.2)

@[simp] theorem mem_quotientGridSupport (r : Ideal Eis) (hr : r ≠ 0)
    (T : Grid) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :
    (p, c) ∈ quotientGridSupport r T ↔ (p, r * c) ∈ T := by
  constructor
  · intro hu
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hu
    obtain ⟨huT, hru⟩ := Finset.mem_filter.mp hu
    have hp : u.1 = p := congrArg Prod.fst he
    have hc : idealQuotient r u.2 = c := congrArg Prod.snd he
    have hec : r * c = u.2 := by rw [← hc, idealQuotient_mul hru]
    simpa only [← hp, hec, Prod.eta] using huT
  · intro hu
    refine Finset.mem_image.mpr ⟨(p, r * c), Finset.mem_filter.mpr ⟨hu, dvd_mul_right _ _⟩, ?_⟩
    refine Prod.ext (show p = p from rfl) ?_
    exact mul_left_cancel₀ hr (idealQuotient_mul (dvd_mul_right r c))

theorem sum_quotientGridSupport {A : Type*} [AddCommMonoid A]
    (r : Ideal Eis) (T : Grid) (f : (Ideal Eis × Ideal Eis) × Ideal Eis → A) :
    (∑ u ∈ T, if r ∣ u.2 then f u else 0) =
      ∑ u ∈ quotientGridSupport r T, f (u.1, r * u.2) := by
  rw [← Finset.sum_filter, quotientGridSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [idealQuotient_mul (Finset.mem_filter.mp hu).2]
  · intro u hu v hv he
    apply Prod.ext
    · simpa only using congrArg Prod.fst he
    · exact idealQuotient_injective_on r (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2 (congrArg Prod.snd he)

theorem quotientGridSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis)
    (hu : (p, c) ∈ quotientGridSupport r (hybridGridSupport D)) :
    ∃ d ∈ D, (d.residualN, d.residualB) = p ∧ d.common = r * c := by
  have hm := (mem_quotientGridSupport r hr (hybridGridSupport D) p c).mp hu
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  exact ⟨d, hd, congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem quotientGridCommonSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (quotientGridSupport r (hybridGridSupport D)) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = r * c := by
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hc
  obtain ⟨huQ, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, hp, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 huQ
  refine ⟨d, hd, (congrArg Prod.fst hp).trans hum, ?_⟩
  simpa only [he] using hdc

def extractedGridCoefficient (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  if ((m, h), c) ∈ T then beta c m h * (if IsCoprime R (h * t) then 1 else 0) else 0

theorem extractedGridCoefficient_norm_le_one (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (hb : ∀ u ∈ T, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1)
    (c m h : Ideal Eis) : ‖extractedGridCoefficient T R t beta c m h‖ ≤ 1 := by
  unfold extractedGridCoefficient
  split_ifs with hu hcop
  · simpa using hb ((m, h), c) hu
  · simp
  · simp

def gridDivisorHybridBlock (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) : ℂ :=
  ∑ u ∈ T, if r ∣ u.2 then ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (quadraticRow k (primaryGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0)
    else 0 else 0

theorem gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hQ : quotientGridSupport r T = ∅) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport, hQ]
  exact Finset.sum_empty

theorem gridDivisorHybridBlock_extract
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hR : R ≠ 0) (hr : r ≠ 0)
    (hk : Admissible ((R * r) * k))
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P) :
    gridDivisorHybridBlock T Pset a beta t ((R * r) * k) R r =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        ∑ p ∈ (quotientGridSupport r T).image Prod.fst,
          quadraticRow k (primaryGenerator (p.1 * p.2)) *
            ∑ c ∈ gridCommonSupport (quotientGridSupport r T) p.1,
              hybridColumnCoefficient R r (extractedGridCoefficient T R t beta) c p.1 p.2 *
                ∑ P ∈ quotientSupport R Pset,
                  hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1) := by
  have hmask (P h : Ideal Eis) :
      (if IsCoprime (R * P) (h * t) then (1 : ℂ) else 0) =
      (if IsCoprime R (h * t) then 1 else 0) *
        (if IsCoprime P (h * t) then 1 else 0) := by
    simp only [IsCoprime.mul_left_iff]
    split_ifs <;> simp_all
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport]
  have hinner (u : (Ideal Eis × Ideal Eis) × Ideal Eis) :
      (∑ P ∈ Pset, if R ∣ P then
        a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (quadraticRow ((R * r) * k) (primaryGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel P ((r * u.2) * u.1.1)) *
              (if IsCoprime P (u.1.2 * t) then 1 else 0) else 0) =
      ∑ P ∈ quotientSupport R Pset,
        a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (quadraticRow ((R * r) * k) (primaryGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel (R * P) ((r * u.2) * u.1.1)) *
              (if IsCoprime (R * P) (u.1.2 * t) then 1 else 0) := by
    rw [← Finset.sum_filter]
    exact sum_quotientSupport R Pset _
  simp_rw [hinner]
  rw [finite_triple_support_reindex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hu : (p, c) ∈ quotientGridSupport r T
  · have huc := (mem_quotientGridSupport r hr T p c).mp hu
    simp only [hu, ite_true]
    apply Finset.sum_congr rfl
    intro P hPP
    have hpgen := (quotientSupport_cubic_admissible R hR Pset hP P hPP).2
    have hid := hybrid_extracted_block_identity R r k P c p.1 p.2 t hk hpgen a
      (extractedGridCoefficient T R t beta)
    simp only [extractedGridCoefficient, huc, ite_true] at hid
    rw [hmask]
    calc
      _ = a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) *
          (beta (r * c) p.1 p.2 * (if IsCoprime R (p.2 * t) then 1 else 0)) *
          (quadraticRow ((R * r) * k) (primaryGenerator (p.1 * p.2)) *
            inverseCubicKernel (R * P) ((r * c) * p.1)) *
          (if IsCoprime P (p.2 * t) then 1 else 0) := by ring
      _ = _ := by rw [hid]; ring
  · have huc : (p, r * c) ∉ T := (mem_quotientGridSupport r hr T p c).not.mp hu
    simp [hu, hybridColumnCoefficient, extractedGridCoefficient, huc]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.DyadicBlock -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_extracted_dyadic_block_nonempty (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (quotientGridSupport r (hybridGridSupport D)).Nonempty →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_original_quotient_block ε hε
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta hQ
  let Q := quotientGridSupport r (hybridGridSupport D)
  let X := N * B / (C ^ 2 * T ^ 2)
  let A := 2 * C / (Ideal.absNorm r : ℝ)
  let H := B / (C * T ^ 2)
  have hC0 : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  have hnr : 0 < (Ideal.absNorm r : ℝ) := QuadraticMainBoundary.norm_pos hr
  have hnorm (d : HybridColumnData) (hd : d ∈ D) :
      (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
      (Ideal.absNorm d.residualB : ℝ) ≤ H ∧
      (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ X := by
    have hd' := hD d hd
    apply d.residual_norm_bounds N B C T (by linarith) (by linarith) hC0 hT0
      (hn _ hd'.2.2.2.1).2 hd'.2.2.2.2 hd'.2.1
    simpa only [hd'.1] using ht
  have hcBound (d : HybridColumnData) (hd : d ∈ D) (c : Ideal Eis)
      (hdc : d.common = r * c) : c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A := by
    have hcz : c ≠ 0 := by
      intro hz
      apply d.common_ne_zero
      simp [hdc, hz]
    refine ⟨hcz, (le_div_iff₀ hnr).mpr ?_⟩
    have hdcN := (hD d hd).2.2.1
    rw [hdc, map_mul, Nat.cast_mul] at hdcN
    simpa only [mul_comm] using hdcN
  have hpair (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst) :
      Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X ∧
      p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H := by
    obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, he, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 hu
    have he' : (d.residualN, d.residualB) = p := he.trans hup
    have hm := congrArg Prod.fst he'
    have hh := congrArg Prod.snd he'
    have hdB : d.residualB ≠ 0 :=
      ne_zero_of_dvd_ne_zero d.g_squarefree.ne_zero (dvd_mul_left _ _)
    exact ⟨by simpa only [← hm, ← hh] using d.residual_product_squarefree,
      by simpa only [← hm, ← hh] using (hnorm d hd).2.2,
      by simpa only [← hh] using hdB,
      by simpa only [← hh] using (hnorm d hd).2.1⟩
  have hcset (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst)
      (c : Ideal Eis) (hc : c ∈ gridCommonSupport Q p.1) :
      c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset := by
    obtain ⟨d, hd, hm, hdc⟩ := quotientGridCommonSupport_origin r hr D p.1 c hc
    have hc' := hcBound d hd c hdc
    exact ⟨hc'.1, hc'.2, by simpa only [hdc, hm] using (hD d hd).2.2.2.1⟩
  obtain ⟨u₀, hu₀⟩ := hQ
  have hp₀ : u₀.1 ∈ Q.image Prod.fst := Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩
  have hc₀ : u₀.2 ∈ gridCommonSupport Q u₀.1.1 :=
    Finset.mem_image.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀, rfl⟩, rfl⟩
  have hX : 1 ≤ X :=
    (QuadraticMainBoundary.norm_one_le (hpair u₀.1 hp₀).1.ne_zero).trans (hpair u₀.1 hp₀).2.1
  have hH : 1 ≤ H :=
    (QuadraticMainBoundary.norm_one_le (hpair u₀.1 hp₀).2.2.1).trans (hpair u₀.1 hp₀).2.2.2
  have hA : 1 ≤ A :=
    (QuadraticMainBoundary.norm_one_le (hcset u₀.1 hp₀ u₀.2 hc₀).1).trans
      (hcset u₀.1 hp₀ u₀.2 hc₀).2.1
  have hbGrid : ∀ u ∈ hybridGridSupport D, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact hbeta d hd
  have he := hblock K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset
    (Q.image Prod.fst) (gridCommonSupport Q) a
    (extractedGridCoefficient (hybridGridSupport D) R t beta)
    hrows hn hP ha (fun p hp => ⟨(hpair p hp).1, (hpair p hp).2.1⟩)
    (fun p hp => (hpair p hp).2.2) hcset
    (fun p _ c _ => extractedGridCoefficient_norm_le_one _ R t beta hbGrid (r * c) p.1 p.2)
  have hrow (k : Ideal Eis) (hk : k ∈ quotientSupport (R * r) rows) :=
    gridDivisorHybridBlock_extract (hybridGridSupport D) Pset a beta t k R r hR hr
      (hrows _ ((mem_quotientSupport (R * r) k (mul_ne_zero hR hr) rows).mp hk)).1
      (fun P hP' => (hP P hP').1)
  have he' : (∑ k ∈ quotientSupport (R * r) rows,
      ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₁ * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
    calc
      _ = _ := Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
      _ ≤ _ := he
  have hXupper : X ≤ N * B := by
    apply div_le_self (by positivity : 0 ≤ N * B)
    have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    exact one_le_mul_of_one_le_of_one_le hC2 hT2
  apply he'.trans
  calc
    _ ≤ C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
      have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
      gcongr
    _ = _ := by
      dsimp only [A, H]
      field_simp

theorem hybrid_extracted_dyadic_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := hybrid_extracted_dyadic_block_nonempty ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  by_cases hQ : (quotientGridSupport r (hybridGridSupport D)).Nonempty
  · exact he K N B L C T hK hN hB hC hT R r t hR hr ht
      rows nset Pset D a beta hrows hn hP ha hD hbeta hQ
  · have hQ' := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp only [gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty _ _ _ _ _ _ _ _ hQ',
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    positivity

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.MaskedGrid -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

def maskedGridHybridRow (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) : ℂ :=
  ∑ u ∈ T, ∑ P ∈ Pset, (if IsCoprime k (P * u.2) then 1 else 0) *
    (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (quadraticRow k (primaryGenerator (u.1.1 * u.1.2)) * inverseCubicKernel P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0))

theorem maskedGridHybridRow_mobius (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) (hk : k ≠ 0) :
    maskedGridHybridRow T Pset a beta t k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) *
          gridDivisorHybridBlock T Pset a beta t k D.1 D.2 := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold maskedGridHybridRow
  simp_rw [hm, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  unfold gridDivisorHybridBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hrc : D.2 ∣ u.2
  · simp only [hrc, ite_true, and_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hRP : D.1 ∣ P <;> simp [hRP]
  · simp [hrc]

theorem gridDivisorHybridBlock_zero_of_not_coprime
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hRr : ¬ IsCoprime R r)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
    (hT : ∀ u ∈ T, primaryGenerator (u.2 * u.1.1) ≠ 0) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hrc : r ∣ u.2
  · simp only [hrc, ite_true]
    apply Finset.sum_eq_zero
    intro P hPP
    by_cases hRP : R ∣ P
    · simp only [hRP, ite_true]
      rw [inverseCubicKernel_divisor_overlap_zero R r P u.2 u.1.1
        (hP P hPP) (hT u hu) hRP hrc hRr]
      simp
    · simp only [hRP, ite_false]
  · simp only [hrc, ite_false]

theorem maskedGridHybridRow_divisor_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (T : Grid) (Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (t : Ideal Eis),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖maskedGridHybridRow T Pset a beta t k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖gridDivisorHybridBlock T Pset a beta t k D.1 D.2‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows T Pset a beta t hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) :=
    maskedGridHybridRow_mobius T Pset a beta t k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (fun k D => gridDivisorHybridBlock T Pset a beta t k D.1 D.2) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.1)
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FixedSquare -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_fixed_square_grid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (t : Ideal Eis), T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ rows, ‖maskedGridHybridRow (hybridGridSupport D) Pset a beta t k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_extracted_dyadic_block ε hε
  obtain ⟨C₂, hC₂, hmask⟩ := maskedGridHybridRow_divisor_energy ε hε
  refine ⟨C₁ * C₂ * 256 ^ 2, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT t ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  have hr0 : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K :=
    fun k hk => ⟨(hrows k hk).1.1, (hrows k hk).2⟩
  let E := C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
    CubicSieve.sieveNorm N (2 * L)
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hTprim : ∀ u ∈ hybridGridSupport D, primaryGenerator (u.2 * u.1.1) ≠ 0 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact (hn _ (hD d hd).2.2.2.1).1.2
  have hterm (v : Ideal Eis × Ideal Eis) (hv : v ∈ hybridDivisorPairPool rows) :
      (∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) := by
    have hp := Finset.mem_product.mp (hybridDivisorPairPool_subset rows hv)
    have hR := (hybridDivisorPool_bounds rows K hr0 v.1 hp.1).1
    have hr := (hybridDivisorPool_bounds rows K hr0 v.2 hp.2).1
    by_cases hcop : IsCoprime v.1 v.2
    · rw [double_divisor_row_reindex rows (fun k hk => (hr0 k hk).1) v.1 v.2 hcop]
      have he := hblock K N B L C T hK hN hB hC hT v.1 v.2 t hR hr ht
        rows nset Pset D a beta hrows hn hP ha hD hbeta
      convert he using 1
      dsimp only [E]
      field_simp
    · simp only [gridDivisorHybridBlock_zero_of_not_coprime _ _ _ _ _ _ _ _ hcop
          (fun P hPP => (hP P hPP).1.2) hTprim,
        norm_zero, zero_pow (by norm_num : 2 ≠ 0), ite_self, Finset.sum_const_zero]
      exact mul_nonneg hE (by positivity)
  have he := hmask K hK rows (hybridGridSupport D) Pset a beta t hr0
  have hsum : (∑ v ∈ hybridDivisorPairPool rows,
      ∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ hybridDivisorPairPool rows,
          E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = E * ∑ v ∈ hybridDivisorPairPool rows,
          1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hybrid_divisor_pair_inverse_norm_sum rows K hr0) hE
  apply he.trans
  calc
    _ ≤ C₂ * K ^ ε * (E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [E]; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReflectedDual -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff MatrixGroups
open CompletedGauss CubicEisenstein ConcreteTraceCRT CubicKubota CompletedDyadic
open CubicJacobiGlobal ShortDraftCusp FiniteGaussPhase LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance dualQuotientFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def mixedSmoothedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ,
    fullLocalFourierWeight hp (mixedPrimeFunction p hg j S) v *
      (D.datum hN hr hbase s hp hc0 v).smoothedKernel W X

def mixedReflectedValue (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) *
    ∑' t : ThetaFullIndex,
      (s.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val /
        ((ramifiedScale 1 completedRamifiedStep t.2.1 *
          Real.sqrt (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) : ℝ) : ℂ)) *
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X / (27 * (sourceCuspScale s.index) ^ 2 * (Ideal.absNorm (Ideal.span {c0 * ∏ i, p i}) : ℝ) ^ 2)) *
          (ramifiedScale 1 completedRamifiedStep t.2.1) ^ 3 *
          (Ideal.absNorm t.2.2.1.val : ℝ) * (Ideal.absNorm t.2.2.2.val : ℝ) ^ 3) *
      ((star D.fixedFactor * A4BadPhase c0 hc0 (D.matrix (fun _ => 1) 1 1) D.U
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))) *
        ∏ i, mixedActiveBracket hp hg j S D i
          (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t)))

theorem mixed_smoothed_eq_reflected (D : ControlledStratumArithmetic p N a0 c0 mode)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X =
      mixedReflectedValue D s hp hc0 hg j S W X := by
  have hden : c0 * (∏ i, p i) ≠ 0 :=
    mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hmat (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      (D.sourceGamma hN hr hbase v : SL(2, Eis)) *
        ControlledStratumArithmetic.fixedCusp a0 c0 mode = D.matrix v :=
    D.sourceGamma_mul hN hr hbase v
  have hchar (v : ∀ i, (Eis ⧸ Ideal.span {p i})ˣ) :
      levelTwoComplexCharacter (D.sourceGamma hN hr hbase v) =
        complexCharacter (D.relativeGamma hN hr hbase v) :=
    D.sourceGamma_character hN hr hbase v
  have hC : ∀ v, ((D.sourceGamma hN hr hbase v : SL(2, Eis)) *
      ControlledStratumArithmetic.fixedCusp a0 c0 mode) 1 0 = c0 * ∏ i, p i := by
    intro v
    exact (congrArg (fun M : SL(2, Eis) => M 1 0) (hmat v)).trans (D.denominator v)
  have he := s.sum_smoothedKernel_integral_phase (D.sourceGamma hN hr hbase) _ hden hC
    (fullLocalFourierWeight hp (mixedPrimeFunction p hg j S)) W lo hi hlo hsupp hW X hX
  change mixedSmoothedValue D hN hr hbase s hp hc0 hg j S W X = _ at he
  rw [he]
  unfold mixedReflectedValue
  apply congrArg (fun z : ℂ => fixedRadialCoefficientScalar * s.stratumShapeFactor (c0 * ∏ i, p i) * z)
  apply tsum_congr
  intro t
  congr 1
  simpa only [hchar, hmat, map_mul] using
    controlled_mixed_multiplier D hN hr hbase hp hc0 hcop hg hc j hj S
      (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t))

end
end SevenEighths.InverseMoment

end OAI

end

