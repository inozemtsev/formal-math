module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part014

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Reflection / Part005

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedRow -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem markedCompletedT_twist_congr_primary (Ψ Φ : Eis→*ℂ)
    (h : ∀ n : Eis, λ₀^2∣n-1 → Ψ n=Φ n) (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT Ψ W X d=markedCompletedT Φ W X d := by
  unfold markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

theorem actual_marked_row_fixed_factor {m f z : Eis} (D : GoodMaskRowData m f z)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ m f z) W X d=
      markedCompletedT (D.fixedFactor Ψ Q*freePrimeRow D.movingIdeal D.movingSupported
        (Q*Ideal.span {(72:Eis)})) W X d :=
by
  apply markedCompletedT_twist_congr_primary
  intro n hn
  exact D.row_primary Ψ Q hmLam hm2 n hn

def freePrimeFamily (I Q : Ideal Eis) (hI : Supported I) : PrimeFamily (FreePrimeIndex I Q) where
  ideal P := P.val.val
  maximal _P := inferInstance
  good P := (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

def markedSumSlots {ι σ : Type*} [Fintype ι] [Fintype σ] : Finset (ι⊕σ) :=
  Finset.univ.filter (fun x => x.isRight)

lemma actual_sextic_power_congr (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hP : λ₀∉P) (hQ : λ₀∉Q) (hPQ : P=Q) (j : ℕ) (n : Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic Q hQ^j) (Ideal.Quotient.mk Q n) := by
  subst Q
  rfl

lemma unmarked_sum_twist {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) (n : Eis) :
    unmarkedSexticTwist (G.sum S).generator (G.sum S).generator_good
      (Sum.elim j (fun _ => 0)) markedSumSlots n =
    ∏ i, (actualSextic (G.ideal i) (G.good i)^j i) (Ideal.Quotient.mk _ n) := by
  let : DecidableEq (ι⊕σ) := Classical.decEq _
  have hset : (Finset.univ : Finset (ι⊕σ))\markedSumSlots = Finset.univ.filter (fun x => x.isLeft) := by
    ext x
    cases x <;> simp [markedSumSlots]
  unfold unmarkedSexticTwist
  change (∏ i∈Finset.univ\markedSumSlots, _) = _
  rw [hset,Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isLeft_inl,Sum.isLeft_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,mul_one,Sum.elim_inl]
  apply Finset.prod_congr rfl
  intro i hi
  exact actual_sextic_power_congr _ _ ((G.sum S).generator_good (Sum.inl i)) (G.good i)
    ((G.sum S).generator_span (Sum.inl i)) (j i) n

theorem free_row_eq_joined_unmarked {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ) :
    freePrimeRow I hI Q =
      unmarkedSexticTwist ((freePrimeFamily I Q hI).sum S).generator
        ((freePrimeFamily I Q hI).sum S).generator_good
        (Sum.elim (fun P : FreePrimeIndex I Q => (UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
          (fun _ => 0)) markedSumSlots := by
  ext n
  rw [unmarked_sum_twist]
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedOverlap -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_zero_at_prime (I Q : Ideal Eis) (hI : Supported I)
    (P : FreePrimeIndex I Q) (n : Eis) (hn : n∈P.val.val) : freePrimeRow I hI Q n=0 := by
  unfold freePrimeRow
  change (∏ p : FreePrimeIndex I Q, _)=0
  apply Finset.prod_eq_zero (Finset.mem_univ P)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma primaryGenerator_mem_of_ideal_dvd (P A : Ideal Eis) (hPA : P∣A) : primaryGenerator A∈P := by
  by_cases hz : primaryGenerator A=0
  · rw [hz]
    exact Ideal.zero_mem _
  have ha0 : primaryGenerator A∈Ideal.span {primaryGenerator A} := Ideal.subset_span (by simp)
  have ha : primaryGenerator A∈A := ((primaryGenerator_spec A hz).1.le) ha0
  exact (Ideal.dvd_iff_le.mp hPA) ha

lemma free_row_whole_mark_overlap {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val) (A : Ideal Eis) :
    freePrimeRow I hI Q (primaryGenerator A)*
      (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  by_cases hd : S.ideal i∣A
  · have hn := primaryGenerator_mem_of_ideal_dvd (S.ideal i) A hd
    rw [heq] at hn
    rw [freePrimeRow_zero_at_prime I Q hI P _ hn,zero_mul]
  · have hz : (∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right hd]
    rw [hz,mul_zero]

theorem markedCompletedT_free_overlap_zero {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (P : FreePrimeIndex I Q) (i : σ) (heq : S.ideal i=P.val.val)
    (φ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (φ*freePrimeRow I hI Q) W X
      (fun A => ∏ j, if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  unfold markedCompletedT
  calc
    _ = ∑' n : Ideal Eis, ∑' b : Ideal Eis, (0:ℂ) := by
      apply tsum_congr
      intro n
      apply tsum_congr
      intro b
      rw [mul_comm φ (freePrimeRow I hI Q),summand_mul_fixed_twist]
      have hgen : primaryGenerator (n*b^3)=primaryGenerator n*(primaryGenerator b)^3 := by
        rw [primaryGenerator_mul,show primaryGenerator (b^3)=primaryGenerator b^3 from map_pow primaryGeneratorHom b 3]
      rw [← hgen]
      have hz := free_row_whole_mark_overlap I Q hI S P i heq (n*b^3)
      calc
        _ = summand φ W X n b*(freePrimeRow I hI Q (primaryGenerator (n*b^3))*
          (∏ j, if S.ideal j∣n*b^3 then (1:ℂ) else 0)) := by ring
        _ = 0 := by rw [hz,mul_zero]
    _ = 0 := by simp

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedJoined -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma joined_whole_prime_mark {ι σ : Type*} [Fintype ι] [Fintype σ]
    (G : PrimeFamily ι) (S : PrimeFamily σ) (A : Ideal Eis) :
    (∏ i∈(markedSumSlots : Finset (ι⊕σ)),
      if Ideal.span {(G.sum S).generator i}∣A then (1:ℂ) else 0)=
      ∏ i, if S.ideal i∣A then (1:ℂ) else 0 := by
  unfold markedSumSlots
  rw [Finset.prod_filter,Fintype.prod_sum_type]
  simp only [Sum.isRight_inl,Sum.isRight_inr,Bool.false_eq_true,ite_false,ite_true,
    Finset.prod_const_one,one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(G.sum S).generator_span]
  rfl

theorem actual_marked_row_eq_joined {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (X : ℝ) :
    let Q₀ := Q*Ideal.span {(72:Eis)}
    let G := (freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S
    let j := Sum.elim
      (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ => 0)
    markedCompletedT (rowTwist Ψ m f z) W X (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
      markedCompletedT (D.fixedFactor Ψ Q*unmarkedSexticTwist G.generator G.generator_good j markedSumSlots)
        W X (fun A => ∏ i∈markedSumSlots, if Ideal.span {G.generator i}∣A then (1:ℂ) else 0) := by
  dsimp only
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2,
    free_row_eq_joined_unmarked D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S]
  congr 1
  funext A
  exact (joined_whole_prime_mark (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported) S A).symm

lemma joined_free_pairwise {σ : Type*} [Fintype σ]
    (I Q : Ideal Eis) (hI : Supported I) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hdis : ∀ P : FreePrimeIndex I Q, ∀ i, S.ideal i≠P.val.val) :
    Pairwise (Function.onFun IsCoprime ((freePrimeFamily I Q hI).sum S).ideal) := by
  apply PrimeFamily.sum_pairwise (freePrimeFamily I Q hI) S
  · exact freePrimeIndex_pairwise_coprime I Q
  · exact hS
  · intro P i
    exact Ideal.isCoprime_of_isMaximal (hdis P i).symm

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)
lemma generator_prime (i : ι) : Prime (P.generator i) :=
  (Ideal.span_singleton_prime (P.generator_ne_zero i)).mp inferInstance

def restrict (A : Finset ι) : PrimeFamily A where
  ideal i := P.ideal i.val
  maximal i := P.maximal i.val
  good i := P.good i.val

lemma restrict_pairwise (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (P.restrict A).ideal) := by
  intro i k hik
  exact hP (fun h => hik (Subtype.ext h))

def activeControlled [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) :
    ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode :=
  Classical.choice ((P.restrict A).exists_controlled N (G h).a0 (G h).c0 (G h).mode
    (G h).denominator_ne_zero (hN h) (G h).primary (G h).coprime
    (P.restrict_pairwise hP A) (fun i => hNp i.val))

theorem marked_source [Fintype ι]
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    (P.activeControlled hP c G N hN hNp) call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedActualSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

abbrev markedRowFamily {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis) :=
  (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported).sum S

def markedRowExponent {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}) ⊕ σ → ℕ :=
  Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => 0)

theorem actual_marked_row_overlap_zero {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})) (i : σ)
    (hPi : S.ideal i=P.val.val) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=0 := by
  rw [actual_marked_row_fixed_factor D Ψ Q hmLam hm2]
  exact markedCompletedT_free_overlap_zero D.movingIdeal (Q*Ideal.span {(72:Eis)})
    D.movingSupported S P i hPi (D.fixedFactor Ψ Q) W X

def markedCuspSource {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
    fixedActiveFunctionWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
    (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
      (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X

theorem actual_marked_row_source {σ : Type*} [Fintype σ]
    {m f z : Eis} (D : GoodMaskRowData m f z) (S : PrimeFamily σ)
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hQ : Q≠0)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm : ∀ n, ‖Ψ n‖≤1)
    (hmLam : λ₀∣m) (hm2 : (2:Eis)∣m)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}), ∀ i, S.ideal i≠P.val.val)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((markedRowFamily D S Q).ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    markedCuspSource (markedRowFamily D S Q)
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) c hc G N hN hNp W X := by
  have hQ0 : Q*Ideal.span {(72:Eis)}≠0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  exact (actual_marked_row_eq_joined D S Ψ Q hmLam hm2 W X).trans
    ((markedRowFamily D S Q).marked_source
      (joined_free_pairwise D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported S hS hdis)
      (markedRowExponent D Q) markedSumSlots (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm)
      (Q*Ideal.span {(72:Eis)}) hQ0 (D.fixedFactor_periodic Ψ Q hΨ) c hc hcQ G N hN hNp
      W hWcompact lo hi hlo hsupp hW X hX)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedLevel -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.level_coprime {ι : Type*} (P : PrimeFamily ι)
    (Q : Ideal Eis) (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q)
    (hQ : ∀ i, IsCoprime Q (P.ideal i)) (i : ι) :
    IsCoprime (Ideal.span {(9:Eis)*c}) (P.ideal i) := by
  have h9 : IsCoprime (Ideal.span {(9:Eis)}) (P.ideal i) := by
    rw [← P.generator_span i]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (ShortDraftCRT.primary_coprime_nine _ (P.generator_primary i)).symm
  rw [← Ideal.span_singleton_mul_span_singleton,hcQ]
  exact h9.mul_left (h9.mul_left (hQ i))

lemma markedRowFamily_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i))
    (c : Eis) (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)})) :
    ∀ i, IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D S Q).ideal i) := by
  apply PrimeFamily.level_coprime _ _ _ hcQ
  intro i
  cases i with
  | inl P => exact freePrimeIndex_coprime _ _ P
  | inr i => exact hS i

lemma markedRowFamily_odd {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2) :
    ∀ i, ringChar (Eis⧸(markedRowFamily D S Q).ideal i)≠2 := by
  intro i
  cases i with
  | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  | inr i => exact hS i

lemma markedRowExponent_lt {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (Q : Ideal Eis) :
    ∀ i : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})⊕σ, markedRowExponent D Q i<6 := by
  intro i
  cases i with
  | inl P => exact Nat.mod_lt _ (by norm_num)
  | inr i => norm_num [markedRowExponent]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.FixedLevel -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def reflectionSourceConductor (Q : Ideal Eis) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))

lemma reflectionSourceConductor_span (Q : Ideal Eis) :
    Ideal.span {reflectionSourceConductor Q}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}) :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma reflectionSourceConductor_ne_zero (Q : Ideal Eis) (hQ : Q≠0) :
    reflectionSourceConductor Q≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  apply mul_ne_zero _ (mul_ne_zero hQ _)
  all_goals simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]; norm_num

def reflectionSourceLevel (Q : Ideal Eis) : Eis := (9:Eis)*reflectionSourceConductor Q

lemma reflectionSourceLevel_ne_zero (Q : Ideal Eis) (hQ : Q≠0) :
    reflectionSourceLevel Q≠0 := mul_ne_zero (by norm_num) (reflectionSourceConductor_ne_zero Q hQ)

lemma reflectionSourceGeometry_level (Q : Ideal Eis) (hQ : Q≠0)
    (h : Eis⧸Ideal.span {reflectionSourceConductor Q}) :
    (9:Eis)*(fixedFourierGeometry (reflectionSourceConductor Q)
      (reflectionSourceConductor_ne_zero Q hQ) h).c0∣reflectionSourceLevel Q :=
  mul_dvd_mul_left (9:Eis) (fixedFourierGeometry _ _ h).denominator_dvd

lemma reflectionSourceLevel_original_period {σ : Type*} {m f z : Eis}
    (D : GoodMaskRowData m f z) (S : PrimeFamily σ) (Q : Ideal Eis)
    (hS : ∀ i, IsCoprime (Q*Ideal.span {(72:Eis)}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {reflectionSourceLevel Q}) ((markedRowFamily D S Q).ideal i) :=
  markedRowFamily_period D S Q hS (reflectionSourceConductor Q) (reflectionSourceConductor_span Q)

lemma reflectionSourceLevel_ray_finite (Q : Ideal Eis) (hQ : Q≠0) :
    Finite (Eis⧸Ideal.span {(reflectionSourceLevel Q)^2}) :=
  ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (reflectionSourceLevel_ne_zero Q hQ))

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedRestriction -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]
def activeMarks (A S : Finset ι) : Finset A := Finset.univ.filter (fun i => i.val∈S)

omit [Fintype ι] in
lemma mem_activeMarks (A S : Finset ι) (i : A) : i∈activeMarks A S ↔ i.val∈S := by
  simp [activeMarks]

omit [Fintype ι] in
lemma mixedPrimeFunction_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (i : A) (x : Eis⧸Ideal.span {P.generator i.val}) :
    mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) i x =
    mixedPrimeFunction P.generator P.generator_good j S i.val x := by
  simp only [mixedPrimeFunction,mem_activeMarks]
  rfl

omit [Fintype ι] in
lemma localActiveWeight_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ) :
    localActiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A v =
    fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v := by
  unfold localActiveWeight fullLocalFourierWeight
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext x
  exact (mixedPrimeFunction_restrict P j A S i x).symm

lemma active_sum_eq_mixed (P : PrimeFamily ι) (j : ι→ℕ) (S : Finset ι)
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (c : Eis) (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (h : Eis⧸Ideal.span {c}) (A : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    (∑ v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ,
      localActiveWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) A v *
      (activeStratumDatum P.generator P.generator_ne_zero P.generator_primary
        (P.activeControlled hP c G N hN hNp h) (hN h) (G h).denominator_ne_zero
        (G h).primary (G h).shape A v).smoothedKernel W X)=
    mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
      (P.restrict A).generator_product_primary (G h).primary (G h).shape
      (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) W X := by
  unfold mixedSmoothedValue
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedDualSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

lemma fixed_active_sum_eq_mixed
    (hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i)) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        (P.activeControlled hP c G N hN hNp) t).smoothedKernel W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (P.activeControlled hP c G N hN hNp h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  rw [← active_sum_eq_mixed P j S hP c G N hN hNp h A W X]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  ring

theorem marked_reflected_source
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (P.ideal i))
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (P.activeControlled hP c G N hN hNp h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN hNp
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed hP j S φ c hc G N hN hNp W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedChosenSource -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)

theorem marked_source_of_controlled [Fintype ι]
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    C call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedChosenDual -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

lemma fixed_active_sum_eq_mixed_of_controlled
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (C h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  simp only [mixedSmoothedValue,Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  have hw : fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v =
      fullLocalFourierWeight (fun i : A => P.generator_ne_zero i.val)
        (mixedPrimeFunction (fun i : A => P.generator i.val) (fun i => P.generator_good i.val)
          (fun i => j i.val) (activeMarks A S)) v := rfl
  rw [hw]
  dsimp only [activeStratumDatum]
  ring

theorem marked_reflected_source_of_controlled
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (C h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source_of_controlled hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN C
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed_of_controlled hP j S φ c hc G N hN C W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedInactive -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mixed_inactive_coefficient (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (i : ι) :
    finiteAdditiveFourierCoeff (quotientTrace (P.generator i) (P.generator_ne_zero i))
      (mixedPrimeFunction P.generator P.generator_good j S i) 0 =
    if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
      else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  change finiteAdditiveFourierCoeff (quotientTrace (P.generator i) (P.generator_ne_zero i))
    (fun x => if i∈S then zeroMark x else (actualSextic (Ideal.span {P.generator i}) (P.generator_good i)^j i) x) 0 = _
  by_cases hi : i∈S
  · simp only [hi,ite_true,zeroMark,finiteAdditiveFourierCoeff_zero_delta]
    have hcard : Fintype.card (Eis⧸Ideal.span {P.generator i})=Ideal.absNorm (P.ideal i) := by
      rw [← P.generator_span i,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
    rw [hcard]
  · simp only [hi,ite_false]
    have ho : ringChar (Eis⧸Ideal.span {P.generator i})≠2 := by
      rw [P.generator_span]
      exact hodd i
    rw [prime_zeroFourier_norm_formula (P.generator i) (P.generator_ne_zero i)
      (P.generator_good i) ho (j i) (hj i),P.generator_span]

lemma mixed_inactive_weight (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A =
    ∏ i∈(Finset.univ:Finset ι)\A,
      if i∈S then (Ideal.absNorm (P.ideal i):ℂ)⁻¹
        else if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0 := by
  unfold localInactiveWeight
  apply Finset.prod_congr rfl
  intro i hi
  exact mixed_inactive_coefficient P hodd j hj S i

lemma mixed_inactive_zero_of_omitted (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι) (i : ι) (hi : i∉S) (hji : j i≠0) (hiA : i∉A) :
    localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A=0 := by
  rw [mixed_inactive_weight P hodd j hj]
  apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hiA⟩)
  simp only [hi,hji,ite_false]

lemma mixed_inactive_nonzero_requires (P : PrimeFamily ι)
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S A : Finset ι)
    (h : localInactiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A≠0) :
    ∀ i, i∉S → j i≠0 → i∈A := by
  intro i hi hji
  by_contra hiA
  exact h (mixed_inactive_zero_of_omitted P hodd j hj S A i hi hji hiA)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedActiveSets -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype σ]

def joinedFiberEquiv (e : α⊕β≃γ) : α⊕(β⊕σ)≃γ⊕σ :=
  (Equiv.sumAssoc α β σ).symm.trans (Equiv.sumCongr e (Equiv.refl σ))

def markedActiveSet (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) : Finset (γ⊕σ) :=
  residualActivePrimes (joinedFiberEquiv (σ:=σ) e) ∪
    (B.disjSum T).image (fun x => joinedFiberEquiv e (Sum.inr x))

lemma inactive_product_disjSum (z : β⊕σ→ℂ) (B : Finset β) (T : Finset σ) :
    (∏ x∈(Finset.univ:Finset (β⊕σ))\B.disjSum T,z x)=
    (∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl b))*
    ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t) := by
  have hs : (Finset.univ:Finset (β⊕σ))\B.disjSum T=
      ((Finset.univ:Finset β)\B).disjSum ((Finset.univ:Finset σ)\T) := by
    ext x
    cases x <;> simp
  rw [hs,Finset.prod_disjSum]

theorem inactive_weight_three_blocks (e : α⊕β≃γ) (z : γ⊕σ→ℂ)
    (hz : ∀ a, z (Sum.inl (e (Sum.inl a)))=0) (F : Finset (γ⊕σ)→ℂ) :
    (∑ A : Finset (γ⊕σ), (∏ x∈(Finset.univ:Finset (γ⊕σ))\A,z x)*F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,z (Sum.inl (e (Sum.inr b))))*
        ∏ t∈(Finset.univ:Finset σ)\T,z (Sum.inr t))*F (markedActiveSet e B T) := by
  have he := inactive_weight_nonresidual_subsets (joinedFiberEquiv e) z hz F
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
    intro A hA
    congr 1
    apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
    intro x hx
    rfl
  · rw [← Fintype.sum_prod_type']
    apply Fintype.sum_equiv Finset.sumEquiv.toEquiv
    intro B
    have hB : B=B.toLeft.disjSum B.toRight := (Finset.toLeft_disjSum_toRight).symm
    conv_lhs => rw [hB]
    congr 1
    · refine Eq.trans ?_ (inactive_product_disjSum (fun x => z (joinedFiberEquiv e (Sum.inr x))) B.toLeft B.toRight)
      apply Finset.prod_congr (by ext x; simp only [Finset.mem_sdiff,Finset.mem_univ])
      intro x hx
      rfl
    · apply congrArg F
      ext x
      simp only [markedActiveSet,Finset.sumEquiv,Equiv.coe_fn_mk,Finset.mem_union,Finset.mem_image]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ActiveDictionary -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section
variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

def disjSumIndexEquiv (B : Finset β) (T : Finset σ) : B⊕T≃B.disjSum T where
  toFun x := match x with
    | Sum.inl b => ⟨Sum.inl b.val,by simp⟩
    | Sum.inr t => ⟨Sum.inr t.val,by simp⟩
  invFun x := match x with
    | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,by simpa using hb⟩
    | ⟨Sum.inr t,ht⟩ => Sum.inr ⟨t,by simpa using ht⟩
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨x,hx⟩; cases x <;> rfl

omit [Fintype β] [Fintype σ] in
lemma complete_marked_set (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    completeActiveSet (joinedFiberEquiv e) (B.disjSum T)=markedActiveSet e B T := by
  ext x
  simp only [completeActiveSet,markedActiveSet,Finset.mem_union,Finset.mem_image]

def markedActiveEquiv (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) :
    B⊕(α⊕T)≃markedActiveSet e B T :=
  (((((Equiv.sumAssoc B α T).symm.trans
    (Equiv.sumCongr (Equiv.sumComm B α) (Equiv.refl T))).trans (Equiv.sumAssoc α B T)).trans
    (Equiv.sumCongr (Equiv.refl α) (disjSumIndexEquiv B T))).trans
    (selectedActiveEquiv (joinedFiberEquiv e) (B.disjSum T))).trans
    (Equiv.subtypeEquivRight (fun x => by rw [complete_marked_set e B T]))

lemma markedActiveEquiv_frozen (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (b : B) :
    (markedActiveEquiv e B T (Sum.inl b)).val=Sum.inl (e (Sum.inr b.val)) := rfl
lemma markedActiveEquiv_residual (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (a : α) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inl a))).val=Sum.inl (e (Sum.inl a)) := rfl
lemma markedActiveEquiv_slot (e : α⊕β≃γ) (B : Finset β) (T : Finset σ) (t : T) :
    (markedActiveEquiv e B T (Sum.inr (Sum.inr t))).val=Sum.inr t.val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.MarkedFiber -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [Fintype ι] [Fintype σ]

def joinedInactiveCoefficient (P : PrimeFamily ι) (S : PrimeFamily σ) (j : ι→ℕ) : ι⊕σ→ℂ :=
  Sum.elim (fun i => if j i=0 then 1-(Ideal.absNorm (P.ideal i):ℂ)⁻¹ else 0)
    (fun i => (Ideal.absNorm (S.ideal i):ℂ)⁻¹)

lemma joined_inactive_weight (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (A : Finset (ι⊕σ)) :
    localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
      (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
        (Sum.elim j (fun _ => 0)) markedSumSlots) A =
    ∏ i∈(Finset.univ:Finset (ι⊕σ))\A, joinedInactiveCoefficient P S j i := by
  have ho : ∀ i, ringChar (Eis⧸(P.sum S).ideal i)≠2 := by
    intro i
    cases i with
    | inl i => exact hP i
    | inr i => exact hS i
  have hj' : ∀ i : ι⊕σ, Sum.elim j (fun _ => 0) i<6 := by
    intro i
    cases i with
    | inl i => exact hj i
    | inr i => norm_num
  rw [mixed_inactive_weight (P.sum S) ho _ hj']
  apply Finset.prod_congr (by ext i; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro i hi
  cases i <;> simp [markedSumSlots,joinedInactiveCoefficient,PrimeFamily.sum]
  rfl

theorem joined_inactive_three_blocks {α β : Type*} [Fintype α] [Fintype β]
    (P : PrimeFamily ι) (S : PrimeFamily σ)
    (hP : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (j : ι→ℕ) (hj : ∀ i, j i<6) (e : α⊕β≃ι) (he : ∀ a, j (e (Sum.inl a))=1)
    (F : Finset (ι⊕σ)→ℂ) :
    (∑ A : Finset (ι⊕σ),
      localInactiveWeight (P.sum S).generator (P.sum S).generator_ne_zero
        (mixedPrimeFunction (P.sum S).generator (P.sum S).generator_good
          (Sum.elim j (fun _ => 0)) markedSumSlots) A * F A)=
    ∑ B : Finset β, ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset β)\B,
        if j (e (Sum.inr b))=0 then 1-(Ideal.absNorm (P.ideal (e (Sum.inr b))):ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*F (markedActiveSet e B T) := by
  have hz : ∀ a, joinedInactiveCoefficient P S j (Sum.inl (e (Sum.inl a)))=0 := by
    intro a
    simp [joinedInactiveCoefficient,he a]
  have h := inactive_weight_three_blocks e (joinedInactiveCoefficient P S j) hz F
  refine Eq.trans ?_ h
  apply Finset.sum_congr (by ext A; simp only [Finset.mem_univ])
  intro A hA
  congr 1
  exact joined_inactive_weight P S hP hS j hj A
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalFiber -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_fiber_inactive_sum (S : PrimeFamily σ)
    (hS : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (H : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ)→ℂ) :
    (∑ A : Finset (FreePrimeIndex D.movingIdeal Q₀⊕σ),
      localInactiveWeight ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
        ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_ne_zero
        (mixedPrimeFunction ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator
          ((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).generator_good
          (Sum.elim (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
            (fun _ => 0)) markedSumSlots) A * H A)=
    ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀), ∑ T : Finset σ,
      ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
        if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
        ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*H (markedActiveSet E B T) := by
  have hodd : ∀ P : FreePrimeIndex D.movingIdeal Q₀,
      ringChar (Eis⧸(freePrimeFamily D.movingIdeal Q₀ D.movingSupported).ideal P)≠2 := by
    intro P
    exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.2
  have hres : ∀ a, (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count
      (E (Sum.inl a)).val.val%6=1 := by
    intro a
    exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
  have he := joined_inactive_three_blocks (freePrimeFamily D.movingIdeal Q₀ D.movingSupported)
    S hodd hS (fun P => (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
    (fun _ => Nat.mod_lt _ (by norm_num)) E hres H
  refine he.trans ?_
  apply Finset.sum_congr (by ext B; simp only [Finset.mem_univ])
  intro B hB
  apply Finset.sum_congr (by ext T; simp only [Finset.mem_univ])
  intro T hT
  congr 2
  apply Finset.prod_congr (by ext b; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro b hb
  rw [D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  change (if completedLocalExponent R F b.val=0 then
    1-(Ideal.absNorm (E (Sum.inr b)).val.val:ℂ)⁻¹ else 0)=_
  rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Reindex -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein CompletedGauss CubicJacobiGlobal FiniteGaussPhase ShortDraftCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma cofactor_reindex (p : ι→Eis) (e : κ≃ι) (k : κ) :
    cofactor (fun k => p (e k)) k=cofactor p (e k) := by
  unfold cofactor
  apply Finset.prod_equiv e
  · intro i
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,ne_eq,EmbeddingLike.apply_eq_iff_eq]
  · intro i hi
    rfl

lemma finiteCrossNumerator_reindex (a c l : Eis) (p : ι→Eis) (e : κ≃ι) (h : ι→Eis) :
    finiteCrossNumerator a c l (fun k => p (e k)) (fun k => h (e k))=
      finiteCrossNumerator a c l p h := by
  unfold finiteCrossNumerator
  simp_rw [cofactor_reindex]
  rw [e.prod_comp,e.sum_comp (fun i => h i*cofactor p i)]

def unitFrequencyEquiv (p : ι→Eis) (e : κ≃ι) :
    (∀ k, (Eis⧸Ideal.span {p (e k)})ˣ)≃(∀ i, (Eis⧸Ideal.span {p i})ˣ) :=
  Equiv.piCongrLeft (fun i => (Eis⧸Ideal.span {p i})ˣ) e

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_apply (p : ι→Eis) (e : κ≃ι)
    (v : ∀ k, (Eis⧸Ideal.span {p (e k)})ˣ) (k : κ) :
    unitFrequencyEquiv p e v (e k)=v k := Equiv.piCongrLeft_apply_apply _ _ _ _

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_one (p : ι→Eis) (e : κ≃ι) :
    unitFrequencyEquiv p e (fun _ => 1)=(fun _ => 1) := by
  funext i
  obtain ⟨k,rfl⟩ := e.surjective i
  exact unitFrequencyEquiv_apply p e _ k

def reindexControlled {p : ι→Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    ControlledStratumArithmetic (fun k => p (e k)) N a c mode where
  lift v k := D.lift (unitFrequencyEquiv p e v) (e k)
  lift_period v k := D.lift_period _ _
  lift_residue v k := (D.lift_residue _ _).trans (congrArg Units.val (unitFrequencyEquiv_apply p e v k))
  U := D.U
  w := D.w
  bezout := by simpa only [e.prod_comp] using D.bezout
  sigma k := D.sigma (e k)
  epsilon k := D.epsilon (e k)
  sigma_value k := by simpa only [cofactor_reindex] using D.sigma_value (e k)
  epsilon_value k := by simpa only [cofactor_reindex] using D.epsilon_value (e k)
  matrix v := D.matrix (unitFrequencyEquiv p e v)
  numerator v := by
    rw [D.numerator,finiteCrossNumerator_reindex]
  denominator v := by simpa only [e.prod_comp] using D.denominator (unitFrequencyEquiv p e v)
  matrix_fixed v i j := by
    simpa only [unitFrequencyEquiv_one] using D.matrix_fixed (unitFrequencyEquiv p e v) i j
  conditions v := D.conditions (unitFrequencyEquiv p e v)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ReindexReflection -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}

lemma reindexControlled_matrix_one (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).matrix (fun _ => 1)=D.matrix (fun _ => 1) := by
  change D.matrix (unitFrequencyEquiv p e (fun _ => 1))=_
  rw [unitFrequencyEquiv_one]

lemma reindexControlled_fixedFactor (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).fixedFactor=D.fixedFactor := by
  unfold ControlledStratumArithmetic.fixedFactor
  rw [reindexControlled_matrix_one]

lemma reindexControlled_U (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).U=D.U := rfl

def reindexMarks (e : κ≃ι) (S : Finset ι) : Finset κ := Finset.univ.filter (fun k => e k∈S)

omit [Fintype ι] in
lemma mem_reindexMarks (e : κ≃ι) (S : Finset ι) (k : κ) : k∈reindexMarks e S ↔ e k∈S := by
  simp [reindexMarks]

lemma mixedActiveBracket_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (hp : ∀ i, p i≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (k : κ) (x : Eis) :
    mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
      (reindexMarks e S) (reindexControlled D e) k x =mixedActiveBracket hp hg j S D (e k) x := by
  simp only [mixedActiveBracket,mem_reindexMarks]
  rfl

theorem mixedReflectedValue_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =mixedReflectedValue D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [mixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalDictionary -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def poolPrimeFamily (R Q Q₀ : Ideal Eis) : PrimeFamily (FreeReflection.pool R Q Q₀) where
  ideal P := P.val
  maximal P := FreeReflection.pool_maximal R Q Q₀ P
  good P := FreeReflection.pool_good R Q Q₀ P

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

lemma original_active_family_ideal (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).ideal (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).ideal x := by
  cases x with
  | inl b =>
    change (E (Sum.inr b.val)).val.val=b.val.val
    exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a =>
      change (E (Sum.inl a)).val.val=a.val
      exact D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_family_generator (S : PrimeFamily σ)
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    (((freePrimeFamily D.movingIdeal Q₀ D.movingSupported).sum S).restrict
      (markedActiveSet E B T)).generator (markedActiveEquiv E B T x)=
    (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator x :=
  congrArg primaryPrime (original_active_family_ideal D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T x)

lemma original_active_exponent
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
    (x : B⊕(PrimeIndex K⊕T)) :
    Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
      (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6) (fun _ : σ => 0)
      (markedActiveEquiv E B T x).val =
    Sum.elim (fun b : B => completedLocalExponent R F b.val.val)
      (Sum.elim (fun _ : PrimeIndex K => 1) (fun _ : T => 0)) x := by
  cases x with
  | inl b => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b.val)
  | inr x => cases x with
    | inl a => exact D.primeFiberEquiv_exponent R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)
    | inr t => rfl

lemma original_active_marks
    (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ) :
    reindexMarks (markedActiveEquiv E B T) (activeMarks (markedActiveSet E B T) markedSumSlots)=
    Finset.univ.filter (fun x : B⊕(PrimeIndex K⊕T) => match x with
      | Sum.inr (Sum.inr _) => True | _ => False) := by
  ext x
  simp only [mem_reindexMarks,mem_activeMarks,Finset.mem_filter,Finset.mem_univ,true_and]
  cases x with
  | inl b => simp [markedActiveEquiv_frozen,markedSumSlots]
  | inr x => cases x with
    | inl a => simp [markedActiveEquiv_residual,markedSumSlots]
    | inr t => simp [markedActiveEquiv_slot,markedSumSlots]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalTransport -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def castControlled {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode) :
    ControlledStratumArithmetic q N a c mode := h ▸ D

lemma mixedReflectedValue_cast {ι : Type*} [Fintype ι] {p q : ι→Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (h : p=q) (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ i, q i≠0) (hc : c≠0)
    (hgp : ∀ i, λ₀∉Ideal.span {p i}) (hgq : ∀ i, λ₀∉Ideal.span {q i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (castControlled h D) s hq hc hgq j S W X=
      mixedReflectedValue D s hp hc hgp j S W X := by
  subst q
  rfl

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

lemma original_active_marks_eq_slots :
    reindexMarks EA (activeMarks (markedActiveSet E B T) markedSumSlots)=slotIndices B (PrimeIndex K) T := by
  rw [original_active_marks D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  ext x
  cases x with
  | inl b => simp [slotIndices]
  | inr x => cases x with
    | inl a => simp [slotIndices]
    | inr t => simp [slotIndices]

def originalCanonicalControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PS).generator N a c mode) :
    ControlledStratumArithmetic (PF).generator N a c mode :=
  castControlled (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T))
    (reindexControlled C EA)

theorem original_reflected_source_eq {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PS).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue C s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    mixedReflectedValue (originalCanonicalControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  rw [← mixedReflectedValue_reindex C EA]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
  exact (mixedReflectedValue_cast _ (reindexControlled C EA) s _ (PF).generator_ne_zero hc _ (PF).generator_good _ _ W X).symm
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.InactiveAggregation -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inactive_slot_mass {ι : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hinj : Function.Injective P.ideal) (L : Finset ι) (H : ℝ)
    (hH : ∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H) :
    (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)≤256*(columnDyadicLength H+1:ℝ) := by
  have he : (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)=
      ∑ I∈L.image P.ideal, 1/(Ideal.absNorm I:ℝ) := by
    rw [Finset.sum_image hinj.injOn]
    simp only [norm_inv,Complex.norm_natCast,one_div]
  rw [he]
  apply finite_inverse_norm_sum
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact NeZero.ne (P.ideal i)
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hH i hi

theorem inactive_slot_mass_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (P : PrimeFamily ι),
      Function.Injective P.ideal → ∀ (L : Finset ι) (H : ℝ), 1≤H →
      (∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H) →
      (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹‖)≤C*H^ε := by
  refine ⟨256*(2+(ε*Real.log 2)⁻¹),by positivity,?_⟩
  intro ι _ P hinj L H hH hnorm
  exact (inactive_slot_mass P hinj L H hnorm).trans
    (by simpa only [mul_assoc,one_div] using (mul_le_mul_of_nonneg_left
      (columnDyadicLength_small_power ε hε H hH) (by norm_num : (0:ℝ)≤256)))

theorem original_pool_choice_count (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (R Q Q₀ : Ideal Eis), R≠0 → Q≠0 →
      (Fintype.card (FreeReflection.pool R Q Q₀→Fin 6):ℝ)^2≤C*(Ideal.absNorm (R*Q):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro R Q Q₀ hR hQ
  let (P : FreeReflection.pool R Q Q₀) : P.val.IsMaximal := FreeReflection.pool_maximal R Q Q₀ P
  have hh := hbound (R*Q) (mul_ne_zero hR hQ) (fun P : FreeReflection.pool R Q Q₀ => P.val)
    Subtype.val_injective (FreeReflection.pool_divides R Q Q₀ hR hQ)
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,← pow_mul,
    Nat.mul_comm (Fintype.card (FreeReflection.pool R Q Q₀)) 2] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma weighted_finite_row_energy {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤
      (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*(∑ k∈rows, ‖f i k‖^2) := by
  calc
    _ ≤ ∑ k∈rows, (∑ i∈L, ‖w i‖*‖f i k‖^2)*(∑ i∈L, ‖w i‖) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [star_one,mul_one,norm_one,one_pow] using
        DescentWeightedCauchy.weighted_cauchy_sq L w (fun i => f i k) (fun _ => 1)
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      ring

lemma weighted_finite_row_energy_uniform {ι κ : Type*} (L : Finset ι) (rows : Finset κ)
    (w : ι→ℂ) (f : ι→κ→ℂ) (B : ℝ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, w i*f i k‖^2)≤(∑ i∈L, ‖w i‖)^2*B := by
  apply (weighted_finite_row_energy L rows w f).trans
  calc
    _ ≤ (∑ i∈L, ‖w i‖)*∑ i∈L, ‖w i‖*B := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem inactive_slot_energy {ι κ : Type*} [Fintype ι] (P : PrimeFamily ι)
    (hinj : Function.Injective P.ideal) (L : Finset ι) (rows : Finset κ) (H B : ℝ)
    (hB : 0≤B) (hH : ∀ i∈L, (Ideal.absNorm (P.ideal i):ℝ)≤H)
    (a : ι→ℂ) (ha : ∀ i∈L, ‖a i‖≤1) (f : ι→κ→ℂ)
    (hf : ∀ i∈L, (∑ k∈rows, ‖f i k‖^2)≤B) :
    (∑ k∈rows, ‖∑ i∈L, (Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i*f i k‖^2)≤
      (256*(columnDyadicLength H+1:ℝ))^2*B := by
  have hm : (∑ i∈L, ‖(Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i‖)≤256*(columnDyadicLength H+1:ℝ) := by
    apply (Finset.sum_le_sum (fun i hi => ?_)).trans (inactive_slot_mass P hinj L H hH)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (ha i hi)
  apply (weighted_finite_row_energy_uniform L rows (fun i => (Ideal.absNorm (P.ideal i):ℂ)⁻¹*a i) f B hf).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun i hi => norm_nonneg _)) hm 2) hB
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalMask -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma maximal_coprime_iff_ne (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal] :
    IsCoprime P Q ↔ P≠Q := by
  constructor
  · intro h he
    subst Q
    exact (show P.IsPrime from inferInstance).ne_top (by simpa using h.sup_eq)
  · exact Ideal.isCoprime_of_isMaximal

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem original_slot_mask_iff (S : PrimeFamily σ) :
    (∀ P : FreePrimeIndex D.movingIdeal Q₀, ∀ t, S.ideal t≠P.val.val) ↔
    IsCoprime K (∏ t, S.ideal t) ∧
      ∀ b : FreeReflection.pool R (Ideal.span {m}*F) Q₀, ∀ t, S.ideal t≠b.val := by
  constructor
  · intro h
    constructor
    · rw [← PrimeFamily.residual_product K hK]
      apply IsCoprime.prod_left_iff.mpr
      intro a ha
      apply IsCoprime.prod_right_iff.mpr
      intro t ht
      apply Ideal.isCoprime_of_isMaximal
      have hh := h (E (Sum.inl a)) t
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)] at hh
      exact hh.symm
    · intro b t
      have hh := h (E (Sum.inr b)) t
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)] at hh
      exact hh
  · rintro ⟨hrow,hfixed⟩ P t
    obtain ⟨x,rfl⟩ := (E).surjective P
    cases x with
    | inl a =>
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inl a)]
      have hc := (hrow.of_isCoprime_of_dvd_left (PrimeFamily.residual_dvd K hK a)).of_isCoprime_of_dvd_right
        (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ t))
      exact ((maximal_coprime_iff_ne _ _).mp hc).symm
    | inr b =>
      rw [D.primeFiberEquiv_val R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask (Sum.inr b)]
      exact hfixed b t
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.PoolArithmetic -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma poolPrimeFamily_pairwise (R Q Q₀ : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (poolPrimeFamily R Q Q₀).ideal) := by
  intro P T hPT
  exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPT)

lemma poolPrimeFamily_period (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    IsCoprime Q₀ ((poolPrimeFamily R Q Q₀).ideal P) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  exact FreeReflection.pool_free R Q Q₀ P (Ideal.dvd_iff_le.mp h)

lemma poolPrimeFamily_odd (R Q Q₀ : Ideal Eis) (P : FreeReflection.pool R Q Q₀) :
    ringChar (Eis⧸(poolPrimeFamily R Q Q₀).ideal P)≠2 := FreeReflection.pool_odd R Q Q₀ P

lemma poolPrimeFamily_fiber_row_coprime (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    IsCoprime ((poolPrimeFamily R Q Q₀).ideal P) (rowResidualPart I Q) := by
  apply maximal_coprime_of_not_dvd
  exact FreeReflection.pool_nonresidual I Q Q₀
    (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_divides (R I Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    (poolPrimeFamily R Q Q₀).ideal P∣I*Q :=
  FreeReflection.pool_divides I Q Q₀ hI hQ (nonresidualPoolEquiv R I Q Q₀ hR hI hQ hpow hmask P)

lemma poolPrimeFamily_fiber_exponent (R I F Q Q₀ : Ideal Eis)
    (hR : R≠0) (hI : I≠0) (hQ : Q≠0)
    (hpow : rowPowerfulPart R=rowPowerfulPart I) (hmask : rowMaskPart R Q=rowMaskPart I Q)
    (P : FreeReflection.pool R Q Q₀) :
    completedLocalExponent I F ((poolPrimeFamily R Q Q₀).ideal P)=completedLocalExponent R F P.val :=
  nonresidualPoolEquiv_exponent R I F Q Q₀ hR hI hQ hpow hmask P

lemma pool_restrict_completion_coprime (R Q Q₀ : Ideal Eis)
    (B : Finset (FreeReflection.pool R Q Q₀)) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) :
    ∀ b : B, IsCoprime (Ideal.span {(9:Eis)*c}) (((poolPrimeFamily R Q Q₀).restrict B).ideal b) := by
  exact ((poolPrimeFamily R Q Q₀).restrict B).level_coprime Q₀ c hc
    (fun b => poolPrimeFamily_period R Q Q₀ b.val)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma finite_ideal_count_polynomial (rows : Finset (Ideal Eis)) (Z H Lcap : ℝ)
    (hZ : 128≤Z) (hH : 1≤H) (hn : ∀ I∈rows,I≠0)
    (hbound : ∀ I∈rows,(Ideal.absNorm I:ℝ)≤H) (hcap : H≤Z^Lcap) :
    (rows.card:ℝ)≤Z^(Lcap+1) := by
  have hz : 0<Z := by linarith
  calc
    _ ≤ 128*H := DescentFiberCost.finite_ideal_count_real rows H hH hn hbound
    _ ≤ Z*Z^Lcap := mul_le_mul hZ hcap (by linarith) hz.le
    _ = _ := by rw [Real.rpow_add hz,Real.rpow_one];ring

lemma original_pool_restricted_norm (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) :
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  exact completed_conductor_norm_bound I Q hI hQ ((poolPrimeFamily J Q Q₀).restrict A).ideal
    ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    (fun b => poolPrimeFamily_fiber_divides J I Q Q₀ hJ hI hQ hpower hmask b.val)

lemma original_pool_restricted_cap (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (Z Li Lq : ℝ) (hZ : 0<Z)
    (hi : (Ideal.absNorm I:ℝ)≤Z^Li) (hq : (Ideal.absNorm Q:ℝ)≤Z^Lq) :
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤Z^(Li+Lq) := by
  apply (original_pool_restricted_norm J I Q Q₀ hJ hI hQ hpower hmask A).trans
  rw [Real.rpow_add hZ]
  exact mul_le_mul hi hq (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem actual_finite_source_tail_budget {a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (Lcap δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
      (rows Pset : Finset (Ideal Eis)) (Z X QK QP : ℝ),
      128≤Z → 0<X → 1≤QK → 1≤QP →
      (∀ K∈rows,K≠0 ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,P≠0 ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap →
      QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      (rows.card:ℝ)*(Pset.card*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        (Z^δ)^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹)^2≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^4*Z^(-saving) := by
  obtain ⟨A,hA⟩ := actual_row_tail_energy_budget s Lcap (Lcap+1) δ saving hδ
  refine ⟨A,?_⟩
  intro φ _ F rows Pset Z X QK QP hZ hX hQK hQP hrows hPs hF hK hP hXi
  have hz : 1≤Z := by linarith
  exact hA F Z X QK QP rows.card Pset.card hz hX (by linarith) (by linarith)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hF hK hP hXi
    (finite_ideal_count_polynomial rows Z QK Lcap hZ hQK (fun K hK => (hrows K hK).1) (fun K hK => (hrows K hK).2) hK)
    (finite_ideal_count_polynomial Pset Z QP Lcap hZ hQP (fun P hP => (hPs P hP).1) (fun P hP => (hPs P hP).2) hP)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.ActualSizeCapsUniformDegree -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_finite_source_tail_budget_uniform_degree
    (Lcap δ saving : ℝ) (hδ : 0<δ) :
    ∃ A : ℕ, ∀ {a c : Eis} {mode : Bool}
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)), ∀ {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
      (rows Pset : Finset (Ideal Eis)) (Z X QK QP : ℝ),
      128≤Z → 0<X → 1≤QK → 1≤QP →
      (∀ K∈rows,K≠0 ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,P≠0 ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)≤Z^Lcap →
      QK≤Z^Lcap → QP≤Z^Lcap → X⁻¹≤Z^Lcap →
      (rows.card:ℝ)*(Pset.card*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        (Z^δ)^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹)^2≤
      (27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2)^4*Z^(-saving) := by
  obtain ⟨A,hA⟩ := actual_row_tail_energy_budget_uniform_degree Lcap (Lcap+1) δ saving hδ
  refine ⟨A,?_⟩
  intro a c mode s φ _ F rows Pset Z X QK QP hZ hX hQK hQP hrows hPs hF hK hP hXi
  have hz : 1≤Z := by linarith
  exact hA s F Z X QK QP rows.card Pset.card hz hX (by linarith) (by linarith)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hF hK hP hXi
    (finite_ideal_count_polynomial rows Z QK Lcap hZ hQK (fun K hK => (hrows K hK).1) (fun K hK => (hrows K hK).2) hK)
    (finite_ideal_count_polynomial Pset Z QP Lcap hZ hQP (fun P hP => (hPs P hP).1) (fun P hP => (hPs P hP).2) hP)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.CanonicalCaps -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_mask_norm_cap (B F R : Ideal Eis) (Z V Q L : ℝ)
    (hZ : 1≤Z) (hB : (Ideal.absNorm B:ℝ)≤Z)
    (hF : (Ideal.absNorm F:ℝ)≤Z^V) (hR : (Ideal.absNorm R:ℝ)≤Z^Q)
    (hV : V≤L) (hQ : Q≤L) :
    (Ideal.absNorm (B*F*R):ℝ)≤Z^(2*L+1) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [map_mul,map_mul,Nat.cast_mul,Nat.cast_mul]
  calc
    _ ≤ Z*Z^V*Z^Q := mul_le_mul
      (mul_le_mul hB hF (Nat.cast_nonneg _) hz.le) hR (Nat.cast_nonneg _) (by positivity)
    _ = Z^(1+V+Q) := by rw [Real.rpow_add hz,Real.rpow_add hz,Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem canonical_actual_arithmetic_caps (L : ℝ) (hL : 0≤L)
    (J I B F R Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hB : B≠0) (hF : F≠0) (hR : R≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I)
    (hmask : rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R))
    (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
    (Z M V Q z N hhat QK QP : ℝ) (hZ : 2≤Z)
    (hBn : (Ideal.absNorm B:ℝ)≤Z)
    (hIn : (Ideal.absNorm I:ℝ)≤Z^M)
    (hFn : (Ideal.absNorm F:ℝ)≤Z^V)
    (hRn : (Ideal.absNorm R:ℝ)≤Z^Q)
    (hM : M≤L) (hV : V≤L) (hQ : Q≤L) (hz : z≤L)
    (hN : 0≤N) (hh : hhat≤L)
    (hK : QK≤2*Z^M) (hP : QP≤2*Z^z) :
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal b):ℝ)≤Z^(4*L+2) ∧
      QK≤Z^(4*L+2) ∧ QP≤Z^(4*L+2) ∧ (Z^(N-3*hhat))⁻¹≤Z^(4*L+2) := by
  have hZ1 : 1≤Z := by linarith
  have hZp : 0<Z := by linarith
  have hmaskn := canonical_mask_norm_cap B F R Z V Q L hZ1 hBn hFn hRn hV hQ
  have hfrozen := original_pool_restricted_cap J I (B*F*R) Q₀ hJ hI
    (mul_ne_zero (mul_ne_zero hB hF) hR) hpower hmask A Z M (2*L+1) hZp hIn hmaskn
  refine ⟨hfrozen.trans (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)),?_,?_,?_⟩
  · calc
      QK ≤ 2*Z^M := hK
      _ ≤ Z*Z^M := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hZp.le _)
      _ = Z^(M+1) := by rw [Real.rpow_add hZp,Real.rpow_one];ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  · calc
      QP ≤ 2*Z^z := hP
      _ ≤ Z*Z^z := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hZp.le _)
      _ = Z^(z+1) := by rw [Real.rpow_add hZp,Real.rpow_one];ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  · rw [←Real.rpow_neg hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.CanonicalParameters -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseMoment InverseTerminalWidths
noncomputable section

theorem canonical_reflection_parameters (L c η : ℝ)
    (hL : 0≤L) (hc : 0<c) (hη : 0<η) (hη1 : η≤1) (hηc : η≤ c/100000) :
    ∃ ε ρ κ δ π : ℝ,0<ε ∧ 0<ρ ∧ 0<κ ∧ 0<δ ∧
      0≤δ+(7*L+1) ∧ η≤ c/1000 ∧ δ+η≤ c/1000 ∧ π≤ c/1000 ∧
      ε*(L+L+2*(δ+(7*L+1)+η))+η/2≤π ∧ κ+ρ*L≤ c/16 := by
  let ε := c/(100000*(L+1))
  let ρ := c/(64*(L+1))
  let κ := c/64
  refine ⟨ε,ρ,κ,η,c/1000,div_pos hc (by positivity),div_pos hc (by positivity),
    div_pos hc (by norm_num),hη,by positivity,by linarith,by linarith,le_refl _,?_,?_⟩
  · have hep : 0≤ε := (div_pos hc (by positivity : 0<100000*(L+1))).le
    have hed : ε*(L+1)=c/100000 := by dsimp [ε];field_simp
    have hb : L+L+2*(η+(7*L+1)+η)≤22*(L+1) := by linarith
    have hh := mul_le_mul_of_nonneg_left hb hep
    have he22 : ε*(22*(L+1))=22*(c/100000) := by calc
      _ = 22*(ε*(L+1)) := by ring
      _ = _ := by rw [hed]
    rw [he22] at hh
    linarith
  · have hrp : 0≤ρ := (div_pos hc (by positivity : 0<64*(L+1))).le
    have hrd : ρ*(L+1)=c/64 := by dsimp [ρ];field_simp
    have hb := mul_le_mul_of_nonneg_left (show L≤L+1 by linarith) hrp
    dsimp only [κ]
    rw [hrd] at hb
    linarith

lemma canonical_reflected_target_positive (F M Q z margin c O : ℝ)
    (h : CanonicalMargins F M Q z margin) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0<c) (hm : c/2≤ margin) (hO : O≤M) :
    0<F-3*c/16-O/2 := by
  obtain ⟨hfirst,hsecond⟩ := h
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.LowWidth -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonresidual_prime_product_square_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal Eis) (hI : I≠0) (P : ι→Ideal Eis) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i,P i∣I*Q) (hres : ∀ i,¬P i∣rowResidualPart I Q) :
    (∏ i,P i)^2∣rowPowerfulPart I*Q^2 := by
  rw [←Finset.prod_pow]
  apply Fintype.prod_dvd_of_coprime (fun i j hij => (hcop hij).pow)
  intro i
  have hp := Ideal.prime_of_isPrime (NeZero.ne (P i)) (inferInstance : (P i).IsPrime)
  by_cases hi : P i∣I
  · exact (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)).trans
      (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd (rowMaskPart_dvd I Q) 2))
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ((hp.dvd_mul.mp (hpool i)).resolve_left hi) 2) _

lemma nonresidual_prime_product_width {ι : Type*} [Fintype ι]
    (I Q : Ideal Eis) (hI : I≠0) (hQ : Q≠0) (P : ι→Ideal Eis) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i,P i∣I*Q) (hres : ∀ i,¬P i∣rowResidualPart I Q)
    (Z : ℝ) (hZ : 1<Z) :
    2*normWidth Z (∏ i,P i)≤normWidth Z (rowPowerfulPart I)+2*normWidth Z Q := by
  have hd := nonresidual_prime_product_square_dvd I Q hI P hcop hpool hres
  have hn := QuadraticMainBoundary.norm_le_of_dvd (mul_ne_zero (rowPowerfulPart_ne_zero I) (pow_ne_zero 2 hQ)) hd
  have hp : 0<(Ideal.absNorm (∏ i,P i):ℝ) := actual_ideal_norm_pos _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hpn := actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
  have hqn := actual_ideal_norm_pos Q hQ
  simp only [map_pow,map_mul,Nat.cast_pow,Nat.cast_mul] at hn
  have hh := Real.logb_le_logb_of_le hZ (sq_pos_of_pos hp) hn
  rw [Real.logb_pow,Real.logb_mul hpn.ne' (pow_ne_zero 2 hqn.ne'),Real.logb_pow] at hh
  norm_num at hh
  simpa only [normWidth,map_prod,Nat.cast_prod] using hh

lemma original_optional_powerful_width (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (Z : ℝ) (hZ : 1<Z) :
    2*normWidth Z (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b)≤
      normWidth Z (rowPowerfulPart I)+2*normWidth Z Q := by
  exact nonresidual_prime_product_width I Q hI hQ ((poolPrimeFamily J Q Q₀).restrict A).ideal
    ((poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A)
    (fun b => poolPrimeFamily_fiber_divides J I Q Q₀ hJ hI hQ hpower hmask b.val)
    (fun b => FreeReflection.pool_nonresidual I Q Q₀
      (CanonicalRowCompletion.nonresidualPoolEquiv J I Q Q₀ hJ hI hQ hpower hmask b.val)) Z hZ
lemma frozenExtracted_width_le {ι : Type*} [Fintype ι] (G : PrimeFamily ι)
    (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) (Z : ℝ) (hZ : 1<Z) :
    normWidth Z (frozenExtracted G j e v)≤normWidth Z (∏ i,G.ideal i) := by
  have hd : reflectionExtractedDivisor G.ideal j e v∣∏ i,G.ideal i := by
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    unfold reflectionExtractedPrime
    split_ifs
    · rfl
    · exact one_dvd _
  rw [←frozenExtracted_eq_ideal] at hd
  have hn := QuadraticMainBoundary.norm_le_of_dvd
    (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (G.ideal i))) hd
  exact Real.logb_le_logb_of_le hZ (actual_ideal_norm_pos _ (frozenExtracted_ne_zero G j e v)) hn

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.LowCaps -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma low_actual_scale_caps (J I Q Q₀ : Ideal Eis) (hJ : J≠0) (hI : I≠0) (hQ : Q≠0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I) (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q₀))
    (Z Ck d ell0 shift η QK QP : ℝ) (hZ : 2≤Z) (hCkp : 0<Ck) (hCk : Ck≤Z)
    (hQn : (Ideal.absNorm Q:ℝ)≤Z) (hd : 0≤d) (hell : 0≤ell0)
    (hellcap : ell0≤1/6-d+η) (hshift : |shift|≤η) (hη : η≤1)
    (hIn : (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d))
    (hK : QK≤2*Ck*Z^(5/6-2*d)) (hP : QP/2≤Z^ell0) :
    (Ideal.absNorm I:ℝ)≤Z^2 ∧
    (Ideal.absNorm (∏ b : A,((poolPrimeFamily J Q Q₀).restrict A).ideal b):ℝ)≤Z^(8:ℝ) ∧
      QK≤Z^(8:ℝ) ∧ QP≤Z^(8:ℝ) ∧ (Z^(1+ell0+shift))⁻¹≤Z^(8:ℝ) := by
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hcp : Ck*Z^(5/6-2*d)≤Z^2 := by
    calc
      _ ≤ Z*Z^(5/6-2*d) := mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(5/6-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := by
        rw [←Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hi := hIn.trans hcp
  refine ⟨hi,?_,?_,?_,?_⟩
  · calc
      _ ≤ (Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := original_pool_restricted_norm J I Q Q₀ hJ hI hQ hpower hmask A
      _ ≤ Z^2*Z := mul_le_mul hi hQn (Nat.cast_nonneg _) (sq_nonneg _)
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QK ≤ 2*(Ck*Z^(5/6-2*d)) := by linarith
      _ ≤ Z*Z^2 := mul_le_mul hZ hcp (by positivity) hz.le
      _ = Z^(3:ℝ) := by norm_num;ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  · calc
      QP ≤ 2*Z^ell0 := by linarith
      _ ≤ Z*Z^ell0 := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+ell0) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1 (by have hs := (abs_le.mp hshift).1;linarith)

lemma low_reflection_parameters (η : ℝ) (hη : 0<η) :
    0<η/(200*(1+η)) ∧
    η/(200*(1+η))*(8+8+2*(η/2+57+η))+η/2≤2*η := by
  have hp : 0<200*(1+η) := by positivity
  constructor
  · positivity
  · apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    nlinarith [sq_nonneg η]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OptionalWidth -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem original_optional_terminal_saving
    (J I F B R Q₀ : Ideal O) (hJ : J≠0) (hI : I ≠ 0) (hF : F ≠ 0) (hB : B ≠ 0) (hR : R ≠ 0)
    (hpower : rowPowerfulPart J=rowPowerfulPart I)
    (hmask : rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R))
    (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
    (e : A→Fin 3)
    (Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf : ℝ)
    (hZ : 1 < Z) (hCk : 0 < Ck) (hCO : 0 < CO) (hCH : 0 < CH) (hCf : 0 < Cf)
    (hk : (Ideal.absNorm I : ℝ) ≤ Ck * Z ^ M)
    (hpow : Z ^ O₀ / CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ))
    (hrow : Z ^ H / CH ≤ (Ideal.absNorm (rowResidualPart I (B * F * R)) : ℝ))
    (hf : (Ideal.absNorm F : ℝ) ≤ Cf * Z ^ V)
    (hlogH : Real.log (CH * Ck * CO) / Real.log Z ≤ η)
    (hlogT : Real.log (widthConstant B Ck CO CH Cf) / Real.log Z ≤ η)
    (hinv : CanonicalMargins F₀ M (normWidth Z R) z₀ c) (hF₀ : F₀ = N + V)
    (hscale : Nstar = N - 3 * hhat) (hV : V ≤ d) (hh : hhat ≤ d + η)
    (hM : 0 ≤ M) (hO : 0 ≤ O₀) (hz : 0 ≤ za) (hzcap : za ≤ z₀)
    (hv : 0 ≤ v) (hl : 0 ≤ ell) (he : -η ≤ el)
    (hret : v + 3 * ell + el ≤
      terminalDualWidth Z H za Nstar ((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal (fun a : A => completedLocalExponent J F a.val.val) e + τ)
    (hc : 0 < cstar) (hmargin : cstar / 2 ≤ c) (hd : d ≤ cstar / 200)
    (hη : η ≤ cstar / 1000) (hτ : τ ≤ cstar / 1000) (hπ : π ≤ cstar / 1000) :
    InverseTerminalWidths.reflectedExponent 0 H
      (normWidth Z (frozenExtracted ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (fun a : A => completedLocalExponent J F a.val.val) e 0))
      (normWidth Z (frozenExtracted ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (fun a : A => completedLocalExponent J F a.val.val) e 2))
      za v ell el (terminalDualWidth Z H za Nstar ((poolPrimeFamily J (B*F*R) Q₀).restrict A).ideal (fun a : A => completedLocalExponent J F a.val.val) e) + O₀/2 + π ≤
        F₀ - cstar / 4 := by
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun a : A => completedLocalExponent J F a.val.val
  have hQ : B*F*R≠0 := mul_ne_zero (mul_ne_zero hB hF) hR
  have hj : (fun i => completedLocalExponent I F (G.ideal i))=j := by
    funext i
    exact poolPrimeFamily_fiber_exponent J I F (B*F*R) Q₀ hJ hI hQ hpower hmask i.val
  have hret' : v+3*ell+el≤terminalDualWidth Z H za Nstar G.ideal
      (fun i => completedLocalExponent I F (G.ideal i)) e+τ := by
    rw [hj]
    exact hret
  have hh := actual_terminal_saving I F B R hI hF hB hR G.ideal
    ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A)
    (fun a => poolPrimeFamily_fiber_divides J I (B*F*R) Q₀ hJ hI hQ hpower hmask a.val)
    (fun a => FreeReflection.pool_nonresidual I (B*F*R) Q₀
      (CanonicalRowCompletion.nonresidualPoolEquiv J I (B*F*R) Q₀ hJ hI hQ hpower hmask a.val)) e
    Z F₀ N V M z₀ c cstar O₀ H za Nstar hhat v ell el d η τ π Ck CO CH Cf
    hZ hCk hCO hCH hCf hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    hM hO hz hzcap hv hl he hret' hc hmargin hd hη hτ hπ
  rw [hj,← frozenExtracted_eq_ideal G j e 0,← frozenExtracted_eq_ideal G j e 2] at hh
  convert hh using 1
  unfold InverseTerminalWidths.reflectedExponent
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.Pullback -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {q : κ→Eis}
    {N a c : Eis} {mode : Bool}

omit [Fintype ι] [Fintype κ] in
lemma pullback_generator_eq (e : κ≃ι) (h : (fun k => p (e k))=q) :
    (fun i => q (e.symm i))=p := by
  rw [← h]
  simp only [Equiv.apply_symm_apply]

def pullbackControlled (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode) :
    ControlledStratumArithmetic p N a c mode :=
  castControlled (pullback_generator_eq e h) (reindexControlled D e.symm)

lemma reindexMarks_symm (e : κ≃ι) (S : Finset ι) :
    reindexMarks e.symm (reindexMarks e S)=S := by
  ext i
  simp only [mem_reindexMarks,Equiv.apply_symm_apply]

theorem mixedReflectedValue_pullback
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ k, (Ideal.span {q k}).IsMaximal]
    (e : κ≃ι) (h : (fun k => p (e k))=q)
    (D : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hq : ∀ k, q k≠0) (hc : c≠0)
    (hgp : ∀ i, λ₀∉Ideal.span {p i}) (hgq : ∀ k, λ₀∉Ideal.span {q k})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (pullbackControlled e h D) s hp hc hgp j S W X=
      mixedReflectedValue D s hq hc hgq (fun k => j (e k)) (reindexMarks e S) W X := by
  unfold pullbackControlled
  rw [mixedReflectedValue_cast _ _ s (fun i => hq (e.symm i)) hp hc
    (fun i => hgq (e.symm i)) hgp]
  have hj : (fun i => j (e (e.symm i)))=j := by funext i; simp only [Equiv.apply_symm_apply]
  have he := mixedReflectedValue_reindex D e.symm s hq hc hgq
    (fun k => j (e k)) (reindexMarks e S) W X
  rw [hj,reindexMarks_symm] at he
  exact he
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.OriginalChosen -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ) (B : Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀)) (T : Finset σ)
local notation "E" => D.primeFiberEquiv R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "PS" => PrimeFamily.restrict (PrimeFamily.sum (freePrimeFamily D.movingIdeal Q₀ D.movingSupported) S) (markedActiveSet E B T)
local notation "PF" => PrimeFamily.reflected (PrimeFamily.restrict (poolPrimeFamily R (Ideal.span (Set.singleton m)*F) Q₀) B) K hK (S.restrict T)
local notation "EA" => markedActiveEquiv E B T

def originalChosenControlled {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode) :
    ControlledStratumArithmetic (PS).generator N a c mode :=
  pullbackControlled EA
    (funext (original_active_family_generator D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T)) C

theorem original_chosen_reflected_source_eq {N a c : Eis} {mode : Bool}
    (C : ControlledStratumArithmetic (PF).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (originalChosenControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask S B T C)
      s (PS).generator_ne_zero hc (PS).generator_good
      (fun i => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) i.val) (activeMarks (markedActiveSet E B T) markedSumSlots) W X =
    mixedReflectedValue C s (PF).generator_ne_zero hc (PF).generator_good
      (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val)) (slotIndices B (PrimeIndex K) T) W X := by
  unfold originalChosenControlled
  rw [mixedReflectedValue_pullback]
  have hj : (fun x => Sum.elim (fun P : FreePrimeIndex D.movingIdeal Q₀ =>
        (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val%6)
        (fun _ : σ => 0) (EA x).val)=
      reflectedExponent (fun b : B => completedLocalExponent R F b.val.val) := by
    funext x
    exact original_active_exponent D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T x
  rw [hj,original_active_marks_eq_slots D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask B T]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RetainedWidth -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

lemma family_center_eq_kernel {φ : Type u} [Fintype φ] (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (X QK QP : ℝ) (i : ℕ×ℕ×ℕ) :
    rawDyadicCenter (familyRawScale F s X QK QP) i=
      kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
  unfold rawDyadicCenter familyRawScale kernelCenter actualKernelCoefficient fixedKernelCoefficient
  simp only [map_one,Nat.cast_one,one_pow,mul_one,ramifiedScale,pow_zero,one_mul]
  ring

theorem actual_retained_width_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      Real.logb Z (kn*((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
        3*Real.logb Z (kb*((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+
        InverseTerminalWidths.ramifiedWidth Z i.1 ≤
      InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
        F.ideal jF e + δ+η := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,hlog⟩ := InverseTerminalWidths.constant_log_error (16*Cf) η (by positivity) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ F jF e Z X QK QP δ i hZ hX hQK hQP hi
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hs := familyRawScale_pos F s hc X QK QP hX hQK hQP
  have hret := (mem_retainedDyads _ _ hs i).mp hi
  rw [family_center_eq_kernel] at hret
  have hR : 0<kernelCenter (actualKernelCoefficient F s i.1 X) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) := by
    have hcoef := actualKernelCoefficient_pos F s hc i.1 X hX
    unfold kernelCenter
    positivity
  have hrl := Real.logb_le_logb_of_le hz hR hret
  rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos (lt_trans zero_lt_one hz) δ).ne',
    Real.logb_rpow (lt_trans zero_lt_one hz) (ne_of_gt hz)] at hrl
  have he := actual_kernel_upper_threshold F jF e s hc i.1 Z X QK QP
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) kK kP kn kb hX hQK hQP (by positivity) (by positivity) hkK hkP hkn hkb
  rw [literal_ramified_width_offset] at he
  have hl : Real.logb Z 16+Real.logb Z Cf≤η := by
    rw [←Real.logb_mul (by norm_num : (16:ℝ)≠0) hCf.ne']
    exact hlog Z hZ
  have hoff : 0≤4*Real.logb Z 3 := mul_nonneg (by norm_num) (Real.logb_nonneg hz (by norm_num))
  change _ = _+Real.logb Z Cf at he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.RetainedCaps -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retained_shell_le_ratio (scale T : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*T)) :
    (2:ℝ)^i.2.2≤16*T/scale ∧ (2:ℝ)^i.2.1≤16*T/scale := by
  have hh := (mem_retainedDyads _ _ hs i).mp hi
  have hl := rawDyadicCenter_pow_lower scale hs.le i
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤16*T/scale := by
    exact (le_div_iff₀ hs).mpr (by nlinarith)
  constructor
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.2 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.1 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp

lemma retained_shell_log_cap (scale Z δ Lcap η : ℝ) (hs : 0<scale) (hZ : 1<Z)
    (hscale : scale⁻¹≤Z^Lcap) (hconst : Real.logb Z 16≤η)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ)) :
    Real.logb Z ((2:ℝ)^i.2.2)≤δ+Lcap+η ∧
    Real.logb Z ((2:ℝ)^i.2.1)≤δ+Lcap+η := by
  have hz := lt_trans zero_lt_one hZ
  have hb : 16*Z^δ/scale≤16*Z^(δ+Lcap) := by
    rw [Real.rpow_add hz,div_eq_mul_inv,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (by positivity)
  have hshell := retained_shell_le_ratio scale (Z^δ) hs i hi
  have hlog (n : ℕ) (hn : (2:ℝ)^n≤16*Z^(δ+Lcap)) :
      Real.logb Z ((2:ℝ)^n)≤δ+Lcap+η := by
    have hh := Real.logb_le_logb_of_le hZ (by positivity : (0:ℝ)<2^n) hn
    rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz (ne_of_gt hZ)] at hh
    linarith
  exact ⟨hlog _ (hshell.1.trans hb),hlog _ (hshell.2.trans hb)⟩

lemma extracted_log_le_shell (Z Q : ℝ) (hZ : 1<Z) (hQ : 0<Q)
    (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
    Real.logb Z (Q/Ideal.absNorm I)≤Real.logb Z Q := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Real.logb_le_logb_of_le hZ (div_pos hQ (lt_of_lt_of_le zero_lt_one hn))
  exact div_le_self hQ.le hn

lemma retained_extracted_log_budget (scale Z δ Lscale Lrow Lslot η X L : ℝ)
    (hs : 0<scale) (hZ : 1<Z) (hX : 0<X) (hL : 0<L)
    (hscale : scale⁻¹≤Z^Lscale) (hconst : Real.logb Z 16≤η)
    (hrow : X≤Z^Lrow) (hslot : L≤Z^Lslot)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ))
    (D1 D2 : Ideal ActualEisensteinCubic.O) (h1 : D1≠0) (h2 : D2≠0) :
    Real.logb Z X+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm D1)+
      Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm D2)+Real.logb Z L≤
        Lrow+Lslot+2*(δ+Lscale+η) := by
  have hz := lt_trans zero_lt_one hZ
  have hr := Real.logb_le_logb_of_le hZ hX hrow
  have hl := Real.logb_le_logb_of_le hZ hL hslot
  rw [Real.logb_rpow hz (ne_of_gt hZ)] at hr hl
  obtain ⟨hn,hb⟩ := retained_shell_log_cap scale Z δ Lscale η hs hZ hscale hconst i hi
  have hn' := extracted_log_le_shell Z ((2:ℝ)^i.2.2) hZ (by positivity) D1 h1
  have hb' := extracted_log_le_shell Z ((2:ℝ)^i.2.1) hZ (by positivity) D2 h2
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

end

