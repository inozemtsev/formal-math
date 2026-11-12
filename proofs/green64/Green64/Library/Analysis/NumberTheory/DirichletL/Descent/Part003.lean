module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part017
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part001

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part003

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.MarkedPhase -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance markedPhaseFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis ⧸ P) := Fintype.ofFinite _
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

def markedActiveExponent (S : Finset ι) (j : ι → ℕ) (i : ι) : ℕ := if i ∈ S then 0 else j i

theorem mixedActiveBracket_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode)
    (i : ι) (x : Eis) :
    mixedActiveBracket hp hg j S D i x = (if i ∈ S then (-1 : ℂ) else 1) *
      ((((actualSextic (Ideal.span {p i}) (hg i))⁻¹) ^ 2) (D.sigma i) *
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i))
          (markedActiveExponent S j i) (D.epsilon i) *
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (markedActiveExponent S j i)
          (Ideal.Quotient.mk _ x)) := by
  by_cases hi : i ∈ S
  · simp only [mixedActiveBracket, markedActiveExponent, hi,
      phase, bracket, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte, inv_pow, map_mul]
    ring
  · simp only [mixedActiveBracket, markedActiveExponent, hi, ite_false, one_mul]

theorem mixedActiveBracket_product [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (D : ControlledStratumArithmetic p N a0 c0 mode) (x : Eis) :
    (∏ i, mixedActiveBracket hp hg j S D i x) =
      (-1 : ℂ) ^ S.card * D.bracketProduct hp hg (markedActiveExponent S j) x := by
  simp_rw [mixedActiveBracket_eq_signed]
  rw [Finset.prod_mul_distrib]
  have hsign : (∏ i : ι, if i ∈ S then (-1 : ℂ) else 1) = (-1 : ℂ) ^ S.card := by
    rw [Finset.prod_ite]
    simp
  rw [hsign]
  rfl

theorem mixedReflectedValue_eq_signed [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    mixedReflectedValue D s hp hc0 hg j S W X =
      (-1 : ℂ) ^ S.card * D.reflectedValue s hp hc0 hg (markedActiveExponent S j) W X := by
  unfold mixedReflectedValue ControlledStratumArithmetic.reflectedValue
  simp_rw [mixedActiveBracket_product]
  conv_rhs => rw [mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  ring

theorem mixed_model_coefficient [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp : ∀ i, p i ≠ 0) (hc0 : c0 ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m I J)) =
    ((-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m) *
      ∑ e : ι → Fin 3,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c0 hc0
            (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1) * D.U))
            (s.modelDualNumerator u) u) m I J *
        reflectedBranch (fun i => Ideal.span {p i}) hg (markedActiveExponent S j) e
          (primaryGenerator I) (primaryGenerator J) := by
  rw [mixedActiveBracket_product]
  calc
    _ = (-1 : ℂ) ^ S.card * (s.amplitude u m I J *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c0 hc0
        (D.matrix (fun _ => 1) 1 1) D.U (s.modelDualNumerator u m I J)) *
      D.bracketProduct hp hg (markedActiveExponent S j) (s.modelDualNumerator u m I J)) := by ring
    _ = _ :=
      (congrArg ((-1 : ℂ) ^ S.card * ·)
        (D.model_coefficient s hp hc0 hg (markedActiveExponent S j) u m I J)).trans
          (mul_assoc _ _ _).symm

theorem marked_modelRowPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hN : (9 : Eis) * c0 ∣ N) (hr : λ₀ ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj : ∀ i, j i < 6) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖(-1 : ℂ) ^ S.card * D.modelRowPhase s hp hg (markedActiveExponent S j) u m‖ = 1 := by
  have hj' : ∀ i, markedActiveExponent S j i < 6 := by
    intro i
    unfold markedActiveExponent
    split_ifs
    · norm_num
    · exact hj i
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact D.modelRowPhase_norm hN hr hbase s hp hg hchar _ hj' u m

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedSource -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem bounded_row_square_expansion {β : Type*}
    (C : Finset β) (a : β→ℂ) (r : β→O→ℂ) (hr : ∀b∈C,∀z,‖r b z‖≤1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ))=
      ∑b∈C,∑c∈C,(star (a b)*a c)*∑'z:O,(star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K) := by
  have hs (b c : β) (hb:b∈C) (hc:c∈C) : Summable (fun z:O =>
      (star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    have hW : Summable (fun z:O=>‖W (‖eisEmbedding z‖^2/K)‖) := by
      simpa only [EisensteinSchwartzPoisson.scaledRadialTest_apply] using
        EisensteinSchwartzPoisson.actual_eisenstein_summable_norm
          (EisensteinSchwartzPoisson.scaledRadialTest W K hK)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z=>norm_nonneg _) _ hW
    intro z
    simp only [norm_mul,norm_star]
    calc
      _ ≤ 1*1*‖W (‖eisEmbedding z‖^2/K)‖ := by
        gcongr
        · exact hr b hb z
        · exact hr c hc z
      _ = _ := by ring
  have he (z:O) : W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ)=
      ∑b∈C,∑c∈C,(star (a b)*a c)*((star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    rw [Complex.sq_norm (∑b∈C,a b*r b z),Complex.normSq_eq_conj_mul_self]
    simp only [map_sum,map_mul,starRingEnd_apply]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b hb=>summable_sum (fun c hc=>(hs b c hb hc).mul_left _))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c hc=>(hs b c hb hc).mul_left _)]
  apply Finset.sum_congr rfl
  intro c hc
  exact tsum_mul_left

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def varyingReopenedRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : (ι→₀ℕ)→Finset ι→ℂ) (z : O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hp hcop hg Ψ m f (H v) S)*
    (multiplicityRow (fun i=>Ideal.span {p i}) hg pool v z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)

theorem varyingReopenedRow_const (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (z : O) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f (fun _=>H) z =
      reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z := rfl

theorem varying_reopened_smoothed_expand
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f : O) (H : (ι→₀ℕ)→Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖eisEmbedding z‖^2/K)*(‖varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=
      ∑v₂∈Q,∑v₁∈Q,(star (β v₂)*β v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ Ψ m m f (H v₂) (H v₁) W K := by
  let a : (ι→₀ℕ)×Finset ι→ℂ := fun b=>β b.1*canonicalSourceCoefficient p hp hcop hg Ψ m f (H b.1) b.2
  let r : (ι→₀ℕ)×Finset ι→O→ℂ := fun b z=>
    multiplicityRow (fun i=>Ideal.span {p i}) hg pool b.1 z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg b.2 z
  have hr (b : (ι→₀ℕ)×Finset ι) (hb:b∈Q×ˢpool.powerset) (z:O) : ‖r b z‖≤1 := by
    dsimp [r]
    rw [norm_mul,norm_pow]
    calc
      _ ≤ 1 * ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b.2 z‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (multiplicityRow_norm_le_one p hg pool b.1 z))
          (norm_nonneg _)
      _ ≤ 1 := by simpa using finiteSquarefreeRow_norm_le_one _ hg b.2 z
  have he:=bounded_row_square_expansion (Q×ˢpool.powerset) a r hr W K hK
  simp only [Finset.sum_product] at he
  change (∑'z:O,W (‖eisEmbedding z‖^2/K)*
    (‖varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v₂ hv₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  simp only [canonicalCubeCorrelation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hB₁ : v₁.support⊆v₁.support∪v₂.support:=Finset.subset_union_left
  have hB₂ : v₂.support⊆v₁.support∪v₂.support:=Finset.subset_union_right
  have hr₁ (z:O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₁ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z := by
    rw [multiplicityRow_support p hg pool v₁ (hQ v₁ hv₁),multiplicityRow_support p hg _ v₁ hB₁]
  have hr₂ (z:O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₂ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z := by
    rw [multiplicityRow_support p hg pool v₂ (hQ v₂ hv₂),multiplicityRow_support p hg _ v₂ hB₂]
  simp only [a,r,canonicalCubeSourcePair,star_mul,hr₁,hr₂]
  have ht : (∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z^3)*
      (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z))*W (‖eisEmbedding z‖^2/K))=
      ∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z^3)*
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z^3)*W (‖eisEmbedding z‖^2/K) := by
    apply tsum_congr
    intro z
    ring
  rw [ht]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedBlocks -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def varyingCanonicalSourceTotal {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑b∈reopenedCubeFamily Q,∑C∈(pool\b.support).powerset,∑I∈labels,
    reopenedPairCoefficient β b C I *
      canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (H I b.rightExponent) (H I b.leftExponent) W K

theorem varying_reopened_smoothed_source {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (H : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (H I) z‖^2 : ℝ)) =
    varyingCanonicalSourceTotal p hp hcop hg pool Q labels β Ψ m H W K := by
  rw [varyingCanonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (H I v₂)
          (H I v₁) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact varying_reopened_smoothed_expand p hp hcop hg pool Q hQ (β I) Ψ m
        (idealGenerator I) (H I) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (H I v₂)
          (H I v₁) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedMarks -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_span_primeProduct (S : Finset ι) (v : ι→ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣Ideal.span {primeProduct p S v} ↔ i∈S ∧ 0<v i := by
  simp only [primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  rw [←dvd_iff_emultiplicity_pos,primeIdealProduct_emultiplicity (fun i=>Ideal.span {p i}) hinj]
  by_cases hi : i∈S <;> simp [hi]

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_reopened_index (S : Finset ι) (v : ι→₀ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣(Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 ↔
      i∈S∪v.support := by
  have hi : Prime (Ideal.span {p i}:Ideal O) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hs := prime_dvd_span_primeProduct p hinj S (fun _=>1) i
  simp only [primeProduct,pow_one,Nat.zero_lt_one,and_true] at hs
  rw [hi.dvd_mul,hi.dvd_pow_iff_dvd (by decide : (3:ℕ)≠0),hs,
    prime_dvd_span_primeProduct p hinj v.support v i,Finset.mem_union]
  have hv : i∈v.support ↔ 0<v i := by rw [Finsupp.mem_support_iff]; omega
  tauto

include hinj in

omit [DecidableEq σ] in
theorem reopened_whole_mark_divisibility (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
    ∏j∈slots,∑i∈lists j,if (Ideal.span {p i}:Ideal O)∣
      (Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 then a j i else 0 := by
  unfold primeMark primeSlot
  simp_rw [prime_dvd_reopened_index p hinj]

theorem reopened_mark_priority (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
      ∑J∈slots.powerset,primeMark J lists a v.support *
        primeMark (slots\J) (fun j=>lists j\v.support) a S := by
  rw [Finset.union_comm,primeMark_priority]
  simp only [primeMark_residual_lists]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def indexedIdealMark {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (primes : ι→Ideal O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (I : Ideal O) : ℂ :=
  ∏j∈slots,∑i∈lists j,if primes i∣I then a j i else 0

theorem complete_pool_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val) =
      primeMark slots lists a T := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T 0
  simp only [Finsupp.support_zero,Finset.union_empty,primeProduct,Finset.prod_empty,
    Ideal.span_singleton_one,←Ideal.one_eq_top,one_pow,mul_one] at he
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem finiteCanonicalMarkedRow_complete_global {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a I*W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b X hX hW hD
    (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)
  dsimp only at he
  have hmark : (fun T:Finset (primePool F)=>W (primeProductNorm (poolPrimary F) T/X)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val)) =
      (fun T=>primeMark slots lists a T*W (primeProductNorm (poolPrimary F) T/X)) := by
    funext T
    rw [complete_pool_mark F hF slots lists a T,mul_comm]
  rw [hmark] at he
  unfold finiteCanonicalMarkedRow
  calc
    _ = _ := he
    _ = _ := tsum_congr (fun I=>by ring)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CompletedReopening -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def outsideCanonicalMarkedRow {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O →* ℂ) (m f z : O) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X

theorem outsideCanonicalMarkedRow_cube_split {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑' I:Ideal O,summand Ψrow W X I B*mark (I*B^3) := by
  dsimp only
  unfold outsideCanonicalMarkedRow
  rw [finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f z W b X hX hW hD]
  rw [marked_completed_cube_inverse_split _ W hWc X H₀ hX]
  rw [marked_large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]

theorem outsideCanonicalMarkedRow_reopened {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B*cubeWeight Ψrow B*
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹)*
        ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*mark (I*B^3) := by
  rw [outsideCanonicalMarkedRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  rw [marked_inner_completed_sum _ W X hX B (outsideIdealsUpTo_ne_bot S D B hB)]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedPriority -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_reopened_prime_priority
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : (ι→₀ℕ)→Finset ι→ℂ) (z : O) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v S=>primeMark slots lists a (S∪v.support)*V v S) z =
    ∑J∈slots.powerset,varyingReopenedRow p hp hcop hg pool Q
      (fun v=>β v*primeMark J lists a v.support) Ψ m f
      (fun v S=>primeMark (slots\J) (fun j=>lists j\v.support) a S*V v S) z := by
  unfold varyingReopenedRow
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [canonicalSourceCoefficient]
  rw [reopened_mark_priority]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem allocated_cube_coefficient_bound
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hJ : J⊆slots) (hslots : (slots : Set σ).PairwiseDisjoint lists)
    (ha : ∀ j∈slots,∀ i∈lists j,‖a j i‖≤1)
    (β : (ι→₀ℕ)→ℂ) (v : ι→₀ℕ) :
    ‖β v*primeMark J lists a v.support‖≤‖β v‖*(2:ℝ)^v.support.card := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact primeMark_norm_le_divisor_count J lists a v.support
    (fun i hi j hj hne=>hslots (hJ hi) (hJ hj) hne) (fun j hj i hi=>ha j (hJ hj) i hi)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedIdentification -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem complete_pool_whole_cube_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) (v : primePool F→₀ℕ) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      ((∏i∈T,i.val)*cubeIdeal F v^3) = primeMark slots lists a (T∪v.support) := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T v
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan,cubeIdeal_eq_primeProduct_span F hF v] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem reopened_marked_global_column {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
    (∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*W ((Ideal.absNorm I:ℝ)/Y)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)) =
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>primeMark slots lists a (T∪v.support)*W (primeProductNorm (poolPrimary F) T/Y)) f z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
  have hN := norm_at_least_one (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hY : 0<Y := by dsimp [Y];positivity
  have hYD : b*Y≤D := (mul_le_mul_of_nonneg_left
    (div_le_self hX.le (one_le_pow₀ hN)) hb).trans hD
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b Y hY hW hYD
    (fun I=>indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3))
  dsimp only at he ⊢
  rw [←he]
  congr 1
  funext T
  rw [complete_pool_whole_cube_mark F hF slots lists a T v,mul_comm]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedOriginalRow -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def markedReopenedCubeBin {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
  ∑ v∈Q,(largeCubeCoefficient H₀ (cubeIdeal F v)*cubeWeight Ψrow (cubeIdeal F v)*
    (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹)*
    ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)

theorem original_marked_split_to_bins {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool F=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      markedReopenedCubeBin S D ((outsideIdealsUpTo S D).image (cubeIndex F)) Ψ m f z W X H₀ slots lists a := by
  rw [outsideCanonicalMarkedRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  rw [sum_outside_cubeIndex S D]
  rfl

theorem markedReopenedCubeBin_eq_varying {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)*
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a =
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q β Ψ m f
        (fun v T=>primeMark slots lists a (T∪v.support)*
          W (primeProductNorm (poolPrimary F) T/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  unfold markedReopenedCubeBin varyingReopenedRow
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hX hW hD slots lists a v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  unfold fixedChildRow
  simp only [Finset.mul_sum,secondChildColumn,canonicalSourceCoefficient]
  apply Finset.sum_congr rfl
  intro T hT
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedSeparation -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varyingReopenedRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m f z : O) (H : (ι→₀ℕ)→Finset ι → ℂ) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
          canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) * H v T := by
  unfold varyingReopenedRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

theorem varying_canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      fixedChildRow p hp hcop hg pool Ψ m
        (fun T => mark v T*W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow p hp hcop hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
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
      rw [varyingReopenedRow_integrand p hp hcop hg]
      simp only [A, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [columnLog]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedCommonMeasure -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_separated {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u,|u|≤ columnWindowRadius a b→V u=1)
    (B ell X H₀ : ℝ) (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell)
    (hD : b*X≤D)
    (hn : ∀ v∈Q,B≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀ v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights =
      ((B*Real.sqrt ell:ℝ):ℂ)⁻¹ * ∫ ξ:ℝ,reopeningCoefficient W a b ha hs hW ξ*
        varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
          (separatedCubeCoefficient β n B ξ) Ψ m f
          (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  have hXp : 0<X := hX ▸ mul_pos (pow_pos hB _) hell
  have hupper : ∀ t,W t≠0→t≤b := fun t ht=>(hs ht).2
  dsimp only
  rw [←varying_canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n (fun v T=>primeMark slots lists weights (T∪v.support))
    Ψ m f z B ell X hB hell hX hn hn']
  unfold markedReopenedCubeBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hXp hupper hD slots lists weights v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hc' : β v*(n v:ℂ)⁻¹=largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedIntegralEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [varyingReopenedRow_integrand p hp hcop hg]
  simp only [A,Finset.mul_sum,columnLog]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem varying_separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (Ψ : O →* ℂ) (m : O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal O) (z : O) : Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) :=
    varying_separated_canonical_integrable p hp hcop hg pool Q (β I) n mark Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedBinEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hD : b*X≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W X H₀ slots lists weights) K ≤
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W X H₀ slots lists weights) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
            (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact markedReopenedCubeBin_separated S D hbad hSp Q Ψ m (idealGenerator I) z W a b ha hb hs hW V hV
      B ell X H₀ hB hell hX hD hn hn' slots lists weights
  rw [hrows]
  exact varying_separated_canonical_family_energy (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels β n (fun v T=>primeMark slots lists weights (T∪v.support)) Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ReopenedBins -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_column_zero_of_subunit (Ψ : O→*ℂ) (W : ℝ→ℂ) (b Y : ℝ)
    (hY : 0<Y) (hW : ∀ t,W t≠0→t≤b) (hsub : b*Y<1) (mark : Ideal O→ℂ) :
    (∑' I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I)=0 := by
  suffices hz : ∀ I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I=0 by
    simp only [hz,tsum_zero]
  intro I
  by_cases hI : I=0
  · simp only [hI,columnWeight_zero,zero_mul]
  have hw : W ((Ideal.absNorm I:ℝ)/Y)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hY).mp (hW _ hn)
    have hone := norm_at_least_one I hI
    linarith
  simp only [hw,mul_zero,zero_mul]

variable {σ : Type*} [DecidableEq σ]
  (S : Finset (Ideal O)) (D : ℕ)
  (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ)
  (slots : Finset σ)
  (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
  (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)

theorem markedReopenedCubeBin_eq_active (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) :
    markedReopenedCubeBin S D
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ slots lists a =
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 := by
    exact lt_of_not_ge (fun hh=>hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3)<1 := by
    rw [←mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [marked_column_zero_of_subunit _ W b _ (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem markedReopenedCubeBin_log_bins :
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a =
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

def markedShortCompletedSum (Ψrow : O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) : ℂ :=
  ∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
      markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0

theorem original_marked_reopened_binned (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
    markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a) +
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  rw [original_marked_split_to_bins S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [markedReopenedCubeBin_eq_active S D Ψ m f z W b X H₀ slots lists a hX hW,
    markedReopenedCubeBin_log_bins]
  rfl

theorem original_marked_binned_energy (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 ≤
    2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2 +
    (cubeLogRange b X).card*∑ j∈cubeLogRange b X,
      ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a))
    (fun j=>markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a)
  rw [←original_marked_reopened_binned S D Ψ m f z W b X H₀ slots lists a hbad hSp hWc hX hW hD] at hs
  have hn : ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 =
      X*‖(Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondTailCost -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem residualPairWeight_bounded_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O)
    (Hcol : Finset ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => Hcol (G ∪ U)) (fun U => Hcol (G ∪ U)) S T‖ ≤ B^2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) S).trans (hcol _)
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) T).trans (hcol _)
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) hB

include hp hinj
theorem residualTailCost_bounded_test
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => Hcol (G∪S))
      (fun S => Hcol (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * (B^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => Hcol (G∪S))
    (fun S => Hcol (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    have hGS := hsupport (G ∪ S) hS
    have hGT := hsupport (G ∪ T) hT
    have hG := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS
    exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [ite_eq_left hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [ite_eq_left hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [ite_eq_left ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_bounded_test p hg hinj Ψ hΨ m c d Hcol B hB hcol G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [ite_eq_right hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [ite_eq_right hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [ite_eq_left hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [ite_eq_right hd]
    exact hz.le

theorem secondSourceTailCost_bounded_test
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * (B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h128 : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [ite_eq_left hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
            rw [ite_eq_left hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [ite_eq_right hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
        rw [ite_eq_right hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg h128 _) hC)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondWholeTail -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_secondSourceTail_bound order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp K hK
  exact (htail p hp hg hinj hc F Ψ m c d Hcol W Y H hY hH K hK).trans
    (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol B Y H lengthScale
      (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) order hB hY hH (by positivity) hL hcol hsupp)

def supportedSecondRadius (d : O) (lengthScale Y H : ℝ) : ℝ :=
  childOuterRadius Y (‖eisEmbedding d‖^2 * lengthScale) lengthScale lengthScale lengthScale H

lemma supportedSecondRadius_eq (d : O) (lengthScale Y H : ℝ) :
    supportedSecondRadius d lengthScale Y H = ‖eisEmbedding d‖^2 * lengthScale^4 * H / Y := by
  unfold supportedSecondRadius childOuterRadius
  ring

theorem full_second_child_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      supportedSecondRadius d lengthScale Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H lengthScale R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hGS' := hsupp (G ∪ S) hGS
  have hGT' := hsupp (G ∪ T) hGT
  have hGn := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS'
  have hEn := (primeProductNorm_mono p hp (Finset.mem_powerset.mp E.property)).trans hGn
  have hSn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS'
  have hTn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT'
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde : d*e ≠ 0 := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have hL0 : 0 < lengthScale := lt_of_lt_of_le zero_lt_one hL
  have heN : ‖eisEmbedding e‖^2 ≤ lengthScale := by
    simpa only [e,primeSubsetGenerator_norm_eq_productNorm] using hEn
  have hdeN : ‖eisEmbedding (d*e)‖^2 ≤ ‖eisEmbedding d‖^2 * lengthScale := by
    simp only [map_mul,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_left heN (sq_nonneg _)
  apply childFrequencyBall_raw_tail p hp Y (‖eisEmbedding d‖^2*lengthScale)
    lengthScale lengthScale lengthScale H hY (mul_pos hdN hL0) hL0 hL0 hL0 hH
    (d*e) e hde he hdeN heN S T hST hSn hTn k
  intro hsmall
  apply hk
  apply (mem_childFrequencyBall (d*e) hde R k).mpr
  exact ((mem_childFrequencyBall (d*e) hde _ k).mp hsmall).trans hR

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondWholeCutoff -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_whole_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal] (G E S T : Finset ι)
    (hEG : E ⊆ G) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤ L^2 := by
  have hE := primeProductNorm_mono p hp hEG
  have hE0 := (primeProductNorm_pos p hp E).le
  have hS0 := (primeProductNorm_pos p hp S).le
  have hT0 := (primeProductNorm_pos p hp T).le
  rw [primeProductNorm_union p G S hGS] at hS
  rw [primeProductNorm_union p G T hGT] at hT
  calc
    _ ≤ (primeProductNorm p G)^2 * (primeProductNorm p S * primeProductNorm p T) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hE 2) (mul_nonneg hS0 hT0)
    _ = (primeProductNorm p G * primeProductNorm p S) *
      (primeProductNorm p G * primeProductNorm p T) := by ring
    _ ≤ L*L := mul_le_mul hS hT (mul_nonneg (primeProductNorm_pos p hp G).le hT0) hL
    _ = _ := by ring

def wholeSecondRadius (d : O) (L Y H : ℝ) : ℝ := ‖eisEmbedding d‖^2 * L^2 * H / Y

theorem full_second_whole_column_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      wholeSecondRadius d L Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_whole_column_denominator p hp G E.val S T
    (Finset.mem_powerset.mp E.property) hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde R k hk).le
  have hR' : ‖eisEmbedding d‖^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp hR
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤
      (primeProductNorm p E/primeProductNorm p G)^2 * L^2 := by
  have hG0 := (primeProductNorm_pos p hp G).ne'
  have hbound := second_whole_column_denominator p hp G G S T Finset.Subset.rfl hGS hGT L hL hS hT
  calc
    _ = (primeProductNorm p E/primeProductNorm p G)^2 *
      ((primeProductNorm p G)^2 * (primeProductNorm p S*primeProductNorm p T)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

def correlatedSecondRadius {ι : Type*} [DecidableEq ι] (p : ι → O)
    (d : O) (G E : Finset ι) (L Y H : ℝ) : ℝ :=
  ‖eisEmbedding d‖^2 * (primeProductNorm p E/primeProductNorm p G)^2 * L^2 * H / Y

theorem full_second_correlated_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L : ℝ) (R : Finset ι → Finset ι → ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        correlatedSecondRadius p d G E.val L Y H ≤ R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E))‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_correlated_column_denominator p hp G E.val S T hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde (R G E.val) k hk).le
  have hR' : ‖eisEmbedding d‖^2 * (primeProductNorm p E.val/primeProductNorm p G)^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp (hR G hG E)
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    rw [←henorm] at hR'
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ShortCompletionEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem markedShortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) :
    markedShortCompletedSum Ψ W X H₀ mark = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) := by
  unfold markedShortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => ite_eq_left ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact ite_eq_right hn

theorem marked_short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (mark : κ→Ideal O→ℂ) (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2)≤A) :
    (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤
      A*(256*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
    rw [markedShortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤256*(columnDyadicLength H₀+1:ℝ) :=
    finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SourceHybrid -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def sourceGridCoefficient (beta : Ideal Eis → Ideal Eis → ℂ)
    (t c m h : Ideal Eis) : ℂ := beta (c * m) ((c * h) * t ^ 2)

theorem reconstructed_fixed_square_grid
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d) =
      (if IsCoprime k t then 1 else 0) *
        maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k := by
  unfold maskedGridHybridRow hybridGridSupport
  rw [Finset.sum_image]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro P hP
    simp only [reconstructedHybridTerm, HybridColumnData.gridIndex,
      sourceGridCoefficient, hD d hd]
    ac_rfl
  · intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg

theorem reconstructed_fixed_square_energy_le
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (rows Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤
      ∑ k ∈ rows,
        ‖maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  rw [reconstructed_fixed_square_grid D t hD Pset a beta k]
  by_cases hkt : IsCoprime k t
  · simp only [hkt, ite_true, one_mul, le_refl]
  · simp only [hkt, ite_false, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

theorem finite_double_row_energy {I J : Type*} [Fintype I] [Fintype J]
    (rows : Finset (Ideal Eis)) (F : I → J → Ideal Eis → ℂ) (E : ℝ) (_hE : 0 ≤ E)
    (hF : ∀ i j, (∑ k ∈ rows, ‖F i j k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i, ∑ j, F i j k‖ ^ 2) ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 * E := by
  have hk (k : Ideal Eis) :
      ‖∑ i, ∑ j, F i j k‖ ^ 2 ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
          ∑ i, ∑ j, ‖F i j k‖ ^ 2 := by
    simpa only [one_mul, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul] using
      bounded_coefficient_sum_sq (fun _ : I × J => 1) (fun u => F u.1 u.2 k) (by simp)
  calc
    _ ≤ ∑ k ∈ rows, ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ‖F i j k‖ ^ 2 := Finset.sum_le_sum (fun k _ => hk k)
    _ = ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ∑ k ∈ rows, ‖F i j k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) * ∑ _i : I, ∑ _j : J, E := by
      gcongr with i hi j hj
      exact hF i j
    _ = _ := by simp; ring

theorem supportedHybridRow_energy_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 *
          (columnDyadicLength N + 1 : ℝ) ^ 2 * (columnDyadicLength B + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hfixed⟩ := hybrid_fixed_square_grid_energy ε hε
  refine ⟨256 ^ 2 * C₁, by positivity, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  let nset := S.image Prod.fst
  let E := C₁ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
    CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2
  let F (j : Fin (columnDyadicLength B + 1)) (i : Fin (columnDyadicLength N + 1))
      (k : Ideal Eis) : ℂ :=
    ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      ∑ d ∈ hybridCommonBlock S N i t, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hnset : ∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨⟨(hS p hp).1, (hS p hp).2.1⟩, (hS p hp).2.2.2.1⟩
  have hBsup : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B := fun p hp => (hS p hp).2.2.2.2
  have hlen : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B :=
    fun p hp => (hS p hp).2.2.2
  have hlabel (j : Fin (columnDyadicLength B + 1))
      (i : Fin (columnDyadicLength N + 1)) :
      (∑ k ∈ rows, ‖F j i k‖ ^ 2) ≤ 256 ^ 2 * E := by
    let Td := divisorDyadicScale j.val
    have hTd : 0 < Td := by dsimp only [Td]; linarith [divisorDyadicScale_ge_one j.val]
    have htEnergy (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j) :
        (∑ k ∈ rows, ‖∑ d ∈ hybridCommonBlock S N i t,
          ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤ E / Td ^ 2 := by
      let D := hybridCommonBlock S N i t
      have hD (d : HybridColumnData) (hd : d ∈ D) :
          d.square = t ∧ divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) ∧
          (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val ∧
          d.common * d.residualN ∈ nset ∧
          (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B := by
        obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
        have hdorig := (mem_hybridColumnSupport S d).mp hdS
        have hb := hybridCommonBlock_bounds S N B (by linarith) (by linarith) hlen i j t ht d hd
        exact ⟨hdt, hb.1, hb.2.1, Finset.mem_image.mpr ⟨d.reconstruct, hdorig, rfl⟩,
          hBsup d.reconstruct hdorig⟩
      have hβ : ∀ d ∈ D, ‖sourceGridCoefficient beta t d.common d.residualN d.residualB‖ ≤ 1 := by
        intro d hd
        have hdo := (mem_hybridColumnSupport S d).mp (Finset.mem_filter.mp hd).1
        simpa only [sourceGridCoefficient, ← (hD d hd).1, HybridColumnData.reconstruct] using
          hbeta d.reconstruct hdo
      have hfix := hfixed K N B L (divisorDyadicScale i.val) Td hK hN hB
        (divisorDyadicScale_ge_one i.val) (divisorDyadicScale_ge_one j.val) t
        (divisorDyadicBin_bounds (hybridSquarePool S) B (hybridSquarePool_bounds S B hBsup) j t ht).1
        rows nset Pset D a (sourceGridCoefficient beta t) hrows hnset hP ha hD hβ
      apply (reconstructed_fixed_square_energy_le D t (fun d hd => (hD d hd).1) rows Pset a beta).trans
      convert hfix using 1 ; dsimp only [E] ; ring
    have he := hybrid_square_dyad_energy S B hBsup j rows
      (fun t k => ∑ d ∈ hybridCommonBlock S N i t,
        ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d)
      (E / Td ^ 2) (div_nonneg hE (sq_nonneg _)) htEnergy
    calc
      _ ≤ (256 * Td) ^ 2 * (E / Td ^ 2) := he
      _ = 256 ^ 2 * E := by field_simp
  have hrow (k : Ideal Eis) (hk : k ∈ rows) :
      supportedHybridRow S Pset a beta k = ∑ j, ∑ i, F j i k := by
    rw [supportedHybridRow_reconstruct S Pset
      (fun p hp => ⟨(hS p hp).1,
        primaryGenerator_ne_zero_ideal p.2 (hS p hp).2.2.1,
        (hS p hp).2.1, (hS p hp).2.2.1⟩)
      (fun P hPP => (hP P hPP).1.2) a beta k (hrows k hk).1]
    exact hybrid_dyadic_reindex S N B _
  calc
    _ = ∑ k ∈ rows, ‖∑ j, ∑ i, F j i k‖ ^ 2 :=
      Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
    _ ≤ ((Fintype.card (Fin (columnDyadicLength B + 1)) : ℝ) *
        (Fintype.card (Fin (columnDyadicLength N + 1)) : ℝ)) ^ 2 * (256 ^ 2 * E) :=
      finite_double_row_energy rows F (256 ^ 2 * E) (by positivity) hlabel
    _ = _ := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, E]; ring

end
end SevenEighths.InverseMoment

end OAI

end

