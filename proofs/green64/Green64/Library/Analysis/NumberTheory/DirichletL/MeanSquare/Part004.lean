module

public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part015

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / MeanSquare / Part004

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.PolynomialHeight -/

section

namespace OAI

noncomputable section

namespace CompletedHeight

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

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
theorem polynomial_reflected_branch_series
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e (Wfamily θ) K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e (Wfamily θ) K Y ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨heightDegree,C,hC,h⟩ := polynomial_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,C,hC,?_⟩
  intro θ K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h θ K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

theorem polynomial_reflected_fiber_fixed_scale
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e (Wfamily θ)
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_reflected_branch_series Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,Cbase*B^(2*deltaLoss+1),by positivity,?_⟩
  intro θ K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hn (J : Ideal ActualEisensteinCubic.O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale,C]) <;> ring

theorem polynomial_branch_energy
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀θ K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value (Wfamily θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,C,hC,h⟩ := polynomial_reflected_fiber_fixed_scale Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨heightDegree,C,hC,?_⟩
  intro θ K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h θ K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

theorem polynomial_fiber_energy
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value (Wfamily θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_branch_energy Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨heightDegree,Cbase*Cp,by positivity,?_⟩
  intro θ rays K X hK hX I F Q hI hQ hIK hk d
  let Cb := Cbase*(1+‖θ‖)^heightDegree
  have hCb : 0<Cb := by dsimp [Cb]; positivity
  have hb := hbase θ
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := ReflectedFiberData.finite_energy_bound
    (fun b => (d.branch b).value (Wfamily θ) X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value (Wfamily θ) X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; dsimp [Cb]; ring

theorem polynomial_energy_of_exact_models
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedModels rays rows K X ρ q levelBound F Q (Wfamily θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_fiber_energy Wfamily hWfamily deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨heightDegree,Co*Cbase,by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let Cm := Cbase*(1+‖θ‖)^heightDegree
  have hCm : 0<Cm := by dsimp [Cm]; positivity
  have hm := hbase θ
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B,Cm]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (d.idealValue (Wfamily θ) X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [ReflectedFiberData.idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) (Wfamily θ) X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖d.idealValue (Wfamily θ) X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B,Cm]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) (Wfamily θ) X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B,Cm]
  ring

theorem polynomial_mean_square_of_exact_reflection
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (Wfamily θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  let deltaLoss : ℝ := ε/12
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_energy_of_exact_models Wfamily hWfamily deltaLoss deltaLoss ρ q levelBound hδ hδ hρ hq hlevel
  let s : ℝ := 10*deltaLoss+deltaLoss
  have hs : 0≤ s := by dsimp [s]; positivity
  refine ⟨heightDegree,Cbase*(16*(2:ℝ)^s),by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodels
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^deltaLoss
  have hA : 0≤A := by dsimp [A]; positivity
  rw [←completedRowDyad_sum rows K (by linarith : 0≤K) (fun I hI => (hrows I hI).2)
    (fun I => ‖completedT (Ψ I) (Wfamily θ) X‖^2)]
  have hper (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      (∑I∈completedRowDyad rows j,‖completedT (Ψ I) (Wfamily θ) X‖^2)≤
        A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
    have hb := h rays ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX
      (completedRowDyad rows j) F Q hQ hbad
      (fun I hI => ⟨(completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).1,
        (completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).2.2⟩)
      Ψ lengthScale (hmodels j hj)
    convert hb using 1
    dsimp [A,s,C]
    ring
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := Finset.sum_le_sum hper
    _ = A*∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)) :=
      mul_le_mul_of_nonneg_left (completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) hs hK
        (by linarith) hnQ) hA
    _ ≤ (C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
        (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
      have hnq : (Ideal.absNorm Q:ℝ)^deltaLoss≤(K*(Ideal.absNorm Q:ℝ))^deltaLoss := by
        apply Real.rpow_le_rpow hnQ.le _ hδ.le
        exact le_mul_of_one_le_left hnQ.le hK
      have hpower : (Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s≤
          (K*(Ideal.absNorm Q:ℝ))^ε := by
        apply (mul_le_mul_of_nonneg_right hnq (by positivity)).trans_eq
        rw [←Real.rpow_add (mul_pos (by linarith) hnQ)]
        congr 1
        dsimp [s,deltaLoss]
        ring
      calc
        _ = ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          ((Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s) := by dsimp [A]; ring
        _ ≤ ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          (K*(Ideal.absNorm Q:ℝ))^ε := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring

    _ = _ := by dsimp [C]; ring

theorem polynomial_short_completed_average
    (Wfamily : ℝ→ℝ→ℂ) (hWfamily : HasPolynomialKernel Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (Wfamily θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨heightDegree,Cbase,hCbase,hbase⟩ := polynomial_mean_square_of_exact_reflection
    Wfamily hWfamily ε ρ q levelBound hε hρ hq hlevel
  obtain ⟨Cs,hCs,hs⟩ := short_completed_normalized_small_power ε hε
  refine ⟨heightDegree,Cs*Cbase,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodels
  let Cr := Cbase*(1+‖θ‖)^heightDegree
  have hCr : 0<Cr := by dsimp [Cr]; positivity
  have hr := hbase θ
  have hG1 : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε
  have hA : 0≤A := by dsimp [A]; positivity
  have hcompleted (f : idealRange F) (H : Ideal ActualEisensteinCubic.O) (hH : H∈shortCubeRange (Z^(1/1000:ℝ))) :
      (∑I : rows,‖completedT (Ψ f I.val) (Wfamily θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X) := by
    have hf0 := (mem_idealRange.mp f.property).1.1
    have hfN := (mem_idealRange.mp f.property).2
    have hHN := (mem_shortCubeRange _ H).mp hH
    have hH1 : 1≤(Ideal.absNorm H:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hHN.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH0 : (Ideal.absNorm H:ℝ)≠0 := by linarith
    have hscale := short_cube_scales Z K (Ideal.absNorm G:ℝ) X F (Ideal.absNorm H:ℝ)
      hZ hK hG1 hF hFZ hH1 hHN.2.le hmargin
    have hb := hr rays K (X/(Ideal.absNorm H:ℝ)^3) hK hscale.1 rows f.val (G*f.val)
      (mul_ne_zero hG hf0) (fun P hP => dvd_trans (hbad P hP) (dvd_mul_right G f.val))
      hrows (Ψ f) lengthScale (hmodels f H hH)
    rw [Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖completedT (Ψ f I) (Wfamily θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    simp only [map_mul,Nat.cast_mul]
    have hpow : (K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε≤
        (K*(Ideal.absNorm G:ℝ)*F)^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hh := mul_le_mul_of_nonneg_left hfN (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
      nlinarith
    have hshape : K+K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))/(X/(Ideal.absNorm H:ℝ)^3)=
        K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X := by
      field_simp

    rw [hshape]
    change Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε*_≤A*_
    have hX0 : 0<X := by
      have hh := (le_div_iff₀ (show 0<(Ideal.absNorm H:ℝ)^3 by positivity)).mp hscale.1
      exact (show 0<(Ideal.absNorm H:ℝ)^3 by positivity).trans_le (by simpa only [one_mul] using hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hb := hs Z K (Ideal.absNorm G:ℝ) X F A hZ hK hG1 hF hFZ hA hmargin
    (fun f (I : rows) => Ψ f I.val) (fun f I z => hΨ f I.val z) (Wfamily θ) hcompleted
  have hsum (f : idealRange F) :
      (∑I : rows,‖shortCompletedSum (Ψ f I.val) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2)=
      ∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2 :=
    Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖shortCompletedSum (Ψ f I) (Wfamily θ) X (Z^(1/1000:ℝ))‖^2)
  simp_rw [hsum] at hb
  apply hb.trans_eq
  dsimp [A,Cr]
  ring

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem completed_mean_square_norm_height
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (normTwistedSource W θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (normTwistedSource W θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  exact polynomial_mean_square_of_exact_reflection (normTwistedSource W)
    (normTwistedSource_polynomial_kernel W a b ha hsupp hW)
    ε ρ q levelBound hε hρ hq hlevel

theorem short_completed_average_norm_height
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (normTwistedSource W θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  exact polynomial_short_completed_average (normTwistedSource W)
    (normTwistedSource_polynomial_kernel W a b ha hsupp hW)
    ε ρ q levelBound hε hρ hq hlevel

end

section

open scoped BigOperators Classical
open CompletedGauss hiding O
open ActualEisensteinCubic
open SecondPassArithmetic (normPhase normHeightTwist)
open FourierBridge (logPhase)

lemma logPhase_triple (t x : ℝ) : logPhase t (3*x)=(logPhase t x)^3 := by
  rw [show 3*x=x+x+x by ring,FourierBridge.logPhase_add,FourierBridge.logPhase_add]
  ring

lemma columnWeight_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) (I : Ideal ActualEisensteinCubic.O) :
    columnWeight (normHeightTwist Ψ t) I =
      logPhase t (Real.log (Ideal.absNorm I:ℝ))*columnWeight Ψ I := by
  by_cases hI : primaryGenerator I=0
  · have hz : squarefreeGaussCoefficient I=0 := by simp [squarefreeGaussCoefficient,hI]
    simp only [columnWeight,hz,zero_mul,mul_zero]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryGenerator I) hI
    rw [primaryGenerator_norm_sq I hI] at hn
    simp only [columnWeight,normHeightTwist,MonoidHom.mul_apply,hn]
    ring

lemma cubeWeight_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) (I : Ideal ActualEisensteinCubic.O) :
    cubeWeight (normHeightTwist Ψ t) I =
      logPhase t (3*Real.log (Ideal.absNorm I:ℝ))*cubeWeight Ψ I := by
  by_cases hI : primaryGenerator I=0
  · simp [cubeWeight,hI,FiniteGaussPhase.angularFactor]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryGenerator I) hI
    rw [primaryGenerator_norm_sq I hI] at hn
    change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
        (Ψ (primaryGenerator I)*normPhase t (primaryGenerator I))^3/(Ideal.absNorm I:ℂ)=_
    rw [hn,logPhase_triple]
    change _ = (logPhase t (Real.log (Ideal.absNorm I:ℝ)))^3*
      (star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
        Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ))
    ring

lemma summand_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X)
    (I J : Ideal ActualEisensteinCubic.O) :
    summand (normHeightTwist Ψ t) W X I J =
      logPhase t (Real.log X)*summand Ψ (normTwistedSource W t) X I J := by
  by_cases hI : I=0
  · simp only [hI,CompletedGauss.summand_zero_left,mul_zero]
  by_cases hJ : J=0
  · simp only [hJ,CompletedGauss.summand_zero_right,mul_zero]
  have hni : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)
  have hnj : 0<(Ideal.absNorm J:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one J hJ)
  have hl : Real.log X+Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)=
      Real.log (Ideal.absNorm I:ℝ)+3*Real.log (Ideal.absNorm J:ℝ) := by
    rw [Real.log_div (mul_pos hni (pow_pos hnj 3)).ne' hX.ne',
      Real.log_mul hni.ne' (pow_pos hnj 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (Real.log X)*
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)) =
      logPhase t (Real.log (Ideal.absNorm I:ℝ))*logPhase t (3*Real.log (Ideal.absNorm J:ℝ)) := by
    rw [←FourierBridge.logPhase_add,hl,FourierBridge.logPhase_add]
  simp only [summand,columnWeight_normHeight,cubeWeight_normHeight,Vstar,normTwistedSource]
  linear_combination -(columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I:ℝ):ℂ) * cubeWeight Ψ J *
    (Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X):ℂ)*
      W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X))*hphase

theorem completedT_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    completedT (normHeightTwist Ψ t) W X =
      logPhase t (Real.log X)*completedT Ψ (normTwistedSource W t) X := by
  simp only [completedT,summand_normHeight Ψ W t X hX,tsum_mul_left]

@[simp] theorem completedT_normHeight_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (t X : ℝ) (hX : 0<X) :
    ‖completedT (normHeightTwist Ψ t) W X‖=‖completedT Ψ (normTwistedSource W t) X‖ := by
  rw [completedT_normHeight Ψ W t X hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem shortCompletedSum_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (t X H₀ : ℝ) (hX : 0<X) :
    shortCompletedSum (normHeightTwist Ψ t) W X H₀ =
      logPhase t (Real.log X)*shortCompletedSum Ψ (normTwistedSource W t) X H₀ := by
  rw [shortCompletedSum_eq,shortCompletedSum_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hn : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one
    (norm_at_least_one H ((mem_shortCubeRange H₀ H).mp hH).1)
  rw [cubeWeight_normHeight,completedT_normHeight Ψ W t _ (div_pos hX (pow_pos hn 3))]
  have hl : 3*Real.log (Ideal.absNorm H:ℝ)+Real.log (X/(Ideal.absNorm H:ℝ)^3)=Real.log X := by
    rw [Real.log_div hX.ne' (pow_pos hn 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : logPhase t (3*Real.log (Ideal.absNorm H:ℝ))*
      logPhase t (Real.log (X/(Ideal.absNorm H:ℝ)^3))=logPhase t (Real.log X) := by
    rw [←FourierBridge.logPhase_add,hl]
  linear_combination (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedT Ψ (normTwistedSource W t) (X/(Ideal.absNorm H:ℝ)^3)*hphase

@[simp] theorem shortCompletedSum_normHeight_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (t X H₀ : ℝ) (hX : 0<X) :
    ‖shortCompletedSum (normHeightTwist Ψ t) W X H₀‖=
      ‖shortCompletedSum Ψ (normTwistedSource W t) X H₀‖ := by
  rw [shortCompletedSum_normHeight Ψ W t X H₀ hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end

open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem completed_mean_square_twist
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (normTwistedSource W θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (SecondPassArithmetic.normHeightTwist (Ψ I) θ) W X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨n,C,hC,h⟩ := completed_mean_square_norm_height W a b ha hsupp hW ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,C,hC,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodel
  simp_rw [completedT_normHeight_norm _ _ _ _ (lt_of_lt_of_le zero_lt_one hX)]
  exact h θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodel

theorem short_completed_average_twist
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (SecondPassArithmetic.normHeightTwist (Ψ f I) θ) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,C,hC,h⟩ := short_completed_average_norm_height W a b ha hsupp hW ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel
  have hGpos : 0<(Ideal.absNorm G:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one G hG)
  have hright : 0 < F*Z^(-(1/40:ℝ)) := mul_pos (lt_of_lt_of_le zero_lt_one hF)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _)
  have hprod : 0 < X*(F*Z^(-(1/40:ℝ))) := by
    have hh := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le zero_lt_one hK) hGpos) hmargin
    simpa only [mul_assoc] using hh
  have hX : 0<X := (mul_pos_iff_of_pos_right hright).mp hprod
  simp_rw [shortCompletedSum_normHeight_norm _ _ _ _ _ hX]
  exact h θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel

end CompletedHeight

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.UniformPolynomialHeight -/

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

namespace CompletedHeight

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open CompletedGauss hiding O
open ActualEisensteinCubic CompletedDyadic
open CanonicalQuadraticSieve hiding O
theorem uniform_polynomial_reflected_branch_series {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e (Wfamily w θ) K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e (Wfamily w θ) K Y ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hheight w
  refine ⟨C,hC,?_⟩
  intro θ K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h θ K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

theorem uniform_polynomial_reflected_fiber_fixed_scale {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal ActualEisensteinCubic.O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal ActualEisensteinCubic.O→Ideal ActualEisensteinCubic.O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e (Wfamily w θ)
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_reflected_branch_series Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*B^(2*deltaLoss+1),by positivity,?_⟩
  intro θ K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hn (J : Ideal ActualEisensteinCubic.O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale,C]) <;> ring

theorem uniform_polynomial_branch_energy {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value (Wfamily w θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_reflected_fiber_fixed_scale Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hheight w
  refine ⟨C,hC,?_⟩
  intro θ K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h θ K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

theorem uniform_polynomial_fiber_energy {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal ActualEisensteinCubic.O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤ completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value (Wfamily w θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_branch_energy Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*Cp,by positivity,?_⟩
  intro θ rays K X hK hX I F Q hI hQ hIK hk d
  let Cb := Cbase*(1+‖θ‖)^heightDegree
  have hCb : 0<Cb := by dsimp [Cb]; positivity
  have hb := hbase θ
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := ReflectedFiberData.finite_energy_bound
    (fun b => (d.branch b).value (Wfamily w θ) X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value (Wfamily w θ) X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; dsimp [Cb]; ring

theorem uniform_polynomial_energy_of_exact_models {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedModels rays rows K X ρ q levelBound F Q (Wfamily w θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^ε*
          (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_fiber_energy Wfamily hWfamily deltaLoss ε ρ q levelBound hδ hε hρ hq hlevel
  obtain ⟨Co,hCo,ho⟩ := completed_outer_row_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Co*Cbase,by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hexact
  let Cm := Cbase*(1+‖θ‖)^heightDegree
  have hCm : 0<Cm := by dsimp [Cm]; positivity
  have hm := hbase θ
  let B : ℝ := Cm*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*
    (K+K^2*(Ideal.absNorm Q:ℝ)/X)
  have hB : 0≤B := by dsimp [B,Cm]; positivity
  have hblocks : ∀A∈rows.image rowPowerfulPart,∀T∈rows.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber rows Q A T,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤B/(Ideal.absNorm A:ℝ) := by
    intro A hA T hT
    by_cases hempty : (completedRowFiber rows Q A T).Nonempty
    · obtain ⟨I,hIf,d,hd⟩ := hexact A hA T hT hempty
      obtain ⟨hIr,hIA,hIT⟩ := Finset.mem_filter.mp hIf
      have hI := (hrows I hIr).1
      have hIK := (hrows I hIr).2
      have hk := one_le_completedResidualScale K I Q hI hIK
      have hdenergy := hm rays K X hK hX I F Q hI hQ hIK hk d
      have hembed := completedRowFiber_energy_le rows Q A T hbad K hrows
        (d.idealValue (Wfamily w θ) X ρ q)
      have hscale : K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))=completedResidualScale K I Q := by
        simp only [completedResidualScale,hIA,hIT]
      rw [hscale] at hembed
      simp_rw [ReflectedFiberData.idealValue_at] at hembed
      have hsource : (∑J∈completedRowFiber rows Q A T,‖completedT (Ψ J) (Wfamily w θ) X‖^2)=
          ‖lengthScale‖^2*∑J∈completedRowFiber rows Q A T,‖d.idealValue (Wfamily w θ) X ρ q (rowResidualPart J Q)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hd J hJ,norm_mul,mul_pow]
      rw [hsource]
      apply (mul_le_mul_of_nonneg_left (hembed.trans hdenergy) (sq_nonneg _)).trans
      apply le_of_eq
      dsimp [B,Cm]
      rw [hIA]
      ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty,Finset.sum_empty]
      exact div_nonneg hB (Nat.cast_nonneg _)
  have hh := ho rows Q hQ (fun I => ‖completedT (Ψ I) (Wfamily w θ) X‖^2) B hB hblocks
  apply hh.trans_eq
  dsimp [B,Cm]
  ring

theorem uniform_polynomial_mean_square_of_exact_reflection {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (Wfamily w θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  let deltaLoss : ℝ := ε/12
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_energy_of_exact_models Wfamily hWfamily deltaLoss deltaLoss ρ q levelBound hδ hδ hρ hq hlevel
  let s : ℝ := 10*deltaLoss+deltaLoss
  have hs : 0≤ s := by dsimp [s]; positivity
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*(16*(2:ℝ)^s),by positivity,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodels
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := C*(rays:ℝ)^2*‖lengthScale‖^2*(Ideal.absNorm Q:ℝ)^deltaLoss
  have hA : 0≤A := by dsimp [A]; positivity
  rw [←completedRowDyad_sum rows K (by linarith : 0≤K) (fun I hI => (hrows I hI).2)
    (fun I => ‖completedT (Ψ I) (Wfamily w θ) X‖^2)]
  have hper (j : ℕ) (hj : j∈Finset.range (completedRowDyadicLength K+1)) :
      (∑I∈completedRowDyad rows j,‖completedT (Ψ I) (Wfamily w θ) X‖^2)≤
        A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
          ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := by
    have hb := h rays ((2:ℝ)^j) X (one_le_pow₀ (by norm_num)) hX
      (completedRowDyad rows j) F Q hQ hbad
      (fun I hI => ⟨(completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).1,
        (completedRowDyad_bounds rows j (fun I hI => (hrows I hI).1) I hI).2.2⟩)
      Ψ lengthScale (hmodels j hj)
    convert hb using 1
    dsimp [A,s,C]
    ring
  calc
    _ ≤ ∑j∈Finset.range (completedRowDyadicLength K+1),
      A*(((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X)) := Finset.sum_le_sum hper
    _ = A*∑j∈Finset.range (completedRowDyadicLength K+1),
      ((2:ℝ)^j*(Ideal.absNorm Q:ℝ))^s*
        ((2:ℝ)^j+((2:ℝ)^j)^2*(Ideal.absNorm Q:ℝ)/X) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*((16*(2:ℝ)^s)*(K*(Ideal.absNorm Q:ℝ))^s*(K+K^2*(Ideal.absNorm Q:ℝ)/X)) :=
      mul_le_mul_of_nonneg_left (completedRowDyadic_shape s K X (Ideal.absNorm Q:ℝ) hs hK
        (by linarith) hnQ) hA
    _ ≤ (C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
        (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
      have hnq : (Ideal.absNorm Q:ℝ)^deltaLoss≤(K*(Ideal.absNorm Q:ℝ))^deltaLoss := by
        apply Real.rpow_le_rpow hnQ.le _ hδ.le
        exact le_mul_of_one_le_left hnQ.le hK
      have hpower : (Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s≤
          (K*(Ideal.absNorm Q:ℝ))^ε := by
        apply (mul_le_mul_of_nonneg_right hnq (by positivity)).trans_eq
        rw [←Real.rpow_add (mul_pos (by linarith) hnQ)]
        congr 1
        dsimp [s,deltaLoss]
        ring
      calc
        _ = ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          ((Ideal.absNorm Q:ℝ)^deltaLoss*(K*(Ideal.absNorm Q:ℝ))^s) := by dsimp [A]; ring
        _ ≤ ((C*(16*(2:ℝ)^s))*(rays:ℝ)^2*‖lengthScale‖^2*(K+K^2*(Ideal.absNorm Q:ℝ)/X))*
          (K*(Ideal.absNorm Q:ℝ))^ε := mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring

    _ = _ := by dsimp [C]; ring

theorem uniform_polynomial_short_completed_average {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (Wfamily w θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_mean_square_of_exact_reflection
    Wfamily hWfamily ε ρ q levelBound hε hρ hq hlevel
  obtain ⟨Cs,hCs,hs⟩ := short_completed_normalized_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cs*Cbase,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodels
  let Cr := Cbase*(1+‖θ‖)^heightDegree
  have hCr : 0<Cr := by dsimp [Cr]; positivity
  have hr := hbase θ
  have hG1 : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε
  have hA : 0≤A := by dsimp [A]; positivity
  have hcompleted (f : idealRange F) (H : Ideal ActualEisensteinCubic.O) (hH : H∈shortCubeRange (Z^(1/1000:ℝ))) :
      (∑I : rows,‖completedT (Ψ f I.val) (Wfamily w θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X) := by
    have hf0 := (mem_idealRange.mp f.property).1.1
    have hfN := (mem_idealRange.mp f.property).2
    have hHN := (mem_shortCubeRange _ H).mp hH
    have hH1 : 1≤(Ideal.absNorm H:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hHN.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH0 : (Ideal.absNorm H:ℝ)≠0 := by linarith
    have hscale := short_cube_scales Z K (Ideal.absNorm G:ℝ) X F (Ideal.absNorm H:ℝ)
      hZ hK hG1 hF hFZ hH1 hHN.2.le hmargin
    have hb := hr rays K (X/(Ideal.absNorm H:ℝ)^3) hK hscale.1 rows f.val (G*f.val)
      (mul_ne_zero hG hf0) (fun P hP => dvd_trans (hbad P hP) (dvd_mul_right G f.val))
      hrows (Ψ f) lengthScale (hmodels f H hH)
    rw [Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖completedT (Ψ f I) (Wfamily w θ) (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    simp only [map_mul,Nat.cast_mul]
    have hpow : (K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε≤
        (K*(Ideal.absNorm G:ℝ)*F)^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hh := mul_le_mul_of_nonneg_left hfN (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
      nlinarith
    have hshape : K+K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))/(X/(Ideal.absNorm H:ℝ)^3)=
        K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X := by
      field_simp

    rw [hshape]
    change Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε*_≤A*_
    have hX0 : 0<X := by
      have hh := (le_div_iff₀ (show 0<(Ideal.absNorm H:ℝ)^3 by positivity)).mp hscale.1
      exact (show 0<(Ideal.absNorm H:ℝ)^3 by positivity).trans_le (by simpa only [one_mul] using hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hb := hs Z K (Ideal.absNorm G:ℝ) X F A hZ hK hG1 hF hFZ hA hmargin
    (fun f (I : rows) => Ψ f I.val) (fun f I z => hΨ f I.val z) (Wfamily w θ) hcompleted
  have hsum (f : idealRange F) :
      (∑I : rows,‖shortCompletedSum (Ψ f I.val) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2)=
      ∑I∈rows,‖shortCompletedSum (Ψ f I) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2 :=
    Finset.sum_coe_sort (s := rows) (f := fun I : Ideal ActualEisensteinCubic.O => ‖shortCompletedSum (Ψ f I) (Wfamily w θ) X (Z^(1/1000:ℝ))‖^2)
  simp_rw [hsum] at hb
  apply hb.trans_eq
  dsimp [A,Cr]
  ring

end

open CompletedGauss hiding O
open ActualEisensteinCubic
open CanonicalQuadraticSieve hiding O
theorem completed_mean_square_uniform_height
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W → ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (normTwistedSource W θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (Ψ I) (normTwistedSource W θ) X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨n,hn⟩ := uniform_polynomial_mean_square_of_exact_reflection
    (fun W : SupportedSmoothSource a b => normTwistedSource W.val)
    (normTwistedSource_uniform_polynomial_kernel a b ha)
    ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  exact hn ⟨W,hsupp,hW⟩

theorem short_completed_average_uniform_height
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W → ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) (normTwistedSource W θ) X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := uniform_polynomial_short_completed_average
    (fun W : SupportedSmoothSource a b => normTwistedSource W.val)
    (normTwistedSource_uniform_polynomial_kernel a b ha)
    ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  exact hn ⟨W,hsupp,hW⟩

theorem completed_mean_square_uniform_twist
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W → ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀(rows : Finset (Ideal ActualEisensteinCubic.O)) (F Q : Ideal ActualEisensteinCubic.O),Q≠0 →
      (∀P∈fixedBadPrimes,P∣Q) → (∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀(Ψ : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ) (lengthScale : ℂ),HasExactCompletedDyadicModels rays rows K X ρ q levelBound F Q (normTwistedSource W θ) Ψ lengthScale →
      (∑I∈rows,‖completedT (SecondPassArithmetic.normHeightTwist (Ψ I) θ) W X‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm Q:ℝ))^ε*
          (K+K^2*(Ideal.absNorm Q:ℝ)/X) := by
  obtain ⟨n,hn⟩ := completed_mean_square_uniform_height a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  obtain ⟨C,hC,h⟩ := hn W hsupp hW
  refine ⟨C,hC,?_⟩
  intro θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodel
  simp_rw [completedT_normHeight_norm _ _ _ _ (lt_of_lt_of_le zero_lt_one hX)]
  exact h θ rays K X hK hX rows F Q hQ hbad hrows Ψ lengthScale hmodel

theorem short_completed_average_uniform_twist
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ, Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W → ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal ActualEisensteinCubic.O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) (normTwistedSource W θ) (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (SecondPassArithmetic.normHeightTwist (Ψ f I) θ) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := short_completed_average_uniform_height a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  obtain ⟨C,hC,h⟩ := hn W hsupp hW
  refine ⟨C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel
  have hGpos : 0<(Ideal.absNorm G:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one G hG)
  have hright : 0 < F*Z^(-(1/40:ℝ)) := mul_pos (lt_of_lt_of_le zero_lt_one hF)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _)
  have hprod : 0 < X*(F*Z^(-(1/40:ℝ))) := by
    have hh := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le zero_lt_one hK) hGpos) hmargin
    simpa only [mul_assoc] using hh
  have hX : 0<X := (mul_pos_iff_of_pos_right hright).mp hprod
  simp_rw [shortCompletedSum_normHeight_norm _ _ _ _ _ hX]
  exact h θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodel

end CompletedHeight

open scoped BigOperators Classical
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open UnrestrictedIdealReindex (unitIdealEquiv span_unit_generator)
local instance : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def rowUnit (z : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ :=
  if hz : z=0 then 1 else (unitIdealEquiv.symm ⟨z,hz⟩).1

lemma rowUnit_spec (z : ActualEisensteinCubic.O) (hz : z≠0) :
    (rowUnit z).val * idealGenerator (Ideal.span {z}) = z := by
  let p := unitIdealEquiv.symm ⟨z,hz⟩
  have hp : p.1.val*idealGenerator p.2.val=z :=
    congrArg Subtype.val (unitIdealEquiv.apply_symm_apply ⟨z,hz⟩)
  have hI : p.2.val=Ideal.span {z} := by
    rw [←hp,span_unit_generator]
  simpa only [rowUnit,dite_eq_right hz,←hI] using hp

def unitIdealPoint (z : ActualEisensteinCubic.O) : ActualEisensteinCubic.Oˣ × Ideal ActualEisensteinCubic.O := (rowUnit z,Ideal.span {z})

lemma unitIdealPoint_inj (z w : ActualEisensteinCubic.O) (hz : z≠0) (hw : w≠0)
    (h : unitIdealPoint z=unitIdealPoint w) : z=w := by
  have hu : rowUnit z=rowUnit w := congrArg Prod.fst h
  have hI : Ideal.span {z}=Ideal.span {w} := congrArg Prod.snd h
  rw [←rowUnit_spec z hz,←rowUnit_spec w hw,hu,hI]

theorem sum_nonzero_element_le_units (T : Finset ActualEisensteinCubic.O) (hT : ∀z∈T,z≠0)
    (v : ActualEisensteinCubic.O→ℝ) (hv : ∀z,0≤v z) :
    (∑z∈T,v z) ≤ ∑u : ActualEisensteinCubic.Oˣ,∑I∈T.image (fun z=>Ideal.span {z}),
      v (u.val*idealGenerator I) := by
  let f : ActualEisensteinCubic.Oˣ×Ideal ActualEisensteinCubic.O→ℝ := fun p=>v (p.1.val*idealGenerator p.2)
  have hinj : Set.InjOn unitIdealPoint T := by
    intro z hz w hw he
    exact unitIdealPoint_inj z w (hT z hz) (hT w hw) he
  have he : (∑z∈T,v z)=∑p∈T.image unitIdealPoint,f p := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro z hz
    dsimp [f,unitIdealPoint]
    rw [rowUnit_spec z (hT z hz)]
  have hsub : T.image unitIdealPoint ⊆
      (Finset.univ : Finset ActualEisensteinCubic.Oˣ) ×ˢ T.image (fun z=>Ideal.span {z}) := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  rw [he]
  calc
    _ ≤ ∑p∈(Finset.univ : Finset ActualEisensteinCubic.Oˣ) ×ˢ T.image (fun z=>Ideal.span {z}),f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>hv _)
    _ = _ := by rw [Finset.sum_product]

lemma image_span_nonzero_norm (T : Finset ActualEisensteinCubic.O) (K : ℝ)
    (hT : ∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤K) :
    ∀I∈T.image (fun z=>Ideal.span {z}),I≠0 ∧ (Ideal.absNorm I:ℝ)≤K := by
  intro I hI
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hI
  exact ⟨Ideal.span_singleton_eq_bot.not.mpr (hT z hz).1,(hT z hz).2⟩

lemma unit_card : Fintype.card ActualEisensteinCubic.Oˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

end CompletedUnitRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.MeanSquare.UnitRows -/

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CanonicalRowCompletion
local instance : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def unitRowFamily (Ψ : ActualEisensteinCubic.O→*ℂ) (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ}
    (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) : ActualEisensteinCubic.O→*ℂ :=
  rowTwist Ψ mask (idealGenerator f.val) (u.val*idealGenerator I)

lemma unitRowFamily_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ} (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) (x : ActualEisensteinCubic.O) :
    ‖unitRowFamily Ψ mask u f I x‖≤1 := rowTwist_norm Ψ hΨ _ _ _ _

lemma rowTwist_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (mask f z : ActualEisensteinCubic.O) (θ : ℝ) :
    rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ) mask f z =
      SecondPassArithmetic.normHeightTwist (rowTwist Ψ mask f z) θ := by
  unfold rowTwist
  exact (SecondPassArithmetic.normHeightTwist_mul Ψ _ θ).symm

theorem short_completed_elements_uniform_twist
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀T : Finset ActualEisensteinCubic.O,(∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤K) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays (T.image (fun z=>Ideal.span {z})) K
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (unitRowFamily Ψ mask u f) lengthScale) →
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := CompletedHeight.short_completed_average_uniform_twist
    a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  obtain ⟨C,hC,hbound⟩ := hn W hsupp hW
  refine ⟨6*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin T hT Ψ hΨ mask lengthScale hmodels
  let rows := T.image (fun z=>Ideal.span {z})
  let R : ℝ := (C*(1+‖θ‖)^n)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε
  have hrows := image_span_nonzero_norm T K hT
  have hu (u : ActualEisensteinCubic.Oˣ) :
      (∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F≤R := by
    simp_rw [rowTwist_normHeight]
    exact hbound θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows
      (unitRowFamily Ψ mask u) (unitRowFamily_norm Ψ hΨ mask u) lengthScale (hmodels u)
  have hsum :
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)≤
      ∑u : ActualEisensteinCubic.Oˣ,∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2 := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro f _
    exact sum_nonzero_element_le_units T (fun z hz=>(hT z hz).1) _ (fun z=>sq_nonneg _)
  calc
    _ ≤ (∑u : ActualEisensteinCubic.Oˣ,∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F :=
      div_le_div_of_nonneg_right hsum (by linarith)
    _ = ∑u : ActualEisensteinCubic.Oˣ,(∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F :=
      Finset.sum_div _ _ _
    _ ≤ ∑u : ActualEisensteinCubic.Oˣ,R := Finset.sum_le_sum (fun u _=>hu u)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,unit_card,nsmul_eq_mul]; dsimp [R]; ring

end CompletedUnitRows

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open CanonicalCoefficientClass (IsBaseRayTwist)
open RayFourExpansion (RayCharacter)

structure CanonicalStateCondition (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ) : Prop where
  coefficient : IsBaseRayTwist base Ψ
  mask_ne_zero : m≠0
  column_pos : 0<X
  label_ge_one : 1≤F
  row_ge_one : 1≤K
  row_le_global : K≤Z^3
  mass_le : X*F≤ canonicalRankMass Z (fixedDepthRank Z K)
  invariant : K*‖eisEmbedding m‖^2≤
    (X*F)*Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K))
  label_bounds : ∀I∈labels,I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤F

theorem CanonicalStateCondition.invariant_reserved
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40) :
    K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((1:ℝ)/40)) :=
  canonicalRankMargin_final_bound Z η _ _ _ hZ hη
    (mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one)) hbudget h.invariant

theorem CanonicalStateCondition.small_or_live
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : Real.exp 9000≤Z) (hZ1 : 1≤Z) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/40) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  have hi := h.invariant_reserved hZ1 hη hbudget
  have hr : Z^(-((1:ℝ)/40))≤1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : -((1:ℝ)/40)≤0))
  have hi' : K*‖eisEmbedding m‖^2≤X*F :=
    hi.trans ((mul_le_mul_of_nonneg_left hr
      (mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one))).trans_eq (mul_one _))
  exact canonical_small_or_live Z X F K _ m hZ h.column_pos h.label_ge_one
    (zero_le_one.trans h.row_ge_one) h.mask_ne_zero h.mass_le hi'

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem canonicalStateCondition_retained
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hpbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (a : RayCharacter) (r : FirstCoreIndex) (ray : SecondRayIndex) (B : ℝ)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hB : 0<B) (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    let labels':=globalCanonicalLabels p source side q j
    let m':=fixedTripleMask m q
    fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧
    CanonicalStateCondition base bad Z η (secondRayMinus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' ∧
    CanonicalStateCondition base bad Z η (secondRayPlus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' := by
  obtain ⟨hXc,hFc,hKc,hrank,hKglobal,hmass,hinvariant,hm,hlabels⟩ :=
    canonical_retained_unpadded_closure p hp source side q j hq Z ((1:ℝ)/20) η X B F K m
      hZ hZbig hη hηsmall hstate.column_pos hB hstate.label_ge_one hstate.row_ge_one
      hstate.mask_ne_zero hprogress hstate.row_le_global hstate.mass_le hstate.invariant
      hk hb₁ hb₂ hretained
  have hbad := globalCanonicalLabels_coprime p bad hpbad source side q j
  have hbnd : ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
    intro I hI
    exact ⟨(hlabels I hI).1,(hlabels I hI).2.1,hbad I hI,(hlabels I hI).2.2⟩
  refine ⟨hrank,?_,?_⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondMinus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant,hbnd⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondPlus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant,hbnd⟩

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open CanonicalCoefficientClass (IsBaseRayTwist)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem canonicalStateCondition_cutoff_retained
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
    (hpbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (a : RayCharacter) (r : FirstCoreIndex) (ray : SecondRayIndex) (B : ℝ)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hB : 0<B) (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    let labels':=globalCanonicalLabels p source side q j
    let m':=fixedTripleMask m q
    fixedDepthRank Z K'+1≤fixedDepthRank Z Ksrc ∧
    CanonicalStateCondition base bad Z η (secondRayMinus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' ∧
    CanonicalStateCondition base bad Z η (secondRayPlus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' := by
  obtain ⟨hXc,hFc,hKc,hrank,hKglobal,hmass,hinvariant,hm,hlabels⟩ :=
    canonical_retained_scale_closure p hp source side q j hq Z
      (canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z Ksrc)) η X B F Ksrc m
      hZ hZbig hη hηsmall hstate.column_pos hB hstate.label_ge_one hstate.row_ge_one
      hstate.mask_ne_zero hprogress hstate.row_le_global hstate.mass_le hstate.invariant
      hk hb₁ hb₂ hretained
  have hinvariant' : (globalLogRep j 8*Real.exp 1)*‖eisEmbedding (fixedTripleMask m q)‖^2≤
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)*
        Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    apply hinvariant.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hXc.le (zero_le_one.trans hFc))
    have hmargin := canonicalRankMargin_step ((1:ℝ)/20) η hη _ _
      (fixedDepthRank_initial Z Ksrc hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global) hrank
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hbad := globalCanonicalLabels_coprime p bad hpbad source side q j
  have hbnd : ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
    intro I hI
    exact ⟨(hlabels I hI).1,(hlabels I hI).2.1,hbad I hI,(hlabels I hI).2.2⟩
  refine ⟨hrank,?_,?_⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondMinus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant',hbnd⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondPlus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant',hbnd⟩

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem nonzeroRowFamily_le_center (labels : Finset (Ideal ActualEisensteinCubic.O))
    (P : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) (K scale B : ℝ) (zero tail : ℂ)
    (hK : 0<K) (hscale : 0<scale)
    (hcenter : ‖(scale:ℂ)⁻¹*((∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
      (‖P I z‖^2:ℝ))-zero-tail)‖≤B) :
    (∑I∈labels,nonzeroRowMajorantSum (P I) K).re≤
      ‖zero‖+‖tail‖+scale*B := by
  let total : ℂ := ∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ)
  have hnonzero : (∑I∈labels,nonzeroRowMajorantSum (P I) K).re≤total.re := by
    simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
      Complex.re_sum,Complex.ofReal_re]
    change (∑I∈labels,(∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ)).re)-
      ∑I∈labels,‖P I 0‖^2≤_
    have hz : 0≤∑I∈labels,‖P I 0‖^2 := Finset.sum_nonneg (fun I hI=>sq_nonneg _)
    dsimp only [total]
    rw [Complex.re_sum]
    linarith
  have hc : ‖total-zero-tail‖≤ scale*B := by
    calc
      _ = scale*‖(scale:ℂ)⁻¹*(total-zero-tail)‖ := by
        rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscale]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hcenter hscale.le
  apply hnonzero.trans
  calc
    total.re ≤ ‖total‖ := Complex.re_le_norm _
    _ = ‖(total-zero-tail)+zero+tail‖ := by congr 1; ring
    _ ≤ ‖total-zero-tail‖+‖zero‖+‖tail‖ := norm_add₃_le
    _ ≤ _ := by linarith

theorem reopenedCanonicalRow_nonzero_twoPassage
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (β:Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (Γ t Ksrc Kcut ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<Kcut → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M≤U → (∀u,‖Ψ u‖≤1) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      (∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p ell S))) Ksrc).re≤
      ‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc ell‖+
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc Kcut ell‖+
      (ell*B^2*F)*(Ksrc/Kcut)*Cfirst*(globalFirstRowCap Kcut ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε Kcut ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε Kcut ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩ :=
    reopenedCanonicalRow_twoPassage_uniform_height rowMajorant g V M Nv hM hNv hgM hV hWin
      ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F H U
    hΓ hKsrc hKcut hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  have ht := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F H U
    hΓ hKsrc hKcut hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  have hscale : 0<ell*B^2*F := mul_pos (mul_pos hell (sq_pos_of_pos (zero_lt_one.trans_le hB))) hF
  have hb := nonzeroRowFamily_le_center labels
    (fun I=>reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
      (ConcretePrimeRowBridge.idealGenerator I)
      (fun S=>frequencyTwist g t (columnLog p ell S))) Ksrc (ell*B^2*F)
    ((Ksrc/Kcut)*Cfirst*(globalFirstRowCap Kcut ell B F)^deltaLoss*
      Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool (reopenedCubeFamily Q))
        (normHeightTwist Ψ t) m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε Kcut ell B F M H U A J N true)*
      Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool (reopenedCubeFamily Q))
        (normHeightTwist Ψ t) m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε Kcut ell B F M H U A J N false))
    (canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc ell)
    (canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc Kcut ell)
    hKsrc hscale (by simpa only [Complex.ofReal_mul,Complex.ofReal_pow] using ht)
  exact hb.trans_eq (by ring)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

def euclideanAxisPath (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) : EuclideanSpatial :=
  WithLp.toLp 2 (Function.update p.ofLp j t)

lemma euclideanAxisPath_affine (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    euclideanAxisPath p j t=p+(t-p j)•euclideanCoordinateVector j := by
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext k
  by_cases hk : k=j
  · subst k
    simp [euclideanAxisPath,euclideanCoordinateVector]
  · simp [euclideanAxisPath,euclideanCoordinateVector,Function.update,hk]

lemma euclideanAxisPath_self (p : EuclideanSpatial) (j : Fin 3) :
    euclideanAxisPath p j (p j)=p := by
  rw [euclideanAxisPath_affine,sub_self,zero_smul,add_zero]

lemma euclideanAxisPath_hasDerivAt (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    HasDerivAt (euclideanAxisPath p j) (euclideanCoordinateVector j) t := by
  have he : euclideanAxisPath p j=(fun t => p+(t-p j)•euclideanCoordinateVector j) :=
    funext (euclideanAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (euclideanCoordinateVector j))

lemma euclideanAxisSlice_deriv (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (j : Fin 3) (t : ℝ) (hf : DifferentiableAt ℝ f (euclideanAxisPath p j t)) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) t=
      fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (euclideanAxisPath_hasDerivAt p j t)).deriv

lemma euclideanAxisSlice_derivatives (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) (p j)=
      fderiv ℝ f p (euclideanCoordinateVector j) ∧
    deriv (deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p (euclideanCoordinateVector j) := by
  constructor
  · simpa only [euclideanAxisPath_self] using euclideanAxisSlice_deriv f p j (p j)
      (by simpa only [euclideanAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => euclideanAxisPath p j t 2) (p j) :=
      (by fun_prop : Continuous (fun q : EuclideanSpatial => q 2)).continuousAt.comp
        (euclideanAxisPath_hasDerivAt p j (p j)).continuousAt
    have hpos : 0<euclideanAxisPath p j (p j) 2 := by rw [euclideanAxisPath_self]; exact hp
    have he : deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact euclideanAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j))
        (euclideanAxisPath p j (p j)) := by rwa [euclideanAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (euclideanAxisPath_hasDerivAt p j (p j))
    simpa only [euclideanAxisPath_self,Function.comp_def] using! hh.deriv

def positiveEuclideanLaplacian (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p
    (euclideanCoordinateVector j))+(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector 2)

lemma positiveEuclideanLaplacian_eq_axis (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian f p=-axisLaplacian (fun q => f (WithLp.toLp 2 q)) p.ofLp := by
  unfold positiveEuclideanLaplacian axisLaplacian
  simp only [(euclideanAxisSlice_derivatives f hf p hp _).1,(euclideanAxisSlice_derivatives f hf p hp _).2]
  ring

lemma positiveEuclideanLaplacian_congr (f g : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (he : f=ᶠ[𝓝 p]g) : positiveEuclideanLaplacian f p=positiveEuclideanLaplacian g p := by
  have hd (j : Fin 3) : (fun q => fderiv ℝ f q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  simp only [positiveEuclideanLaplacian,he.fderiv_eq,(hd _).fderiv_eq]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv Manifold

namespace CubicEisenstein

lemma kernelTestPartitionTerm_tsupport_right {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport f.1 :=
  tsupport_smul_subset_right _ _

lemma kernelSmoothTest_finite_chart_partition_subsupport (f : kernelSmoothTests) :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 ∧
        tsupport (g i).1⊆tsupport f.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact ⟨(kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i),
    kernelTestPartitionTerm_tsupport_right ρ f i⟩

lemma kernelDirichletForm_supported_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
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
      · by_cases hgp : kernelEuclideanProjection p∈tsupport g.1
        · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp) hgp]
          rfl
        · have hz : g.1 (kernelEuclideanProjection p)=0 := image_eq_zero_of_notMem_tsupport hgp
          change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
          rw [hz,mul_zero,zero_div,mul_zero,zero_div]
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

theorem kernelDirichletForm_supported_equation (f g : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition_subsupport g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_supported_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i).1 A hA (fun p hp hgp => heq p hp ((hGsupp i).2 hgp))
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

end CubicEisenstein

end

end OAI

end

