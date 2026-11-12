module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Reflection.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Reflection / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Reflection.RowReindex -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def originalResidualRows (rows : Finset (Ideal Eis)) (R Q : Ideal Eis) : Finset (Ideal Eis) :=
  (representativeRowFiber rows R Q).image (fun I => rowResidualPart I Q)

lemma originalResidualRows_reconstruct (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    reconstructFiberRow R Q K∈representativeRowFiber rows R Q ∧
      rowResidualPart (reconstructFiberRow R Q K) Q=K := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have he := reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)
  rw [he]
  exact ⟨hI,rfl⟩

lemma originalResidualRows_range (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes, P∣Q) (X : ℝ)
    (hrows : ∀ I∈rows, I≠0 ∧ (Ideal.absNorm I:ℝ)≤X)
    (K : Ideal Eis) (hK : K∈originalResidualRows rows R Q) :
    Admissible K ∧ (Ideal.absNorm K:ℝ)≤
      X/((Ideal.absNorm (rowPowerfulPart R):ℝ)*(Ideal.absNorm (rowMaskPart R Q):ℝ)) := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact mem_idealRange.mp (completedRowFiber_residual_range rows Q (rowPowerfulPart R)
    (rowMaskPart R Q) hbad X hrows I hI)

theorem original_fiber_sum_reindex {M : Type*} [AddCommMonoid M]
    (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→M) :
    (∑ I∈representativeRowFiber rows R Q,f I)=
      ∑ K∈originalResidualRows rows R Q,f (reconstructFiberRow R Q K) := by
  rw [originalResidualRows,Finset.sum_image (representativeRowFiber_injective rows R Q hrows)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [reconstructFiberRow_of_original rows R Q I hI (hrows I (Finset.mem_filter.mp hI).1)]

theorem original_fiber_energy_reindex (rows : Finset (Ideal Eis)) (R Q : Ideal Eis)
    (hrows : ∀ I∈rows, I≠0) (f : Ideal Eis→ℂ) :
    (∑ I∈representativeRowFiber rows R Q,‖f I‖^2)=
      ∑ K∈originalResidualRows rows R Q,‖f (reconstructFiberRow R Q K)‖^2 :=
  original_fiber_sum_reindex rows R Q hrows (fun I => ‖f I‖^2)

end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.CompletedAggregation -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_representative_aggregation (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (parents : Finset (Ideal Eis)) (Q : Ideal Eis),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ∀ (E : ℝ) (f : Ideal Eis→ℝ),0≤E →
      (∀ J∈parents,(∑ I∈representativeRowFiber parents J Q,f I)≤
        E*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ))) →
      (∑ I∈parents,f I)≤C*Z^ε*E := by
  obtain ⟨C,hC,hbudget⟩ := InverseReflectedPhasePowerfulBudget.row_mask_powerful_budget L ε hL hε
  refine ⟨C,hC,?_⟩
  intro Z hZ parents Q hparents hQ hQN E f hE hf
  have hb := hbudget Z hZ parents Q hparents hQ hQN
  simp only [neg_div] at hb
  have hblocks (A T : Ideal Eis) : (∑ I∈completedRowFiber parents Q A T,f I)≤
      E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) := by
    by_cases he : (completedRowFiber parents Q A T).Nonempty
    · obtain ⟨J,hJ⟩ := he
      obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
      have hh := hf J hJS
      simpa only [representativeRowFiber,hJA,hJT] using hh
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      exact mul_nonneg hE (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [←sum_completedRowFibers parents Q f]
  calc
    _ ≤ ∑ A∈parents.image rowPowerfulPart,∑ _T∈parents.image (fun I => rowMaskPart I Q),
          E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun T _ => hblocks A T))
    _ = (((parents.image (fun I => rowMaskPart I Q)).card:ℝ)*
          (∑ A∈parents.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-(1/2:ℝ))))*E := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hE
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SectorAggregation -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) : Finset (Ideal Eis) :=
  rows.filter (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r)

lemma mem_fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) (K : Ideal Eis) :
    K∈fullRaySector N rows r ↔ K∈rows ∧ Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r :=
  Finset.mem_filter

lemma sum_fullRaySectors {M : Type*} [AddCommMonoid M] (N : Eis)
    [Fintype (Eis⧸Ideal.span {N^2})] (rows : Finset (Ideal Eis)) (f : Ideal Eis→M) :
    (∑ r : Eis⧸Ideal.span {N^2}, ∑ K∈fullRaySector N rows r,f K)=∑ K∈rows,f K :=
  Finset.sum_fiberwise rows (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)) f

theorem full_ray_sector_energy (N : Eis) [Fintype (Eis⧸Ideal.span {N^2})]
    (rows Pset : Finset (Ideal Eis)) (f : Ideal Eis→Ideal Eis→ℂ) (E : ℝ)
    (hE : ∀ r p : Eis⧸Ideal.span {N^2},
      (∑ K∈fullRaySector N rows r, ‖∑ P∈fullRaySector N Pset p,f K P‖^2)≤E) :
    (∑ K∈rows,‖∑ P∈Pset,f K P‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*E := by
  rw [←sum_fullRaySectors N rows (fun K => ‖∑ P∈Pset,f K P‖^2)]
  calc
    _ ≤ ∑ r : Eis⧸Ideal.span {N^2}, (Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^2*E := by
      apply Finset.sum_le_sum
      intro r hr
      have hh := weighted_finite_row_energy_uniform (Finset.univ : Finset (Eis⧸Ideal.span {N^2}))
        (fullRaySector N rows r) (fun _ => (1:ℂ))
        (fun p K => ∑ P∈fullRaySector N Pset p,f K P) E (fun p _ => hE r p)
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      have he : (∑ K∈fullRaySector N rows r, ‖∑ P∈Pset,f K P‖^2)=
          ∑ K∈fullRaySector N rows r, ‖∑ p : Eis⧸Ideal.span {N^2},∑ P∈fullRaySector N Pset p,f K P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [sum_fullRaySectors]
      rw [he]
      exact hh
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SectorCover -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sector_arithmetic_prescribed (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (hcommon : ∀ (x y : SourcePair rows Pset),
      (D x.val.1 x.val.2 x.property).fixedFactor=(D y.val.1 y.val.2 y.property).fixedFactor ∧
      ∀ u m n b,actualCuspColumn (D x.val.1 x.val.2 x.property) s hc u m n b=
        actualCuspColumn (D y.val.1 y.val.2 y.property) s hc u m n b)
    (D0 : ControlledStratumArithmetic F.generator N a c mode) :
    ∃ E : SectorArithmetic (N:=N) F rows Pset S hrows s hc,E.completion=D := by
  by_cases hn : Nonempty (SourcePair rows Pset)
  · let x0 : SourcePair rows Pset := Classical.choice hn
    exact ⟨{
      referenceIndex := φ⊕(PrimeIndex x0.val.1.val⊕σ)
      referencePrimes := F.reflected x0.val.1.val (hrows x0.val.1.val x0.val.1.property) (S x0.val.2.val)
      referenceArithmetic := D x0.val.1 x0.val.2 x0.property
      completion := D
      fixedFactor_eq := fun K P hp => (hcommon ⟨(K,P),hp⟩ x0).1
      cuspColumn_eq := fun K P hp => (hcommon ⟨(K,P),hp⟩ x0).2
    },rfl⟩
  · let F0 : PrimeFamily (ULift.{v} φ) := ⟨fun x => F.ideal x.down,fun x => F.maximal x.down,fun x => F.good x.down⟩
    let e : ULift.{v} φ ≃ φ := Equiv.ulift
    let D0' := reindexControlled D0 e
    exact ⟨{
      referenceIndex := ULift.{v} φ
      referencePrimes := F0
      referenceArithmetic := D0'
      completion := D
      fixedFactor_eq := fun K P hp => (hn ⟨⟨(K,P),hp⟩⟩).elim
      cuspColumn_eq := fun K P hp => (hn ⟨⟨(K,P),hp⟩⟩).elim
    },rfl⟩

theorem exists_global_sector_completion (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f,IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hprod : ∀ P∈Pset,(∏ i,(S P).ideal i)=P)
    (hScop : ∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P∈Pset,∀ i,IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode,
    ∀ r p : Eis⧸Ideal.span {N^2},
    ∃ E : SectorArithmetic (N:=N) F (fullRaySector N rows r) (fullRaySector N Pset p) S
      (fun K hK => hrows K (Finset.mem_filter.mp hK).1) s hc,
    ∀ (K : fullRaySector N rows r) (P : fullRaySector N Pset p) hp,
      E.completion K P hp=D ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
        ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ hp := by
  obtain ⟨Dpair,κ,A,_,_,hκ,hA⟩ := exists_source_pair_templates F rows Pset S hrows hprod N a c mode s hc
    hN hbase hac hF hNF hrowcop hScop hSN
  let D := fun (K : rows) (P : Pset) (hp : IsCoprime K.val P.val) => Dpair ⟨(K,P),hp⟩
  refine ⟨D,?_⟩
  intro r p
  let Ds := fun (K : fullRaySector N rows r) (P : fullRaySector N Pset p) (hp : IsCoprime K.val P.val) =>
    D ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ hp
  have hh (x y : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
      (Ds x.val.1 x.val.2 x.property).fixedFactor=(Ds y.val.1 y.val.2 y.property).fixedFactor ∧
      ∀ u m n b,actualCuspColumn (Ds x.val.1 x.val.2 x.property) s hc u m n b=
        actualCuspColumn (Ds y.val.1 y.val.2 y.property) s hc u m n b := by
    have hsector (x : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
        separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)=(r,p) :=
      Prod.ext (Finset.mem_filter.mp x.val.1.property).2 (Finset.mem_filter.mp x.val.2.property).2
    let lift (z : SourcePair (fullRaySector N rows r) (fullRaySector N Pset p)) :
        SourcePair rows Pset :=
      ⟨(⟨z.val.1.val, (Finset.mem_filter.mp z.val.1.property).1⟩,
        ⟨z.val.2.val, (Finset.mem_filter.mp z.val.2.property).1⟩), z.property⟩
    constructor
    · dsimp only [Ds,D]
      exact (hκ (lift x)).trans ((congrArg κ ((hsector x).trans (hsector y).symm)).trans (hκ (lift y)).symm)
    · intro u m n b
      dsimp only [Ds,D]
      exact (hA (lift x) u m n b).trans
        ((congrArg (fun q => A q u m n b) ((hsector x).trans (hsector y).symm)).trans
          (hA (lift y) u m n b).symm)
  obtain ⟨D0⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  obtain ⟨E,hE⟩ := sector_arithmetic_prescribed F (fullRaySector N rows r) (fullRaySector N Pset p) S
    (fun K hK => hrows K (Finset.mem_filter.mp hK).1) s hc Ds hh D0
  refine ⟨E,?_⟩
  intro K P hp
  rw [hE]
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SlotChoices -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def slotChoiceSplit (L : σ→Finset (Ideal Eis)) (T : Finset σ) :
    (∀ i, L i)≃(∀ i : T, L i.val)×(∀ i : {i // i∉T}, L i.val) :=
  Equiv.piEquivPiSubtypeProd (fun i => i∈T) (fun i => L i)

omit [Fintype σ] in
lemma slotChoiceSplit_active (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (i : T) :
    (slotChoiceSplit L T).symm (a,b) i.val=a i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dite_eq_left i.property]

omit [Fintype σ] in
lemma slotChoiceSplit_inactive (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (i : {i // i∉T}) :
    (slotChoiceSplit L T).symm (a,b) i.val=b i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dite_eq_right i.property]

lemma slot_choice_inactive_weight (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (p : ∀ i, L i) :
    (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)=
      ∏ i : {i // i∉T}, (Ideal.absNorm ((slotChoiceSplit L T p).2 i).val:ℂ)⁻¹ := by
  exact Finset.prod_subtype (Finset.univ\T) (fun i => by simp)
    (fun i => (Ideal.absNorm (p i).val:ℂ)⁻¹)

theorem sum_slot_choices (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (H : (∀ i, L i)→ℂ) :
    (∑ p : ∀ i, L i, (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)*H p)=
    ∑ b : ∀ i : {i // i∉T}, L i.val,
      (∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹)*
        ∑ a : ∀ i : T, L i.val, H ((slotChoiceSplit L T).symm (a,b)) := by
  simp_rw [slot_choice_inactive_weight L T]
  rw [← (slotChoiceSplit L T).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

lemma slot_choice_coprime_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (K : Ideal Eis) :
    IsCoprime K (∏ i, ((slotChoiceSplit L T).symm (a,b) i).val) ↔
      IsCoprime K (∏ i : T, (a i).val) ∧ IsCoprime K (∏ i : {i // i∉T}, (b i).val) := by
  simp only [IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [slotChoiceSplit_active] using h i.val
    · intro i
      simpa only [slotChoiceSplit_inactive] using h i.val
  · rintro ⟨ha,hb⟩ i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb ⟨i,hi⟩
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SlotMass -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma inactive_choices_mass (L : σ→Finset (Ideal Eis)) (T : Finset σ) :
    (∑ b : ∀ i : {i // i∉T}, L i.val,
      ‖∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹‖)=
    ∏ i : {i // i∉T}, ∑ P∈L i.val, (Ideal.absNorm P:ℝ)⁻¹ := by
  simp only [norm_prod,norm_inv,Complex.norm_natCast]
  refine (Fintype.prod_sum (fun (i : {i // i∉T}) (P : L i.val) => (Ideal.absNorm P.val:ℝ)⁻¹)).symm.trans ?_
  apply Finset.prod_congr rfl
  intro i hi
  exact Finset.sum_coe_sort (L i.val) (fun P => (Ideal.absNorm P:ℝ)⁻¹)

lemma inactive_choices_mass_bound (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (H : σ→ℝ) (hzero : ∀ i, ∀ P∈L i, P≠0)
    (hH : ∀ i, ∀ P∈L i, (Ideal.absNorm P:ℝ)≤H i) :
    (∑ b : ∀ i : {i // i∉T}, L i.val,
      ‖∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹‖)≤
      ∏ i : {i // i∉T}, 256*(columnDyadicLength (H i.val)+1:ℝ) := by
  rw [inactive_choices_mass]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simpa only [one_div] using finite_inverse_norm_sum (L i.val) (H i.val) (hzero i.val) (hH i.val)

theorem original_inactive_choices_energy {κ : Type*}
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (rows : Finset κ)
    (H : σ→ℝ) (hzero : ∀ i, ∀ P∈L i, P≠0)
    (hH : ∀ i, ∀ P∈L i, (Ideal.absNorm P:ℝ)≤H i)
    (f : (∀ i, L i)→κ→ℂ) (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T}, L i.val,
      (∑ k∈rows, ‖∑ a : ∀ i : T, L i.val, f ((slotChoiceSplit L T).symm (a,b)) k‖^2)≤E) :
    (∑ k∈rows, ‖∑ p : ∀ i, L i,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)*f p k‖^2)≤
    (∏ i : {i // i∉T}, 256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  simp_rw [sum_slot_choices L T]
  apply (weighted_finite_row_energy_uniform Finset.univ rows
    (fun b : ∀ i : {i // i∉T}, L i.val => ∏ i, (Ideal.absNorm (b i).val:ℂ)⁻¹)
    (fun b k => ∑ a : ∀ i : T, L i.val, f ((slotChoiceSplit L T).symm (a,b)) k)
    E (fun b hb => hf b)).trans
  apply mul_le_mul_of_nonneg_right _ hE
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun b hb => norm_nonneg _))
    (inactive_choices_mass_bound L T H hzero hH) 2
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.InactiveBudget -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section

lemma subtype_product_le_full {σ : Type*} [Fintype σ] (p : σ→Prop) [DecidablePred p]
    (H : σ→ℝ) (hH : ∀ i,1≤H i) :
    (∏ i : {i // p i},H i.val)≤∏ i,H i := by
  rw [←Finset.prod_subtype (Finset.univ.filter p) (by simp) H]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
    (fun i _ => (zero_le_one.trans (hH i))) (fun i _ _ => hH i)

theorem harmonic_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤ rmax → (∀ i,1≤H i) →
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  let D := max 1 (256*(2+1/((ε/2)*Real.log 2)))
  have hD : 1≤D := le_max_left _ _
  refine ⟨D^(2*rmax),by positivity,?_⟩
  intro σ _ H hcard hH
  have hp : 0<∏ i,H i := Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hH i))
  have he (i : σ) : 256*(columnDyadicLength (H i)+1:ℝ)≤D*(H i)^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) (H i) (hH i)) (by norm_num : (0:ℝ)≤256)).trans
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans (hH i)) _)
  calc
    _ ≤ (∏ i,D*(H i)^(ε/2))^2 := by
      apply pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => by positivity))
      exact Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => he i)
    _ = D^(2*Fintype.card σ)*(∏ i,H i)^ε := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Real.finsetProd_rpow Finset.univ H (fun i _ => zero_le_one.trans (hH i)),mul_pow,←pow_mul,
        ←Real.rpow_mul_natCast hp.le]
      congr 1
      · congr 1;omega
      · congr 1;norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.mul_le_mul_left 2 hcard)) (Real.rpow_nonneg hp.le _)

theorem inactive_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (T : Finset σ) (H : σ→ℝ),
      Fintype.card σ≤ rmax → (∀ i,1≤H i) →
      (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  obtain ⟨C,hC,hb⟩ := harmonic_product_small_power rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ T H hcard hH
  apply (hb (fun i : {i // i∉T} => H i.val)
    ((Fintype.card_subtype_le _).trans hcard) (fun i => hH i.val)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i.val)))
    (subtype_product_le_full (fun i => i∉T) H hH) hε.le
end
end SevenEighths.InverseReflectedPhase

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Reflection.SourceSelection -/

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CanonicalRowCompletion
noncomputable section

def sourceDependentExtension {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (C : ∀ x, D (f x)) (fallback : ∀ y, D y) (y : Y) : D y :=
  if h : ∃ x, f x=y then h.choose_spec ▸ C h.choose else fallback y

lemma sourceDependentExtension_at {X Y : Type*} {D : Y→Type*}
    (f : X→Y) (hinj : Function.Injective f) (C : ∀ x, D (f x))
    (fallback : ∀ y, D y) (x : X) :
    sourceDependentExtension f C fallback (f x)=C x := by
  have h : ∃ z, f z=f x := ⟨x,rfl⟩
  unfold sourceDependentExtension
  rw [dite_eq_left h]
  have he : h.choose=x := hinj h.choose_spec
  have hcast : ∀ (z x : X) (hf : f z=f x), z=x → (hf ▸ C z)=C x := by
    intro z x hf hx
    subst x
    rfl
  exact hcast _ _ h.choose_spec he

variable {α β γ σ : Type*} [Fintype α] [Fintype β] [Fintype σ]

lemma markedActiveSet_injective (e : α⊕β≃γ) :
    Function.Injective (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2) := by
  intro x y he
  have hh := congrArg (optionalPrimeActive (joinedFiberEquiv e)) he
  dsimp only at hh
  rw [← complete_marked_set,← complete_marked_set,
    optionalPrimeActive_completeActiveSet,optionalPrimeActive_completeActiveSet] at hh
  apply Prod.ext
  · have h := congrArg Finset.toLeft hh
    simpa using h
  · have h := congrArg Finset.toRight hh
    simpa using h

theorem exists_marked_source_selection (e : α⊕β≃γ)
    (D : Finset (γ⊕σ)→Type*) (fallback : ∀ A, D A)
    (C : ∀ B : Finset β, ∀ T : Finset σ, D (markedActiveSet e B T)) :
    ∃ E : ∀ A, D A, ∀ B T, E (markedActiveSet e B T)=C B T := by
  refine ⟨sourceDependentExtension (fun q : Finset β×Finset σ => markedActiveSet e q.1 q.2)
    (fun q => C q.1 q.2) fallback,?_⟩
  intro B T
  exact sourceDependentExtension_at _ (markedActiveSet_injective e) _ _ (B,T)
end
end SevenEighths.InverseReflectedPhase

end OAI

end

