module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part002

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part008

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondCanonicalSplit -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def actualMarkedSecondProfileData {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) (A₁ A₂ : Finset ι) : SecondProfileData ι :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  expansionProfileData p Ψ (m*b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit*d)
    c d z A₁ A₂ x.second

theorem actual_second_split_child_uniform
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (A : Finset ι), A ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon →
      ∀ (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor
      let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
      canonicalMarkedSplit p hp hcop hg F x.second.overlap A Ψ
        (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit*d)
        (secondExpansionQuotient p x.second) c d e k slots lists a W
        (primeProductNorm p x.second.overlap*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪x.second.overlap) *
        secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
          (slots\J) lists a (fun _ => W) X
          (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hchild⟩ := actual_second_canonical_child p hp hcop hg hpr (σ:=σ) x hE
  refine ⟨u,v,?_⟩
  intro F Ψ m k A hA slots lists a W X
  dsimp only
  rw [secondExpansionQuotient_of_subset p x.second hE]
  rw [actual_second_split_fixed_family p hp hcop hg F x.cube.support x.firstCommon
    x.firstDivisor x.second.sourceCommon x.second.divisor x.second.overlap A hCB hD hE hA
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    x.cube.support_pos Ψ m k slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simpa only [actualSecondRawLabel,secondExpansionQuotient_of_subset p x.second hE] using
    hchild F Ψ m k (slots\J) lists a W X

theorem actual_second_separated_pair_canonical
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}}) := by
  obtain ⟨u,v,hsplit⟩ := actual_second_split_child_uniform p hp hcop hg hpr (σ:=σ) x hCB hD hE
  refine ⟨u,v,?_⟩
  intro F Ψ m z A₁ A₂ hA₁ hA₂ slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t
  dsimp only
  have hA (A : Finset ι) (ha : A ⊆ x.cube.support∪x.firstCommon) :
      A∪x.second.sourceCommon ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon :=
    Finset.union_subset_union_left ha
  unfold secondSeparatedPair
  dsimp only [actualMarkedSecondProfileData,expansionProfileData]
  rw [hsplit F (secondRayMinus Ψ z) m x.second.frequency _ (hA A₁ hA₁),
    hsplit F (secondRayPlus Ψ z) m (-x.second.frequency) _ (hA A₂ hA₂)]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondAssignedSource -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def pairedSlotAssignment (J₁ J₂ : Finset σ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : Fin (J₁.card+J₂.card) → ι :=
  Fin.addCases (indexedSlotAssignment J₁ q.1) (indexedSlotAssignment J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

def pairedSlotWeight (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁ q.1)*slotAssignmentWeight J₂ a₂ q.2

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)

def attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0)
    (newAssigned : Fin Jn → ι) : MarkedSecondSource ι Jo Jn where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := newAssigned

omit [DecidableEq ι] in
theorem attachSecondSlots_injective {Jo Jn : ℕ} :
    Function.Injective (fun q : MarkedSecondSource ι Jo 0 × (Fin Jn → ι) => attachSecondSlots q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · apply MarkedSecondSource.ext
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.cube) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstCommon) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstDivisor) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.second) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.quotient) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.oldAssigned) h
    · funext i; exact Fin.elim0 i
  · exact congrArg MarkedSecondSource.newAssigned h

def attachPairedSlots {Jo : ℕ} (J₁ J₂ : Finset σ)
    (q : MarkedSecondSource ι Jo 0 × ((∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))) :
    MarkedSecondSource ι Jo (J₁.card+J₂.card) :=
  attachSecondSlots q.1 (pairedSlotAssignment J₁ J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPairedSlots_injective {Jo : ℕ} (J₁ J₂ : Finset σ) :
    Function.Injective (attachPairedSlots (ι:=ι) (Jo:=Jo) J₁ J₂) := by
  intro q r h
  have he := @attachSecondSlots_injective ι Jo (J₁.card+J₂.card)
    (q.1,pairedSlotAssignment J₁ J₂ q.2) (r.1,pairedSlotAssignment J₁ J₂ r.2) h
  exact Prod.ext (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.2) he))

def assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    Finset (MarkedSecondSource ι Jo (J₁.card+J₂.card)) :=
  ((source ×ˢ ((J₁.pi (fun i => L₁ i)) ×ˢ (J₂.pi (fun i => L₂ i)))).filter
    (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q.2 j ∈ q.1.second.sourceCommon∪q.1.second.overlap)).image
      (attachPairedSlots J₁ J₂)

theorem mem_assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) :
    x ∈ assignedSecondSource source J₁ J₂ L₁ L₂ ↔
      ∃ y ∈ source, ∃ q₁ ∈ J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap)),
      ∃ q₂ ∈ J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap)),
        attachPairedSlots J₁ J₂ (y,(q₁,q₂)) = x := by
  constructor
  · intro hx
    obtain ⟨⟨y,q₁,q₂⟩,hmem,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hy,hq⟩ := Finset.mem_product.mp hmem
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine ⟨y,hy,q₁,Finset.mem_pi.mpr ?_,q₂,Finset.mem_pi.mpr ?_,rfl⟩
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · rintro ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(y,(q₁,q₂)),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,Finset.mem_product.mpr ⟨?_,?_⟩⟩,?_⟩,rfl⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q₁ hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q₂ hq₂ k)).2

theorem assignedSecondSource_conditions (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    ActualSecondSourceConditions p (assignedSecondSource source J₁ J₂ L₁ L₂) := by
  have hmem : ∀ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      ∃ y ∈ source, ∃ q, attachPairedSlots J₁ J₂ (y,q)=x ∧
        ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ y.second.sourceCommon∪y.second.overlap := by
    intro x hx
    obtain ⟨⟨y,q⟩,hmem,he⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hmem
    exact ⟨y,(Finset.mem_product.mp hmem).1,q,he,hq⟩
  constructor
  all_goals
    intro x hx
    obtain ⟨y,hy,q,rfl,hq⟩ := hmem x hx
  · exact hs.admissible y hy
  · exact hs.common_disjoint y hy
  · exact hs.first_divisor y hy
  · exact hs.second_divisor y hy
  · exact hs.old_support y hy
  · exact hq
  · exact hs.quotient_nonzero y hy

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)

def eraseSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : MarkedSecondSource ι Jo 0 where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0) (a : Fin Jn → ι) :
    eraseSecondSlots (attachSecondSlots x a) = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def assignedSecondCoefficient {Jo : ℕ} (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi => x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi => x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2

theorem assignedSecondSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card) → ℂ) :
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂, F x =
      ∑ y ∈ source, ∑ q ∈
        (J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap))) ×ˢ
        (J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap))),
          F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [assignedSecondSource,Finset.sum_image (fun q _ r _ h => attachPairedSlots_injective J₁ J₂ h),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem assignedSecondSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (w P : MarkedSecondSource ι Jo 0 → ℂ) :
    (∑ y ∈ source, w y * (star (primeMark J₁ L₁ a₁ (y.second.sourceCommon∪y.second.overlap)) *
      primeMark J₂ L₂ a₂ (y.second.sourceCommon∪y.second.overlap)) * P y) =
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x) * P (eraseSecondSlots x) := by
  rw [assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

theorem assignedSecondCoefficient_norm_le_one {Jo : ℕ}
    (source : Finset (MarkedSecondSource ι Jo 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card))
    (hx : x ∈ assignedSecondSource source J₁ J₂ L₁ L₂) :
    ‖assignedSecondCoefficient J₁ J₂ a₁ a₂ x‖ ≤ 1 := by
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  rw [assignedSecondCoefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ (q₁,q₂)
    (Finset.mem_product.mpr ⟨hq₁,hq₂⟩) ha₁ ha₂

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondMarkedEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondChild_erase {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

theorem actualSecondChild_neg_frequency {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  simp only [actualSecondChild,secondChild,originalSecondTuple,markedSecondOriginal,cubeSecondSource,
    secondUnitFrequency_neg,mul_neg]

include hp hcop in
theorem actual_second_marked_weighted_count
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  let S := assignedSecondSource source J₁ J₂ L₁ L₂
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card) =>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hs' : ActualSecondSourceConditions p S := assignedSecondSource_conditions p source hs J₁ J₂ L₁ L₂
  have herase : ∀ x ∈ S, eraseSecondSlots x ∈ source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  have hw' : ∀ x ∈ S, ‖w' x‖ ≤ 1 := by
    intro x hx
    rw [show w' x = w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ x hx)
  have hc' : ∀ x ∈ S, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := assignedSecondSource_sum_marks source J₁ J₂ L₁ L₂ a₁ a₂ w
    (fun x => F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSquarefree -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourcePrime sourceIdeal_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem sourceIdeal_squarefree (S : Finset ι) : Squarefree (sourceIdeal p S) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (sourcePrime p i).property.squarefree

include hcop in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_coprime_of_disjoint (S T : Finset ι) (hST : Disjoint S T) :
    IsCoprime (sourceIdeal p S) (sourceIdeal p T) := by
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (fun he => Finset.disjoint_left.mp hST hi (he.symm ▸ hj))

omit [DecidableEq ι] in
lemma prime_span_coprime_of_not_mem (i : ι) (c : Eis) (hc : c ∉ Ideal.span {p i}) :
    IsCoprime (Ideal.span {p i}) (Ideal.span {c} : Ideal Eis) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he := (inferInstance : (Ideal.span {p i}).IsMaximal).eq_of_le hne le_sup_left
  apply hc
  rw [he]
  exact (show Ideal.span {c} ≤ (Ideal.span {p i} : Ideal Eis) ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (by simp))

omit [DecidableEq ι] in
theorem sourceIdeal_coprime_of_not_mem (S : Finset ι) (c : Eis)
    (hc : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (sourceIdeal p S) (Ideal.span {c} : Ideal Eis) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact IsCoprime.prod_left (fun i hi => prime_span_coprime_of_not_mem p i c (hc i hi))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem jLabel_span_dvd_source (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {jLabel p B v ε₁ ε₂} : Ideal Eis) ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i^bit (retained (parity (v i)) (ε₁ i) (ε₂ i))) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases retained (parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit]

omit [DecidableEq ι] in
theorem secondInputCoefficient_zero_of_label_mem (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S) (hc : c ∈ Ideal.span {p i}) :
    secondInputCoefficient p hg Ψ m c d H S = 0 := by
  have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
  have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
  simp only [secondInputCoefficient,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondPreColumn_zero_of_mask_label_mem (Ψ : Eis →* ℂ) (m c d e k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hc : m*c ∈ Ideal.span {p i}) : secondPreColumn p hp hcop hg Ψ m c d e k H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hc with hm|hc
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m = 0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondPreColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
    have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
    simp only [secondPreColumn,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondSignedSourceWeight_nonzero_masks
    (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondSignedSourceWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (sourceIdeal p x.sourceCommon) (Ideal.span {c}) ∧
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.sourceCommon * Ideal.span {c}) := by
  constructor
  · apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    have hz := secondInputCoefficient_zero_of_label_mem p hg Ψ m c d (fun _ => 1) x.sourceCommon i hi hc
    apply hw
    simp only [secondSignedSourceWeight,hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      Complex.ofReal_zero,zero_mul]
  · change IsCoprime (sourceIdeal p x.overlap) (Ideal.span {∏ i ∈ x.sourceCommon,p i} * Ideal.span {c})
    rw [Ideal.span_singleton_mul_span_singleton]
    apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
    let r := secondExpansionQuotient p x
    have her : e*r = ∏ j ∈ x.sourceCommon,p j := by
      dsimp only [r]
      rw [secondExpansionQuotient_of_subset p x hE]
      exact (secondMaskQuotient_spec p _ _ hE).symm
    have hmc : (m*(e*r))*c ∈ Ideal.span {p i} := by
      rw [her,mul_assoc]
      exact Ideal.mul_mem_left _ m hc
    have hz := secondPreColumn_zero_of_mask_label_mem p hp hcop hg (secondRayPlus Ψ z)
      (m*(e*r)) c d e (-x.frequency) (fun _ => 1) x.overlap i hi hmc
    dsimp only [e,r] at hz
    apply hw
    simp only [secondSignedSourceWeight,secondCommonWeight,hz,mul_zero]

def actualSecondSignedWeight {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ℂ :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  secondSignedSourceWeight p hp hcop hg Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit*d) c d z x.second

theorem actualSecondSignedWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ‖actualSecondSignedWeight p hp hcop hg Ψ m z x‖ ≤ 1 :=
  secondSignedSourceWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ _ _ _ z x.second

theorem actual_second_nonzero_weight_squarefree
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m z x ≠ 0) (u v : Eisˣ) :
    Squarefree (actualSecondChild p u v x).2.1 := by
  let J : Ideal Eis := Ideal.span {(jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}
  let C := sourceIdeal p x.firstCommon
  let E := sourceIdeal p x.second.divisor
  let G := sourceIdeal p x.second.sourceCommon
  let V := sourceIdeal p x.second.overlap
  have hj : J ∣ sourceIdeal p x.cube.support := jLabel_span_dvd_source p _ _ _ _
  have hJ : Squarefree J := (sourceIdeal_squarefree p hcop x.cube.support).squarefree_of_dvd hj
  have hC : Squarefree C := sourceIdeal_squarefree p hcop _
  have hG : Squarefree G := sourceIdeal_squarefree p hcop _
  have hV : Squarefree V := sourceIdeal_squarefree p hcop _
  have hJC : IsCoprime J C :=
    (sourceIdeal_coprime_of_disjoint p hcop x.cube.support x.firstCommon hCB.symm).of_isCoprime_of_dvd_left hj
  have hdg : E ∣ G := sourceIdeal_dvd p _ _ hE
  have hcspan : Ideal.span {((∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)} = C*J :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  obtain ⟨hgmask,hvmask⟩ := secondSignedSourceWeight_nonzero_masks p hp hcop hg Ψ _ _ _ z x.second hE hw
  rw [hcspan] at hgmask hvmask
  change IsCoprime G (C*J) at hgmask
  change IsCoprime V (G*(C*J)) at hvmask
  have heJC : IsCoprime E (J*C) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : J*C*E ∣ G*(C*J) := by
    obtain ⟨r,hr⟩ := hdg
    refine ⟨r,?_⟩
    rw [hr]
    ring
  have hvJCE := hvmask.of_isCoprime_of_dvd_right hdiv
  change Squarefree (J*C*E*V)
  exact squarefree_mul_iff.mpr ⟨hvJCE.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨heJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime,hJ,hC⟩,hG.squarefree_of_dvd hdg⟩,hV⟩

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondPuncture -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem rowCoprimeMask_radical_generator (S : Finset ι) (a : Eis) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a =
      rowCoprimeMask (fun i => Ideal.span {p i}) S
        (ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical) := by
  have he (i : ι) : a ∈ Ideal.span {p i} ↔
      ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ∈ Ideal.span {p i} := by
    rw [←Ideal.span_singleton_le_iff_mem,←Ideal.span_singleton_le_iff_mem,
      ConcretePrimeRowBridge.span_idealGenerator]
    exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.symm
  simp only [rowCoprimeMask,he]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_radical_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ
        (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical) f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn,
    ←rowCoprimeMask_radical_generator p]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_le_radical_primeProduct (B : Finset ι) (v : ι → ℕ) :
    sourceIdeal p B ≤ (Ideal.span {primeProduct p B v} : Ideal Eis).radical := by
  simp only [sourceIdeal,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  induction B using Finset.induction_on with
  | empty => simp
  | @insert i B hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Ideal.radical_mul]
    apply le_inf
    · apply Ideal.mul_le_left.trans
      by_cases hv : v i = 0
      · rw [hv,pow_zero,Ideal.one_eq_top]
        exact le_trans le_top Ideal.le_radical
      · rw [Ideal.radical_pow _ hv]
        exact Ideal.le_radical
    · exact Ideal.mul_le_right.trans ih

theorem actual_second_q0_radical_norm (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0.radical : ℝ) ≤
      primeProductNorm p x.cube.support := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le (sourceIdeal_le_radical_primeProduct p x.cube.support
    (fun i => b0Exponent (x.cube.leftExponent i+x.cube.rightExponent i) (x.cube.leftBit i) (x.cube.rightBit i)))
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (sourceIdeal_ne_zero p hp x.cube.support))) hd
  change (Ideal.absNorm (Ideal.span {(b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}).radical : ℝ) ≤ _
  have he : (Ideal.absNorm (sourceIdeal p x.cube.support) : ℝ) = primeProductNorm p x.cube.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ x.cube.support,p i)).symm
  rw [←he]
  exact_mod_cast hb

def actualSecondRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {actualSecondPuncture m γ}).radical

theorem secondCanonicalPolynomial_radical_puncture
    (F : Finset ι) (Ψ : InverseSecondFibers.OuterTriple → Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : InverseSecondFibers.OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondPuncture m) slots lists a W X c =
      secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondRadicalPuncture m) slots lists a W X c :=
  finiteCanonicalMarkedRow_radical_puncture p hp hcop hg F (Ψ c.1) _ _ _ slots lists a (W c.1) X

theorem radical_product_norm_le (I J B R : Ideal Eis) (hI : I ≠ 0) (hB : B ≠ 0)
    (hR : R ≠ 0) (hBJ : B ≤ J.radical) :
    (Ideal.absNorm (I*J*R).radical : ℝ) ≤
      (Ideal.absNorm I.radical : ℝ)*Ideal.absNorm B*Ideal.absNorm R := by
  have hi : I.radical ≠ 0 := by
    intro he
    apply hI
    exact le_antisymm (he ▸ Ideal.le_radical) bot_le
  have hle : I.radical*B*R ≤ (I*J*R).radical := by
    rw [Ideal.radical_mul,Ideal.radical_mul]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact Ideal.mul_le_left.trans Ideal.mul_le_left
    · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans hBJ
    · exact Ideal.mul_le_right.trans Ideal.le_radical
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (mul_ne_zero (mul_ne_zero hi hB) hR))) (Ideal.absNorm_dvd_absNorm_of_le hle)
  simpa only [map_mul,Nat.cast_mul] using (show (Ideal.absNorm (I*J*R).radical : ℝ) ≤
    Ideal.absNorm (I.radical*B*R) from by exact_mod_cast hb)

include hp in

theorem actual_second_radical_puncture_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {(b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn x.cube.support,←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_le_radical_primeProduct p _ _)

def actualSecondInheritedPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ

def actualSecondInheritedRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondRadicalPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ

include hp in

theorem actual_second_inherited_puncture_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (primeProductNorm_pos p hp _).le) (primeProductNorm_pos p hp _).le

include hp in

theorem actualSecondTriples_q0_radical_bound
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn)) (B : ℝ)
    (hB : ∀ x ∈ source, primeProductNorm p x.cube.support ≤ B) :
    ∀ γ ∈ actualSecondTriples p u v source, (Ideal.absNorm γ.q0.radical : ℝ) ≤ B := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact (actual_second_q0_radical_norm p hp x u v).trans (hB x hx)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondParentLists -/

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def actualSecondRawInheritedPuncture {Jo Jn : ℕ} (m : O) (x : MarkedSecondSource ι Jo Jn) : O :=
  ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*b0Label p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    secondExpansionQuotient p x.second

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_parent_deleted_prime_killed {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (_hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (m : O) (i : ι)
    (hi : i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient) :
    actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x∈Ideal.span {p i} := by
  rcases hi with hi|hi
  · have hv : ∀ j∈x.cube.support,0<x.cube.leftExponent j+x.cube.rightExponent j := by
      intro j hj
      simp only [CubeCoordinates.support,Finset.mem_union,Finsupp.mem_support_iff] at hj
      omega
    have hk := actual_second_extracted_support_killed p
      x.cube.support x.firstCommon x.second.sourceCommon x.second.divisor x.second.overlap
      (x.cube.support∪x.firstCommon) hE Finset.subset_union_left
      (fun j=>x.cube.leftExponent j+x.cube.rightExponent j) x.cube.leftBit x.cube.rightBit hv
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) i hi
    simpa only [actualSecondRawInheritedPuncture,actualSecondRawLabel,
      secondExpansionQuotient_of_subset p x.second hE] using hk
  · have hq : ConcretePrimeRowBridge.idealGenerator x.quotient∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp hi)
      have hmem : ConcretePrimeRowBridge.idealGenerator x.quotient∈
          Ideal.span {ConcretePrimeRowBridge.idealGenerator x.quotient} := Ideal.subset_span (by simp)
      simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hmem
    unfold actualSecondRawInheritedPuncture
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq)))

theorem actual_second_parent_lists_restore {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (deleted : Finset ι)
    (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : O→*ℂ) (m k : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots (fun j=>lists j\deleted) a W X =
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots lists a W X := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  exact fun i hi=>actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)

theorem actual_second_parent_lists_restore_quotient {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (D : Finset ι)
    (hq : x.quotient=sourceIdeal p D) (deleted : Finset ι)
    (hdeleted : deleted⊆(x.cube.support∪x.firstCommon)∪D)
    (pool : Finset ι) (Ψ : O→*ℂ) (m k : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots (fun j=>lists j\deleted) a W X =
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots lists a W X := by
  apply actual_second_parent_lists_restore p hp hcop hg x hb hE deleted
  intro i hi
  rcases Finset.mem_union.mp (hdeleted hi) with hi|hi
  · exact Or.inl hi
  · right
    rw [hq]
    exact InverseInitialArithmetic.source_prime_dvd p D i hi

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondPunctureBudget -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_eq_div (E G : Finset ι) (hE : E ⊆ G) :
    primeProductNorm p (G\E) = primeProductNorm p G/primeProductNorm p E := by
  have he : primeProductNorm p G = primeProductNorm p E*primeProductNorm p (G\E) := by
    rw [←primeProductNorm_union p E (G\E) Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hE]
  rw [he]
  field_simp [(primeProductNorm_pos p hp E).ne']

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_power_bound (E G : Finset ι) (hE : E ⊆ G)
    (Z g theta eta : ℝ) (hZ : 0 < Z)
    (hg : primeProductNorm p G ≤ Z^(g+eta))
    (hd : Z^(theta-eta) ≤ primeProductNorm p E) :
    primeProductNorm p (G\E) ≤ Z^(g-theta+2*eta) := by
  rw [second_residual_norm_eq_div p hp E G hE]
  calc
    _ ≤ Z^(g+eta)/Z^(theta-eta) := div_le_div₀ (Real.rpow_pos_of_pos hZ _).le hg
      (Real.rpow_pos_of_pos hZ _) hd
    _ = Z^((g+eta)-(theta-eta)) := (Real.rpow_sub hZ _ _).symm
    _ = _ := by congr 1; ring

include hp in

theorem actual_second_puncture_power_budget
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  apply (actual_second_inherited_puncture_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hb0 := (primeProductNorm_pos p hp x.cube.support).le
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

def actualSecondSurvivingSource {Jo : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (source : Finset (MarkedSecondSource ι Jo 0)) : Finset (MarkedSecondSource ι Jo 0) :=
  source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ m z x ≠ 0)

theorem assignedSecondSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S ⊆ T)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSecondSource S J₁ J₂ L₁ L₂ ⊆ assignedSecondSource T J₁ J₂ L₁ L₂ := by
  intro x hx
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,he⟩ := (mem_assignedSecondSource S J₁ J₂ L₁ L₂ x).mp hx
  exact (mem_assignedSecondSource T J₁ J₂ L₁ L₂ x).mpr ⟨y,hST hy,q₁,hq₁,q₂,hq₂,he⟩

theorem actualSecondTriples_mono {Jo Jn : ℕ} (u v : Eisˣ)
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (hST : S ⊆ T) :
    actualSecondTriples p u v S ⊆ actualSecondTriples p u v T :=
  Finset.image_subset_image hST

theorem actual_second_supported_marked_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := actualSecondSurvivingSource p hp hcop hg Ψ m z source
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ m z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ m z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ m z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ m z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondInheritedEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_marked_energy_varying_puncture
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
        (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondMultiplier {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor

omit [DecidableEq ι] in
theorem actualSecondMultiplier_ne_zero {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    actualSecondMultiplier p x ≠ 0 := by
  apply mul_ne_zero
  · exact primeSubsetGenerator_ne_zero _ _
  · exact primeSubsetGenerator_ne_zero _ _

include hp in

theorem actual_second_row_norm_sq
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    ‖eisEmbedding (actualSecondChild p u v x).2.2‖^2 =
      ‖eisEmbedding (actualSecondMultiplier p x*x.second.frequency)‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.firstDivisor)*
      primaryGenerator (sourceIdeal p x.second.divisor)*secondUnitFrequency u v x.second.frequency)‖^2 = _
  rw [sourceIdeal_gen p hp hpr,sourceIdeal_gen p hp hpr]
  simp only [map_mul,norm_mul,mul_pow,secondUnitFrequency_norm,actualSecondMultiplier,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in

theorem actual_second_row_ball
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) (R : ℝ) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R ↔
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x),
    mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,actual_second_row_norm_sq p hp hpr]

omit [DecidableEq ι] in
theorem actual_second_row_radius_one
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (R : ℝ)
    (hsource : source.Nonempty)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) : 1 ≤ R := by
  obtain ⟨x,hx⟩ := hsource
  by_contra hR
  have he := nonzeroChildFrequencyBall_empty _ (actualSecondMultiplier_ne_zero p x) R (lt_of_not_ge hR)
  simpa [he] using hrows x hx

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSectorAssembly -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def SecondPairCanonicalAt {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) : Prop :=
∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}})

theorem exists_second_uniform_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ x ∈ source, SecondPairCanonicalAt (σ:=σ) p hp hcop hg x (sector x).1 (sector x).2 := by
  have he (x : {x // x ∈ source}) :=
    actual_second_separated_pair_canonical p hp hcop hg hpr (σ:=σ) x.val
      (hs.common_disjoint x.val x.property) (hs.first_divisor x.val x.property)
      (hs.second_divisor x.val x.property)
  choose u v hu using he
  let sector := fun x => if hx : x ∈ source then (u ⟨x,hx⟩,v ⟨x,hx⟩) else (1,1)
  refine ⟨sector,?_⟩
  intro x hx
  simpa only [sector,dite_eq_left hx,SecondPairCanonicalAt] using hu ⟨x,hx⟩

def secondSourceSector {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (uv : Eisˣ × Eisˣ) :
    Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => sector x = uv)

omit [DecidableEq ι] in
theorem secondSourceSector_partition {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (H : MarkedSecondSource ι Jo Jn → ℂ) :
    ∑ x ∈ source,H x = ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,H x :=
  (Finset.sum_fiberwise source sector H).symm

theorem second_unit_sector_card : Fintype.card (Eisˣ × Eisˣ) = 36 := by
  have hc : Fintype.card Eisˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  rw [Fintype.card_prod,hc]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondModeCanonical -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondInheritedProfile {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) : SecondProfileData ι :=
  actualMarkedSecondProfileData p x Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅

def secondModeLeft (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : SecondChild → ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) X

def secondModeRight (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) (c : SecondChild) : ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) X
    (c.1,c.2.1,-c.2.2)

def secondModeOuter {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2)
    (secondRelativeLog (secondActualNorms p (secondInheritedProfile p x Ψ m z) ∅ ∅) G E V B X)

def secondModeBranch {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondModeOuter p x Ψ m z G E V B X t *
    (star (primeMark J₁ lists₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
      primeMark J₂ lists₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
    star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
    secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x)

theorem second_inherited_mode_canonical {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (hx : SecondPairCanonicalAt (σ:=σ) p hp hcop hg x u v)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) :
    secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t =
    ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t := by
  have he := hx pool Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅
    (Finset.empty_subset _) (Finset.empty_subset _) slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t
  dsimp only at he
  have hq : (actualSecondChild p u v x).1.quotient = x.quotient := rfl
  simpa only [secondInheritedProfile,secondModeBranch,secondModeOuter,secondModeLeft,secondModeRight,
    secondCanonicalPolynomial,actualSecondInheritedPuncture,actualSecondChild_neg_frequency,
    Finset.empty_union,Finset.mul_sum,mul_assoc,hq] using he

theorem actual_second_modes_common_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondModeEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_mode_branch_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  let phase := fun x => w x * secondModeOuter p x Ψ m z G E V B X t
  have hphase : ∀ x ∈ source,‖phase x‖ ≤ 1 := by
    intro x hx
    simpa only [phase,norm_mul,secondModeOuter,secondOuterPhase_norm,mul_one] using hw x hx
  have hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
    intro x hx
    exact ⟨hlabels x hx,(actual_second_row_ball p hp hpr x u v R).mp (hrows x hx)⟩
  have he := actual_second_supported_marked_energy_varying_puncture p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*ConcretePrimeRowBridge.idealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [secondModeBranch,phase]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondModeIntegral -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem second_geometric_energy_of_bound (K : ℕ) (labels : Finset (Ideal Eis))
    (rows : Finset Eis) (Γ : Finset OuterTriple) (F G : SecondChild → ℂ)
    (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ Γ,secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ Γ,secondLabelEnergy K labels rows G γ ≤ E) :
    Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ) (hP : ∀ γ ∈ Γ,secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  calc
    _ ≤ Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) *
        Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

theorem actual_second_mode_integral_of_child_bound
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1)
    (gwin : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),
      ∀ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),
      ∀ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),fullProfileDensity gwin b₁ b₂ b₃ t *
      ∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t‖ ≤
      (A * ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ) *
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*
        ‖fullProfileDensity gwin b₁ b₂ b₃ t‖ := by
  let Γ := actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂)
  let mass := ∑ γ ∈ Γ,tripleDivisorWeight K γ
  let H := fun t : Frequency × (Fin 6 → ℝ) => tripleHeight J t.1*coordinateHeight J t.2
  have hH (t : Frequency × (Fin 6 → ℝ)) : 0 ≤ H t := by
    unfold H tripleHeight coordinateHeight
    positivity
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t‖ ≤ (A*H t)*mass := by
    apply (actual_second_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t
      labels hlabels hrows K ho hJ₁ hJ₂ w hw).trans
    exact second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
      Γ _ _ (A*H t) (mul_nonneg hA (hH t)) (hright t) (hleft t)
  have hi := (fullProfileDensity_weighted_integrable gwin b₁ b₂ b₃ J).const_mul (A*mass)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),(A*mass)*(tripleHeight J t.1*coordinateHeight J t.2*
        ‖fullProfileDensity gwin b₁ b₂ b₃ t‖) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by dsimp only [H]; ring)
    _ = _ := by rw [integral_const_mul]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondModeParentLists -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseInitialArithmetic CompletedGauss InverseSecondFibers JointLogSeparation
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
theorem actual_second_canonical_label_span
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Oˣ) :
    Ideal.span {actualSecondRawLabel p x}=
      Ideal.span {primaryGenerator (actualSecondChild p u v x).2.1} := by
  obtain ⟨u₀,v₀,hl,hv⟩ := actual_second_generator_sectors p hp hpr x
  rw [hl,←Ideal.span_singleton_mul_span_singleton]
  simp only [Ideal.span_singleton_eq_top.mpr (Units.isUnit u₀),Ideal.top_mul]
  rfl

theorem secondCanonicalPolynomial_parent_lists_restore
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (u v : Oˣ)
    (deleted : Finset ι)
    (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : OuterTriple→O→*ℂ) (m : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : OuterTriple→ℝ→ℂ) (X : ℝ) (k : O) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots (fun j=>lists j\deleted) a W X ((actualSecondChild p u v x).1,
        (actualSecondChild p u v x).2.1,k) =
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots lists a W X ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,k) := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  intro i hi
  have hk := actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)
  have he : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}=
      Ideal.span {(actualSecondInheritedPuncture m (actualSecondChild p u v x).1*
        primaryGenerator (actualSecondChild p u v x).2.1)} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      actual_second_canonical_label_span p hp hpr x u v]
    congr 1
    exact actual_second_puncture_span p hp hpr x hE u v
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient)
  have hk' : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}≤Ideal.span {p i} :=
    Ideal.span_le.mpr (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl; exact hk)
  rw [he] at hk'
  exact hk' (Ideal.subset_span (by simp))

theorem secondModeBranch_parent_lists_restore
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (u v : Oˣ)
    (deleted₁ deleted₂ : Finset ι)
    (hd₁ : ∀ i∈deleted₁,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (hd₂ : ∀ i∈deleted₂,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (G E V B X : ℝ) (t : Frequency×(Fin 6→ℝ)) :
    secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂
      (fun i=>lists₁ i\deleted₁) (fun i=>lists₂ i\deleted₂) a₁ a₂ ω₁ ω₂ G E V B X t =
    secondModeOuter p x Ψ m z G E V B X t *
      (star (primeMark J₁ (fun i=>lists₁ i\deleted₁) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (fun i=>lists₂ i\deleted₂) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
      secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x) := by
  unfold secondModeBranch secondModeLeft secondModeRight
  rw [secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₁ hd₁,
    secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₂ hd₂]

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondTripleBounds -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)

include hp in

theorem actual_second_common_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z g theta eta : ℝ) (hZ : 1 < Z)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    -2*eta ≤ g-theta := by
  have hh : Z^(theta-eta) ≤ Z^(g+eta) :=
    hD.trans ((primeProductNorm_mono p hp hE).trans hG)
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

include hp in

theorem actual_second_label_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Z ell j eta : ℝ) (hZ : 1 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    j ≤ 2*ell+3*eta := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le h1 h2).1
  have hh := hJ.trans hb
  rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le] at hh
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at hh'
  linarith

variable [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_q0_power_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (Z ell R j eta : ℝ) (hZ : 0 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hactive : primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos hZ _).le h1 h2).2.2
  have ha : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤
      Z^((R+eta)/2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_pos_of_pos hZ _).le).mp
    rw [←Real.rpow_mul_natCast hZ.le]
    norm_num
    simpa only [primeProductNorm,map_prod,norm_prod] using hactive
  change (Ideal.absNorm (Ideal.span {(b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}) : ℝ) ≤ _
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  apply hb.trans
  calc
    _ ≤ (Z^(ell+eta)*Z^((R+eta)/2))/Z^(j-eta) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha (by positivity))
        (Real.rpow_pos_of_pos hZ _) hJ
    _ = Z^((ell+eta)+(R+eta)/2-(j-eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_sub hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondActualMass -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzero_ideal_norm_one (I : Ideal Eis) (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_normalized_mass_source_bounds (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      0 < B → 0 < T → 0 < R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro Γ B T R hB hT hR hz hn
  rcases Γ.eq_empty_or_nonempty with he|⟨γ,hγ⟩
  · subst Γ
    simp only [Finset.sum_empty,mul_zero]
    positivity
  · obtain ⟨hq,ht,hr⟩ := hz γ hγ
    obtain ⟨hqb,htb,hrb⟩ := hn γ hγ
    exact hb Γ B T R ((nonzero_ideal_norm_one _ hq).trans hqb)
      ((nonzero_ideal_norm_one _ ht).trans htb) ((nonzero_ideal_norm_one _ hr).trans hrb) hz hn

theorem actual_second_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      Z^(-(ell+R/2-j+t+g-theta+11*eta/2)) *
        (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*ε) := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass_source_bounds K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hz : ∀ γ ∈ actualSecondTriples p u v source,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0 := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    exact (actualSecondChild_nonzero p hp u v x (ht x hx)).2
  have hn : ∀ γ ∈ actualSecondTriples p u v source,
      (Ideal.absNorm γ.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ Z^(t+eta) ∧
      (Ideal.absNorm γ.residual : ℝ) ≤ Z^(g-theta+2*eta) := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    refine ⟨actual_second_q0_power_bound p hp x u v Z ell R j eta hZ
      (h1 x hx) (h2 x hx) (ha x hx) (hJ x hx),hT x hx,?_⟩
    have hr := second_residual_norm_power_bound p hp _ _ (hE x hx) Z g theta eta hZ (hG x hx) (hD x hx)
    change (Ideal.absNorm (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) : ℝ) ≤ _
    simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hr
  have hm := hb (actualSecondTriples p u v source)
    (Z^(ell+R/2-j+5*eta/2)) (Z^(t+eta)) (Z^(g-theta+2*eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hz hn
  have he : Z^(ell+R/2-j+5*eta/2)*Z^(t+eta)*Z^(g-theta+2*eta) =
      Z^(ell+R/2-j+t+g-theta+11*eta/2) := by
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
    congr 1
    ring
  rw [he,←Real.rpow_mul hZ.le,←Real.rpow_neg hZ.le] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondAdmissible -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_inherited_puncture_ne_zero
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    actualSecondInheritedPuncture m (actualSecondChild p u v x).1 ≠ 0 := by
  change ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*
    primaryGenerator (Ideal.span {(b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}))*
    primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) ≠ 0
  rw [show primaryGenerator (Ideal.span {(b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht))
    (primeProduct_ne_zero p hp _ _)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

lemma radicalGenerator_ne_zero (a : Eis) (ha : a ≠ 0) :
    ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  intro hz
  apply Ideal.span_singleton_eq_bot.not.mpr ha
  apply le_antisymm _ bot_le
  exact (Ideal.le_radical : (Ideal.span {a} : Ideal Eis) ≤ (Ideal.span {a}).radical).trans (le_of_eq hz)

def actualSecondPunctureWidth (Z : ℝ) (m : Eis) (γ : OuterTriple) : ℝ :=
  Real.logb Z (‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2)

include hp in
theorem actual_second_puncture_width_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_budget p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ hB hT hG hD

include hp in

theorem actual_second_child_margins
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_bound p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ hB hT hG hD
  unfold decrease
  linarith

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_row_decrease
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z M ell A t g theta V j eta d : ℝ) (hZ : 1 < Z)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hterminal : d ≤ ell+V) (heta : eta ≤ d/16)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    3*d/2 ≤ M-childM M ell A t g theta V j eta :=
  child_row_decrease hA ht (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hterminal heta

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondOriginalMass -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_second_original_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*(1+ε)) := by
  obtain ⟨C,hC,hb⟩ := actual_second_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hm := hb p hp source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  let c := ell+R/2-j+t+g-theta+11*eta/2
  calc
    _ = Z^c * (Z^(-c)*(∑ γ∈actualSecondTriples p u v source,tripleDivisorWeight K γ)) := by
      rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _ ≤ Z^c*(C*Z^(c*ε)) := mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hZ _).le
    _ = _ := by
      rw [mul_left_comm,←Real.rpow_add hZ]
      congr 2
      dsimp only [c]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_radical_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {(b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _))
    (sourceIdeal_ne_zero p hp _) Ideal.le_radical

include hp in

theorem actual_second_inherited_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_q0_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg _)) (primeProductNorm_pos p hp _).le

include hp in

theorem actual_second_q0_cube_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (B : ℝ) (hB : 0 ≤ B)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ B := by
  change (Ideal.absNorm (Ideal.span {(b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)}) : ℝ) ≤ B
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  exact (cube_label_norm_bounds p hp _ _ _ _ _ x.cube.support_pos B hB h1 h2).2.1

include hp in
theorem actual_second_puncture_power_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  have hb := actual_second_q0_cube_bound p hp x u v _ (Real.rpow_pos_of_pos hZ _).le h1 h2
  apply (actual_second_inherited_puncture_q0_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

include hp in
theorem actual_second_puncture_width_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_from_cubes p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ h1 h2 hT hG hD

include hp in

theorem actual_second_child_margins_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_from_cubes p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ h1 h2 hT hG hD
  unfold decrease
  linarith

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondVaryingLists -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def varyingAssignedGate {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : Prop :=
  (∀ i hi,x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))∈L₁ (eraseSecondSlots x) i) ∧
  (∀ i hi,x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))∈L₂ (eraseSecondSlots x) i)

omit [DecidableEq ι] in
lemma varyingAssignedGate_attach {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i∈J₁,ι)×(∀ i∈J₂,ι)) :
    varyingAssignedGate J₁ J₂ L₁ L₂ (attachPairedSlots J₁ J₂ (x,q)) ↔
      q.1∈J₁.pi (L₁ x) ∧ q.2∈J₂.pi (L₂ x) := by
  simp only [varyingAssignedGate,attachPairedSlots,erase_attachSecondSlots]
  simp only [attachSecondSlots,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,Finset.mem_pi]

def varyingAssignedSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :=
  (assignedSecondSource source J₁ J₂ base₁ base₂).filter (varyingAssignedGate J₁ J₂ L₁ L₂)

theorem varyingAssignedSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S⊆T)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :
    varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂⊆
      varyingAssignedSource T J₁ J₂ base₁ base₂ L₁ L₂ := by
  exact Finset.filter_subset_filter _ (assignedSecondSource_mono hST J₁ J₂ base₁ base₂)

theorem varyingAssignedSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card)→ℂ) :
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,F x =
      ∑ y∈source,∑ q∈(J₁.pi (fun i=>L₁ y i∩(y.second.sourceCommon∪y.second.overlap)))×ˢ
        (J₂.pi (fun i=>L₂ y i∩(y.second.sourceCommon∪y.second.overlap))),F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [varyingAssignedSource,Finset.sum_filter,assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_product,varyingAssignedGate_attach,Finset.mem_pi,Finset.mem_inter]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
    exact ⟨fun i hi=>⟨h₃ i hi,(h₁ i hi).2⟩,fun i hi=>⟨h₄ i hi,(h₂ i hi).2⟩⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨⟨fun i hi=>⟨hL₁ y hy i hi (h₁ i hi).1,(h₁ i hi).2⟩,
      fun i hi=>⟨hL₂ y hy i hi (h₂ i hi).1,(h₂ i hi).2⟩⟩,
      fun i hi=>(h₁ i hi).1,fun i hi=>(h₂ i hi).1⟩

theorem varyingAssignedSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ) (w P : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈source,w y*(star (primeMark J₁ (L₁ y) a₁ (y.second.sourceCommon∪y.second.overlap))*
      primeMark J₂ (L₂ y) a₂ (y.second.sourceCommon∪y.second.overlap))*P y) =
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x)*P (eraseSecondSlots x) := by
  rw [varyingAssignedSource_sum source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_varying_lists_weighted_count
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {Jo : ℕ} (u v : Oˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈base₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈base₂ i,‖a₂ i q‖≤1)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hchild : ∀ x∈source,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows)
    (K : ℕ) (ho : Jo≤2*K) (hJ₁ : J₁.card≤K) (hJ₂ : J₂.card≤K)
    (w : MarkedSecondSource ι Jo 0→ℂ) (hw : ∀ x∈source,‖w x‖≤1) (F G : SecondChild→ℂ) :
    ‖∑ x∈source,w x*(star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap))*
      primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap))*
      F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x))‖ ≤
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ)*
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) := by
  let S := varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂
  have hsub : S⊆assignedSecondSource source J₁ J₂ base₁ base₂ := Finset.filter_subset _ _
  have hs' : ActualSecondSourceConditions p S :=
    (assignedSecondSource_conditions p source hs J₁ J₂ base₁ base₂).mono p hsub
  have herase : ∀ x∈S,eraseSecondSlots x∈source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ base₁ base₂ x).mp (hsub hx)
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card)=>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hw' : ∀ x∈S,‖w' x‖≤1 := by
    intro x hx
    rw [show w' x=w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ base₁ base₂ a₁ a₂ ha₁ ha₂ x (hsub hx))
  have hc' : ∀ x∈S,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := varyingAssignedSource_sum_marks source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂ a₁ a₂ w
    (fun x=>F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondVaryingSupported -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_varying_lists_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ → Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ base₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ base₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_varying_lists_weighted_count p hp hpr hcop hinj u v S
    (hs.mono p hsub) J₁ J₂ base₁ base₂ L₁ L₂
    (fun x hx=>hL₁ x (hsub hx)) (fun x hx=>hL₂ x (hsub hx)) a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (varyingAssignedSource_mono hsub J₁ J₂ base₁ base₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI

end

