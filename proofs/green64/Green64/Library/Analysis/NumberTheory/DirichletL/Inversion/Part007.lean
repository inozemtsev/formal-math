module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part007

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Source (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotientSupport : Finset ι
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def extractedSupport (negative : Bool) (x : Source ι Jo) : Finset ι :=
  ((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪x.quotientSupport

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def parent (x : Source ι Jo) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := sourceIdeal p x.quotientSupport
  oldAssigned := x.oldAssigned

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

def appendParent {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : SecondParentSource ι (Jo+Jn) where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := Fin.addCases x.oldAssigned q

def forgetAppended {Jn : ℕ} (x : SecondParentSource ι (Jo+Jn)) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := fun i=>x.oldAssigned (Fin.castAdd Jn i)

omit [DecidableEq ι] in
@[simp] theorem forget_append {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : forgetAppended (appendParent x q)=x := by
  apply SecondParentSource.ext <;> try rfl
  funext i
  simp only [forgetAppended,appendParent,Fin.addCases_left]

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→SmoothMobiusCorrection.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

def attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) : SecondParentSource ι (Jo+(J.card+J.card)) :=
  appendParent (parent p q.1) (fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→SmoothMobiusCorrection.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem forget_attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    forgetAppended (attach p J q)=parent p q.1 := forget_append _ _

def assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈extractedSupport negative q.1)

def assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (assignmentSource source negative J lists).image (attach p J)

theorem sum_assignmentSource {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈assignmentSource source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (x,q) := by
  rw [assignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_assignedParents (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈assignedParents p source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (attach p J (x,q)) := by
  rw [assignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_assignmentSource source negative J lists _

def coefficient (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) :
    SecondParentSource ι (Jo+(J.card+J.card))→ℂ :=
  Function.extend (attach p J) (fun q=>w q.1*pairedSlotWeight J J a a q.2) (fun _=>0)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

theorem paired_parent_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (extractedSupport negative x))*
      primeMark J lists a (extractedSupport negative x))*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_assignedParents p hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem paired_parent_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    paired_parent_sum p hinj source negative J lists a w H

lemma mem_assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈assignmentSource source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)) := by
  rw [←paired_assignment_filter]
  simp only [assignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈assignedParents p source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),attach p J (x,q)=y := by
  simp only [assignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_assignmentSource source negative J lists x q).mp hq |>.1,
      q,(mem_assignmentSource source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_assignmentSource source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

structure SourceValid (x : Source ι Jo) : Prop where
  admissible : x.cube.Admissible
  common_disjoint : Disjoint x.firstCommon x.cube.support
  first_divisor : x.firstDivisor⊆x.firstCommon∪x.cube.support
  old_support : ∀ i,(x.oldAssigned i).val∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

theorem attach_old_support (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
      (J.pi (fun i=>lists i∩extractedSupport negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      extracted_prime_dvd p x hx.admissible negative _ (hh k)

omit [DecidableEq σ] in

theorem attach_physical_data (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (m : O) :
    secondParentLabel p (attach p J q)=secondParentLabel p (parent p q.1) ∧
    secondParentDivisor p (attach p J q)=secondParentDivisor p (parent p q.1) ∧
    secondParentPuncture p m (attach p J q)=secondParentPuncture p m (parent p q.1) :=
  ⟨rfl,rfl,rfl⟩

theorem coefficient_norm (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) : ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

theorem assigned_family_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈assignedParents p source negative J lists,∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily (assignedParents p source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact attach_old_support p negative J lists x (hs x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

def fixedPoint (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (D : Finset ι) : Source ι Jo :=
  ⟨b,C,E,D,old⟩

def fixedSource (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Finset (Source ι Jo) :=
  F.powerset.image (fixedPoint b C E old)

omit [DecidableEq ι] in
theorem fixedPoint_injective (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Function.Injective (fixedPoint b C E old) := by
  intro D D' h
  exact congrArg Source.quotientSupport h

def parentFunction (H : Source ι Jo→ℂ) : SecondParentSource ι Jo→ℂ :=
  Function.extend (parent p) H (fun _=>0)

theorem parentFunction_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (H : Source ι Jo→ℂ) (x : Source ι Jo) : parentFunction p H (parent p x)=H x :=
  (parent_injective p hinj).extend_apply _ _ _

theorem paired_source_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w H : Source ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H x) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*parentFunction p H (forgetAppended y) := by
  simpa only [parentFunction_parent p hinj] using
    paired_parent_sq_sum p hinj source negative J lists a w (parentFunction p H)

theorem fixed_priority_complex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w H : Finset ι→ℂ) :
    (∑ D∈F.powerset,w D*(‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 : ℝ)*H D) =
    ∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>w x.quotientSupport) y *
        parentFunction p (fun x=>H x.quotientSupport) (forgetAppended y) := by
  have he := paired_source_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>w x.quotientSupport) (fun x=>H x.quotientSupport)
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  simpa only [fixedPoint,extractedSupport,fixedSource] using he

theorem fixed_priority_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Finset ι→ℝ) :
    (∑ D∈F.powerset,w D*‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(w x.quotientSupport:ℂ)) y).re := by
  have he := paired_parent_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>(w x.quotientSupport:ℂ)) (fun _=>1)
  simp only [mul_one] at he
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    fixedPoint,extractedSupport,fixedSource] using hr

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityOuter (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℝ :=
  (‖RayFourExpansion.crossCoeff r.1 r.2‖*‖selector D‖) *
    ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖

def priorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)) a U)
    ω X (∏i∈C,p i) d core t Y

theorem first_priority_physical_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter) (core : FirstCoreIndex) :
    (∑ D∈F.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core D).re) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
      parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  have he := fixed_priority_complex p hinj F b C E old negative J lists a
    (fun D=>(priorityOuter p hg b negative Ψ m selector r core D:ℂ))
    (priorityPoisson p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots J lists a ω X t Y r core)
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using hr

theorem first_priority_energy_reindex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) :
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector ω X t Y =
    (32*512)*(2:ℝ)^slots.card *
      ∑ r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
      (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
        coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
          slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  simp_rw [←first_priority_physical_slice p hp hg hinj]
  unfold firstPrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter priorityPoisson
  ring

end SevenEighths.InverseFirstPriorityParents

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev Core (ι : Type*) := CubeCoordinates ι×Finset ι×Finset ι

def core {ι : Type*} {Jo : ℕ} (x : Source ι Jo) : Core ι :=
  (x.cube,x.firstCommon,x.quotientSupport)

def divisorTarget {ι : Type*} [DecidableEq ι] (p : ι→O) (q : Core ι) : Ideal O :=
  sourceIdeal p q.1.support*sourceIdeal p q.2.1*sourceIdeal p q.2.2

lemma divisorTarget_ne_zero {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) : divisorTarget p q≠0 :=
  mul_ne_zero (mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)

lemma firstDivisor_dvd_target {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ} (x : Source ι Jo) (hx : SourceValid p x) :
    sourceIdeal p x.firstDivisor∣divisorTarget p (core x) := by
  have hd := sourceIdeal_dvd p _ _ hx.first_divisor
  rw [sourceIdeal_union p _ _ hx.common_disjoint] at hd
  apply hd.trans
  change sourceIdeal p x.firstCommon*sourceIdeal p x.cube.support∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport
  rw [mul_comm (sourceIdeal p x.firstCommon)]
  exact dvd_mul_right _ _

theorem core_fiber_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) {Jo : ℕ}
    (S : Finset (Source ι Jo)) (q : Core ι)
    (hS : ∀x∈S,SourceValid p x) (hq : ∀x∈S,core x=q) :
    S.card≤(idealDivisors (divisorTarget p q)).card^(Jo+1) := by
  let D := idealDivisors (divisorTarget p q)
  have hD := divisorTarget_ne_zero p hp q
  let encode (x : S) : D×(Fin Jo→D) :=
    (⟨sourceIdeal p x.val.firstDivisor,(mem_idealDivisors hD).mpr (by
      simpa only [hq x.val x.property] using firstDivisor_dvd_target p x.val (hS x.val x.property))⟩,
      fun i=>⟨(x.val.oldAssigned i).val,(mem_idealDivisors hD).mpr (by
        have hh := (hS x.val x.property).old_support i
        change (x.val.oldAssigned i).val∣divisorTarget p (core x.val) at hh
        simpa only [hq x.val x.property] using hh)⟩)
  have hi : Function.Injective encode := by
    intro x y he
    have hk := (hq x.val x.property).trans (hq y.val y.property).symm
    have hd : x.val.firstDivisor=y.val.firstDivisor :=
      sourceIdeal_injective p hinj (congrArg (fun z=>z.1.val) he)
    have ho : x.val.oldAssigned=y.val.oldAssigned := by
      funext i
      apply Subtype.ext
      exact congrArg (fun z=>(z.2 i).val) he
    apply Subtype.ext
    exact Source.ext (congrArg Prod.fst hk) (congrArg (fun q=>q.2.1) hk) hd
      (congrArg (fun q=>q.2.2) hk) ho
  have hh := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,D,pow_succ,mul_comm] using hh

theorem core_fiber_small_power (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(q : Core ι),
    (∀x∈S,SourceValid p x) → (∀x∈S,core x=q) →
    (S.card:ℝ)≤C*(Ideal.absNorm (divisorTarget p q):ℝ)^eps := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power
    (eps/(Jmax+1)) (by positivity)
  refine ⟨D^(Jmax+1),by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S q hS hq
  have h0 := divisorTarget_ne_zero p hp q
  have hcard : S.card≤(idealDivisors (divisorTarget p q)).card^(Jmax+1) :=
    (core_fiber_card p hp hinj S q hS hq).trans
      (Nat.pow_le_pow_right (InverseInitialFibers.divisor_card_pos _ h0) (Nat.add_le_add_right hJo 1))
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ h0) (Jmax+1)
  apply (show (S.card:ℝ)≤((idealDivisors (divisorTarget p q)).card:ℝ)^(Jmax+1) by exact_mod_cast hcard).trans
  apply hb.trans_eq
  rw [mul_pow]
  congr 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  field_simp

lemma divisorTarget_norm_bound {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) (B V T : ℝ)
    (hB : 0≤B) (hV : 0≤V) (_hT : 0≤T)
    (hb₁ : ‖eisEmbedding (primeProduct p q.1.support q.1.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p q.1.support q.1.rightExponent)‖^2≤B)
    (hC : primeProductNorm p q.2.1≤V) (ht : primeProductNorm p q.2.2≤T) :
    (Ideal.absNorm (divisorTarget p q):ℝ)≤B^2*V*T := by
  unfold divisorTarget
  simp only [map_mul,Nat.cast_mul,sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
  change primeProductNorm p q.1.support*primeProductNorm p q.2.1*primeProductNorm p q.2.2≤_
  exact mul_le_mul (mul_le_mul (cubeCoordinates_radical_bound p hp q.1 B hB hb₁ hb₂)
    hC (primeProductNorm_pos p hp _).le (sq_nonneg _)) ht (primeProductNorm_pos p hp _).le
    (mul_nonneg (sq_nonneg _) hV)

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassCount -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma support_family_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (S : Finset (Finset ι)) (U : ℝ) (hU : 0<U) (hS : ∀A∈S,primeProductNorm p A≤U) :
    (S.card:ℝ)≤128*U := by
  by_cases h1 : 1≤U
  · have hh := DescentFiberCost.finite_ideal_count_real (S.image (sourceIdeal p)) U h1
      (by intro I hI;obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI;exact sourceIdeal_ne_zero p hp A)
      (by
        intro I hI
        obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI
        simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hS A hA)
    simpa only [Finset.card_image_of_injective S (sourceIdeal_injective p hinj)] using hh

  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact h1 ((primeProductNorm_ge_one p hp A).trans (hS A hA))
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem original_source_card (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T : ℝ),
    1≤B → 0≤H → 0<V → 0<T → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    (S.card:ℝ)≤C*B^(1+eps)*H*V*T*(B^2*V*T)^eps := by
  obtain ⟨Cf,hCf,hfiber⟩ := core_fiber_small_power Jmax eps heps
  obtain ⟨Cb,hCb,hcube⟩ := cube_coordinates_parity_count eps heps
  refine ⟨Cf*Cb*128^2,by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T hB hH hV hT hS hleft hright hactive hcommon hquot
  let Q := S.image core
  let bs := S.image Source.cube
  let cs := S.image Source.firstCommon
  let ts := S.image Source.quotientSupport
  have hbcount : (bs.card:ℝ)≤Cb*B^(1+eps)*H := hcube p hp hinj bs B H hB hH
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact (hS x hx).admissible)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hleft x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hright x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hactive x hx)
  have hccount : (cs.card:ℝ)≤128*V := support_family_card p hp hinj cs V hV
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hcommon x hx)
  have htcount : (ts.card:ℝ)≤128*T := support_family_card p hp hinj ts T hT
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hquot x hx)
  have hsub : Q⊆bs×ˢ(cs×ˢts) := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩⟩
  have hQcard : (Q.card:ℝ)≤(Cb*B^(1+eps)*H)*(128*V)*(128*T) := by
    have hh : (Q.card:ℝ)≤(bs.card:ℝ)*((cs.card:ℝ)*(ts.card:ℝ)) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp only [Finset.card_product])
    apply hh.trans
    calc
      _ ≤ (Cb*B^(1+eps)*H)*((128*V)*(128*T)) := by gcongr
      _ = _ := by ring
  have hF (q : Core ι) (hq : q∈Q) :
      ((S.filter (fun x=>core x=q)).card:ℝ)≤Cf*(B^2*V*T)^eps := by
    have hf := hfiber p hp hinj Jo hJo (S.filter (fun x=>core x=q)) q
      (fun x hx=>hS x (Finset.mem_filter.mp hx).1) (fun x hx=>(Finset.mem_filter.mp hx).2)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hCf.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (divisorTarget_norm_bound p hp (core x) B V T (zero_le_one.trans hB) hV.le hT.le
        (hleft x hx) (hright x hx) (hcommon x hx) (hquot x hx)) heps.le
  have he : (S.card:ℝ)=∑q∈Q,((S.filter (fun x=>core x=q)).card:ℝ) := by
    calc
      _ = ∑_x∈S,(1:ℝ) := by simp
      _ = ∑q∈Q,∑_x∈S.filter (fun x=>core x=q),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem core hx) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑_q∈Q,Cf*(B^2*V*T)^eps := Finset.sum_le_sum hF
    _ = (Q.card:ℝ)*(Cf*(B^2*V*T)^eps) := by simp
    _ ≤ ((Cb*B^(1+eps)*H)*(128*V)*(128*T))*(Cf*(B^2*V*T)^eps) :=
      mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = _ := by ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassWeighted -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def principalSupport {ι : Type*} [DecidableEq ι] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo) : Finset ι :=
  (extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪x.quotientSupport

lemma principalSupport_norm {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo)
    (hx : SourceValid p x) (hextra : extra x.cube⊆x.cube.support)
    (B V T : ℝ) (hB : 0≤B) (hV : 0≤V)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hC : primeProductNorm p x.firstCommon≤V) (ht : primeProductNorm p x.quotientSupport≤T) :
    primeProductNorm p (principalSupport extra negative x)≤B^2*V*T := by
  have hh := first_whole_extracted_norm p hp x.cube hx.admissible x.firstCommon (extra x.cube)
    hextra negative B hB hb₁ hb₂
  unfold principalSupport
  apply (primeProductNorm_union_le_mul p hp _ _).trans
  exact mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg _))) ht
    (primeProductNorm_pos p hp _).le (mul_nonneg (sq_nonneg _) hV)

theorem original_weighted_mass (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T a : ℝ),
    1≤B → 0≤H → 0<V → 0<T → 0≤a → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*B^(1+eps)*H*V*T*(B^2*V*T)^(eps+a) := by
  obtain ⟨C,hC,hcount⟩ := original_source_card Jmax eps heps
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T a hB hH hV hT ha hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hcard := hcount p hp hinj Jo hJo S B H V T hB hH hV hT hS hb₁ hb₂ hactive hcommon hquot
  have hBp : 0<B := zero_lt_one.trans_le hB
  calc
    _ ≤ ∑_x∈S,(B^2*V*T)^a := Finset.sum_le_sum (fun x hx=>
      Real.rpow_le_rpow (primeProductNorm_pos p hp _).le
        (principalSupport_norm p hp extra negative x (hS x hx) (hextra x hx) B V T hBp.le hV.le
          (hb₁ x hx) (hb₂ x hx) (hcommon x hx) (hquot x hx)) ha)
    _ = (S.card:ℝ)*(B^2*V*T)^a := by simp
    _ ≤ (C*B^(1+eps)*H*V*T*(B^2*V*T)^eps)*(B^2*V*T)^a :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by positivity : 0<B^2*V*T)]

lemma weighted_mass_power (Z ell R Bfirst t eta eps a : ℝ) (hZ : 0<Z) :
    (Z^(ell+eta))^(1+eps)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(eps+a)=
    Z^(ell+R/2+Bfirst+t+7*eta/2+eps*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul_natCast hZ.le]
  repeat rw [←Real.rpow_add hZ]
  rw [←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
  congr 1
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassSource -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma active_norm_of_square {ι : Type*} [DecidableEq ι] (p : ι→O)
    (A : Finset ι) (Z R eta : ℝ) (hZ : 0<Z)
    (hA : primeProductNorm p A≤Z^(R+eta)) :
    ‖eisEmbedding (∏i∈A,p i)‖≤Z^((R+eta)/2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hZ.le _)).mp
  have hh : (Z^((R+eta)/2))^2=Z^(R+eta) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    norm_num
  rw [hh]
  exact hA

theorem original_weighted_source (Jmax : ℕ) (delta : ℝ) (hdelta : 0<delta) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z ell R Bfirst t eta a loss : ℝ),
    1≤Z → 0≤ell+eta → 0≤a →
    7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)≤loss →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*Z^(ell+R/2+Bfirst+t+loss) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax delta hdelta
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z ell R Bfirst t eta a loss hZ hell ha hloss hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^(ell+eta)) (Z^((R+eta)/2))
    (Z^(Bfirst+eta)) (Z^(t+eta)) a (Real.one_le_rpow hZ hell)
    (Real.rpow_nonneg hZp.le _) (Real.rpow_pos_of_pos hZp _)
    (Real.rpow_pos_of_pos hZp _) ha hS hb₁ hb₂
    (fun x hx=>active_norm_of_square p _ Z R eta hZp (hactive x hx))
    hcommon hquot extra negative hextra
  apply hh.trans
  calc
    _ = C*( (Z^(ell+eta))^(1+delta)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(delta+a)) := by ring
    _ = C*Z^(ell+R/2+Bfirst+t+7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
      rw [weighted_mass_power Z ell R Bfirst t eta delta a hZp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassPrefactor -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def physicalPrincipalFactor (Z M r ell V delta A B R j t eta tau eps window : ℝ) : ℝ :=
  (Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
    Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)*
    (Z^(r-A-B-t)*Real.exp window)^(1+eps)

lemma principal_nominal_identity (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R+firstPhysicalHeight M r ell V delta B j+
      (r-A-B-t)+(ell+R/2+B+t)=r+3*ell+V-B-j := by
  unfold firstKappa firstPhysicalHeight
  ring

lemma physical_principal_exact (Z M r ell V delta A B R j t eta tau eps window loss : ℝ)
    (hZ : 0<Z) :
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)=
    Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss) := by
  have he : Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  have hw : (Real.exp window)^(1+eps)=Real.exp (window*(1+eps)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  unfold physicalPrincipalFactor
  rw [he,Real.mul_rpow (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le,
    ←Real.rpow_mul hZ.le,hw]
  have hx : r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss=
    firstKappa M r ell V delta A B R+(9/2:ℝ)*eta+
    (firstPhysicalHeight M r ell V delta B j+12*eta+tau)+
    (r-A-B-t)*(1+eps)+(ell+R/2+B+t+loss) := by
    unfold firstKappa firstPhysicalHeight
    ring
  rw [hx]
  simp only [Real.rpow_add hZ]
  ring

theorem original_physical_weighted_source (Jmax : ℕ) (dsmall : ℝ) (hdsmall : 0<dsmall) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))
    (Z M r ell V delta A B R j t eta tau eps window pi : ℝ),
    1≤Z → 0≤ell+eta → 0≤eps → 0≤B → 0≤j →
    eps*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)≤pi+eta/2 →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(B+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^(2*eps))≤
      C*Real.exp (window*(1+eps))*Z^(r+3*ell+V+17*eta+tau+pi) := by
  obtain ⟨C,hC,hsource⟩ := original_weighted_source Jmax dsmall hdsmall
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z M r ell V delta A B R j t eta tau eps window pi hZ hell heps hB hj hcost hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  let loss := 7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hsource p hp hinj Jo hJo S Z ell R B t eta (2*eps) loss hZ hell
    (by positivity) (le_refl _) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hP : 0≤physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window := by
    unfold physicalPrincipalFactor
    positivity
  calc
    _ ≤ physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (C*Z^(ell+R/2+B+t+loss)) := mul_le_mul_of_nonneg_left hh hP
    _ = C*(physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)) := by ring
    _ = C*(Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss)) := by
      rw [physical_principal_exact Z M r ell V delta A B R j t eta tau eps window loss hZp]
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
      dsimp [loss]
      linarith

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseMomentGlobalPrincipalMass
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_tail_mass (Jmax : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z L : ℝ),
    1≤Z → 0≤L → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^L) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^L) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^L) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,primeProductNorm p (principalSupport extra negative x))≤C*Z^(13*L) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z L hZ hL hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^L) (Z^L) (Z^L) (Z^L) 1
    (Real.one_le_rpow hZ hL) (by positivity) (by positivity) (by positivity)
    (by norm_num) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  simp only [Real.rpow_one] at hh
  apply hh.trans_eq
  have he : Z^(13*L)=(Z^L)^13 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    norm_num
    ring
  rw [he]
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.WholePriorityParents -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def wholeExtractedSupport (extra : Source ι Jo→Finset ι)
    (negative : Bool) (x : Source ι Jo) : Finset ι := extra x∪extractedSupport negative x

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈wholeExtractedSupport extra negative q.1)

def wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (wholeAssignmentSource extra source negative J lists).image (attach p J)

theorem sum_wholeAssignmentSource (extra : Source ι Jo→Finset ι) {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈wholeAssignmentSource extra source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (x,q) := by
  rw [wholeAssignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_wholeAssignedParents (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈wholeAssignedParents p extra source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (attach p J (x,q)) := by
  rw [wholeAssignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_wholeAssignmentSource extra source negative J lists _

theorem wholePaired_parent_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (wholeExtractedSupport extra negative x))*
      primeMark J lists a (wholeExtractedSupport extra negative x))*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_wholeAssignedParents p extra hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem wholePaired_parent_sq_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport extra negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    wholePaired_parent_sum p extra hinj source negative J lists a w H

lemma mem_wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈wholeAssignmentSource extra source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)) := by
  rw [←paired_assignment_filter]
  simp only [wholeAssignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈wholeAssignedParents p extra source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),attach p J (x,q)=y := by
  simp only [wholeAssignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.1,
      q,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_wholeAssignmentSource extra source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

theorem whole_extracted_prime_dvd (extra : Source ι Jo→Finset ι)
    (x : Source ι Jo) (hx : x.cube.Admissible) (he : extra x⊆x.cube.support)
    (negative : Bool) (i : ι) (hi : i∈wholeExtractedSupport extra negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i (he hi)) _) _
  · exact extracted_prime_dvd p x hx negative i hi

theorem whole_attach_old_support (extra : Source ι Jo→Finset ι)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x) (he : extra x⊆x.cube.support)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
      (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      whole_extracted_prime_dvd p extra x hx.admissible he negative _ (hh k)

theorem whole_assigned_family_conditions (hp : ∀ i,p i≠0)
    (extra : Source ι Jo→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (he : ∀ x∈source,extra x⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈wholeAssignedParents p extra source negative J lists,
      ∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p
      (attachedSecondFamily (wholeAssignedParents p extra source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact whole_attach_old_support p extra negative J lists x (hs x hx) (he x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI

end

