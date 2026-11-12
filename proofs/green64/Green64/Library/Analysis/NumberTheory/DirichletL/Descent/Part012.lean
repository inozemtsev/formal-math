module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part007
public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.PrioritySecondSource
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part007

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part012

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.WholePriorityPhysical -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityPhysical
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def fullPhysical (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) : ℂ :=
  let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let ll := fun i=>lists i\extra y.cube
  let H := markedRadial p (slots\J) (residualLists p negative ll y) a ∅ V X
  let K := secondVariableCutoff p y R
  truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J ll a V X Y ray x) +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K

theorem whole_parent_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) (hq : y.quotient=sourceIdeal p (quotientSupport p y)) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y =
    fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y r core R label y :=
  parentPoisson_full p hp hcop hg hinj hc hpr y pool hq negative Ψ m slots J
    (fun i=>lists i\extra y.cube) a om lo hi hlo hs X t Y hX hY r core R label

omit [DecidableEq σ] in
theorem whole_residual_lists_attach
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo×((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative (fun i=>lists i\extra (attach p J q).cube) (attach p J q)=
      fun i=>lists i\wholeExtractedSupport (fun x=>extra x.cube) negative q.1 := by
  rw [residualLists_attach p hinj]
  funext i
  ext k
  simp only [Finset.mem_sdiff,wholeExtractedSupport,Finset.mem_union]
  change (k ∈ lists i ∧ k ∉ extra q.1.cube) ∧ k ∉ extractedSupport negative q.1 ↔ _
  tauto

theorem whole_signed_source_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (Source ι Jo)) (w : Source ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ x∈source,w x*(‖primeMark J lists a
      (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J
        (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x)) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  have he := wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj source negative J lists a w
    (fun y=>parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y)
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨x,hx,q,hq,rfl⟩ :=
    (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists y).mp hy
  rw [forget_attach]
  apply congrArg (coefficient p J a w (attach p J (x,q))* ·)
  have hquot : (attach p J (x,q)).quotient=sourceIdeal p (quotientSupport p (attach p J (x,q))) := by
    rw [quotientSupport_attach p hinj];rfl
  exact whole_parent_full p hp hcop hg hinj hc hpr extra pool negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY r core R label (attach p J (x,q)) hquot

end SevenEighths.InverseMomentWholePriorityPhysical

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.WholeRetainedSource -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMomentWholeRetainedSource
open ActualEisensteinCubic SecondPassArithmetic InverseMoment InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentWholePriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def deleted (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (x : MarkedSecondSource ι Jo 0) : Finset ι :=
  extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x))

theorem retained_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
        R label residual j) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs hextra negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

theorem retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
      R label residual j) :
    ∀ i∈deleted p extra negative x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  have hy := ((mem_retainedPool p pool _ R label residual j x).mp hx).1
  obtain ⟨s,hs₀,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists _).mp hy
  have hc : x.cube=s.cube := (congrArg SecondParentSource.cube he).symm
  have hC : x.firstCommon=s.firstCommon := (congrArg SecondParentSource.firstCommon he).symm
  have ht : x.quotient=sourceIdeal p s.quotientSupport := (congrArg SecondParentSource.quotient he).symm
  have hqs : quotientSupport p (secondParentOf x)=s.quotientSupport := by
    rw [←he,quotientSupport_attach p hinj]
  intro i hi
  change i∈extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x)) at hi
  rw [hc,hC,hqs] at hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Or.inl (Finset.mem_union_left _ (hc.symm ▸ hextra s hs₀ hi))
  · rcases Finset.mem_union.mp hi with hi|hi
    · left
      rw [hc,hC]
      rcases Finset.mem_union.mp hi with hi|hi
      · apply Finset.mem_union_left
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact (hs s hs₀).admissible.1 hi
        · exact (hs s hs₀).admissible.2 hi
      · exact Finset.mem_union_right _ hi
    · right
      rw [ht]
      exact source_prime_dvd p _ i hi

theorem whole_coefficient_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈wholeAssignedParents p extra source negative J lists) :
    ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

end SevenEighths.InverseMomentWholeRetainedSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseSecondChildWindows
open InverseMoment InverseSecondProfileUniform
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O

theorem positive_cutoff (a b : ℝ) (ha : 0<a) (_hab : a≤b) :
    ∃ w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      (∀ x∈Set.Icc a b,w x=1) ∧ tsupport (w : ℝ→ℂ)⊆Set.Icc (a/2) (b+1) := by
  have hKU : Set.Icc a b⊆Set.Ioo (a/2) (b+1) := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hKU
  let v : ℝ→ℂ := fun x => (f x:ℂ)
  have hv : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp (by simpa using hf)
  have hvs : Function.support v⊆Set.Icc (a/2) (b+1) := by
    intro x hx
    have hh : x∈Function.support f := by simpa [v,Function.mem_support] using hx
    rw [hs] at hh
    exact ⟨hh.1.le,hh.2.le⟩
  have hvc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hvs
  refine ⟨hvc.toSchwartzMap hv,hvc,?_,closure_minimal hvs isClosed_Icc⟩
  intro x hx
  change (f x:ℂ)=1
  rw [(hone x).mp hx]
  rfl

theorem positiveSource_log_bound (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (_hm : 0≤ m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤ c) (hcb : c≤bcap) (_hx : 0<x)
    (hn : positiveSource g c θ x≠0) : |Real.log x|≤ m+Real.log bcap := by
  have hc0 : 0<c := zero_lt_one.trans_le hc
  have hgn : g (Real.log x+Real.log c)≠0 := (mul_ne_zero_iff.mp hn).2
  have hh := hs hgn
  have hcl : 0≤Real.log c := Real.log_nonneg hc
  have hclb : Real.log c≤Real.log bcap := Real.log_le_log hc0 hcb
  rw [abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem positiveSource_ratio_support (g : 𝓢(ℝ,ℂ)) (m bcap c θ x : ℝ)
    (hm : 0≤ m) (hs : Function.support g⊆Set.Icc (-m) m)
    (hc : 1≤ c) (hcb : c≤bcap) (hx : 0<x)
    (hn : positiveSource g c θ x≠0) :
    x∈Set.Icc (Real.exp (-(m+Real.log bcap))) (Real.exp (m+Real.log bcap)) := by
  have hh := (abs_le.mp (positiveSource_log_bound g m bcap c θ x hm hs hc hcb hx hn))
  exact ⟨(Real.le_log_iff_exp_le hx).mp hh.1,(Real.log_le_iff_le_exp hx).mp hh.2⟩

theorem translated_log_bound (a b x ρ B : ℝ) (ha : 0<a)
    (hx : x∈Set.Icc a b) (hρ : |ρ|≤B) :
    |Real.log x+ρ|≤|Real.log a|+|Real.log b|+B := by
  have hx0 := ha.trans_le hx.1
  have hlo := Real.log_le_log ha hx.1
  have hhi := Real.log_le_log hx0 hx.2
  have hl : |Real.log x|≤|Real.log a|+|Real.log b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  exact (abs_add_le _ _).trans (add_le_add hl hρ)

def outerIndex (i : Fin 4) : Fin 6 := i.castLE (by decide)

theorem fixed_windows (m bcap : ℝ) (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm : 0≤ m) (_hcap : 1≤bcap) (hlo : ∀ i,0<lo i)
    (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w : 𝓢(ℝ,ℂ)) (U : Fin 6→𝓢(ℝ,ℂ)) (M : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M i) ∧ (∀ i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀ (g : 𝓢(ℝ,ℂ)),Function.support g⊆Set.Icc (-m) m →
        ∀ (c θ u v n : ℝ),1≤ c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → 0<n →
        positiveSource g c θ (u*v*n)≠0 → w n=1) ∧
      (∀ (q : Fin 6→ℝ) (ρ : Fin 6→ℝ),
        (∀ i,|ρ i|≤Bρ i) →
        (∀ i : Fin 4,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w (q 4)≠0 → w (q 5)≠0 → ∀ i,U i (Real.log (q i)+ρ i)=1) := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 2)
  let b := Real.exp R/(lo 0*lo 2)
  have hhi0 (i : Fin 4) : 0<hi i := (hlo i).trans_le (hhi i)
  have ha : 0<a := div_pos (Real.exp_pos _) (mul_pos (hhi0 0) (hhi0 2))
  have hb : 0<b := div_pos (Real.exp_pos _) (mul_pos (hlo 0) (hlo 2))
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  let l : Fin 6→ℝ := ![lo 0,lo 1,lo 2,lo 3,a/2,a/2]
  let u : Fin 6→ℝ := ![hi 0,hi 1,hi 2,hi 3,(a+b+1)+1,(a+b+1)+1]
  have hl (i : Fin 6) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact half_pos ha
    · exact half_pos ha
  let H (i : Fin 6) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 6) : 0≤H i := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 6 => FourierBridge.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 6) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w,U,(fun i=>H i+1),a/2,(a+b+1)+1,half_pos ha,by linarith,hwc,hws,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),?_,?_⟩
  · intro g hg c θ u v n hc hcb hu hv hn hnz
    have hu0 := (hlo 0).trans_le hu.1
    have hv0 := (hlo 2).trans_le hv.1
    have hs := positiveSource_ratio_support g m bcap c θ (u*v*n) hm hg hc hcb
      (mul_pos (mul_pos hu0 hv0) hn) hnz
    have hnlo : a≤n := by
      apply (div_le_iff₀ (mul_pos (hhi0 0) (hhi0 2))).mpr
      calc
        _ ≤ u*v*n := hs.1
        _ ≤ (hi 0*hi 2)*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.2 hv.2 hv0.le (hhi0 0).le) hn.le
        _ = _ := by ring
    have hnhi : n≤b := by
      apply (le_div_iff₀ (mul_pos (hlo 0) (hlo 2))).mpr
      calc
        _ = (lo 0*lo 2)*n := by ring
        _ ≤ u*v*n := mul_le_mul_of_nonneg_right
          (mul_le_mul hu.1 hv.1 (hlo 2).le hu0.le) hn.le
        _ ≤ _ := hs.2
    exact hwone n ⟨hnlo,by linarith⟩
  · intro q ρ hρ hblock hleft hright i
    have hq (k : Fin 6) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hws (subset_tsupport _ hleft)
      · exact hws (subset_tsupport _ hright)
    exact hVone i _ (translated_log_bound (l i) (u i) (q i) (ρ i) (Bρ i) (hl i) (hq i) (hρ i))

def actualOuterRatios {ι : Type*} [DecidableEq ι] (p : ι→O)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (G E V B : ℝ) : Fin 4→ℝ :=
  ![primeProductNorm p x.second.sourceCommon/G,
    ‖ConcreteTraceCRT.eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.second.divisor)‖^2/E,
    primeProductNorm p x.second.overlap/V,‖ConcreteTraceCRT.eisEmbedding x.second.frequency‖^2/B]

lemma actualRelativeNorm_outer {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (Q₁ Q₂ : Finset ι) (G E V B X : ℝ) (i : Fin 4) :
    secondRelativeNorm (secondActualNorms p (secondInheritedProfile p x Ψ m z) Q₁ Q₂)
      G E V B X (outerIndex i)=actualOuterRatios p x G E V B i := by
  fin_cases i <;> rfl

theorem actual_second_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (Bρ : Fin 6→ℝ)
    (hm₁ : 0≤ m₁) (_hm₂ : 0≤ m₂) (hcap : 1≤bcap)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hBρ : ∀ i,0≤Bρ i) :
    ∃ (w₁ w₂ : 𝓢(ℝ,ℂ)) (U₀ : Fin 6→𝓢(ℝ,ℂ)) (M₀ : Fin 6→ℝ) (a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀ i,0≤M₀ i) ∧ (∀ i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀ i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (_hp : ∀ i,p i≠0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (pool : Finset ι)
      (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex) (G E V B X : ℝ)
      (ρ : Fin 6→ℝ) (c₁ c₂ θ₁ θ₂ : ℝ),
      0<G → 0<E → 0<V → 0<B → 0<X →
      (∀ i,|ρ i|≤Bρ i) → 1≤ c₁ → c₁≤bcap → 1≤ c₂ → c₂≤bcap →
      (∀ x∈source,∀ i,actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        star (positiveSource g₁ c₁ θ₁
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X)))≠0 →
        w₁ (primeProductNorm p Q/X)=1) ∧
      (∀ x∈source,∀ Q∈(pool\x.second.overlap).powerset,
        positiveSource g₂ c₂ θ₂
          (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X))≠0 →
        w₂ (primeProductNorm p Q/X)=1) ∧
      (∀ j∈secondProfileIndices source pool (fun x=>secondInheritedProfile p x Ψ m z),
        w₁ (primeProductNorm p j.2.1/X)≠0 → w₂ (primeProductNorm p j.2.2/X)≠0 → ∀ i,
        U₀ i (secondRelativeLog
          (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X i+ρ i)=1) := by
  let mmax := max m₁ m₂
  have hmmax : 0≤ mmax := hm₁.trans (le_max_left _ _)
  have hg₁' : Function.support g₁⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₁ hx
    exact ⟨(neg_le_neg (le_max_left _ _)).trans h.1,h.2.trans (le_max_left _ _)⟩
  have hg₂' : Function.support g₂⊆Set.Icc (-mmax) mmax := by
    intro x hx
    have h := hg₂ hx
    exact ⟨(neg_le_neg (le_max_right _ _)).trans h.1,h.2.trans (le_max_right _ _)⟩
  obtain ⟨w,U,M,a,b,ha,hab,hwc,hws,hM,hUc,hUs,hfresh,hcut⟩ :=
    fixed_windows mmax bcap lo hi Bρ hmmax hcap hlo hhi hBρ
  refine ⟨w,w,U,M,a,b,ha,hab,hwc,hwc,hws,hws,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ Jo Jn source pool Ψ m z G E V B X ρ c₁ c₂ θ₁ θ₂ hG hE hV hB hX hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  have he (x : MarkedSecondSource ι Jo Jn) (Q : Finset ι) :
      (primeProductNorm p x.second.sourceCommon/G)*(primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X)=
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*primeProductNorm p Q/(G*V*X) := by
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro x hx Q _ hn
    apply hfresh g₁ hg₁' c₁ θ₁ _ _ _ hc₁ hcb₁ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₁ c₁ θ₁ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact star_ne_zero.mp hn
  · intro x hx Q _ hn
    apply hfresh g₂ hg₂' c₂ θ₂ _ _ _ hc₂ hcb₂ (hblock x hx 0) (hblock x hx 2)
      (div_pos (primeProductNorm_pos p hp Q) hX)
    change positiveSource g₂ c₂ θ₂ ((primeProductNorm p x.second.sourceCommon/G)*
      (primeProductNorm p x.second.overlap/V)*(primeProductNorm p Q/X))≠0
    rw [he]
    exact hn
  · intro j hj hleft hright i
    apply hcut (secondRelativeNorm
      (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2) G E V B X) ρ hρ
      (fun k=>?_) hleft hright i
    rw [actualRelativeNorm_outer]
    exact hblock j.1 ((mem_secondProfileIndices source pool _ j).mp hj).1 k

end SevenEighths.InverseSecondChildWindows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ClippedFourier -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier SecondPassIntegration JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem clipped_fixed_window (W:ℝ→ℂ) (lo hi b:ℝ) (hlo:0<lo) (hb:1≤b)
    (hW:Function.support W⊆Set.Icc lo hi):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀c,1≤ c→c≤b→∀y,0<y→wFresh y*W (c*y)=W (c*y):=by
  have hb0:0<b:=zero_lt_one.trans_le hb
  let a:=lo/b
  let B:=a+|hi|+1
  have ha:0<a:=div_pos hlo hb0
  obtain ⟨wFresh,hc,hone,hs⟩:=InverseSecondChildWindows.positive_cutoff a B ha (by dsimp [B];linarith [abs_nonneg hi])
  refine ⟨wFresh,a/2,B+1,half_pos ha,by dsimp [B];linarith [abs_nonneg hi],hc,hs,?_⟩
  intro c hc hcb y hy
  by_cases hz:W (c*y)=0
  · simp only [hz,mul_zero]
  have hw:=hW hz
  have hay:a≤y:=by
    apply (div_le_iff₀ hb0).mpr
    calc
      lo≤ c*y:=hw.1
      _≤y*b:=by nlinarith
  have hyhi:y≤hi:=le_trans (by nlinarith) hw.2
  have hyB:y≤B:=by dsimp [B];linarith [le_abs_self hi]
  rw [hone y ⟨hay,hyB⟩,one_mul]

theorem clipped_test_fourier (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hs:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ y:ℝ)(hc:0<c)(hy:0<y)(hwFresh:wFresh y*W (c*y)=W (c*y)):
    clippedTest W c θ y =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        childLogTest wFresh (θ+t) y:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  change clippedTest W c θ y=∫t:ℝ,density g (Real.log c) t*childLogTest wFresh (θ+t) y
  have he (t:ℝ):density g (Real.log c) t*childLogTest wFresh (θ+t) y=
      ((𝓕 g) t*logPhase t (Real.log c+Real.log y))*(wFresh y*logPhase θ (Real.log y)):=by
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  have hi':(∫t:ℝ,(𝓕 g) t*logPhase t (Real.log c+Real.log y))=W (c*y):=by
    calc
      _=(∫t:ℝ,logPhase t (Real.log c+Real.log y)*(𝓕 g) t):=by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _=g (Real.log c+Real.log y):=(schwartz_logPhase_inversion g _).symm
      _= _:=by
        simp only [g,CubicReflectionKernel.logSchwartz_apply,Real.exp_add,Real.exp_log hc,Real.exp_log hy]
  rw [hi']
  unfold clippedTest childLogTest
  calc
    W (c*y)*logPhase θ (Real.log y)=(wFresh y*W (c*y))*logPhase θ (Real.log y):=by rw [hwFresh]
    _= _:=by ring

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_clipped_mode_integrable
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m f k:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (g:𝓢(ℝ,ℂ))(wFresh:ℝ→ℂ)(c θ X:ℝ):
    Integrable (fun t:ℝ=>density g (Real.log c) t*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X):=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro U hU
  convert fourier_phase_integrable g (Real.log c+Real.log (primeProductNorm p U/X))
    (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
      primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
  funext t
  simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
  ring

theorem canonical_clipped_fourier
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m f k:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X:ℝ)(hc:0<c)(hX:0<X)(hwFresh:∀y,0<y→wFresh y*W (c*y)=W (c*y)):
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (clippedTest W c θ) X=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a (childLogTest wFresh (θ+t)) X:=by
  simp_rw [finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr]
  simp only [Finset.mul_sum]
  have hints (U:Finset ι):Integrable (fun t:ℝ=>
      density (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW) (Real.log c) t*
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        (primeMark slots lists a U*childLogTest wFresh (θ+t) (primeProductNorm p U/X)))):=by
    convert fourier_phase_integrable (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)
      (Real.log c+Real.log (primeProductNorm p U/X))
      (columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k) (Ideal.span {∏i∈U,p i})*
        primeMark slots lists a U*wFresh (primeProductNorm p U/X)*logPhase θ (Real.log (primeProductNorm p U/X))) using 1
    funext t
    simp only [density,childLogTest,logPhase_add_frequency,logPhase_add]
    ring
  rw [integral_finsetSum _ (fun U _=>hints U)]
  apply Finset.sum_congr rfl
  intro U hU
  rw [clipped_test_fourier W lo hi hlo hs hW wFresh c θ _ hc
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX) (hwFresh _ (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U) hX))]
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstChildWindows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform
open InverseSecondChildWindows

theorem fresh_three_window (g : 𝓢(ℝ,ℂ)) (m bcap : ℝ)
    (lo hi : Fin 3→ℝ) (hm : 0≤ m)
    (hg : Function.support g⊆Set.Icc (-m) m)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤hi i) :
    ∃(w : 𝓢(ℝ,ℂ))(a b : ℝ),0<a ∧ a≤b ∧ HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ)⊆Set.Icc a b ∧
      ∀(c θ u v r n : ℝ),1≤ c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 1) (hi 1) → r∈Set.Icc (lo 2) (hi 2) →
        0<n → positiveSource g c θ (u*v*r*n)≠0 → w n=1 := by
  let R := m+Real.log bcap
  let a := Real.exp (-R)/(hi 0*hi 1*hi 2)
  let b := Real.exp R/(lo 0*lo 1*lo 2)
  have hhip (i : Fin 3) : 0<hi i := (hlo i).trans_le (hhi i)
  have hh0 := hhip 0
  have hh1 := hhip 1
  have hh2 := hhip 2
  have hl0 := hlo 0
  have hl1 := hlo 1
  have hl2 := hlo 2
  have ha : 0<a := by dsimp [a];positivity
  have hb : 0<b := by dsimp [b];positivity
  obtain ⟨w,hwc,hwone,hws⟩ := positive_cutoff a (a+b+1) ha (by linarith)
  refine ⟨w,a/2,a+b+2,half_pos ha,by linarith,hwc,by convert hws using 1; ring_nf,?_⟩
  intro c θ u v r n hc hcb hu hv hr hn hnz
  have hu0 := (hlo 0).trans_le hu.1
  have hv0 := (hlo 1).trans_le hv.1
  have hr0 := (hlo 2).trans_le hr.1
  have hs := positiveSource_ratio_support g m bcap c θ (u*v*r*n) hm hg hc hcb (by positivity) hnz
  have hnlo : a≤n := by
    apply (div_le_iff₀ (by positivity : 0<hi 0*hi 1*hi 2)).mpr
    calc
      _ ≤ u*v*r*n := hs.1
      _ ≤ (hi 0*hi 1*hi 2)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hu.2 hv.2 hv0.le (hhip 0).le) hr.2 hr0.le (by positivity)) hn.le
      _ = _ := by ring
  have hnhi : n≤b := by
    apply (le_div_iff₀ (by positivity : 0<lo 0*lo 1*lo 2)).mpr
    calc
      _ = (lo 0*lo 1*lo 2)*n := by ring
      _ ≤ u*v*r*n := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hu.1 hv.1 (hlo 1).le hu0.le) hr.1 (hlo 2).le (by positivity)) hn.le
      _ ≤ _ := hs.2
  exact hwone n ⟨hnlo,by linarith⟩

def outerIndex (i : Fin 7) : Fin 9 := i.castLE (by decide)

theorem fixed_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 7→ℝ) (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤hi i) (hBρ : ∀i,0≤Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U : Fin 9→𝓢(ℝ,ℂ))(M : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤M i) ∧ (∀i,HasCompactSupport (U i : ℝ→ℂ)) ∧
      (∀i,Function.support (U i)⊆Set.Icc (-M i) (M i)) ∧
      (∀(c θ u v r n : ℝ),1≤ c → c≤bcap →
        u∈Set.Icc (lo 0) (hi 0) → v∈Set.Icc (lo 2) (hi 2) → r∈Set.Icc (lo 5) (hi 5) →
        0<n → positiveSource g₁ c θ (u*v*r*n)≠0 → w₁ n=1) ∧
      (∀(c θ u v r n : ℝ),1≤ c → c≤bcap →
        u∈Set.Icc (lo 1) (hi 1) → v∈Set.Icc (lo 2) (hi 2) → r∈Set.Icc (lo 5) (hi 5) →
        0<n → positiveSource g₂ c θ (u*v*r*n)≠0 → w₂ n=1) ∧
      (∀(q ρ : Fin 9→ℝ),(∀i,|ρ i|≤Bρ i) →
        (∀i : Fin 7,q (outerIndex i)∈Set.Icc (lo i) (hi i)) →
        w₁ (q 7)≠0 → w₂ (q 8)≠0 → ∀i,U i (Real.log (q i)+ρ i)=1) := by
  let left : Fin 3→Fin 7 := ![0,2,5]
  let right : Fin 3→Fin 7 := ![1,2,5]
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hwc₁,hws₁,hfresh₁⟩ := fresh_three_window g₁ m₁ bcap
    (lo ∘ left) (hi ∘ left) hm₁ hg₁ (fun i=>hlo (left i)) (fun i=>hhi (left i))
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hwc₂,hws₂,hfresh₂⟩ := fresh_three_window g₂ m₂ bcap
    (lo ∘ right) (hi ∘ right) hm₂ hg₂ (fun i=>hlo (right i)) (fun i=>hhi (right i))
  let l : Fin 9→ℝ := ![lo 0,lo 1,lo 2,lo 3,lo 4,lo 5,lo 6,a₁,a₂]
  let u : Fin 9→ℝ := ![hi 0,hi 1,hi 2,hi 3,hi 4,hi 5,hi 6,b₁,b₂]
  have hl (i : Fin 9) : 0<l i := by
    fin_cases i
    · exact hlo 0
    · exact hlo 1
    · exact hlo 2
    · exact hlo 3
    · exact hlo 4
    · exact hlo 5
    · exact hlo 6
    · exact ha₁
    · exact ha₂
  let H (i : Fin 9) := |Real.log (l i)|+|Real.log (u i)|+Bρ i
  have hH (i : Fin 9) : 0≤H i := by dsimp [H];exact add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (hBρ i)
  choose V hVc hVs hVone hVsupport hVzero using
    fun i : Fin 9=>FourierBridge.exists_complex_smooth_cutoff (H i) (hH i)
  let U (i : Fin 9) : 𝓢(ℝ,ℂ) := (hVc i).toSchwartzMap (hVs i)
  refine ⟨w₁,w₂,U,(fun i=>H i+1),min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hwc₁,hwc₂,?_,?_,
    (fun i=>by linarith [hH i]),hVc,(fun i=>(subset_tsupport _).trans (hVsupport i)),hfresh₁,hfresh₂,?_⟩
  · intro x hx
    exact ⟨(min_le_left _ _).trans (hws₁ hx).1,(hws₁ hx).2.trans (le_max_left _ _)⟩
  · intro x hx
    exact ⟨(min_le_right _ _).trans (hws₂ hx).1,(hws₂ hx).2.trans (le_max_right _ _)⟩
  · intro q ρ hρ hblock hw₁ hw₂ i
    have hq (k : Fin 9) : q k∈Set.Icc (l k) (u k) := by
      fin_cases k
      · exact hblock 0
      · exact hblock 1
      · exact hblock 2
      · exact hblock 3
      · exact hblock 4
      · exact hblock 5
      · exact hblock 6
      · exact hws₁ (subset_tsupport _ hw₁)
      · exact hws₂ (subset_tsupport _ hw₂)
    exact hVone i _ (translated_log_bound _ _ _ _ _ (hl i) (hq i) (hρ i))

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsActual -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform ActualEisensteinCubic
open FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def actualOuterRatios {ι : Type*} (p : ι→O) (A₁ A₂ C R : ℝ) (d h : O)
    (j : FirstCommonIndex ι) (s : Fin 9→ℝ) (i : Fin 7) : ℝ :=
  firstCommonNorms p A₁ A₂ C R d h j (outerIndex i)/s (outerIndex i)

theorem actual_first_child_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 7→ℝ) (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hlo : ∀i,0<lo i) (hhi : ∀i,lo i≤hi i) (hBρ : ∀i,0≤Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U₀ : Fin 9→𝓢(ℝ,ℂ))(M₀ : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤M₀ i) ∧ (∀i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀{ι κ : Type*}[DecidableEq ι][DecidableEq κ]
      (p : ι→O)(_hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (source : Finset κ)(F : Finset ι)(selector C₁ C₂ : κ→Finset ι→ℂ)
      (A₁ A₂ C R : κ→ℝ)(d h : κ→O)(s : Fin 9→ℝ)
      (ρ : Fin 9→ℝ)(c₁ c₂ θ₁ θ₂ : ℝ),
      (∀i,0<s i) → (∀i,|ρ i|≤Bρ i) →
      1≤ c₁ → c₁≤bcap → 1≤ c₂ → c₂≤bcap →
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j s i∈Set.Icc (lo i) (hi i)) →
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        positiveSource g₁ c₁ θ₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7))≠0 →
        w₁ (primeProductNorm p j.2.2.1/s 7)=1) ∧
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        positiveSource g₂ c₂ θ₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8))≠0 →
        w₂ (primeProductNorm p j.2.2.2/s 8)=1) ∧
      (∀x∈source,∀j∈firstCommonIndices F,
        selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0 →
        w₁ (primeProductNorm p j.2.2.1/s 7)≠0 → w₂ (primeProductNorm p j.2.2.2/s 8)≠0 →
        ∀i,U₀ i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i+ρ i)=1) := by
  obtain ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,hfresh₁,hfresh₂,hcut⟩ :=
    fixed_windows g₁ g₂ m₁ m₂ bcap lo hi Bρ hm₁ hm₂ hg₁ hg₂ hlo hhi hBρ
  refine ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,?_⟩
  intro ι κ _ _ p hp _ hg source F selector C₁ C₂ A₁ A₂ C R d h s ρ c₁ c₂ θ₁ θ₂
    hs hρ hc₁ hcb₁ hc₂ hcb₂ hblock
  refine ⟨?_,?_,?_⟩
  · intro x hx j hj hn hg₁n
    apply hfresh₁ c₁ θ₁ (A₁ x/s 0) (C x/s 2) (primeProductNorm p j.2.1/s 5) _
      hc₁ hcb₁ (hblock x hx j hj hn 0) (hblock x hx j hj hn 2) (hblock x hx j hj hn 5)
      (div_pos (primeProductNorm_pos p hp _) (hs 7))
    convert hg₁n using 2 ; ring
  · intro x hx j hj hn hg₂n
    apply hfresh₂ c₂ θ₂ (A₂ x/s 1) (C x/s 2) (primeProductNorm p j.2.1/s 5) _
      hc₂ hcb₂ (hblock x hx j hj hn 1) (hblock x hx j hj hn 2) (hblock x hx j hj hn 5)
      (div_pos (primeProductNorm_pos p hp _) (hs 8))
    convert hg₂n using 2 ; ring
  · intro x hx j hj hn hw₁ hw₂ i
    exact hcut (fun i=>firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j i/s i)
      ρ hρ (hblock x hx j hj hn) hw₁ hw₂ i

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondBlockEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff SchwartzMap

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory InverseInitialClippedColumns
open InverseSecondProfileUniform InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_fixed_block_recursive
    (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (B₀ : Fin 6→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂) (hcap : 1≤bcap)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hB₀ : ∀ i,0≤B₀ i)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) (Aker J K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,∀ i,InverseSecondChildWindows.actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ g₂ m₁ m₂ bcap lo hi B₀
      hm₁ hm₂ hcap hg₁ hg₂ hlo hhi hB₀
  obtain ⟨C,hC,henergy⟩ := actual_second_deleted_moving_mass_recursive (ι:=ι) (σ:=σ)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hUs hg₁ hg₂ Aker J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hblock hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp source pool Ψ m z G E V B (Z^N) ρ c₁ c₂ θ₁ θ₂
    hG hE hV hB hX hρ hc₁ hc₁b hc₂ hc₂b hblock
  exact henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityProfile -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def priorityLogWindow (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool):𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤))
  else CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤)

def priorityHeight (negative:Bool) (t:ℝ):ℝ := if negative then -t else t

theorem priorityLogWindow_support (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) :
    Function.support (priorityLogWindow om a b ha hs negative)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro y hy
  have hn:om (Real.exp y)≠0:=by
    cases negative <;> simpa only [priorityLogWindow,Bool.false_eq_true,ite_true,ite_false,
      conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,Function.mem_support,star_ne_zero] using hy
  have hh:=hs hn
  have hlo:=Real.log_le_log ha hh.1
  have hhi:=Real.log_le_log (Real.exp_pos y) hh.2
  rw [Real.log_exp] at hlo hhi
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

theorem principalWindow_positiveSource (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) (t x:ℝ) (hx:0<x) :
    principalWindow om a b ha hs negative t x =
      positiveSource (priorityLogWindow om a b ha hs negative) 1 (priorityHeight negative t) x := by
  rw [principalWindow_apply]
  cases negative <;> simp only [priorityLogWindow,priorityHeight,Bool.false_eq_true,ite_true,ite_false,
    positiveSource,Real.log_one,add_zero,conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,
    Real.exp_log hx,normTwistedSource]

theorem positiveSource_conjugate_one (g:𝓢(ℝ,ℂ)) (t x:ℝ) :
    star (positiveSource (conjugateProfile g) 1 (-t) x)=positiveSource g 1 t x := by
  simp only [positiveSource,Real.log_one,add_zero,conjugateProfile_apply,star_mul,star_star,
    logPhase_conjugate,neg_neg,mul_comm]

theorem actualSecondProfileRow_congr_positive {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (W₁ W₂ V₁ V₂:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X)
    (h₁:∀t,0<t→W₁ t=V₁ t) (h₂:∀t,0<t→W₂ t=V₂ t) :
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ V₁ V₂ Φ Y X := by
  simp only [actualSecondProfileRow_eq_whole p hp hcop hg]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  congr 1
  unfold secondNormProfile
  have h0 : secondActualNorms p x N M 0 = primeProductNorm p x.common := rfl
  have h2 : secondActualNorms p x N M 2 = primeProductNorm p x.overlap := rfl
  have h4 : secondActualNorms p x N M 4 = primeProductNorm p N := rfl
  have h5 : secondActualNorms p x N M 5 = primeProductNorm p M := rfl
  rw [h0,h2,h4,h5]
  dsimp only
  rw [h₁ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX),
    h₂ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX)]

theorem actual_priority_profile_common {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y X := by
  intro g θ
  apply actualSecondProfileRow_congr_positive p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    _ _ _ _ Φ Y X hX
  · intro y hy
    rw [positiveSource_conjugate_one]
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy
  · intro y hy
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondBlockEnergyWindowOrder -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff SchwartzMap

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory InverseInitialClippedColumns
open InverseSecondProfileUniform InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_fixed_block_recursive_window_order
    (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (B₀ : Fin 6→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂) (hcap : 1≤bcap)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hB₀ : ∀ i,0≤B₀ i)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) (Aker K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,∀ i,InverseSecondChildWindows.actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ g₂ m₁ m₂ bcap lo hi B₀
      hm₁ hm₂ hcap hg₁ hg₂ hlo hhi hB₀
  refine ⟨ω₁,ω₂,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩ := actual_second_deleted_moving_mass_recursive (ι:=ι) (σ:=σ)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hUs hg₁ hg₂ Aker J K εmass hεmass
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hblock hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp source pool Ψ m z G E V B (Z^N) ρ c₁ c₂ θ₁ θ₂
    hG hE hV hB hX hρ hc₁ hc₁b hc₂ hc₂b hblock
  exact henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondBlockEnergyWindowOrderUniform -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff SchwartzMap

namespace SevenEighths.InverseMoment
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory InverseInitialClippedColumns
open InverseSecondProfileUniform InverseAmbientProfileTower
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_second_fixed_block_recursive_window_order_uniform_types
    (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (lo hi : Fin 4→ℝ) (B₀ : Fin 6→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂) (hcap : 1≤bcap)
    (hlo : ∀ i,0<lo i) (hhi : ∀ i,lo i≤hi i) (hB₀ : ∀ i,0≤B₀ i)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) (Aker K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x∈source,∀ i,InverseSecondChildWindows.actualOuterRatios p x G E V B i∈Set.Icc (lo i) (hi i)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
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
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨ω₁,ω₂,U₀,M₀,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,hM,hUc,hUs,hwindows⟩ :=
    InverseSecondChildWindows.actual_second_child_windows g₁ g₂ m₁ m₂ bcap lo hi B₀
      hm₁ hm₂ hcap hg₁ hg₂ hlo hhi hB₀
  refine ⟨ω₁,ω₂,af,bf,haf,habf,hωc₁,hωc₂,hωs₁,hωs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩ := actual_second_deleted_moving_mass_recursive_uniform_types
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hUs hg₁ hg₂ Aker J K εmass hεmass
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hblock hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  obtain ⟨hω₁,hω₂,hcut⟩ := hwindows p hp source pool Ψ m z G E V B (Z^N) ρ c₁ c₂ θ₁ θ₂
    hG hE hV hB hX hρ hc₁ hc₁b hc₂ hc₂b hblock
  exact henergy p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFresh -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapFresh
variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem overlap_column_interval (I : Finset σ) (lo hi y : σ→ℝ)
    (a b jlo jhi yj yc : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hy : ∀i∈I,y i∈Set.Icc (lo i) (hi i))
    (hjlo : 0<jlo) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc)
    (hsource : yj*yc/(∏i∈I,y i)∈Set.Icc a b) :
    yc∈Set.Icc (a*(∏i∈I,lo i)/jhi) (b*(∏i∈I,hi i)/jlo) := by
  have hyp : ∀i∈I,0<y i := fun i hi=>(hlo i hi).trans_le (hy i hi).1
  have hip : ∀i∈I,0<hi i := fun i hi=>(hyp i hi).trans_le (hy i hi).2
  have hprod : 0<∏i∈I,y i := Finset.prod_pos hyp
  have hloP : (∏i∈I,lo i)≤∏i∈I,y i :=
    Finset.prod_le_prod₀ (fun i hi=>(hlo i hi).le) (fun i hi=>(hy i hi).1)
  have hhiP : (∏i∈I,y i)≤∏i∈I,hi i :=
    Finset.prod_le_prod₀ (fun i hi=>(hyp i hi).le) (fun i hi=>(hy i hi).2)
  have hyj : 0<yj := hjlo.trans_le hj.1
  have hjhip : 0<jhi := hyj.trans_le hj.2
  have hsourceLo := (le_div_iff₀ hprod).mp hsource.1
  have hsourceHi := (div_le_iff₀ hprod).mp hsource.2
  constructor
  · apply (div_le_iff₀ hjhip).mpr
    calc
      a*(∏i∈I,lo i)≤a*(∏i∈I,y i) := mul_le_mul_of_nonneg_left hloP ha.le
      _≤yj*yc := hsourceLo
      _≤jhi*yc := mul_le_mul_of_nonneg_right hj.2 hc.le
      _=yc*jhi := mul_comm _ _
  · apply (le_div_iff₀ hjlo).mpr
    calc
      yc*jlo=jlo*yc := mul_comm _ _
      _≤yj*yc := mul_le_mul_of_nonneg_right hj.1 hc.le
      _≤b*(∏i∈I,y i) := hsourceHi
      _≤b*(∏i∈I,hi i) := mul_le_mul_of_nonneg_left hhiP (ha.le.trans hab)

omit [DecidableEq σ] in
theorem exists_overlap_fresh (I : Finset σ) (lo hi : σ→ℝ)
    (a b jlo jhi : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hhi : ∀i∈I,lo i≤hi i)
    (hjlo : 0<jlo) (hjhi : jlo≤jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0<A ∧ A≤B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(W:ℝ→ℂ),(Function.support W⊆Set.Icc a b)→
      ∀(y:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,y i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,y i))≠0→wFresh yc=1 := by
  let lower := a*(∏i∈I,lo i)/jhi
  let upper := b*(∏i∈I,hi i)/jlo
  have hl : 0<lower := div_pos (mul_pos ha (Finset.prod_pos hlo)) (hjlo.trans_le hjhi)
  have hu : 0<upper := div_pos (mul_pos (ha.trans_le hab)
    (Finset.prod_pos (fun i hi=>(hlo i hi).trans_le (hhi i hi)))) hjlo
  obtain ⟨w,hwc,hwone,hws⟩ := InverseSecondChildWindows.positive_cutoff
    lower (lower+upper+1) hl (by linarith)
  refine ⟨w,lower/2,lower+upper+2,half_pos hl,by linarith,hwc,?_,?_⟩
  · convert hws using 1 ; ring_nf
  · intro W hW y yj yc hy hj hc hn
    have hb := overlap_column_interval I lo hi y a b jlo jhi yj yc ha hab hlo hy hjlo hj hc (hW hn)
    apply hwone
    exact ⟨hb.1,by change yc≤lower+upper+1;have := hb.2;change yc≤upper at this;linarith⟩

end SevenEighths.InverseInitialOverlapFresh

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlapSource -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapSource
open InverseInitialOverlapFresh InverseInitialOverlapInputFourier
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def tupleCoordinate (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) (i : σ) : ℝ :=
  if hi:i∈I then y i (q i hi) else 1

omit [DecidableEq ι] in
theorem tupleCoordinate_product (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) :
    (∏i∈I,tupleCoordinate I y q i)=∏i∈I.attach,y i.val (q i.val i.property) := by
  rw [←Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [tupleCoordinate,dite_eq_left i.property]

theorem insert_original_fresh
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (lo hi : σ→ℝ) (W wFresh : ℝ→ℂ) (a₀ b₀ jlo jhi : ℝ)
    (_hW : Function.support W⊆Set.Icc a₀ b₀)
    (ha : ∀i∈I,∀q∈L i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
    (hFresh : ∀(v:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,v i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A : Finset ι) (yj yc : ℝ) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc) :
    wFresh yc*(∑q∈I.pi L,
      (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
        W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))) =
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)=0
  · simp only [hz,zero_mul,mul_zero]
  by_cases hw : W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))=0
  · simp only [hw,mul_zero]
  have hcoord : ∀i∈I,tupleCoordinate I y q i∈Set.Icc (lo i) (hi i) := by
    intro i hi
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi⟩ (Finset.mem_attach _ _)
    have hcoeff : a i (q i hi)≠0 := by
      intro he
      apply hn
      split_ifs
      · exact he
      · rfl
    simpa only [tupleCoordinate,dite_eq_left hi] using
      ha i hi (q i hi) ((Finset.mem_pi.mp hq) i hi) hcoeff
  have hf := hFresh (tupleCoordinate I y q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  rw [hf,one_mul]

theorem exists_original_overlap_input
    (I : Finset σ) (lo hi : σ→ℝ) (W : ℝ→ℂ)
    (a₀ b₀ jlo jhi : ℝ) (ha₀ : 0<a₀) (hab : a₀≤b₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (hlo : ∀i∈I,0<lo i) (hhi : ∀i∈I,lo i≤hi i)
    (hjlo : 0<jlo) (hjhi : jlo≤jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0<A ∧ A≤B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(p:ι→ActualEisensteinCubic.O)(_hp:∀i,p i≠0)
        (hpmax:∀i,(Ideal.span {p i}).IsMaximal)
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (F:Finset ι)(Ψ:ActualEisensteinCubic.O→*ℂ)(j u:ActualEisensteinCubic.O)
        (lists:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
        (_hy:∀i∈I,∀q∈lists i,0<y i q)
        (_ha:∀i∈I,∀q∈lists i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
        (Z D yj:ℝ)(_hZ:0<Z)(_hj:yj∈Set.Icc jlo jhi),
      letI := hpmax
      ((Z^(-D/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1
        (fun U=>∑q∈I.pi lists,
          (∏i∈I.attach,if q i.val i.property∈U then a i.val (q i.val i.property) else 0)*
            W (yj*(FirstPassCubeLabels.primeProductNorm p U/Z^D)/
              (∏i∈I.attach,y i.val (q i.val i.property)))) u =
        ∫t:ℝ,InverseInitialOverlapFourier.density
          (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
          (((Z^(-D/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1
            (InverseInitialRayAttachment.initialTest p
              (InverseMoment.primeMark I lists
                (fun i q=>a i q*FourierBridge.logPhase (-t) (Real.log (y i q))))
              (InverseMoment.childLogTest wFresh t) Z D) u) := by
  obtain ⟨w,A,B,hA,hAB,hwc,hws,hfresh⟩ := exists_overlap_fresh I lo hi a₀ b₀ jlo jhi
    ha₀ hab hlo hhi hjlo hjhi
  refine ⟨w,A,B,hA,hAB,hwc,hws,?_⟩
  intro p hp hpmax hg F Ψ j u lists a y hy ha Z D yj hZ hj
  let := hpmax
  have he := original_overlap_input p hg hp F Ψ j u W a₀ b₀ ha₀ hs hW
    I lists a y hy w Z D yj hZ (hjlo.trans_le hj.1)
  convert he using 2
  apply congrArg (fun H:Finset ι→ℂ=>SecondPassArithmetic.inputConjugateRow p hg F Ψ j 1 1 H u)
  funext U
  exact (insert_original_fresh I lists a y lo hi W w a₀ b₀ jlo jhi hs ha
    (hfresh W hs) U yj (FirstPassCubeLabels.primeProductNorm p U/Z^D) hj
    (div_pos (FirstPassCubeLabels.primeProductNorm_pos p hp U)
      (Real.rpow_pos_of_pos hZ D))).symm

end SevenEighths.InverseInitialOverlapSource

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialUniformFresh -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialUniformFresh

theorem exists_uniform_fresh (K:ℕ)(a b:ℝ)(ha:0<a)(hab:a≤b):
    ∃(W:𝓢(ℝ,ℂ))(A B Bnorm:ℝ),0<A ∧ A≤B ∧ 0≤Bnorm ∧
      HasCompactSupport (W:ℝ→ℂ) ∧ tsupport (W:ℝ→ℂ)⊆Set.Icc A B ∧
      (∀x,‖W x‖≤Bnorm) ∧
      ∀{σ:Type*}[DecidableEq σ](I:Finset σ),I.card≤K→
      ∀(V:ℝ→ℂ),Function.support V⊆Set.Icc a b→
      ∀(y:σ→ℝ)(yj yc:ℝ),(∀i∈I,y i∈Set.Icc (1:ℝ) 2)→
        yj∈Set.Icc (1:ℝ) ((2:ℝ)^K)→0<yc→
        V (yj*yc/(∏i∈I,y i))≠0→W yc=1:=by
  let lo:=a/(2:ℝ)^K
  let hi:=lo+b*(2:ℝ)^K+1
  have hlo:0<lo:=by dsimp [lo];positivity
  have hb:0<b:=ha.trans_le hab
  obtain ⟨W,hWc,hWone,hWs⟩:=InverseSecondChildWindows.positive_cutoff lo hi hlo (by
    dsimp [hi]
    have hbp : 0<b*(2:ℝ)^K:=by positivity
    linarith)
  refine ⟨W,lo/2,hi+1,(SchwartzMap.seminorm ℝ 0 0) W,half_pos hlo,?_,by positivity,hWc,hWs,
    SchwartzMap.norm_le_seminorm ℝ W,?_⟩
  · dsimp [hi]
    have hbp : 0<b*(2:ℝ)^K:=by positivity
    linarith
  · intro σ dec I hI V hV y yj yc hy hj hc hn
    have hh:=InverseInitialOverlapFresh.overlap_column_interval I (fun _=>1) (fun _=>2) y
      a b 1 ((2:ℝ)^K) yj yc ha hab (by intros;norm_num) hy (by norm_num) hj hc (hV hn)
    simp only [Finset.prod_const,one_pow,mul_one,div_one] at hh
    apply hWone
    refine ⟨hh.1,?_⟩
    have hp:(2:ℝ)^I.card≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hI
    have hup:yc≤b*(2:ℝ)^K:=hh.2.trans (mul_le_mul_of_nonneg_left hp hb.le)
    dsimp [hi]
    linarith

end SevenEighths.InverseInitialUniformFresh

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

abbrev BlockIndex := Fin 4 → ℕ

def outerNorms (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Fin 4 → ℝ :=
  ![primeProductNorm p x.second.sourceCommon, primeProductNorm p x.second.divisor,
    primeProductNorm p x.second.overlap, ‖eisEmbedding x.second.frequency‖^2]

theorem outerNorms_eq_actual (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (Ψ : O →* ℂ) (m : O)
    (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    outerNorms p x i = secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) := by
  fin_cases i <;> simp [outerNorms,secondActualNorms,secondInheritedProfile,
    actualMarkedSecondProfileData,expansionProfileData,primeSubsetGenerator_norm_eq_productNorm]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem frequency_ne_zero_of_gate (a : O) (R : ℝ) {k : O}
    (hk : k ∈ nonzeroChildFrequencyBall a R) : k ≠ 0 :=
  (Finset.mem_erase.mp hk).1

theorem retained_frequency_ne_zero (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x ∈ retainedPool p pool parents R label residual j) : x.second.frequency ≠ 0 :=
  frequency_ne_zero_of_gate _ _ (retainedPool_original_support p pool parents R label residual j x hx).2.2.2

def dyadIndex (r : ℝ) : ℕ := ⌊Real.logb 2 r⌋₊
def dyadScale (n : ℕ) : ℝ := 2^n

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

def index (p : ι → O) {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : BlockIndex :=
  fun i => dyadIndex (outerNorms p x i)

def keys (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset BlockIndex :=
  source.image (index p)

def cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => index p x = d)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) :
    x ∈ cell p source d ↔ x ∈ source ∧ index p x = d := Finset.mem_filter

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem cell_inherits (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (P : MarkedSecondSource ι Jo Jn → Prop) (hP : ∀ x∈source,P x) :
    ∀ x∈cell p source d,P x := fun x hx => hP x (cell_subset p source d hx)

theorem cell_conditions (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) :
    ActualSecondSourceConditions p (cell p source d) := ActualSecondSourceConditions.mono p hs (cell_subset p source d)

omit [DecidableEq ι] in
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

omit [DecidableEq ι] in
theorem cells_disjoint (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {d e : BlockIndex} (h : d ≠ e) : Disjoint (cell p source d) (cell p source e) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (((mem_cell p source d x).mp hx).2.symm.trans ((mem_cell p source e x).mp hy).2)

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

omit [DecidableEq ι] in
theorem sum_cells (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    {β : Type*} [AddCommMonoid β] (f : MarkedSecondSource ι Jo Jn → β) :
    (∑ x∈source,f x) = ∑ d∈keys p source,∑ x∈cell p source d,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (index p) hx) f).symm

def scales (d : BlockIndex) : Fin 4 → ℝ := fun i => dyadScale (d i)

theorem actual_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i) / scales d i < 2 := by
  rw [←outerNorms_eq_actual p x Ψ m ray N M i]
  exact cell_ratios p hp source hk d x hx i

theorem physical_source_partition
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0 → Finset ι)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈source,(w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑ x∈cell p source d,(w x * actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) *
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x)
          a₁ a₂ W₁ W₂ Φ Y X) := by
  rw [sum_cells p source]
  exact Finset.mul_sum _ _ _

def capBox (A : Fin 4 → ℝ) (Z : ℝ) : Finset BlockIndex :=
  Fintype.piFinset (fun i => Finset.range (dyadIndex (Z^(A i))+1))

omit [DecidableEq ι] in
theorem keys_subset_capBox (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    keys p source ⊆ capBox A Z := by
  intro d hd
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hd
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (lt_of_lt_of_le zero_lt_one (outerNorms_ge_one p hp x (hk x hx) i)) (hcaps x hx i))

omit [DecidableEq ι] in
theorem keys_card_le_product (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (A : Fin 4 → ℝ) (Z : ℝ) (hcaps : ∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) :
    (keys p source).card ≤ ∏ i : Fin 4,(dyadIndex (Z^(A i))+1) := by
  have h := Finset.card_le_card (keys_subset_capBox p hp source hk A Z hcaps)
  simpa [capBox,Fintype.card_piFinset] using h

def capConstant (A : Fin 4 → ℝ) : ℝ := (∑ i,A i)/Real.log 2

theorem capConstant_nonneg (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    0 ≤ capConstant A := by
  unfold capConstant
  exact div_nonneg (Finset.sum_nonneg (fun i _ => hA i)) (Real.log_pos (by norm_num)).le

theorem cap_bin_bound (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) (Z : ℝ) (hZ : 2 ≤ Z)
    (i : Fin 4) : (dyadIndex (Z^(A i)) : ℝ)+1 ≤ 1+capConstant A*Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  have hZi : 1 ≤ Z^(A i) := Real.one_le_rpow (by linarith) (hA i)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hZi)
  have hAi : A i ≤ ∑ j,A j := Finset.single_le_sum (fun j _ => hA j) (Finset.mem_univ i)
  have hc := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAi
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le) (Real.log_nonneg (by linarith : 1 ≤ Z))
  dsimp [dyadIndex,capConstant]
  calc
    _ ≤ 1+Real.logb 2 (Z^(A i)) := by linarith
    _ = 1+(A i/Real.log 2)*Real.log Z := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hZ0,Real.logb]
      ring
    _ ≤ _ := by linarith

omit [DecidableEq ι] in
theorem keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
      (source : Finset (MarkedSecondSource ι Jo Jn)) (Z : ℝ), 2 ≤ Z →
      (∀ x∈source,x.second.frequency ≠ 0) →
      (∀ x∈source,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p source).card : ℝ) ≤ (1+C*Real.log Z)^4 := by
  refine ⟨capConstant A,capConstant_nonneg A hA,?_⟩
  intro p hp _ Jo Jn source Z hZ hk hcaps
  have h := keys_card_le_product p hp source hk A Z hcaps
  have hr : ((keys p source).card:ℝ) ≤ ∏ i : Fin 4,((dyadIndex (Z^(A i)):ℝ)+1) := by
    exact_mod_cast h
  apply hr.trans
  calc
    _ ≤ ∏ _i : Fin 4,(1+capConstant A*Real.log Z) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => cap_bin_bound A hA Z hZ i)
    _ = (1+capConstant A*Real.log Z)^4 := by simp

omit [DecidableEq ι] in
@[simp] theorem keys_empty (p : ι → O) (Jo Jn : ℕ) :
    keys p (∅ : Finset (MarkedSecondSource ι Jo Jn)) = ∅ := by simp [keys]

omit [DecidableEq ι] in
@[simp] theorem cell_empty (p : ι → O) (Jo Jn : ℕ) (d : BlockIndex) :
    cell p (∅ : Finset (MarkedSecondSource ι Jo Jn)) d = ∅ := by simp [cell]

omit [DecidableEq ι] in
theorem cell_empty_of_not_mem (p : ι → O) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (d : BlockIndex) (hd : d ∉ keys p source) :
    cell p source d = ∅ := by
  exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hd ((mem_keys_iff p source d).mpr h))

theorem retained_cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
    (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
    (residual : Finset ι) (j : κ) (d : BlockIndex) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈cell p (retainedPool p pool parents R label residual j) d)
    (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (N M : Finset ι) (i : Fin 4) :
    1 ≤ secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i ∧
    secondActualNorms p (secondInheritedProfile p x Ψ m ray) N M
      (Fin.castLE (by decide : 4 ≤ 6) i)/scales d i < 2 :=
  actual_cell_ratios p hp _ (retained_frequency_ne_zero p pool parents R label residual j)
    d x hx Ψ m ray N M i

theorem retained_keys_card_polynomial (A : Fin 4 → ℝ) (hA : ∀ i,0 ≤ A i) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → O) (_hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
      (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
      (R : SecondParentSource ι Jo → Finset ι → Finset ι → ℝ)
      (label : SecondParentSource ι Jo → Finset ι → SecondExpansionData ι → κ)
      (residual : Finset ι) (j : κ) (Z : ℝ), 2 ≤ Z →
      (∀ x∈retainedPool p pool parents R label residual j,∀ i,outerNorms p x i ≤ Z^(A i)) →
      ((keys p (retainedPool p pool parents R label residual j)).card:ℝ) ≤
        (1+C*Real.log Z)^4 := by
  obtain ⟨C,hC,h⟩ := keys_card_polynomial (ι:=ι) A hA
  refine ⟨C,hC,?_⟩
  intro p hp _ Jo pool parents R label residual j Z hZ hcaps
  exact h p hp _ Z hZ (retained_frequency_ne_zero p pool parents R label residual j) hcaps

end SevenEighths.InverseSecondSourceBlocks

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsCells -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev SourceIndex := Fin 6→ℕ

def sourceNorms {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ) : Fin 6→ℝ :=
  ![A₁ x,A₂ x,C x,‖eisEmbedding (d x)‖^2,R x,‖eisEmbedding (h x)‖^2]

def sourceIndex {κ : Type*} (q : κ→Fin 6→ℝ) (x : κ) : SourceIndex := fun i=>dyadIndex (q x i)
def sourceKeys {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) := S.image (sourceIndex q)
def sourceCell {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ) (k : SourceIndex) :=
  S.filter (fun x=>sourceIndex q x=k)

def commonKeys {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι) : Finset ℕ :=
  F.powerset.image (fun D=>dyadIndex (primeProductNorm p D))

def commonSelector {ι : Type*} [DecidableEq ι] (p : ι→O) (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) : ℂ :=
  if dyadIndex (primeProductNorm p D)=l then selector D else 0

def rawScales (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) : Fin 9→ℝ :=
  ![dyadScale (k 0),dyadScale (k 1),dyadScale (k 2),dyadScale (k 3),dyadScale (k 4),
    dyadScale l,dyadScale (k 5),T₁,T₂]

lemma rawScales_pos (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (h₁ : 0<T₁) (h₂ : 0<T₂) :
    ∀i,0< rawScales k l T₁ T₂ i := by
  intro i
  fin_cases i <;> first | exact dyadScale_pos _ | exact h₁ | exact h₂

lemma sourceNorms_ge_one {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ)
    (hA₁ : 1≤A₁ x) (hA₂ : 1≤A₂ x) (hC : 1≤C x) (hR : 1≤R x)
    (hd : d x≠0) (hh : h x≠0) : ∀i,1≤ sourceNorms A₁ A₂ C R d h x i := by
  intro i
  fin_cases i
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hd
  · exact hR
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hh

lemma sourceCell_ratios {κ : Type*} [DecidableEq κ] (q : κ→Fin 6→ℝ) (S : Finset κ)
    (hq : ∀x∈S,∀i,1≤q x i) (k : SourceIndex) (x : κ) (hx : x∈sourceCell q S k) (i : Fin 6) :
    q x i/dyadScale (k i)∈Set.Icc 1 2 := by
  obtain ⟨hxs,hindex⟩ := Finset.mem_filter.mp hx
  have hh := dyadIndex_bounds (q x i) (hq x hxs i)
  have he : dyadIndex (q x i)=k i := congrFun hindex i
  rw [he] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

theorem actual_original_cell_ratios {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (selector C₁ C₂ : κ→Finset ι→ℂ)
    (A₁ A₂ C R : κ→ℝ) (d h : κ→O)
    (hq : ∀x∈S,∀i,1≤ sourceNorms A₁ A₂ C R d h x i)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (x : κ)
    (hx : x∈sourceCell (sourceNorms A₁ A₂ C R d h) S k) (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j≠0) :
    ∀i,actualOuterRatios p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  have hl : dyadIndex (primeProductNorm p j.2.1)=l := by
    by_contra he
    exact hn (by simp [commonSelector,he])
  have hh := dyadIndex_bounds _ (SecondPassArithmetic.primeProductNorm_ge_one p hp j.2.1)
  rw [hl] at hh
  have hD : primeProductNorm p j.2.1/dyadScale l∈Set.Icc 1 2 :=
    ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
      (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩
  intro i
  fin_cases i
  · exact sourceCell_ratios _ S hq k x hx 0
  · exact sourceCell_ratios _ S hq k x hx 1
  · exact sourceCell_ratios _ S hq k x hx 2
  · exact sourceCell_ratios _ S hq k x hx 3
  · exact sourceCell_ratios _ S hq k x hx 4
  · exact hD
  · exact sourceCell_ratios _ S hq k x hx 5

lemma sum_source_cells {κ β : Type*} [DecidableEq κ] [AddCommMonoid β]
    (q : κ→Fin 6→ℝ) (S : Finset κ) (f : κ→β) :
    (∑x∈S,f x)=∑k∈sourceKeys q S,∑x∈sourceCell q S k,f x := by
  exact (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem (sourceIndex q) hx) f).symm

lemma common_key_of_index {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices F) :
    dyadIndex (primeProductNorm p j.2.1)∈commonKeys p F := by
  apply Finset.mem_image_of_mem
  exact (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1

lemma sum_common_cells {ι : Type*} [DecidableEq ι] (p : ι→O) (F : Finset ι)
    (selector : Finset ι→ℂ) (G : FirstCommonIndex ι→ℂ) :
    (∑j∈firstCommonIndices F,selector j.2.1*G j)=
      ∑l∈commonKeys p F,∑j∈firstCommonIndices F,commonSelector p selector l j.2.1*G j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hkey := common_key_of_index p F j hj
  simp [commonSelector,ite_mul,hkey]

theorem original_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈commonKeys p F,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈commonKeys p F,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_common_cells p F (selector x) (G x)
    _ = _ := Finset.sum_comm

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsLive -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex)
local notation "O" => ActualEisensteinCubic.O

def liveCommonKeys {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) : Finset ℕ :=
  (((S×ˢfirstCommonIndices F).filter (fun x=>selector x.1 x.2.2.1*G x.1 x.2≠0)).image
    (fun x=>dyadIndex (primeProductNorm p x.2.2.1)))

lemma sum_live_common_cells {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) (x : κ) (hx : x∈S) :
    (∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑l∈liveCommonKeys p F S selector G,∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : selector x j.2.1*G x j=0
  · rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    by_cases he : dyadIndex (primeProductNorm p j.2.1)=l
    · simpa only [commonSelector,he,ite_true] using hz
    · simp only [commonSelector,he,ite_false,zero_mul]
  · have hkey : dyadIndex (primeProductNorm p j.2.1)∈liveCommonKeys p F S selector G := by
      exact Finset.mem_image.mpr ⟨(x,j),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [commonSelector,ite_mul,hkey]

theorem original_live_signed_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j)=
      ∑k∈sourceKeys q S,∑l∈liveCommonKeys p F S selector G,∑x∈sourceCell q S k,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
  rw [sum_source_cells q S]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    _ = ∑x∈sourceCell q S k,∑l∈liveCommonKeys p F S selector G,
        ∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_live_common_cells p F S selector G x (Finset.mem_filter.mp hx).1
    _ = _ := Finset.sum_comm

theorem liveCommonKeys_card {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (F : Finset ι) (S : Finset κ) (selector : κ→Finset ι→ℂ)
    (G : κ→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices F,selector x j.2.1*G x j≠0 → primeProductNorm p j.2.1≤R) :
    (liveCommonKeys p F S selector G).card≤dyadIndex R+1 := by
  have hsub : liveCommonKeys p F S selector G⊆Finset.range (dyadIndex R+1) := by
    intro l hl
    obtain ⟨⟨x,j⟩,hmem,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hxj,hn⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hxj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (primeProductNorm_pos p hp _) (hcap x hx j hj hn))
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem original_live_norm_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) (F : Finset ι) (S : Finset κ) (q : κ→Fin 6→ℝ)
    (selector : κ→Finset ι→ℂ) (G : κ→FirstCommonIndex ι→ℂ) :
    ‖∑x∈S,∑j∈firstCommonIndices F,selector x j.2.1*G x j‖≤
      ∑k∈sourceKeys q S,∑l∈liveCommonKeys p F S selector G,
        ‖∑x∈sourceCell q S k,∑j∈firstCommonIndices F,commonSelector p (selector x) l j.2.1*G x j‖ := by
  rw [original_live_signed_partition p F S q selector G]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk=>norm_sum_le _ _))

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsPhysical -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment InverseMomentFirstProfileUniform ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadScale dyadScale_pos)
local notation "O" => ActualEisensteinCubic.O

def columnScales (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) : Fin 9→ℝ :=
  rawScales k l (X₁/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X₂/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma columnScales_pos (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) :
    ∀i,0<columnScales k l X₁ X₂ i := by
  apply rawScales_pos
  · exact div_pos h₁ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos h₂ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma columnScales_left (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) :
    let s := columnScales k l X₁ X₂
    s 0*s 2*s 5*s 7=X₁ := by
  dsimp [columnScales,rawScales]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (dyadScale_pos _).ne' (dyadScale_pos _).ne') (dyadScale_pos _).ne')

lemma columnScales_right (k : SourceIndex) (l : ℕ) (X₁ X₂ : ℝ) :
    let s := columnScales k l X₁ X₂
    s 1*s 2*s 5*s 8=X₂ := by
  dsimp [columnScales,rawScales]
  exact mul_div_cancel₀ _ (mul_ne_zero (mul_ne_zero (dyadScale_pos _).ne' (dyadScale_pos _).ne') (dyadScale_pos _).ne')

lemma physical_scales_congr {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s t : Fin 9→ℝ)
    (hleft : s 0*s 2*s 5*s 7=t 0*t 2*t 5*t 7)
    (hright : s 1*s 2*s 5*s 8=t 1*t 2*t 5*t 8) :
    firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h t := by
  unfold firstFamilyPhysicalRows
  rw [hleft,hright]

theorem original_physical_partition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      ∑k∈sourceKeys (sourceNorms A₁ A₂ C R d h) S,∑l∈commonKeys p F,
        firstFamilyPhysicalRows p hg (sourceCell (sourceNorms A₁ A₂ C R d h) S k) F
          (fun x=>commonSelector p (selector x) l) C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s := by
  let G (x : κ) (j : FirstCommonIndex ι) := w x*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j*
    firstNormProfile (fun y=>W₁ (y/(s 0*s 2*s 5*s 7)))
      (fun y=>W₂ (y/(s 1*s 2*s 5*s 8))) Φ (fun _ _=>1) K
      (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j)
  have rows (T : Finset κ) (sel : κ → Finset ι → ℂ) :
      firstFamilyPhysicalRows p hg T F sel C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s =
        ∑ x ∈ T, ∑ j ∈ firstCommonIndices F, sel x j.2.1 * G x j := by
    unfold firstFamilyPhysicalRows firstBlockedPhysicalRows
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [G]
    ring
  have he := original_signed_partition p F S (sourceNorms A₁ A₂ C R d h) selector G
  simpa only [rows] using he

theorem original_physical_partition_raw {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (S : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      ∑k∈sourceKeys (sourceNorms A₁ A₂ C R d h) S,∑l∈commonKeys p F,
        firstFamilyPhysicalRows p hg (sourceCell (sourceNorms A₁ A₂ C R d h) S k) F
          (fun x=>commonSelector p (selector x) l) C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h
          (columnScales k l (s 0*s 2*s 5*s 7) (s 1*s 2*s 5*s 8)) := by
  rw [original_physical_partition p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  apply physical_scales_congr
  · exact (columnScales_left k l _ _).symm
  · exact (columnScales_right k l _ _).symm

end SevenEighths.InverseMomentFirstChildWindows
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileData -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight FourierBridge
local notation "O" => ActualEisensteinCubic.O
abbrev OriginalIndex (ι : Type*) := Σ _ : FirstOriginalOuter ι,Ideal O×O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def leftNorm (x : OriginalIndex ι) : ℝ := ‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2
def rightNorm (x : OriginalIndex ι) : ℝ := ‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2
def commonNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p x.1.2.1
def activeNorm (x : OriginalIndex ι) : ℝ := primeProductNorm p (cubeActiveSupport x.1.1.support
  (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)
def divisorElement (k : FirstOriginalOuter ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2

include hp in
theorem original_source_positive (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      0<leftNorm p x ∧ 0< rightNorm p x ∧ 0<commonNorm p x ∧ 0<activeNorm p x ∧
      divisorElement p x.1≠0 ∧ x.2.2≠0 := by
  intro x hx
  have hm := (Finset.mem_sigma.mp hx).2
  have hk := ((mem_firstRetainedSource p labels x.1.1 Y x.2).mp hm).2
  refine ⟨?_,?_,primeProductNorm_pos p hp _,primeProductNorm_pos p hp _,?_,(Finset.mem_erase.mp hk).1⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact primeSubsetGenerator_ne_zero _ _

include hp in
theorem original_source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      ∀i,1≤InverseMomentFirstChildWindows.sourceNorms (leftNorm p) (rightNorm p) (commonNorm p)
        (activeNorm p) (fun x=>divisorElement p x.1) (fun x=>x.2.2) x i := by
  intro x hx
  have hh := original_source_positive p hp pool Q labels Y x hx
  apply InverseMomentFirstChildWindows.sourceNorms_ge_one
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_weight_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Γ Y : ℝ)
    (hΓ : 0≤Γ) (hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ) :
    ∀k∈firstOriginalOuter pool Q,∀x∈firstRetainedSource p labels k.1 Y,
      ‖firstOriginalWeight p β R k x‖≤Γ^2 := by
  intro k hk x hx
  have hb := (mem_firstOriginalOuter pool Q k).mp hk
  have hf := ((mem_firstRetainedSource p labels k.1 Y x).mp hx).1
  exact (firstOriginalWeight_norm_le p β R k x).trans
    (reopenedPairCoefficient_bound Q labels β Γ hΓ hβ k.1 hb.1 k.2.1 x.1 hf)

theorem actual_old_profile (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om⊆Set.Icc a b) (theta x : ℝ) (hx : 0<x) :
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs false) 1 theta x=
      normTwistedSource om theta x ∧
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs true) 1 (-theta) x=
      star (normTwistedSource om theta x) := by
  constructor
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      CubicReflectionKernel.logSchwartz_apply,Real.exp_log hx,normTwistedSource]
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      SecondPassIntegration.conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,
      Real.exp_log hx,normTwistedSource,SecondPassIntegration.logPhase_conjugate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileIdentity -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open CompletedHeight FourierBridge
open InverseMomentFirstProfileUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
lemma physical_rows_congr_positive (F : Finset ι) (selector C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O)
    (hA₁ : 0<A₁) (hA₂ : 0<A₂) (hC : 0<C)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstBlockedPhysicalRows p hg F selector C₁ C₂ V₁ V₂ Φ A₁ A₂ C R K d h := by
  unfold firstBlockedPhysicalRows
  apply Finset.sum_congr rfl
  intro j hj
  have he₁ := h₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1)
    (mul_pos (mul_pos (mul_pos hA₁ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  have he₂ := h₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2)
    (mul_pos (mul_pos (mul_pos hA₂ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  simp [firstNormProfile,firstCommonNorms,he₁,he₂]

include hp in
lemma physical_family_congr_positive (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg S F selector C₁ C₂ w V₁ V₂ Φ A₁ A₂ C R K d h s := by
  unfold firstFamilyPhysicalRows
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact physical_rows_congr_positive p hp hg F (selector x) (C₁ x) (C₂ x) _ _ _ _ Φ
    (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x) (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2
    (fun y hy=>h₁ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))))
    (fun y hy=>h₂ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))))

include hp in

theorem original_family_profiles (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K X theta : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (hX : 0<X) (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X)))
      (fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)) Φ A₁ A₂ C R K d h s=
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ A₁ A₂ C R K d h s := by
  apply physical_family_congr_positive p hp hg S F selector C₁ C₂ w _ _ _ _ Φ A₁ A₂ C R K d h s hs hpos
  · intro y hy
    rw [hleft,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).2.symm
  · intro y hy
    rw [hright,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).1.symm

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCells -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def originalNorms (x : OriginalIndex ι) : Fin 6→ℝ :=
  sourceNorms (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) x

def originalOuterCell (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    Finset (FirstOriginalOuter ι) :=
  (firstOriginalOuter pool Q).filter (fun x=>∀i:Fin 5,
    dyadIndex (originalNorms p ⟨x,(1,1)⟩ i.castSucc)=k i.castSucc)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_outer (x : OriginalIndex ι) (i : Fin 5) :
    originalNorms p ⟨x.1,(1,1)⟩ i.castSucc=originalNorms p x i.castSucc := by
  unfold originalNorms sourceNorms
  fin_cases i <;> simp [Fin.castSucc,leftNorm,rightNorm,commonNorm,activeNorm]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem original_cell_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex) :
    sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k ⊆
    firstGlobalRetainedSource p (originalOuterCell p pool Q k) (fun _=>labels) (fun x=>x.1) Y := by
  intro x hx
  obtain ⟨hxs,hk⟩ := Finset.mem_filter.mp hx
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxs
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_filter.mpr ⟨ho,?_⟩,hf⟩
  intro i
  rw [originalNorms_outer p x i]
  exact congrFun hk i.castSucc

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_outer_cell_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k⊆firstOriginalOuter pool Q := Finset.filter_subset _ _

theorem original_outer_cell_ratios (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (x : FirstOriginalOuter ι) (hx : x∈originalOuterCell p pool Q k) (i : Fin 5) :
    originalNorms p ⟨x,(1,1)⟩ i.castSucc/dyadScale (k i.castSucc)∈Set.Icc 1 2 := by
  have hnorm : ∀j:Fin 6,1≤originalNorms p ⟨x,(1,1)⟩ j := by
    apply sourceNorms_ge_one
    · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
    · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
    · exact primeSubsetGenerator_ne_zero _ _
    · exact one_ne_zero
  have hh := dyadIndex_bounds _ (hnorm i.castSucc)
  rw [(Finset.mem_filter.mp hx).2 i] at hh
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hh.1),
    (div_le_iff₀ (dyadScale_pos _)).mpr hh.2.le⟩

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileAssembly -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def coefficient (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (negative : Bool)
    (x : OriginalIndex ι) : Finset ι→ℂ :=
  firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 negative Ψ m (divisorElement p x.1)
    (mark (if negative then x.1.1.rightExponent else x.1.1.leftExponent)) x.2

def weight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (x : OriginalIndex ι) : ℂ :=
  retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
    (divisorElement p x.1) (firstOriginalWeight p β R x.1) x.2

def sourceSummand (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) : ℂ :=
  weight p hp hcop hg β R Ψ m x *
    firstCommonWeight p hg (coefficient p hp hcop hg Ψ m mark true x)
      (coefficient p hp hcop hg Ψ m mark false x) x.2.2 j *
    firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)

theorem original_retained_sum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y,
        ∑j∈firstCommonIndices pool,sourceSummand p hp hcop hg β R Ψ m mark W Φ K x j := by
  have hleft : s 0*s 2*s 5*s 7≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))
  simp only [originalRetainedFamily,firstFamilyPhysicalRows,firstBlockedPhysicalRows,
    Finset.mul_sum,sourceSummand,weight,coefficient,leftNorm,rightNorm,commonNorm,activeNorm,divisorElement,
    Bool.false_eq_true,ite_true,ite_false,one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hleft,mul_div_cancel₀ _ hright]
  ring

theorem original_retained_cell_partition (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β R Ψ m mark W Φ K
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑k∈sourceKeys (originalNorms p) source,∑l∈liveCommonKeys p pool source (fun _ _=>1) term,
        ∑x∈sourceCell (originalNorms p) source k,∑j∈firstCommonIndices pool,
          commonSelector p (fun _=>1) l j.2.1*term x j := by
  intro source term
  rw [original_retained_sum p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s hs]
  simpa only [one_mul] using original_live_signed_partition p pool source (originalNorms p) (fun _ _=>1) term

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstLiveCaps -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma factor_four_bound (a b c d L:ℝ)(ha:1≤a)(hb:1≤b)(hc:1≤ c)(hd:1≤d)
    (h:a*b*c*d≤L): a≤L ∧ b≤L ∧ c≤L ∧ d≤L:=by
  have ha0:0≤a:=zero_le_one.trans ha
  have hb0:0≤b:=zero_le_one.trans hb
  have hc0:0≤ c:=zero_le_one.trans hc
  have hd0:0≤d:=zero_le_one.trans hd
  have hab:1≤a*b:=ha.trans (le_mul_of_one_le_right ha0 hb)
  have habc:1≤a*b*c:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc)
  have habd:1≤a*b*d:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hd)
  have ha':a≤a*b*c*d:=by
    calc
      a≤a*b:=le_mul_of_one_le_right ha0 hb
      _≤a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hb':b≤a*b*c*d:=by
    calc
      b≤a*b:=le_mul_of_one_le_left hb0 ha
      _≤a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hc':c≤a*b*c*d:=by
    calc
      c≤a*b*c:=le_mul_of_one_le_left hc0 hab
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  exact ⟨ha'.trans h,hb'.trans h,hc'.trans h,(le_mul_of_one_le_left hd0 habc).trans h⟩

theorem first_profile_live_factors (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤q i)(hW:∀x,W x≠0→x≤L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0≤L ∧ q 1≤L ∧ q 2≤L ∧ q 5≤L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have hb₁:=factor_four_bound (q 0) (q 2) (q 5) (q 7) L (hq _) (hq _) (hq _) (hq _) (hW _ h₁)
  have hb₂:=factor_four_bound (q 1) (q 2) (q 5) (q 8) L (hq _) (hq _) (hq _) (hq _) (hW _ h₂)
  exact ⟨hb₁.1,hb₂.1,hb₁.2.1,hb₁.2.2.1⟩

variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_profile_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)
    (hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    leftNorm p x≤L ∧ rightNorm p x≤L ∧ commonNorm p x≤L ∧ primeProductNorm p j.2.1≤L:=by
  have hq:∀i,1≤firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hz
    exact hn (by unfold sourceSummand;rw [hz,mul_zero])
  exact first_profile_live_factors W Φ K L _ hq hW hprof

end SevenEighths.InverseMomentFirstLiveCaps

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileScales -/

section

namespace OAI

noncomputable section
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows InverseSecondSourceBlocks

def physicalScales (X : ℝ) (k : SourceIndex) (l : ℕ) : Fin 9→ℝ :=
  rawScales k l (X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))
    (X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))

lemma physicalScales_pos (X : ℝ) (hX : 0<X) (k : SourceIndex) (l : ℕ) :
    ∀i,0<physicalScales X k l i := by
  apply rawScales_pos
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma physicalScales_products (X : ℝ) (k : SourceIndex) (l : ℕ) :
    physicalScales X k l 0*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 7=X ∧
    physicalScales X k l 1*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 8=X := by
  constructor
  · change (dyadScale (k 0)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))
  · change (dyadScale (k 1)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))

theorem physicalScales_rpow (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    physicalScales (Z^r) k l=fun i=>Z^(![Real.logb Z (dyadScale (k 0)),
      Real.logb Z (dyadScale (k 1)),Real.logb Z (dyadScale (k 2)),
      Real.logb Z (dyadScale (k 3)),Real.logb Z (dyadScale (k 4)),Real.logb Z (dyadScale l),
      Real.logb Z (dyadScale (k 5)),
      r-Real.logb Z (dyadScale (k 0))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l),
      r-Real.logb Z (dyadScale (k 1))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l)] i) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he (n : ℕ) : Z^(Real.logb Z (dyadScale n))=dyadScale n :=
    Real.rpow_logb hz (ne_of_gt hZ) (dyadScale_pos n)
  funext i
  fin_cases i <;> simp [physicalScales,rawScales,he,Real.rpow_sub hz,div_div]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

