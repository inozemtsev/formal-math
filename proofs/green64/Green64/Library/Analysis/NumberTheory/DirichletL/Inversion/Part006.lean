module

public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalReassembly
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part003

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part006

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalLimit -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalLimit
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialPhysicalReassembly
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def physicalFrequency (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(h:O):ℂ:=
  ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
    if Disjoint U T then ∑E∈G.powerset,
      initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0

theorem physicalFrequency_finite
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m:=by
  rw [←finite_physical_reassembly p hp hcop hg hinj]
  unfold physicalFrequency
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    exact Finset.sum_comm
  · simp only [hd,ite_false,Finset.sum_const_zero]

theorem physicalFrequency_hasSum
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    HasSum (physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m)
      (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,∑'h:O,
          initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0):=by
  unfold physicalFrequency
  apply hasSum_sum
  intro G hG
  apply hasSum_sum
  intro U hU
  apply hasSum_sum
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    apply hasSum_sum
    intro E hE
    exact (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j marks W Φ hZ D m
      G U T E
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hd).hasSum
  · simpa only [hd,ite_false] using (hasSum_zero : HasSum (fun _ : O=>(0:ℂ)) 0)

theorem original_input_zero_nonzero
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    (∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg pool Ψ j 1 1
        (initialTest p marks W Z D) u‖^2:ℝ))=
    physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m 0+
      ∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
  rw [initial_input_physical p hp hcop hg hinj hc hpr pool Ψ j marks W Φ hZ D m]
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  rw [←hs.tsum_eq]
  exact hs.summable.tsum_eq_add_tsum_ite 0

theorem nonzero_frequency_norm_le
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m B:ℝ)(hZ:0<Z)
    (hfinite:∀freqT:Finset O,(0:O)∉freqT→
      ‖physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
        (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m‖≤B):
    ‖∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h‖≤B:=by
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  have hs0:Summable (fun h:O=>if h=0 then (0:ℂ) else
      physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h):=by
    apply (hs.summable.indicator {h:O|h≠0}).congr
    intro h
    by_cases he:h=0 <;> simp [Set.indicator,he]
  apply InverseInitialHighFrequencyTail.norm_tsum_of_finite_bound _ hs0
  intro T
  let freqT:=T.filter (fun h:O=>h≠0)
  have hzero:(0:O)∉freqT:=by simp [freqT]
  have he:(∑h∈T,if h=0 then (0:ℂ) else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
      ∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
    simp only [freqT,Finset.sum_filter,ite_not]
  rw [he,physicalFrequency_finite p hp hcop hg hinj]
  exact hfinite freqT hzero

end SevenEighths.InverseInitialPhysicalLimit

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSupport -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialRetainedSupport
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem live_cutoffs (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    W₁ (coordinates p x 0*coordinates p x 2*coordinates p x 4/Z^D)≠0 ∧
    W₂ (coordinates p x 0*coordinates p x 2*coordinates p x 5/Z^D)≠0 := by
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ] at hne
  have hk:= (mul_ne_zero_iff.mp hne).2
  unfold physicalKernel at hk
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).2⟩

theorem live_whole_columns (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0*coordinates p x 2*coordinates p x 4≤b*Z^D ∧
    coordinates p x 0*coordinates p x 2*coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_cutoffs p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ hne
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₁ h₁),
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₂ h₂)⟩

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem ideal_coordinates_one (x:Point ι):
    1≤ coordinates p x 0 ∧ 1≤ coordinates p x 1 ∧ 1≤ coordinates p x 2 ∧
    1≤ coordinates p x 4 ∧ 1≤ coordinates p x 5 := by
  have hi (S:Finset ι):(1:ℝ)≤((sourceIdeal p S).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp S))
  exact ⟨hi _,hi _,hi _,hi _,hi _⟩

theorem live_ideal_caps (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0≤b*Z^D ∧ coordinates p x 1≤b*Z^D ∧
    coordinates p x 2≤b*Z^D ∧ coordinates p x 4≤b*Z^D ∧
    coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_whole_columns p hp hcop hg hpr Ψ j σ W₁ W₂ Φ
    Z D m b hZ hs₁ hs₂ x hx ρ hne
  obtain ⟨hC,hd,hs,hn₁,hn₂⟩:=ideal_coordinates_one p hp x
  have hpair:1≤ coordinates p x 0*coordinates p x 2:=by nlinarith
  have hcp:coordinates p x 0≤ coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_right (by linarith) hs
  have hsp:coordinates p x 2≤ coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_left (by linarith) hC
  have hbig:coordinates p x 0*coordinates p x 2≤b*Z^D:=
    (le_mul_of_one_le_right (by positivity) hn₁).trans h₁
  have hdiv:coordinates p x 1≤ coordinates p x 0:=by
    change ((sourceIdeal p x.divisor).absNorm:ℝ)≤(sourceIdeal p x.common).absNorm
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)))
      (map_dvd Ideal.absNorm (sourceIdeal_dvd p _ _ hx.divisor_subset))
  exact ⟨hcp.trans hbig,hdiv.trans (hcp.trans hbig),hsp.trans hbig,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₁,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₂⟩

end SevenEighths.InverseInitialRetainedSupport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

def principalWindow (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t)
  else uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

theorem principalWindow_seminorm_zero (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (principalWindow om a b ha hs negative t)=
      SchwartzMap.seminorm ℝ 0 0 om := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ om x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ (principalWindow om a b ha hs negative t) x

theorem principalWindow_upper (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (M : ℝ) (hb : b≤Real.exp M)
    (negative : Bool) (t x : ℝ) (hx : principalWindow om a b ha hs negative t x≠0) :
    x≤Real.exp M := by
  have hmem : x∈Function.support om := by
    rw [←principalWindow_support om a b ha hs negative t]
    exact hx
  exact (hs hmem).2.trans hb

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0)

include hp in

theorem whole_columnLog (D U : Finset ι) (hDU : Disjoint D U) (X : ℝ) :
    columnLog p (primeProductNorm p D*X) (D∪U)=Real.log (primeProductNorm p U/X) := by
  unfold columnLog
  rw [primeProductNorm_union p D U hDU,
    mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']

omit [DecidableEq σ] in

theorem primeMark_union_of_lists_disjoint (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D) :
    primeMark slots lists coeff (D∪U)=primeMark slots lists coeff U := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.disjoint_left.mp (hD i hi) hk
  simp only [Finset.mem_union,hh,false_or]

include hp in

theorem firstCoreTest_markedRadial (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι) (hDU : Disjoint D U)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) :
    firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D U =
    markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X U := by
  have ht : ∀ y : ℝ,logPhase (-t) (-y)=logPhase t y := by
    intro y
    unfold logPhase
    congr 1
    push_cast
    ring
  simp only [firstCoreTest,primeMark_union_of_lists_disjoint slots lists coeff D U hD,
    whole_columnLog p hp D U hDU X,ht,
    Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),
    markedRadial,Finset.empty_union,principalWindow]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,star_mul] <;> ring

variable [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem secondInputCoefficient_overlap_zero
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (D U : Finset ι)
    (hDU : ¬Disjoint D U) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d H U=0 := by
  rw [secondInputCoefficient_fixed_mask (p := p) (hg := hg),commonProduct_mask p hg hinj]
  split_ifs with h
  · exact (hDU h.symm).elim
  · exact zero_mul _

include hp in

theorem firstCoreTest_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) (Ψ : Eis→*ℂ) (m c d : Eis) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) U =
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X) U := by
  by_cases hd : Disjoint D U
  · unfold secondInputCoefficient
    rw [firstCoreTest_markedRadial p hp slots lists coeff D U hd hD om a b ha hs negative X t hX]
  · rw [secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd,
      secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd]

omit [DecidableEq ι] in

theorem input_diagonal (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * star (H U) * H U =
      ((‖secondInputCoefficient p hg Ψ m c d H U‖^2 : ℝ) : ℂ) := by
  have he : secondInputCoefficient p hg Ψ m c d H U =
      secondInputCoefficient p hg Ψ m c d (fun _=>1) U * H U := by
    simp only [secondInputCoefficient,mul_one]
  have hh : star (H U)*H U=((‖H U‖^2 : ℝ):ℂ) := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [he,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,hh]

omit [DecidableEq ι] in
theorem input_norm_product (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * ‖H U‖^2 =
      ‖secondInputCoefficient p hg Ψ m c d H U‖^2 := by
  simp only [secondInputCoefficient,mul_one,norm_mul,mul_pow]

omit [DecidableEq ι] in

theorem zero_congr_input (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis)
    (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (K : Finset ι→Finset ι→Finset Eis) :
    truncatedSecondZero p hg F Ψ m c d H₁ W Y K=
      truncatedSecondZero p hg F Ψ m c d H₂ W Y K := by
  simp only [truncatedSecondZero,input_diagonal,he]

include hp in

theorem restoration_congr_input
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis) (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (θ : Finset ι→Finset ι→Eis→ℂ) :
    principalRestoration p hg hinj hp F Ψ m c d H₁ W Y θ=
      principalRestoration p hg hinj hp F Ψ m c d H₂ W Y θ := by
  unfold principalRestoration
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro k
  congr 1
  simp only [restorationTerm_eq,←Complex.ofReal_mul,input_norm_product,he]

include hp in

theorem firstCoreInputRow_principal_test
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t : ℝ) (hX : 0<X) (c d : Eis) (r : FirstCoreIndex) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m (primeMark slots lists coeff)
      (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z =
    inputConjugateRow p hg F (firstCoreTwist negative χ Ψ r)
      ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X)
      (if negative then -z else z) := by
  rw [firstCoreInputRow_fixed_pool p hg hinj]
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro U hU
  rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]

include hp in

theorem firstFreshSecondPoisson_markedRadial
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ₀ m₀ c₀ d H₀ G U V *
          maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  intro H₀ Ψ₀ m₀ c₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  have he (z : Eis) : inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z=
      inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z := by
    unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
    apply Finset.sum_congr rfl
    intro U hU
    rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
  calc
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z‖^2 : ℝ) := by
      rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
        (primeMark slots lists coeff) om X c d r t Y hY]
      exact (inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H
        rowMajorant Y hY).symm
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z‖^2 : ℝ) := by simp_rw [he]
    _ = _ := inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀
      rowMajorant Y hY

theorem residual_lists_pairwise (slots J : Finset σ) (lists : σ→Finset ι) (A D : Finset ι)
    (h : (slots : Set σ).PairwiseDisjoint lists) :
    ((slots\J : Finset σ) : Set σ).PairwiseDisjoint (fun i=>lists i\(A∪D)) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe,Finset.mem_sdiff] at hi hj
  exact (h hi.1 hj.1 hij).mono
    Finset.sdiff_subset Finset.sdiff_subset

omit [DecidableEq σ] in
theorem residual_lists_avoid (lists : σ→Finset ι) (A D : Finset ι) (i : σ) :
    Disjoint (lists i\(A∪D)) D := by
  apply Finset.disjoint_left.mpr
  intro k hk hkd
  exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_union_right A hkd)

theorem residual_coeff_bound (slots J : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (A D : Finset ι)
    (h : ∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) :
    ∀ i∈slots\J,∀ k∈lists i\(A∪D),‖coeff i k‖≤1 := by
  intro i hi k hk
  exact h i (Finset.mem_sdiff.mp hi).1 k (Finset.mem_sdiff.mp hk).1

end Arithmetic

theorem firstCore_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := physical_child_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d hd V W X M Y R
    hX hY hR (principalWindow_upper om a b ha hs M hb negative t)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

theorem priority_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots J : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) coeff)
        (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := firstCore_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots J lists coeff hslots hcoeff F D B A v ε₁ ε₂
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR
  exact hbound p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) coeff
    (residual_lists_pairwise slots J lists A D hslots)
    (residual_coeff_bound slots J lists coeff A D hcoeff) F D B v ε₁ ε₂
    (fun i _=>residual_lists_avoid lists A D i) negative χ Ψ hΨ m c d hd r om W a b ha hs
    M t X Y R hb hX hY hR

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondMarkedTail -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy InverseSecondPrincipalCaller
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem marked_radial_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V : 𝓢(ℝ,ℂ)) (X M : ℝ), 0 < X →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      ∀ U, ‖markedRadial p slots lists a A V X U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A V X M hX hV U
  by_cases hz : V (primeProductNorm p U/X) = 0
  · simp only [markedRadial,hz,mul_zero,norm_zero]
    positivity
  · have hn : primeProductNorm p U ≤ X*Real.exp M := by
      simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hz)
    have hn0 : 0 ≤ primeProductNorm p U := (primeProductNorm_pos p hp U).le
    rw [markedRadial,norm_mul]
    apply (mul_le_mul (hmark p hp hcop slots lists a hslots ha A U)
      (V.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem full_marked_second_tail (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V W : 𝓢(ℝ,ℂ)) (X M Y H R : ℝ),
      0 < X → 0 < Y → 0 ≤ H → 1 ≤ X*Real.exp M →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      wholeSecondRadius d (X*Real.exp M) Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (fun _ E => childFrequencyBall (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*(X*Real.exp M))^4 *
          (((2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
              (1+(X*Real.exp M)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_whole_column_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha A V W X M Y H R hX hY hH hL hV hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d hd (markedRadial p slots lists a A V X) W
    _ Y H (X*Real.exp M) R (by positivity) hY hH hL
  · exact hmark p hp hcop slots lists a hslots ha A V X M hX hV
  · exact markedRadial_support p slots lists a A V X M hX hV
  · exact hR

end
end SevenEighths.InverseMoment

end OAI

end

