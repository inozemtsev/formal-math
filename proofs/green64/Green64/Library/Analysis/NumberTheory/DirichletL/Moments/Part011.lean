module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Hecke.Part005
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part009

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Moments / Part011

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformDivisorShell -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def ShellBound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε:ℝ) : Prop := ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2)

theorem uniform_subset_shell {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,ShellBound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ ShellBound p.1 p.2 C ε:=
    paired_all_active_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD T Z hT hZ hlo hhi
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD T Z hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1<Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=>logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>logWindow_nonneg _ _)

theorem paired_entrance_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L)
      (lo hi:ι→ℝ), (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((∑i,logWindow (lo i) (hi i))/Real.log Z) := by
  obtain ⟨C,hC,hbound⟩:=uniform_subset_shell (ι:=ι) ε hε
  refine ⟨C,hC,?_⟩
  intro J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  apply (hbound J L s v Ds hD T Z hT hZ hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hs:=subset_allowance J s lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v lo hi hvlo hvhi Z hZ
  linarith

theorem numerical_allowance (Z H:ℝ) (hZ:1<Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

theorem paired_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤C*Z^δ := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:2*B*ε≤δ:=by
    have hh:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=paired_entrance_allowance (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD T Z hT hZ hTZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hh:=hbound J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  rw [numerical_allowance Z _ hZ,Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le] at hh
  have hpow:T^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  apply hh.trans
  calc
    C*(2^(2*ε)*T^(2*ε))*E=(C*2^(2*ε)*E)*T^(2*ε):=by ring
    _≤(C*2^(2*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hpow (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformDivisorShell

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.EligibleEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => ActualEisensteinCubic.O

structure Data (ι:Type*) [Fintype ι] extends Source ι where
  M : ι→ℝ
  M_ge_one : ∀i,1≤M i
  coefficient_bound : ∀i,∀I∈slots i,‖ν i I*W i ((Ideal.absNorm I:ℝ)/P i)‖≤M i
  b₁ : ℝ
  b₂ : ℝ
  support₁ : Function.support W₁⊆Set.Iic b₁
  support₂ : Function.support W₂⊆Set.Iic b₂
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : Y₁*Y₂=X₁*X₂
  rows : Finset O
  weight : O→ℝ
  weight_nonneg : ∀z∈rows,0≤weight z

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Data.coefficient (s:Data ι) (i:ι) (I:Ideal O) : ℂ :=
  s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)

def Data.energy (s:Data ι) (D:Ideal O) : ℝ :=
  ∑z∈s.rows,s.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def Data.childEnergy (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑z∈s.rows,s.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

def Data.profileFactor (s:Data ι) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2

lemma Data.energy_nonneg (s:Data ι) (D:Ideal O) : 0≤ s.energy D :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (sq_nonneg _))

lemma Data.child_nonneg (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤ s.childEnergy D a :=
  Finset.sum_nonneg (fun z hz=>mul_nonneg (s.weight_nonneg z hz) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤ s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0<formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      s.energy D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s D hD E hE hchild
  have hh:=hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D hD s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product s.rows s.weight s.weight_nonneg
  change s.energy D≤_ at hh
  apply hh.trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      apply mul_le_mul _ (hchild a ha) (s.child_nonneg D a) _
      · apply div_le_div_of_nonneg_right _ (s.reduction_pos D a).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
      · exact div_nonneg s.profile_nonneg (s.reduction_pos D a).le
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma sqrt_sum_le {α:Type*} (S:Finset α) (f:α→ℝ) (hf:∀a∈S,0≤f a) :
    Real.sqrt (∑a∈S,f a)≤∑a∈S,Real.sqrt (f a) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun a _=>Real.sqrt_nonneg _),?_⟩
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun a=>Real.sqrt (f a))
    (fun a _=>Real.sqrt_nonneg _)
  have he:(∑a∈S,Real.sqrt (f a)^2)=∑a∈S,f a:=Finset.sum_congr rfl (fun a ha=>Real.sq_sqrt (hf a ha))
  rwa [he] at hh

lemma sqrt_reciprocal (x:ℝ) (_hx:0<x) : Real.sqrt (1/x)=1/Real.sqrt x := by
  rw [Real.sqrt_div (by norm_num:0≤(1:ℝ)),Real.sqrt_one]

theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤E) →
      Real.sqrt (s.energy D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤ s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentEligibleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ExceptionalAllocationShell -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentExceptionalAllocationShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
open CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O

lemma exact_max_cancellation (r r₁ : ℝ) :
    -r₁-max (r-r₁) 0 = -max r r₁ := by
  by_cases h : r ≤ r₁
  · rw [max_eq_right (by linarith : r-r₁≤0),max_eq_right h]
    ring
  · rw [max_eq_left (by linarith : 0≤ r-r₁),max_eq_left (le_of_not_ge h)]
    ring

def exceptionalWeight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2))) (Z r : ℝ) : ℝ :=
  Z^(-Real.logb Z (formalReductionFactor D a s.P)-
    Real.logb Z (formalReductionFactor D b v.P)-
    max (r-Real.logb Z (formalReductionFactor D a s.P)) 0)

theorem active_exceptional_weight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (s : Source ι) (v : Source κ) (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ⊕Fin 2)))
    (_ha : a∈s.active D) (hb : b∈v.active D) (Z r : ℝ) (hZ : 1<Z) :
    exceptionalWeight s v D a b Z r ≤ Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : (0:ℝ)<Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hv := v.active_boundary D hD b hb Z hZ
  have hm := exact_max_cancellation r (Real.logb Z (formalReductionFactor D a s.P))
  have he : -Real.logb Z (formalReductionFactor D a s.P)-
      Real.logb Z (formalReductionFactor D b v.P)-
      max (r-Real.logb Z (formalReductionFactor D a s.P)) 0 ≤
      v.allowance Z-r-Real.logb Z (Ideal.absNorm D:ℝ) := by
    linarith [le_max_left r (Real.logb Z (formalReductionFactor D a s.P))]
  unfold exceptionalWeight
  apply (Real.rpow_le_rpow_of_exponent_le hZ.le he).trans_eq
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hn]

theorem actual_exceptional_shell {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (N : ℕ) (hι : Fintype.card ι≤N) (hκ : Fintype.card κ≤N) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by
  obtain ⟨C₁,hC₁,hcard₁⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩ := CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z r hT hZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc₁ (D : Ideal O) (hd : D∈Ds) : ((s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D : Ideal O) (hd : D∈Ds) : ((v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε := by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D : Ideal O) (hd : D∈Ds) :
      (∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤
        (C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := by
    have hn : (0:ℝ)<Ideal.absNorm D := ht.trans_le (hlo D hd)
    have he : (Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε) := by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow : (Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε) :=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _ ≤ ∑_a∈s.active D,∑_b∈v.active D,Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ) :=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>
          active_exceptional_weight s v D (hD D hd) a b ha hb Z r hZ))
      _ = ((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by simp; ring
      _ ≤ (C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*
          (Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _ = (C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^(v.allowance Z-r)/(Ideal.absNorm D:ℝ)) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
        (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _ ≤ ∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T) := Finset.sum_le_sum hp
    _ = (Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) := by simp
    _ ≤ (256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^(v.allowance Z-r)/T)) :=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _ = (256*C₁*C₂)*(2*T)^(2*ε)*Z^(v.allowance Z-r) := by field_simp

def ShellBound (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε : ℝ) : Prop := ∀(s : Source ι) (v : Source κ) (Ds : Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r) ≤
        C*(2*T)^(2*ε)*Z^(v.allowance Z-r)

theorem uniform_subset_shell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ℝ) (hε : 0<ε) : ∃C : ℝ,0<C ∧ ∀J L : Finset ι,ShellBound J L C ε := by
  have he (p : Finset ι×Finset ι) : ∃C : ℝ,0<C ∧ ShellBound p.1 p.2 C ε :=
    actual_exceptional_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B : ℝ := 1+∑p : Finset ι×Finset ι,C p
  have hs : 0≤∑p : Finset ι×Finset ι,C p := Finset.sum_nonneg (fun p _=>(hC p).le)
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  intro J L s v Ds hD T Z r hT hZ hlo hhi
  have hc : C (J,L)≤B := by
    have hp := Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]; linarith
  exact (hbound (J,L) s v Ds hD T Z r hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem exceptional_shell_subpower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lo hi : ι→ℝ) (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(J L : Finset ι) (s : Source J) (v : Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds : Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z r : ℝ,
      1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r) := by
  let ε : ℝ := δ/(2*(B+1))
  have hε : 0<ε := div_pos hδ (by positivity)
  have he : 2*B*ε≤δ := by
    have hh : ε*(2*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := uniform_subset_shell (ι:=ι) ε hε
  let E : ℝ := Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E]; positivity,?_⟩
  intro J L s v hvlo hvhi Ds hD T Z r hT hZ hTZ hlo hhi
  have ht : 0<T := zero_lt_one.trans_le hT
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hbound J L s v Ds hD T Z r hT hZ hlo hhi
  have hv : Z^(v.allowance Z-r)≤E*Z^(-r) := by
    calc
      _≤Z^((∑i,logWindow (lo i) (hi i))/Real.log Z-r) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le
          (sub_le_sub_right (subset_allowance L v lo hi hvlo hvhi Z hZ) r)
      _=E*Z^(-r) := by rw [sub_eq_add_neg,Real.rpow_add hz,numerical_allowance Z _ hZ]
  have hpow : T^(2*ε)≤Z^δ := by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith [he])
  apply hh.trans
  calc
    _≤C*(2*T)^(2*ε)*(E*Z^(-r)) := mul_le_mul_of_nonneg_left hv (by positivity)
    _=(C*2^(2*ε)*E)*T^(2*ε)*Z^(-r) := by
      rw [Real.mul_rpow (by norm_num : 0≤(2:ℝ)) ht.le]; ring
    _≤(C*2^(2*ε)*E)*Z^δ*Z^(-r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by dsimp [E]; positivity)) (by positivity)
    _=(C*2^(2*ε)*E)*Z^(δ-r) := by rw [mul_assoc,←Real.rpow_add hz]; rfl

end SevenEighths.CenteredMomentExceptionalAllocationShell

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.PairedEligibleEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => ActualEisensteinCubic.O

lemma reciprocal_sums {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) :
    (∑a∈s.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
      (∑b∈v.active D,1/Real.sqrt (formalReductionFactor D b v.P))=
    ∑a∈s.active D,∑b∈v.active D,
      1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hf:0≤formalReductionFactor D a s.P:=
    (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  rw [Real.sqrt_mul hf]
  ring

theorem actual_paired_source_shell {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  obtain ⟨C₁,hC₁,hl⟩:=actual_source_root_from_children (ι:=ι) N hι ε hε
  obtain ⟨C₂,hC₂,hr⟩:=actual_source_root_from_children (ι:=κ) N hκ ε hε
  obtain ⟨C₃,hC₃,hshell⟩:=paired_all_active_shell (ι:=ι) (κ:=κ) N hι hκ ε hε
  refine ⟨C₁*C₂*C₃,by positivity,?_⟩
  intro s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  let W:ℝ:=Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)
  let θ:ℝ:=(s.toSource.allowance Z+v.toSource.allowance Z)/2
  let F:Ideal O→ℝ:=fun D=>∑a∈s.toSource.active D,∑b∈v.toSource.active D,
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)
  have hW:0≤W:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hF (D:Ideal O):0≤F D:=Finset.sum_nonneg (fun a _=>Finset.sum_nonneg
    (fun b _=>div_nonneg zero_le_one (Real.sqrt_nonneg _)))
  have ht:0<T:=zero_lt_one.trans_le hT
  have hp (D:Ideal O) (hd:D∈Ds):Real.sqrt (s.energy D)*Real.sqrt (v.energy D)≤
      (C₁*C₂)*(2*T)^ε*W*F D:=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have hpow:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
    have hmul:=mul_le_mul (hl s D (hD D hd) E₁ hE₁ (hleft D hd))
      (hr v D (hD D hd) E₂ hE₂ (hright D hd)) (Real.sqrt_nonneg _) (by positivity)
    apply hmul.trans
    calc
      _=(C₁*C₂)*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)^2*W*
          ((∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
           (∑b∈v.toSource.active D,1/Real.sqrt (formalReductionFactor D b v.P))):=by dsimp [W];ring
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^ε*W*F D:=by
        rw [Real.sq_sqrt hpow,reciprocal_sums]
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn.le (hhi D hd).le hε.le) (by positivity)) hW) (hF D)
  calc
    _≤∑D∈Ds,(C₁*C₂)*(2*T)^ε*W*F D:=Finset.sum_le_sum hp
    _=((C₁*C₂)*(2*T)^ε*W)*(∑D∈Ds,F D):=(Finset.mul_sum ..).symm
    _≤((C₁*C₂)*(2*T)^ε*W)*(C₃*(2*T)^(2*ε)*Z^θ):=
      mul_le_mul_of_nonneg_left (hshell s.toSource v.toSource Ds hD T Z hT hZ hlo hhi) (by positivity)
    _=(C₁*C₂*C₃)*(2*T)^(3*ε)*Z^θ*W:=by
      have hpow:(2*T)^ε*(2*T)^(2*ε)=(2*T)^(3*ε):=by
        rw [←Real.rpow_add (by positivity:0<2*T)];congr 1;ring
      calc
        _=(C₁*C₂*C₃)*((2*T)^ε*(2*T)^(2*ε))*Z^θ*W:=by ring
        _=_:=by rw [hpow]

end SevenEighths.CenteredMomentPairedEligibleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.UniformEligibleEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentUniformEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentPairedEligibleEnergy
open CenteredMomentUniformDivisorShell CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def Bound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤E₁ → 0≤E₂ → 1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂))

theorem uniform_subset_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J L:Finset ι,Bound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0<C ∧ Bound p.1 p.2 C ε:=
    actual_paired_source_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0<B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  have hc:C (J,L)≤B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by linarith) _)) (by positivity))

theorem actual_source_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J L:Finset ι) (s:Data J) (v:Data L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀E₁ E₂ T Z:ℝ,
      0≤E₁ → 0≤E₂ → 1≤T → 1<Z → T≤Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*Z^δ*(Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  let ε:ℝ:=δ/(3*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:3*B*ε≤δ:=by
    have hh:ε*(3*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=uniform_subset_energy (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(3*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hTZ hlo hhi hleft hright
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  have hs:=subset_allowance J s.toSource lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v.toSource lo hi hvlo hvhi Z hZ
  have hnum:Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)≤E:=by
    dsimp [E]
    rw [←numerical_allowance Z _ hZ]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hh:=hbound J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans
  rw [Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le]
  have hp:T^(3*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  calc
    C*(2^(3*ε)*T^(3*ε))*E=(C*2^(3*ε)*E)*T^(3*ε):=by ring
    _≤(C*2^(3*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hp (by dsimp [E];positivity)

end SevenEighths.CenteredMomentUniformEligibleEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentWholeDivisorShell
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

lemma divisorPool_nonzero_norm {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (Y : ℝ) (hY : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Y)
    (D : Ideal O) (hD : D∈divisorPool T B) : D≠0 ∧ (D.absNorm:ℝ)≤Y := by
  obtain ⟨j,hj,hd⟩:=Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hB j hj)).mp hd
  have hn : 0<(B j).absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB j hj))
  have hle : (D.absNorm:ℝ)≤(B j).absNorm := by
    exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdiv)
  exact ⟨IdealDivisorBound.divisor_ne_zero (hB j hj) hd,hle.trans (hY j hj)⟩

lemma moebius_norm_le_one (D : Ideal O) : ‖(moebius D:ℂ)‖≤1 := by
  by_cases hD : Squarefree D
  · simp only [hD.moebius_eq,Int.cast_pow,Int.cast_neg,Int.cast_one,norm_pow,norm_neg,norm_one,one_pow,le_refl]
  · simp only [moebius_of_not_squarefree hD,Int.cast_zero,norm_zero,zero_le_one]

lemma squarefree_of_moebius_ne_zero (D : Ideal O) (hD : (moebius D:ℂ)≠0) : Squarefree D := by
  by_contra hn
  exact hD (by rw [moebius_of_not_squarefree hn,Int.cast_zero])

def live (Ds : Finset (Ideal O)) : Finset (Ideal O) := Ds.filter (fun D=>(moebius D:ℂ)≠0)

lemma mem_live (Ds : Finset (Ideal O)) (D : Ideal O) :
    D∈live Ds ↔ D∈Ds ∧ (moebius D:ℂ)≠0 := Finset.mem_filter

lemma live_squarefree (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : Squarefree D :=
  squarefree_of_moebius_ne_zero D ((mem_live Ds D).mp hD).2

lemma live_norm_one (Ds : Finset (Ideal O)) (D : Ideal O) (hD : D∈live Ds) : 1≤(D.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (live_squarefree Ds D hD).ne_zero)

theorem sum_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=∑D∈live Ds,(moebius D:ℂ)*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,zero_mul]

theorem sum_norm_moebius_live (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=∑D∈live Ds,‖(moebius D:ℂ)‖*f D := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro D hD hn
  have hz : (moebius D:ℂ)=0 := by
    by_contra hne
    exact hn ((mem_live Ds D).mpr ⟨hD,hne⟩)
  rw [hz,norm_zero,zero_mul]

def normKey (D : Ideal O) : ℤ := ⌊Real.logb 2 (D.absNorm:ℝ)⌋
def shell (Ds : Finset (Ideal O)) (n : ℤ) : Finset (Ideal O) := (live Ds).filter (fun D=>normKey D=n)
def selectedShells (Ds : Finset (Ideal O)) : Finset ℤ := (live Ds).image normKey

lemma normKey_eq_iff (D : Ideal O) (hD : D≠0) (n : ℤ) :
    normKey D=n ↔ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hn : 0<(D.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hl := Real.logb_le_logb (by norm_num : (1:ℝ)<2) (dyadicScale_pos n) hn
  have hu := Real.logb_lt_logb_iff (by norm_num : (1:ℝ)<2) hn (dyadicScale_pos (n+1))
  simp only [logb_dyadicScale,Int.cast_add,Int.cast_one] at hl hu
  rw [normKey,Int.floor_eq_iff,←hl,←dyadicScale_add,←hu]

lemma mem_shell_iff (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O) :
    D∈shell Ds n ↔ D∈Ds ∧ (moebius D:ℂ)≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  rw [shell,Finset.mem_filter]
  constructor
  · rintro ⟨hd,hk⟩
    exact ⟨((mem_live Ds D).mp hd).1,((mem_live Ds D).mp hd).2,
      (normKey_eq_iff D (live_squarefree Ds D hd).ne_zero n).mp hk⟩
  · rintro ⟨hd,hm,hlo,hhi⟩
    exact ⟨(mem_live Ds D).mpr ⟨hd,hm⟩,
      (normKey_eq_iff D (squarefree_of_moebius_ne_zero D hm).ne_zero n).mpr ⟨hlo,hhi⟩⟩

lemma shell_disjoint (Ds : Finset (Ideal O)) (m n : ℤ) (hmn : m≠n) :
    Disjoint (shell Ds m) (shell Ds n) := by
  apply Finset.disjoint_left.mpr
  intro D hm hn
  exact hmn ((Finset.mem_filter.mp hm).2.symm.trans (Finset.mem_filter.mp hn).2)

lemma shell_nonempty_iff (Ds : Finset (Ideal O)) (n : ℤ) :
    (shell Ds n).Nonempty ↔ n∈selectedShells Ds := by
  constructor
  · rintro ⟨D,hD⟩
    exact Finset.mem_image.mpr ⟨D,(Finset.mem_filter.mp hD).1,(Finset.mem_filter.mp hD).2⟩
  · rintro hn
    obtain ⟨D,hD,hk⟩:=Finset.mem_image.mp hn
    exact ⟨D,Finset.mem_filter.mpr ⟨hD,hk⟩⟩

lemma biUnion_shell (Ds : Finset (Ideal O)) :
    (selectedShells Ds).biUnion (shell Ds)=live Ds := by
  ext D
  simp only [Finset.mem_biUnion,shell,Finset.mem_filter]
  constructor
  · rintro ⟨n,hn,hd,hk⟩;exact hd
  · intro hd
    exact ⟨normKey D,Finset.mem_image.mpr ⟨D,hd,rfl⟩,hd,rfl⟩

theorem sum_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑D∈Ds,(moebius D:ℂ)*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,(moebius D:ℂ)*f D := by
  rw [sum_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

theorem sum_norm_moebius_shells (Ds : Finset (Ideal O)) (f : Ideal O→ℝ) :
    (∑D∈Ds,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells Ds,∑D∈shell Ds n,‖(moebius D:ℂ)‖*f D := by
  rw [sum_norm_moebius_live]
  exact (Finset.sum_fiberwise_of_maps_to (fun D hD=>Finset.mem_image.mpr ⟨D,hD,rfl⟩) _).symm

lemma selected_scale_bounds (Ds : Finset (Ideal O)) (Y : ℝ)
    (hY : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y)
    (n : ℤ) (hn : n∈selectedShells Ds) :
    1≤dyadicScale n ∧ dyadicScale n≤Y := by
  obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hn
  have hd:=live_squarefree Ds D hD
  have hnorm:=live_norm_one Ds D hD
  have hkey : 0≤normKey D := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hnorm)
  have hscale : 1≤dyadicScale (normKey D) := by
    simpa only [dyadicScale,zpow_zero] using
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hkey
  exact ⟨hscale,((normKey_eq_iff D hd.ne_zero _).mp rfl).1.trans
    (hY D ((mem_live Ds D).mp hD).1 ((mem_live Ds D).mp hD).2)⟩

lemma selected_subset_indices (Ds : Finset (Ideal O)) (Y : ℝ) (hY : 1≤Y)
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Y) :
    selectedShells Ds⊆indices 1 Y := by
  intro n hn
  have hh:=selected_scale_bounds Ds Y hbound n hn
  exact (mem_indices_iff_scale 1 Y (by norm_num) (zero_lt_one.trans_le hY) n).mpr
    ⟨hh.1,hh.2.trans (by linarith)⟩

theorem selected_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z)
    (Ds : Finset (Ideal O))
    (hbound : ∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) :
    ((selectedShells Ds).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hc : ((selectedShells Ds).card:ℝ)≤(indices 1 (Z^B)).card := by
    exact_mod_cast Finset.card_le_card (selected_subset_indices Ds (Z^B) hY hbound)
  have hi:=indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY
    (by simp only [div_one,one_mul,le_refl])
  exact hc.trans (by simpa only [Real.logb_one,add_zero] using hi)

theorem selected_card_subpower (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ((selectedShells Ds).card:ℝ)≤C*Z^δ := by
  let C:=2*(3+B/Real.log 2)
  have hC : 0<C := by
    have hh:=div_nonneg hB (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [C];linarith
  have ht:=(isLittleO_log_rpow_rpow_atTop (1:ℝ) hδ).bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,?_⟩
  filter_upwards [ht,eventually_ge_atTop (Real.exp 1)] with Z ht hZ
  have hz : 1<Z := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hZ
  have hl : 1≤Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hZ
  have hp : Real.log Z≤Z^δ := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤Real.log Z),
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hz).le _),one_mul] using ht
  refine ⟨hz,?_⟩
  intro Ds hb
  apply (selected_card_log B Z hB hz.le Ds hb).trans
  have hk : 0≤3+B/Real.log 2 := by positivity
  dsimp [C]
  nlinarith [mul_le_mul_of_nonneg_left hp hk]

theorem divisorPool_card_log {α : Type*} (T : Finset α) (B : α→Ideal O)
    (hB : ∀j∈T,B j≠0) (L Z : ℝ) (hL : 0≤L) (hZ : 1≤Z)
    (hN : ∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) :
    ((selectedShells (divisorPool T B)).card:ℝ)≤(3+L/Real.log 2)*(1+Real.log Z) :=
  selected_card_log L Z hL hZ _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

theorem divisorPool_card_subpower (L δ : ℝ) (hL : 0≤L) (hδ : 0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{α:Type*}(T:Finset α)(B:α→Ideal O),
      (∀j∈T,B j≠0) → (∀j∈T,(Ideal.absNorm (B j):ℝ)≤Z^L) →
      ((selectedShells (divisorPool T B)).card:ℝ)≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower L δ hL hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α T B hB hN
  exact hz.2 _ (fun D hD _=>(divisorPool_nonzero_norm T B hB _ hN D hD).2)

lemma shell_member_data (Ds : Finset (Ideal O)) (n : ℤ) (D : Ideal O)
    (hD : D∈shell Ds n) :
    D∈Ds ∧ (moebius D:ℂ)≠0 ∧ Squarefree D ∧ D≠0 ∧
      dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n := by
  have hh:=(mem_shell_iff Ds n D).mp hD
  have hs:=squarefree_of_moebius_ne_zero D hh.2.1
  exact ⟨hh.1,hh.2.1,hs,hs.ne_zero,hh.2.2⟩

theorem finite_pair_mobius_shells {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α→Ideal O) (B : β→Ideal O) (hB : ∀j∈T,B j≠0) (F : α→β→ℂ) :
    (∑i∈S,∑j∈T,if IsCoprime (A i) (B j) then F i j else 0)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        (moebius D:ℂ)*∑i∈S,∑j∈T,if D∣A i ∧ D∣B j then F i j else 0 := by
  rw [finite_pair_mobius S T A B hB F]
  exact sum_moebius_shells _ _

theorem divisorPool_weighted_shells {α : Type*} (T : Finset α) (B : α→Ideal O)
    (f : Ideal O→ℝ) :
    (∑D∈divisorPool T B,‖(moebius D:ℂ)‖*f D)=
      ∑n∈selectedShells (divisorPool T B),∑D∈shell (divisorPool T B) n,
        ‖(moebius D:ℂ)‖*f D := sum_norm_moebius_shells _ _

end SevenEighths.CenteredMomentWholeDivisorShell

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonHarmonicMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentDivisorAllocation CenteredMomentWholeDivisorShell
open CenteredMomentDyadicCount CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
abbrev Label := (Ideal O × Ideal O) × Finset (Ideal O)

def Valid (s : Ideal O) (v : Label) : Prop :=
  v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ primeSupport v.1.1 = primeSupport v.1.2 ∧
  s ∣ v.1.1 ∧ s ∣ v.1.2 ∧ v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)

def weight (v : Label) : ℝ := 1 / Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm)

lemma commonRadical_norm_le (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    (Ideal.absNorm (commonRadical I J):ℝ) ≤ min (I.absNorm:ℝ) J.absNorm := by
  have hd : commonRadical I J ∣ I ∧ commonRadical I J ∣ J := by
    constructor <;> apply (squarefree_dvd_iff _ _ (commonRadical_squarefree I J)).mpr
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).1)
    · intro P hP
      rw [commonRadical_support] at hP
      exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp hP).2)
  apply le_min
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm hd.1)
  · exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
      (map_dvd Ideal.absNorm hd.2)

lemma min_le_sqrt_mul (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    min x y ≤ Real.sqrt (x*y) := by
  apply (Real.le_sqrt (le_min hx hy) (mul_nonneg hx hy)).mpr
  rcases le_total x y with h|h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

lemma shell_scalar (e Y x y : ℝ) (he : 0<e) (hx : 0<x) (hy : 0<y)
    (hY : min x y ≤ Y) :
    (2*min x y)^(1+e)/Real.sqrt (x*y) ≤ 2^(1+e)*Y^e := by
  have hm : 0< min x y := lt_min hx hy
  have hsqrt : 0<Real.sqrt (x*y) := Real.sqrt_pos.2 (mul_pos hx hy)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hm.le,
    Real.rpow_add hm,Real.rpow_one]
  have hp := Real.rpow_le_rpow hm.le hY he.le
  have hs := min_le_sqrt_mul x y hx.le hy.le
  apply (div_le_iff₀ hsqrt).mpr
  calc
    _ ≤ 2^(1+e)*(Real.sqrt (x*y)*Y^e) := by gcongr
    _ = _ := by ring

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀(s : Ideal O),Squarefree s → s≠0 →
      ∀(S : Finset Label),(∀v∈S,Valid s v) → ∀Y T₁ T₂ : ℝ,
      0<T₁ → 0<T₂ → min T₁ T₂≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T₁≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*T₁ ∧
        T₂≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*T₂) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T₁ T₂ hT₁ hT₂ hTY hN hshell
  have hY : 0<Y := (lt_min hT₁ hT₂).trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hsq : 0<Real.sqrt (T₁*T₂) := Real.sqrt_pos.2 (mul_pos hT₁ hT₂)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*min T₁ T₂) hY hY (by positivity) hN (by
      intro v hv
      apply (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      exact min_le_min (hshell v hv).2.1.le (hshell v hv).2.2.2.le)
  calc
    _ ≤ ∑_v∈S,1/Real.sqrt (T₁*T₂) := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le hsq
      apply Real.sqrt_le_sqrt
      exact mul_le_mul (hshell v hv).1 (hshell v hv).2.2.1 hT₂.le (hT₁.le.trans (hshell v hv).1)
    _ = (S.card:ℝ)/Real.sqrt (T₁*T₂) := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*min T₁ T₂)^(1+e)/(s.absNorm:ℝ))/Real.sqrt (T₁*T₂) :=
      div_le_div_of_nonneg_right hc hsq.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*min T₁ T₂)^(1+e)/Real.sqrt (T₁*T₂)) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T₁ T₂ he hT₁ hT₂ hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

def key (v : Label) : ℤ×ℤ := (normKey v.1.1,normKey v.1.2)
def keys (S : Finset Label) : Finset (ℤ×ℤ) := S.image key
def shell (S : Finset Label) (n : ℤ×ℤ) : Finset Label := S.filter (fun v=>key v=n)

lemma norm_scale_bounds (I : Ideal O) (hI : I≠0) (Y : ℝ) (hY : (I.absNorm:ℝ)≤Y) :
    1≤dyadicScale (normKey I) ∧ dyadicScale (normKey I)≤Y := by
  have hn : 1≤(I.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hk : 0≤normKey I := Int.floor_nonneg.mpr
    (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hn)
  refine ⟨?_,((normKey_eq_iff I hI _).mp rfl).1.trans hY⟩
  simpa only [dyadicScale,zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2) hk

lemma shell_norm_bounds (S : Finset Label) (n : ℤ×ℤ) (v : Label)
    (hv : v∈shell S n) (hC : v.1.1≠0) (hD : v.1.2≠0) :
    dyadicScale n.1≤(v.1.1.absNorm:ℝ) ∧ (v.1.1.absNorm:ℝ)<2*dyadicScale n.1 ∧
    dyadicScale n.2≤(v.1.2.absNorm:ℝ) ∧ (v.1.2.absNorm:ℝ)<2*dyadicScale n.2 := by
  have he := (Finset.mem_filter.mp hv).2
  have h₁ := (normKey_eq_iff v.1.1 hC n.1).mp (congrArg Prod.fst he)
  have h₂ := (normKey_eq_iff v.1.2 hD n.2).mp (congrArg Prod.snd he)
  exact ⟨h₁.1,h₁.2,h₂⟩

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)^2*(1+Real.log Z)^2 := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ (indices 1 (Z^B))×ˢ(indices 1 (Z^B)) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (h0 v hv).1 (Z^B) (hN v hv).1
    have hd := norm_scale_bounds v.1.2 (h0 v hv).2 (Z^B) (hN v hv).2
    apply Finset.mem_product.mpr
    constructor
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hc.1,hc.2.trans (by linarith)⟩
    · exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
        ⟨hd.1,hd.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ)^2 := by
    have hh := Finset.card_le_card hsub
    rw [Finset.card_product] at hh
    exact_mod_cast (by simpa only [pow_two] using hh)
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  calc
    _ ≤ ((indices 1 (Z^B)).card:ℝ)^2 := hc
    _ ≤ ((3+B/Real.log 2)*(1+Real.log Z))^2 := by gcongr
    _ = _ := by ring

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,weight v)≤C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K^2,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ×ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hc := norm_scale_bounds v.1.1 (hS v hv).1 (Z^B) (hN v hv).1
    have hm : min (dyadicScale n.1) (dyadicScale n.2)≤Z^B := by
      have heq : normKey v.1.1=n.1 := congrArg Prod.fst hkey
      exact (min_le_left _ _).trans (heq ▸ hc.2)
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n.1) (dyadicScale n.2) (dyadicScale_pos _) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw (hS w (Finset.mem_filter.mp hw).1).1
        (hS w (Finset.mem_filter.mp hw).1).2.1)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K^2*(1+Real.log Z)^2)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K^2)*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

lemma log_square_subpower (d : ℝ) (hd : 0<d) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → (1+Real.log Z)^2≤C*Z^d := by
  let a : ℝ := d/2
  have ha : 0<a := by dsimp [a]; positivity
  refine ⟨(1+1/a)^2,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hp : 1≤Z^a := Real.one_le_rpow hZ ha.le
  have hl := Real.log_le_rpow_div hz.le ha
  have hh : 1+Real.log Z≤(1+1/a)*Z^a := by
    calc
      _ ≤ Z^a+Z^a/a := add_le_add hp hl
      _ = _ := by ring
  calc
    _ ≤ ((1+1/a)*Z^a)^2 := by
      apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hh
    _ = (1+1/a)^2*Z^d := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le]
      congr 2
      dsimp [a]; ring

theorem common_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,1/Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm))≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)^2/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr; exact hlog Z hZ1
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end SevenEighths.CenteredMomentCommonHarmonicMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.CommonRadicalHarmonicMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadicalHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical CenteredMomentRankinLabels
open CenteredMomentWholeDivisorShell CenteredMomentDyadicCount CenteredMomentSectorLocalization
open CenteredMomentCommonHarmonicMass (Label Valid commonRadical_norm_le norm_scale_bounds log_square_subpower)
local notation "O" => ActualEisensteinCubic.O

def weight (v : Label) : ℝ := 1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)
def key (v : Label) : ℤ := normKey (commonRadical v.1.1 v.1.2)
def keys (S : Finset Label) : Finset ℤ := S.image key
def shell (S : Finset Label) (n : ℤ) : Finset Label := S.filter (fun v=>key v=n)

lemma radical_ne_zero (v : Label) : commonRadical v.1.1 v.1.2≠0 :=
  Squarefree.ne_zero (commonRadical_squarefree _ _)

lemma shell_scalar (e Y T : ℝ) (he : 0<e) (hT : 0<T) (hTY : T≤Y) :
    (2*T)^(1+e)/T≤2^(1+e)*Y^e := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hT.le,
    Real.rpow_add hT,Real.rpow_one]
  calc
    _ = 2^(1+e)*T^e := by field_simp
    _ ≤ 2^(1+e)*Y^e := by gcongr

theorem shell_bound (e : ℝ) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) → ∀Y T : ℝ,0<T → T≤Y →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Y ∧ (v.1.2.absNorm:ℝ)≤Y) →
      (∀v∈S,T≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
        (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*T) →
      (∑v∈S,weight v)≤C*Y^(3*e)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count e e he he
  refine ⟨C*2^(1+e),by positivity,?_⟩
  intro s hs hs0 S hS Y T hT hTY hN hshell
  have hY : 0<Y := hT.trans_le hTY
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hc := hcount s hs hs0 S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩)
    (fun v hv=>(hS v hv).2.2.1) (fun v hv=>⟨(hS v hv).2.2.2.1,(hS v hv).2.2.2.2.1⟩)
    (fun v hv=>(hS v hv).2.2.2.2.2) Y Y (2*T) hY hY (by positivity) hN
    (fun v hv=>(hshell v hv).2.le)
  calc
    _ ≤ ∑_v∈S,1/T := by
      apply Finset.sum_le_sum
      intro v hv
      exact one_div_le_one_div_of_le hT (hshell v hv).1
    _ = (S.card:ℝ)/T := by simp [div_eq_mul_inv]
    _ ≤ (C*Y^e*Y^e*(2*T)^(1+e)/(s.absNorm:ℝ))/T :=
      div_le_div_of_nonneg_right hc hT.le
    _ = (C*Y^e*Y^e/(s.absNorm:ℝ))*((2*T)^(1+e)/T) := by ring
    _ ≤ (C*Y^e*Y^e/(s.absNorm:ℝ))*(2^(1+e)*Y^e) :=
      mul_le_mul_of_nonneg_left (shell_scalar e Y T he hT hTY) (by positivity)
    _ = (C*2^(1+e))*Y^(3*e)/(s.absNorm:ℝ) := by
      rw [show 3*e=e+e+e by ring,Real.rpow_add hY,Real.rpow_add hY]
      ring

lemma shell_norm_bounds (S : Finset Label) (n : ℤ) (v : Label) (hv : v∈shell S n) :
    dyadicScale n≤(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ∧
    (Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)<2*dyadicScale n := by
  exact (normKey_eq_iff _ (radical_ne_zero v) n).mp (Finset.mem_filter.mp hv).2

theorem sum_shells (S : Finset Label) (f : Label→ℝ) :
    (∑v∈S,f v)=∑n∈keys S,∑v∈shell S n,f v := by
  exact (Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _).symm

lemma keys_card_log (B Z : ℝ) (hB : 0≤B) (hZ : 1≤Z) (S : Finset Label)
    (h0 : ∀v∈S,v.1.1≠0 ∧ v.1.2≠0)
    (hN : ∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) :
    ((keys S).card:ℝ)≤(3+B/Real.log 2)*(1+Real.log Z) := by
  have hY : 1≤Z^B := Real.one_le_rpow hZ hB
  have hsub : keys S ⊆ indices 1 (Z^B) := by
    intro n hn
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (h0 v hv).1 (h0 v hv).2).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z^B) hr
    exact (mem_indices_iff_scale 1 (Z^B) (by norm_num) (by positivity) _).mpr
      ⟨hc.1,hc.2.trans (by linarith)⟩
  have hc : ((keys S).card:ℝ)≤((indices 1 (Z^B)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hi := indices_card_log_bound 1 B Z 1 (Z^B) le_rfl hB hZ (by norm_num) hY (by simp)
  simp only [Real.logb_one,add_zero] at hi
  exact hc.trans hi

theorem polynomial_cap_log_bound (B e : ℝ) (hB : 0≤B) (he : 0<e) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,weight v)≤C*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := shell_bound e he
  let K : ℝ := 3+B/Real.log 2
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨C*K,by positivity,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hb (n : ℤ) (hn : n∈keys S) :
      (∑v∈shell S n,weight v)≤C*(Z^B)^(3*e)/(s.absNorm:ℝ) := by
    obtain ⟨v,hv,hkey⟩ := Finset.mem_image.mp hn
    have hr := (commonRadical_norm_le _ _ (hS v hv).1 (hS v hv).2.1).trans
      ((min_le_left _ _).trans (hN v hv).1)
    have hc := norm_scale_bounds _ (radical_ne_zero v) (Z^B) hr
    have hm : dyadicScale n≤Z^B := by
      exact hkey ▸ hc.2
    exact hbound s hs hs0 (shell S n) (fun w hw=>hS w (Finset.mem_filter.mp hw).1)
      (Z^B) (dyadicScale n) (dyadicScale_pos _) hm
      (fun w hw=>hN w (Finset.mem_filter.mp hw).1)
      (fun w hw=>shell_norm_bounds S n w hw)
  have hk := keys_card_log B Z hB hZ S (fun v hv=>⟨(hS v hv).1,(hS v hv).2.1⟩) hN
  rw [sum_shells]
  calc
    _ ≤ ∑_n∈keys S,C*(Z^B)^(3*e)/(s.absNorm:ℝ) := Finset.sum_le_sum hb
    _ = ((keys S).card:ℝ)*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) := by simp
    _ ≤ (K*(1+Real.log Z))*(C*(Z^B)^(3*e)/(s.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ = (C*K)*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := by
      rw [←Real.rpow_mul hz.le,show B*(3*e)=3*B*e by ring]
      ring

theorem common_radical_harmonic_mass (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,2≤Z → ∀s : Ideal O,Squarefree s → s≠0 →
      ∀S : Finset Label,(∀v∈S,Valid s v) →
      (∀v∈S,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      (∑v∈S,1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ))≤C*Z^δ/(s.absNorm:ℝ) := by
  let e : ℝ := δ/(6*(B+1))
  have he : 0<e := by dsimp [e]; positivity
  have hbudget : 3*B*e+δ/2≤δ := by
    have hh : e*(6*(B+1))=δ := div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := polynomial_cap_log_bound B e hB he
  obtain ⟨D,hD,hlog⟩ := log_square_subpower (δ/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro Z hZ s hs hs0 S hS hN
  have hz : 0<Z := by linarith
  have hZ1 : 1≤Z := by linarith
  have hsn : 0<(s.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs0)
  have hl : 1+Real.log Z≤D*Z^(δ/2) := by
    have hn := Real.log_nonneg hZ1
    exact (show 1+Real.log Z≤(1+Real.log Z)^2 by nlinarith).trans (hlog Z hZ1)
  calc
    _ ≤ C*Z^(3*B*e)*(1+Real.log Z)/(s.absNorm:ℝ) := hbound Z hZ1 s hs hs0 S hS hN
    _ ≤ C*Z^(3*B*e)*(D*Z^(δ/2))/(s.absNorm:ℝ) := by gcongr
    _ = (C*D)*Z^(3*B*e+δ/2)/(s.absNorm:ℝ) := by rw [Real.rpow_add hz]; ring
    _ ≤ (C*D)*Z^δ/(s.absNorm:ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hbudget) (mul_pos hC hD).le) hsn.le

end SevenEighths.CenteredMomentCommonRadicalHarmonicMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentMobiusHarmonicMass
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentDivisorBoundary CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

lemma shell_mass (Ds:Finset (Ideal O)) (n:ℤ) (hn:n∈selectedShells Ds) :
    (∑D∈shell Ds n,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤256 := by
  have ht:1≤dyadicScale n:=
    (selected_scale_bounds Ds (∑D∈Ds,(Ideal.absNorm D:ℝ))
      (fun D hD _=>Finset.single_le_sum (fun D _=>Nat.cast_nonneg _) hD) n hn).1
  have htp:0<dyadicScale n:=zero_lt_one.trans_le ht
  have hcard:=divisor_dyad_card (shell Ds n) (dyadicScale n) ht
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.1)
    (fun D hd=>(shell_member_data Ds n D hd).2.2.2.2.2)
  calc
    _≤∑D∈shell Ds n,1/dyadicScale n:=by
      apply Finset.sum_le_sum
      intro D hd
      have hh:=(shell_member_data Ds n D hd).2.2.2.2.1
      exact div_le_div₀ (by norm_num) (moebius_norm_le_one D) htp hh
    _=((shell Ds n).card:ℝ)/dyadicScale n:=by simp [div_eq_mul_inv]
    _≤256:=(div_le_iff₀ htp).mpr hcard

 theorem full_mass_subpower (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Ds:Finset (Ideal O),
      (∀D∈Ds,(moebius D:ℂ)≠0 → (Ideal.absNorm D:ℝ)≤Z^B) →
      (∑D∈Ds,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=selected_card_subpower B δ hB hδ
  refine ⟨256*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Ds hn
  have he:=sum_norm_moebius_shells Ds (fun D=>1/(Ideal.absNorm D:ℝ))
  simp only [mul_one_div] at he
  rw [he]
  calc
    _≤∑n∈selectedShells Ds,(256:ℝ):=Finset.sum_le_sum (fun n hn=>shell_mass Ds n hn)
    _=((selectedShells Ds).card:ℝ)*256:=by simp
    _≤(C*Z^δ)*256:=mul_le_mul_of_nonneg_right (hZ.2 Ds hn) (by norm_num)
    _=_:=by ring

 theorem actual_divisorPool_mass (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀{α:Type*} (T:Finset α) (v:α→Ideal O),(∀j∈T,v j≠0) →
      (∀j∈T,(Ideal.absNorm (v j):ℝ)≤Z^B) →
      (∑D∈divisorPool T v,‖(moebius D:ℂ)‖/(Ideal.absNorm D:ℝ))≤C*Z^δ := by
  obtain ⟨C,hC,hbound⟩:=full_mass_subpower B δ hB hδ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro α T v hv hn
  exact hZ.2 (divisorPool T v) (fun D hd _=>(divisorPool_nonzero_norm T v hv (Z^B) hn D hd).2)

end SevenEighths.CenteredMomentMobiusHarmonicMass

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.ZeroMode -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentZeroMode
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcreteTraceCRT CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount CenteredExceptionalProfile
local notation "O" => ActualEisensteinCubic.O

@[simp] theorem pairResidue_mul (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x y : Residue (a * b)) :
    pairResidue a b ha hb (x * y) =
      pairResidue a b ha hb x * pairResidue a b ha hb y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, pairResidue_mk, pairResidue_mk, pairResidue_mk,
    idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

@[simp] theorem pairFourier_zero (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    pairFourier a b ha hb 0 = ∑' x : Residue (a * b), pairResidue a b ha hb x := by
  simp [pairFourier, quotientTrace]

theorem pairResidue_unit_eq_one_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (u : (Residue (a * b))ˣ) :
    pairResidue a b ha hb u = 1 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype] at hm
  have he : pairResidue a b ha hb u * (∑ x : Residue (a * b), pairResidue a b ha hb x) =
      ∑ x : Residue (a * b), pairResidue a b ha hb x := by
    simpa only [Finset.mul_sum, pairResidue_mul] using
      u.mulLeft_bijective.sum_comp (pairResidue a b ha hb)
  exact (mul_right_cancel₀ hm (he.trans (one_mul _).symm))

theorem rows_agree_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (n : O)
    (hn : IsCoprime (Ideal.span {n}) (Ideal.span {a} * Ideal.span {b})) :
    idealRowHom n (Ideal.span {a}) = idealRowHom n (Ideal.span {b}) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {a * b}) n) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [Ideal.span_singleton_mul_span_singleton] using hn
  have he := pairResidue_unit_eq_one_of_mean_ne_zero a b ha hb hm hunit.unit
  rw [hunit.unit_spec, pairResidue_mk] at he
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) n) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hn.of_mul_right_right
  have hj : idealRowHom n (Ideal.span {b}) * star (idealRowHom n (Ideal.span {b})) = 1 := by
    change supportedModulusCharacter b hb (Ideal.Quotient.mk _ n) *
      star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ n)) = 1
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
    exact MulChar.one_apply hu
  exact mul_right_cancel₀ (by intro hz; simp [hz] at hj) (he.trans hj.symm)

theorem valuation_profile_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (P : Ideal O) [P.IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ P)
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    valuation (Ideal.span {a}) P % 6 = valuation (Ideal.span {b}) P % 6 := by
  apply valuation_mod_six_of_unit_agreement 1
    (Ideal.span {a} * Ideal.span {b}) _ _ P (mul_ne_zero ha.1 hb.1) ha hb
    hg hodd isCoprime_one_left
  intro n _ hn
  exact rows_agree_of_mean_ne_zero a b ha hb hm n hn

theorem powerful_product_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) :
    CompletedGauss.PowerfulIdeal (Ideal.span {a} * Ideal.span {b}) := by
  have hs := (supported_mul_iff _ _).mpr ⟨ha, hb⟩
  refine ⟨hs.1, ?_⟩
  intro P hP
  obtain ⟨hmax, hg, hodd⟩ := supported_factors_good _ hs P hP
  let := hmax
  have he := valuation_profile_of_mean_ne_zero a b ha hb hm P hg hodd
  have hp := Multiset.count_pos.mpr hP
  rw [normalizedFactors_mul ha.1 hb.1, Multiset.count_add] at hp ⊢
  unfold valuation at he
  omega

theorem powerful_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O × Ideal O)) (Y : ℝ), 1 ≤ Y →
      (∀ p ∈ S, CompletedGauss.PowerfulIdeal (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hp⟩ := CompletedGauss.powerful_ideal_count (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro S Y hY hS
  let T := S.image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hT (I : Ideal O) (hI : I ∈ T) :
      CompletedGauss.PowerfulIdeal I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hS p hp
  have hcard : (S.card : ℝ) = ∑ I ∈ T,
      ((S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card : ℝ) := by
    calc
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ I ∈ T, ∑ _p ∈ S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp =>
          Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp) _).symm
      _ = _ := by simp
  rw [hcard]
  calc
    _ ≤ ∑ I ∈ T, D * Y ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) := by
          exact_mod_cast product_fiber_card S I (hT I hI).1.1
        _ ≤ D * (Ideal.absNorm I : ℝ) ^ (ε / 2) := hd I (hT I hI).1.1
        _ ≤ D * Y ^ (ε / 2) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT I hI).2 (by positivity)) hD.le
    _ = (T.card : ℝ) * (D * Y ^ (ε / 2)) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε / 2)) * (D * Y ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hp T Y hY hT) (by positivity)
    _ = (C * D) * (Y ^ (1 / 2 + ε / 2) * Y ^ (ε / 2)) := by ring
    _ = (C * D) * Y ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < Y)]
      congr 2
      ring

theorem pairFourier_zero_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    ‖pairFourier a b ha hb 0‖ ≤ (Ideal.absNorm (Ideal.span {a * b}) : ℝ) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a * b), ‖pairResidue a b ha hb x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a * b), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [pairResidue_mk, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans
        (idealRowHom_norm _ _)
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem scaled_zero_mean_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (K : ℝ) (hK : 0 ≤ K) :
    ‖((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) * pairFourier a b ha hb 0‖ ≤ K := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {a * b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
        (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    eisEmbedding_norm_sq_eq_absNorm_span, abs_of_nonneg (div_nonneg hK hn.le)]
  calc
    _ ≤ (K / (Ideal.absNorm (Ideal.span {a * b}) : ℝ)) *
        (Ideal.absNorm (Ideal.span {a * b}) : ℝ) :=
      mul_le_mul_of_nonneg_left (pairFourier_zero_norm_le a b ha hb) (div_nonneg hK hn.le)
    _ = K := div_mul_cancel₀ _ hn.ne'

theorem nonzero_mean_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (Y : ℝ), 1 ≤ Y →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      ((S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)).card : ℝ)
        ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := powerful_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb Y hY hinj hN
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  let f := fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})
  have hf : Set.InjOn f (T : Set (α × β)) := by
    intro p hp q hq he
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have ht : (T.image f).card = T.card := Finset.card_image_of_injOn hf
  have hbound := hc (T.image f) Y hY (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hp' := Finset.mem_filter.mp hp
    exact ⟨powerful_product_of_mean_ne_zero (a p.1) (b p.2) (ha p.1) (hb p.2) hp'.2,
      hN p hp'.1⟩)
  simpa only [ht] using hbound

theorem first_zero_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (d : α × β → ℂ)
      (Y K B : ℝ), 1 ≤ Y → 0 ≤ K → 0 ≤ B →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      (∀ p ∈ S, ‖d p‖ ≤ B) →
      ‖∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ ≤
        C * K * B * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := nonzero_mean_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb d Y K B hY hK hB hinj hN hd
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  have hsum : (∑ p ∈ S, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)) =
      ∑ p ∈ T, d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpt
    have hz : pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 = 0 := by
      simpa only [T, Finset.mem_filter, hp, true_and, not_not] using hpt
    rw [hz, mul_zero, mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ p ∈ T, ‖d p * (((K / ‖eisEmbedding (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B * K := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hd p (Finset.mem_filter.mp hp).1)
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (norm_nonneg _) hB
    _ = (T.card : ℝ) * (B * K) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε)) * (B * K) :=
      mul_le_mul_of_nonneg_right (hc S a b ha hb Y hY hinj hN) (mul_nonneg hB hK)
    _ = C * K * B * Y ^ (1 / 2 + ε) := by ring

theorem productColumnCoefficient_sextic_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    (∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)) =
      ∑ K ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2),
        productColumnCoefficient S T β K * idealRowHom z K := by
  rw [← Finset.sum_product (f := fun p : Ideal O × Ideal O =>
    β p.1 p.2 * idealRowHom z (p.1 * p.2))]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p ∈ S ×ˢ T) => Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp)]
  apply Finset.sum_congr rfl
  intro K hK
  rw [productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem productColumnCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ),
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ 1) →
      ∀ (I : Ideal O) (X : ℝ), I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ X →
        ‖productColumnCoefficient S T β I‖ ≤ D * X ^ ε := by
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro S T β hβ I X hI hX
  exact (productColumnCoefficient_norm S T β hβ I hI).trans
    ((hd I hI).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le) hD.le))

def idealColumn (S : Finset (Ideal O)) (I : S) : O :=
  ConcretePrimeRowBridge.idealGenerator I.val

@[simp] theorem idealColumn_span (S : Finset (Ideal O)) (I : S) :
    Ideal.span {idealColumn S I} = I.val :=
  ConcretePrimeRowBridge.span_idealGenerator _

theorem idealColumn_supported (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {idealColumn S I}) := by
  rw [idealColumn_span]
  exact hS I.val I.property

def idealZeroEnergy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (K : ℝ) : ℂ :=
  ∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
    (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (idealColumn S I) (idealColumn S J)
        (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0)

theorem ideal_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
      (c : Ideal O → ℂ) (X K B : ℝ), 1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ S, ‖c I‖ ≤ B) →
      ‖idealZeroEnergy S hS c K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := first_zero_sum_bound (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S hS c X K B hX hK hB hN hd
  have hinj : Set.InjOn (fun p : S × S =>
      (Ideal.span {idealColumn S p.1}, Ideal.span {idealColumn S p.2}))
        (↑(Finset.univ : Finset (S × S)) : Set (S × S)) := by
    intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.fst he)
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.snd he)
  have hNpair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      (Ideal.absNorm (Ideal.span {idealColumn S p.1} * Ideal.span {idealColumn S p.2}) : ℝ) ≤ X ^ 2 := by
    rw [idealColumn_span, idealColumn_span, map_mul, Nat.cast_mul, pow_two]
    exact mul_le_mul (hN _ p.1.property) (hN _ p.2.property) (Nat.cast_nonneg _) (by linarith)
  have hdPair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      ‖c p.1.val * star (c p.2.val)‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hd _ p.1.property) (hd _ p.2.property) (norm_nonneg _) hB
  have hh := hc Finset.univ (idealColumn S) (idealColumn S)
    (idealColumn_supported S hS) (idealColumn_supported S hS)
    (fun p : S × S => c p.1.val * star (c p.2.val)) (X ^ 2) K (B ^ 2)
    (by nlinarith) hK (sq_nonneg _) hinj hNpair hdPair
  have hp : (X ^ 2) ^ (1 / 2 + ε / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]
    congr 1
    ring
  simpa only [idealZeroEnergy, Fintype.sum_prod_type, hp] using hh

theorem productColumnCoefficient_norm_le (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖productColumnCoefficient S T β I‖ ≤ B * (IdealMobiusDivisorSum.idealDivisors I).card := by
  unfold productColumnCoefficient
  calc
    _ ≤ ∑ p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), ‖β p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), B := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = B * ((S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast product_fiber_card (S ×ˢ T) I hI) hB

theorem productColumns_supported (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J) :
    ∀ I ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2), Supported I := by
  intro I hI
  obtain ⟨⟨J, K⟩, hp, rfl⟩ := Finset.mem_image.mp hI
  have hh := Finset.mem_product.mp hp
  exact (supported_mul_iff J K).mpr ⟨hS J hh.1, hT K hh.2⟩

def productZeroEnergy (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (K : ℝ) : ℂ :=
  idealZeroEnergy ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (productColumns_supported S T hS hT) (productColumnCoefficient S T β) K

theorem product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖productZeroEnergy S T hS hT β K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := ideal_zero_energy_bound (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 4) (by positivity)
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hs := productColumns_supported S T hS hT
  have hn (I : Ideal O) (hI : I ∈ P) : (Ideal.absNorm I : ℝ) ≤ X := by
    obtain ⟨⟨J, L⟩, hp, rfl⟩ := Finset.mem_image.mp hI
    have hh := Finset.mem_product.mp hp
    exact hN J hh.1 L hh.2
  have hb (I : Ideal O) (hI : I ∈ P) :
      ‖productColumnCoefficient S T β I‖ ≤ B * (D * X ^ (ε / 4)) := by
    apply (productColumnCoefficient_norm_le S T β B hB hβ I (hs I hI).1).trans
    apply mul_le_mul_of_nonneg_left _ hB
    exact (hd I (hs I hI).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hn I hI) (by positivity)) hD.le)
  have hh := hc P hs (productColumnCoefficient S T β) X K (B * (D * X ^ (ε / 4)))
    hX hK (by positivity) hn hb
  change ‖productZeroEnergy S T hS hT β K‖ ≤ _ at hh
  apply hh.trans_eq
  have hx0 : 0 < X := by linarith
  have hp : (X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    C * K * (B * (D * X ^ (ε / 4))) ^ 2 * X ^ (1 + ε / 2) =
        (C * D ^ 2) * K * B ^ 2 * ((X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2)) := by ring
    _ = _ := by rw [hp]

theorem normalized_product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) * productZeroEnergy S T hS hT β K‖ ≤
        C * K * B ^ 2 * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  have hx0 : 0 < X := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  calc
    _ ≤ X⁻¹ * (C * K * B ^ 2 * X ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left (hc S T hS hT β X K B hX hK hB hN hβ) (by positivity)
    _ = C * K * B ^ 2 * X ^ ε := by
      rw [Real.rpow_add hx0, Real.rpow_one]
      field_simp

theorem aggregated_rowPolynomial (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowPolynomial Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) z =
      ∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J) := by
  dsimp only
  rw [rowPolynomial]
  simp only [idealColumn_span]
  rw [Finset.sum_coe_sort ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (fun I : Ideal O => productColumnCoefficient S T β I * idealRowHom z I)]
  exact (productColumnCoefficient_sextic_row_sum S T β z).symm

theorem aggregated_rowEnergy (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowEnergy Finset.univ (idealColumn P)
      (fun I : P => productColumnCoefficient S T β I.val) W K =
      ∑' z : O, ((‖∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)‖ ^ 2 : ℝ) : ℂ) *
        W (‖eisEmbedding z‖ ^ 2 / K) := by
  simp only [CenteredMomentRowNorm.rowEnergy, aggregated_rowPolynomial]

theorem idealZeroEnergy_first_frequency (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ)
    (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      (((K / ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
        (pairFourier (idealColumn S I) (idealColumn S J)
          (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0 *
          EisensteinSchwartzPoisson.paperRadialFourier W
            (K * ‖eisEmbedding (0 : O)‖ ^ 2 /
              ‖eisEmbedding (idealColumn S I * idealColumn S J)‖ ^ 2)))) =
      idealZeroEnergy S hS c K * EisensteinSchwartzPoisson.paperRadialFourier W 0 := by
  simp [idealZeroEnergy, Finset.sum_mul, mul_assoc]

theorem normalized_product_zero_mode_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        (productZeroEnergy S T hS hT β K * EisensteinSchwartzPoisson.paperRadialFourier W 0)‖ ≤
        C * K * B ^ 2 * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := normalized_product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β W X K B hX hK hB hN hβ
  rw [← mul_assoc, norm_mul]
  calc
    _ ≤ (C * K * B ^ 2 * X ^ ε) * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ :=
      mul_le_mul_of_nonneg_right (hc S T hS hT β X K B hX hK hB hN hβ) (norm_nonneg _)
    _ = _ := by ring

end SevenEighths.CenteredMomentZeroMode

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.AddedZero -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle CenteredMomentExtraction
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

theorem pairFourier_one (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    pairFourier u 1 hu supported_one_element h =
      ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) h := by
  have hone (x : Residue (1 : O)) : supportedModulusCharacter 1 supported_one_element x = 1 := by
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [supportedModulusCharacter_mk]
    simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using (idealRowHom n).map_one
  have aux (v : O) (hd : u ∣ v) (hv : v ≠ 0) (he : v = u) :
      (∑' x : Residue v, supportedModulusCharacter u hu (frequencyReduction u v hd x) *
        CubicEisenstein.quotientTrace v hv (Ideal.Quotient.mk _ h * x)) =
      residueGauss u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
        (Ideal.Quotient.mk _ h) := by
    subst v
    apply tsum_congr
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [frequencyReduction_mk]
  rw [← residueGauss_supported_mk u hu h]
  simpa only [pairFourier, pairResidue, hone, star_one, mul_one] using
    aux (u * 1) (dvd_mul_right u 1)
      (mul_ne_zero (supported_element_ne_zero u hu) (supported_element_ne_zero 1 supported_one_element))
      (mul_one u)

theorem gaussRow_zero_sixthRemainder (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) : sixthRemainder (Ideal.span {u}) = 1 := by
  have hg : ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) 0 ≠ 0 := by
    intro hz
    apply hzero
    simp only [gaussRow, hz, zero_div]
  have hm : pairFourier u 1 hu supported_one_element 0 ≠ 0 := by
    rwa [pairFourier_one]
  apply sixthRemainder_eq_of_prime_profile one_ne_zero
  intro P hP
  by_cases hmem : P ∈ normalizedFactors (Ideal.span {u})
  · obtain ⟨hmax, hlam, hodd⟩ := supported_factors_good _ hu P hmem
    let := hmax
    have hv := valuation_profile_of_mean_ne_zero u 1 hu supported_one_element hm P hlam hodd
    simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, valuation,
      normalizedFactors_one, Multiset.count_zero, Nat.zero_mod] using hv
  · simp only [valuation, Multiset.count_eq_zero.mpr hmem, normalizedFactors_one,
      Multiset.count_zero, Nat.zero_mod]

theorem gaussRow_zero_ideal_sixth_power (u : O) (hu : Supported (Ideal.span {u}))
    (hzero : gaussRow u hu 0 ≠ 0) :
    sixthQuotient (Ideal.span {u}) ^ 6 = Ideal.span {u} := by
  simpa only [gaussRow_zero_sixthRemainder u hu hzero, one_mul] using
    sixth_normal_form (Ideal.span {u}) hu.1

theorem gaussRow_norm_le (u : O) (hu : Supported (Ideal.span {u})) (h : O) :
    ‖gaussRow u hu h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  have hb := CenteredMomentTail.normalizedResidueGauss_norm_le u
    (supported_element_ne_zero u hu) (supportedModulusCharacter u hu) (Ideal.Quotient.mk _ h)
  simpa only [normalizedResidueGauss, residueGauss_supported_mk,
    gaussRow] using hb

theorem squarefree_divisor_sixth_of_gauss_zero (u : O)
    (hu : Supported (Ideal.span {u})) (hzero : gaussRow u hu 0 ≠ 0)
    (s : Ideal O) (hs : Squarefree s) (hd : s ∣ Ideal.span {u}) :
    s ^ 6 ∣ Ideal.span {u} := by
  have he := gaussRow_zero_ideal_sixth_power u hu hzero
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

def idealGaussRow (I : Ideal O) (hI : Supported I) (h : O) : ℂ :=
  gaussRow (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h

lemma idealGaussRow_norm_le (I : Ideal O) (hI : Supported I) (h : O) :
    ‖idealGaussRow I hI h‖ ≤ Real.sqrt (Ideal.absNorm I : ℝ) := by
  have hb := gaussRow_norm_le (primaryGenerator I) ((supported_span_primaryGenerator_iff I).mpr hI) h
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

lemma idealGaussRow_zero_sixthRemainder (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) : sixthRemainder I = 1 := by
  have hb := gaussRow_zero_sixthRemainder (primaryGenerator I)
    ((supported_span_primaryGenerator_iff I).mpr hI) hz
  simpa only [idealGaussRow, (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1] using hb

def tupleProduct {r : ℕ} (v : Fin r → Ideal O) : Ideal O := ∏ i, v i

lemma tupleEntry_dvd {r : ℕ} (v : Fin r → Ideal O) (i : Fin r) : v i ∣ tupleProduct v :=
  Finset.dvd_prod_of_mem v (Finset.mem_univ i)

theorem tuple_product_fiber_card {r : ℕ} (S : Finset (Fin r → Ideal O))
    (I : Ideal O) (hI : I ≠ 0) :
    (S.filter (fun v => tupleProduct v = I)).card ≤ (idealDivisors I).card ^ r := by
  let T := S.filter (fun v => tupleProduct v = I)
  let f (v : T) : Fin r → idealDivisors I := fun i => ⟨v.val i, by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact tupleEntry_dvd v.val i⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, T] using
    Fintype.card_le_of_injective f hf

def idealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) : ℂ :=
  ∑ I : S, c I.val * idealGaussRow I.val (hS I.val I.property) 0

theorem idealAddedZero_norm_le (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖idealAddedZero S hS c‖ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) := by
  let F := S.filter (fun I => sixthRemainder I = 1)
  have hcount : (F.card : ℝ) ≤ 128 * Y ^ (1 / 6 : ℝ) := by
    simpa only [map_one, Nat.cast_one, div_one] using
      ideal_count_fixed_remainder F 1 one_ne_zero Y hY
        (fun I hI => (hS I (Finset.mem_filter.mp hI).1).1)
        (fun I hI => (Finset.mem_filter.mp hI).2)
        (fun I hI => hN I (Finset.mem_filter.mp hI).1)
  have hb (I : S) : ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ ≤
      if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 := by
    by_cases hr : sixthRemainder I.val = 1
    · simp only [hr, ite_true, norm_mul]
      exact mul_le_mul (hc I.val I.property)
        ((idealGaussRow_norm_le _ _ _).trans (Real.sqrt_le_sqrt (hN I.val I.property)))
        (norm_nonneg _) hB
    · have hz : idealGaussRow I.val (hS I.val I.property) 0 = 0 := by
        by_contra hn
        exact hr (idealGaussRow_zero_sixthRemainder _ _ hn)
      simp only [hr, ite_false, hz, mul_zero, norm_zero, le_refl]
  calc
    ‖idealAddedZero S hS c‖ ≤ ∑ I : S,
        ‖c I.val * idealGaussRow I.val (hS I.val I.property) 0‖ := norm_sum_le _ _
    _ ≤ ∑ I : S, if sixthRemainder I.val = 1 then B * Real.sqrt Y else 0 :=
      Finset.sum_le_sum (fun I _ => hb I)
    _ = (F.card : ℝ) * (B * Real.sqrt Y) := by
      rw [Finset.sum_coe_sort S (fun I => if sixthRemainder I = 1 then B * Real.sqrt Y else 0)]
      rw [← Finset.sum_filter]
      simp only [F, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hB (Real.sqrt_nonneg _))

def normalizedIdealAddedZero (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (T : ℝ) : ℂ := (Real.sqrt T : ℂ)⁻¹ * idealAddedZero S hS c

theorem idealAddedZero_energy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (B Y T : ℝ) (hB : 0 ≤ B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B) (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y) :
    ‖normalizedIdealAddedZero S hS c T‖ ^ 2 ≤ 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
  have hb := idealAddedZero_norm_le S hS c B Y hB hY hc hN
  have hp : (Y ^ (1 / 6 : ℝ)) ^ 2 * Y = Y ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hY]
    norm_num only [Nat.cast_ofNat]
    conv_lhs => rhs; rw [← Real.rpow_one Y]
    rw [← Real.rpow_add' hY (by norm_num : (1 / 3 : ℝ) + 1 ≠ 0)]
    norm_num
  have hs := sq_le_sq₀ (norm_nonneg (idealAddedZero S hS c)) (by positivity : 0 ≤ (128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y))
  have hb2 := hs.mpr hb
  have hn : ‖normalizedIdealAddedZero S hS c T‖ ^ 2 = T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 := by
    simp only [normalizedIdealAddedZero, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T), mul_pow, inv_pow,
      Real.sq_sqrt hT.le]
  rw [hn]
  calc
    T⁻¹ * ‖idealAddedZero S hS c‖ ^ 2 ≤ T⁻¹ * ((128 * Y ^ (1 / 6 : ℝ)) * (B * Real.sqrt Y)) ^ 2 :=
      mul_le_mul_of_nonneg_left hb2 (inv_nonneg.mpr hT.le)
    _ = 16384 * B ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hY]
      rw [← hp]
      ring

def tupleCoefficient {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (I : Ideal O) : ℂ :=
  ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v

def tupleColumns {r : ℕ} (S : Finset (Fin r → Ideal O)) : Finset (Ideal O) :=
  S.image tupleProduct

lemma tupleColumns_supported {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) :
    ∀ I ∈ tupleColumns S, Supported I := by
  intro I hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
  exact hS v hv

theorem tupleCoefficient_norm_le {r : ℕ} (S : Finset (Fin r → Ideal O))
    (β : (Fin r → Ideal O) → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ v ∈ S, ‖β v‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖tupleCoefficient S β I‖ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
  calc
    ‖tupleCoefficient S β I‖ ≤ ∑ v ∈ S.filter (fun v => tupleProduct v = I), ‖β v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v ∈ S.filter (fun v => tupleProduct v = I), B :=
      Finset.sum_le_sum (fun v hv => hβ v (Finset.mem_filter.mp hv).1)
    _ = B * ((S.filter (fun v => tupleProduct v = I)).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ B * ((idealDivisors I).card : ℝ) ^ r := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast tuple_product_fiber_card S I hI

theorem tuple_added_zero_energy (r : ℕ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Fin r → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v))
      (β : (Fin r → Ideal O) → ℂ) (B Y T : ℝ),
      0 ≤ B → 1 ≤ Y → 0 < T →
      (∀ v ∈ S, ‖β v‖ ≤ B) →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
          (tupleCoefficient S β) T‖ ^ 2 ≤ C * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let δ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hr')
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨16384 * (D ^ r) ^ 2, by positivity, ?_⟩
  intro S hS β B Y T hB hY hT hβ hN
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hδr : δ * (r : ℝ) = ε / 2 := by dsimp [δ]; field_simp
  have hc (I : Ideal O) (hI : I ∈ tupleColumns S) :
      ‖tupleCoefficient S β I‖ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    have hI0 := (hS v hv).1
    have hn0 : (0 : ℝ) ≤ Ideal.absNorm (tupleProduct v) := Nat.cast_nonneg _
    calc
      ‖tupleCoefficient S β (tupleProduct v)‖ ≤
          B * ((idealDivisors (tupleProduct v)).card : ℝ) ^ r :=
        tupleCoefficient_norm_le S β B hB hβ _ hI0
      _ ≤ B * (D * (Ideal.absNorm (tupleProduct v) : ℝ) ^ δ) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hI0) _) hB
      _ = B * (D ^ r * (Ideal.absNorm (tupleProduct v) : ℝ) ^ (ε / 2)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hn0, hδr]
      _ ≤ B * (D ^ r * Y ^ (ε / 2)) := by
        gcongr
        exact hN v hv
  have hn (I : Ideal O) (hI : I ∈ tupleColumns S) : (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
    exact hN v hv
  have he := idealAddedZero_energy (tupleColumns S) (tupleColumns_supported S hS)
    (tupleCoefficient S β) (B * (D ^ r * Y ^ (ε / 2))) Y T (by positivity) hY0.le hT hc hn
  have hy : (Y ^ (ε / 2)) ^ 2 * Y ^ (4 / 3 : ℝ) = Y ^ (4 / 3 + ε : ℝ) := by
    rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0]
    congr 1
    norm_num
    ring
  calc
    _ ≤ 16384 * (B * (D ^ r * Y ^ (ε / 2))) ^ 2 * T⁻¹ * Y ^ (4 / 3 : ℝ) := he
    _ = (16384 * (D ^ r) ^ 2) * B ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
      rw [← hy]
      ring

def originalCoefficient (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Fin (N + 2) → Ideal O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

lemma idealRectangle_norm_le (W₁ W₂ : ℝ → ℂ) (B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) :
    ‖idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J‖ ≤ 2 * B₁ * B₂ := by
  have hprod (x y : ℝ) : ‖W₁ x * W₂ y‖ ≤ B₁ * B₂ := by
    rw [norm_mul]
    exact mul_le_mul (hW₁ x) (hW₂ y) (norm_nonneg _) hB₁
  unfold idealRectangle
  exact (norm_sub_le _ _).trans ((add_le_add
    (hprod ((Ideal.absNorm I : ℝ) / X₁) ((Ideal.absNorm J : ℝ) / X₂))
    (hprod ((Ideal.absNorm I : ℝ) / Y₁) ((Ideal.absNorm J : ℝ) / Y₂))).trans_eq (by ring))

theorem originalCoefficient_norm_le (N : ℕ) (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ)
    (hBslot : ∀ j, 0 ≤ Bslot j) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hν : ∀ j I, ‖ν j I‖ ≤ 1) (hWslot : ∀ j x, ‖Wslot j x‖ ≤ Bslot j)
    (hW₁ : ∀ x, ‖W₁ x‖ ≤ B₁) (hW₂ : ∀ x, ‖W₂ x‖ ≤ B₂)
    (v : Fin (N + 2) → Ideal O) (hv : tupleProduct v ≠ 0) :
    ‖originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v‖ ≤
      (∏ j, Bslot j) * (2 * B₁ * B₂) := by
  have hslots : ‖∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)‖ ≤ ∏ j, Bslot j := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro j hj
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hν j _) (hWslot j _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hweight := idealWeight_norm_le_one c hc χ R t (tupleProduct v) hv
  have hrect := idealRectangle_norm_le W₁ W₂ B₁ B₂ hB₁ hB₂ hW₁ hW₂ X₁ X₂ Y₁ Y₂
    (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩)
  by_cases hs : s ∣ tupleProduct v
  · simp only [originalCoefficient, hs, ite_true, mul_one, norm_mul]
    have hsw := mul_le_mul hslots hweight (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
    simp only [mul_one] at hsw
    exact mul_le_mul hsw hrect (norm_nonneg _) (Finset.prod_nonneg (fun j _ => hBslot j))
  · simp only [originalCoefficient, hs, ite_false, mul_zero, norm_zero]
    exact mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)

lemma originalCoefficient_eq_zero_of_not_dvd (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (v : Fin (N + 2) → Ideal O) (hs : ¬s ∣ tupleProduct v) :
    originalCoefficient N c χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s v = 0 := by
  simp only [originalCoefficient, hs, ite_false, mul_zero]

theorem original_added_zero_energy (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : O), c ≠ 0 →
      ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
      (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
      (Bslot : Fin N → ℝ) (B₁ B₂ : ℝ),
      (∀ j, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j I, ‖ν j I‖ ≤ 1) → (∀ j x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Fin (N + 2) → Ideal O))
      (hS : ∀ v ∈ S, Supported (tupleProduct v)) (Y T : ℝ), 1 ≤ Y → 0 < T →
      (∀ v ∈ S, (Ideal.absNorm (tupleProduct v) : ℝ) ≤ Y) →
      ‖normalizedIdealAddedZero (tupleColumns S) (tupleColumns_supported S hS)
        (tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
          X₁ X₂ Y₁ Y₂ b₁ b₂ s)) T‖ ^ 2 ≤
        C * ((∏ j, Bslot j) * (2 * B₁ * B₂)) ^ 2 * T⁻¹ * Y ^ (4 / 3 + ε : ℝ) := by
  obtain ⟨C, hC, he⟩ := tuple_added_zero_energy (N + 2) (by omega) ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s Bslot B₁ B₂
    hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ S hS Y T hY hT hN
  apply he S hS _ _ Y T (mul_nonneg (Finset.prod_nonneg (fun j _ => hBslot j)) (by positivity)) hY hT _ hN
  intro v hv
  exact originalCoefficient_norm_le N c hc χ R t ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s
    Bslot B₁ B₂ hBslot hB₁ hB₂ hν hWslot hW₁ hW₂ v (hS v hv).1

theorem idealAddedZero_eq_gaussPolynomial (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) :
    idealAddedZero S hS c =
      gaussPolynomial (Finset.univ : Finset S)
        (fun I => primaryGenerator I.val)
        (fun I => (supported_span_primaryGenerator_iff I.val).mpr (hS I.val I.property))
        (fun I => c I.val) 0 := rfl

lemma idealGaussRow_zero_divisor_sixth (I : Ideal O) (hI : Supported I)
    (hz : idealGaussRow I hI 0 ≠ 0) (s : Ideal O) (hs : Squarefree s) (hd : s ∣ I) :
    s ^ 6 ∣ I := by
  have hrem := idealGaussRow_zero_sixthRemainder I hI hz
  have he : sixthQuotient I ^ 6 = I := by
    simpa only [hrem, one_mul] using sixth_normal_form I hI.1
  rw [← he] at hd ⊢
  exact pow_dvd_pow_of_dvd ((hs.dvd_pow_iff_dvd (by decide : 6 ≠ 0)).mp hd) 6

theorem idealAddedZero_nonzero_mask_norm (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Y : ℝ)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Y)
    (hz : idealAddedZero S hS c ≠ 0) : (Ideal.absNorm s : ℝ) ^ 6 ≤ Y := by
  obtain ⟨I, _, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hg : idealGaussRow I.val (hS I.val I.property) 0 ≠ 0 := by
    intro he
    exact hI (by rw [he, mul_zero])
  have hd : s ∣ I.val := by
    by_contra hn
    exact hI (by rw [hmask I.val I.property hn, zero_mul])
  have hpow := idealGaussRow_zero_divisor_sixth I.val (hS I.val I.property) hg s hs hd
  have hn := (norm_le_of_dvd (hS I.val I.property).1 hpow).trans (hN I.val I.property)
  simpa only [map_pow, Nat.cast_pow] using hn

theorem original_tupleCoefficient_mask (N : ℕ) (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : Fin N → Ideal O → ℂ) (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O)
    (S : Finset (Fin (N + 2) → Ideal O)) (I : Ideal O) (hs : ¬s ∣ I) :
    tupleCoefficient S (originalCoefficient N c χ R t ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ b₁ b₂ s) I = 0 := by
  apply Finset.sum_eq_zero
  intro v hv
  apply originalCoefficient_eq_zero_of_not_dvd
  rwa [(Finset.mem_filter.mp hv).2]

theorem added_zero_exponent (a s θ : ℝ) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6) :
    a / 3 + 4 * θ / 3 ≤ a - s + 2 * θ := by linarith

theorem added_zero_scale_identity (Z a θ : ℝ) (hZ : 0 < Z) :
    (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) = Z ^ (a / 3 + 4 * θ / 3) := by
  rw [← Real.rpow_neg hZ.le, ← Real.rpow_mul hZ.le, ← Real.rpow_add hZ]
  congr 1
  ring

theorem idealAddedZero_source_energy (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (B Z a s θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 ≤ Z) (ha : -θ ≤ a) (hs : s ≤ (a + θ) / 6)
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s + 2 * θ) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := idealAddedZero_energy S hS c B (Z ^ (a + θ)) (Z ^ a)
    hB (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hc hN
  calc
    _ ≤ 16384 * B ^ 2 * (Z ^ a)⁻¹ * (Z ^ (a + θ)) ^ (4 / 3 : ℝ) := he
    _ = 16384 * B ^ 2 * Z ^ (a / 3 + 4 * θ / 3) := by
      rw [mul_assoc, added_zero_scale_identity Z a θ hZ0]
    _ ≤ 16384 * B ^ 2 * Z ^ (a - s + 2 * θ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (added_zero_exponent a s θ ha hs))
        (by positivity)

theorem idealAddedZero_nonzero_mask_dyad (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (Z a s₀ θ : ℝ) (hZ : 1 < Z)
    (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ))
    (hz : idealAddedZero S hS c ≠ 0) : -θ ≤ a ∧ s₀ ≤ (a + θ) / 6 := by
  have hZ0 : 0 < Z := lt_trans zero_lt_one hZ
  obtain ⟨I, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hY : 1 ≤ Z ^ (a + θ) :=
    (norm_one_le (hS I.val I.property).1).trans (hN I.val I.property)
  have ha : 0 ≤ a + θ := (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero] using hY)
  have hm := idealAddedZero_nonzero_mask_norm S hS c s hs hmask (Z ^ (a + θ)) hN hz
  have hp : Z ^ (s₀ * (6 : ℕ)) ≤ Z ^ (a + θ) := by
    rw [Real.rpow_mul_natCast hZ0.le]
    exact (pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) hNs 6).trans hm
  have hsp := (Real.rpow_le_rpow_left_iff hZ).mp hp
  constructor <;> norm_num at hsp ⊢ <;> linarith

theorem idealAddedZero_source_energy_of_mask (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ) (s : Ideal O) (hs : Squarefree s)
    (hmask : ∀ I ∈ S, ¬s ∣ I → c I = 0) (B Z a s₀ θ : ℝ)
    (hB : 0 ≤ B) (hZ : 1 < Z) (hNs : Z ^ s₀ ≤ (Ideal.absNorm s : ℝ))
    (hc : ∀ I ∈ S, ‖c I‖ ≤ B)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ Z ^ (a + θ)) :
    ‖normalizedIdealAddedZero S hS c (Z ^ a)‖ ^ 2 ≤
      16384 * B ^ 2 * Z ^ (a - s₀ + 2 * θ) := by
  by_cases hz : idealAddedZero S hS c = 0
  · simp only [normalizedIdealAddedZero, hz, mul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.rpow_nonneg (by linarith) _)
  · obtain ⟨ha, hss⟩ := idealAddedZero_nonzero_mask_dyad S hS c s hs hmask Z a s₀ θ hZ hNs hN hz
    exact idealAddedZero_source_energy S hS c B Z a s₀ θ hB hZ.le ha hss hc hN

theorem actual_tuple_gauss_eq_columns {r : ℕ} (S : Finset (Fin r → Ideal O))
    (hS : ∀ v ∈ S, Supported (tupleProduct v)) (β : (Fin r → Ideal O) → ℂ) :
    gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 =
    idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) := by
  let g (I : Ideal O) : ℂ := if hI : Supported I then idealGaussRow I hI 0 else 0
  have hl : gaussPolynomial (Finset.univ : Finset S)
      (fun v => primaryGenerator (tupleProduct v.val))
      (fun v => (supported_span_primaryGenerator_iff (tupleProduct v.val)).mpr (hS v.val v.property))
      (fun v => β v.val) 0 = ∑ v ∈ S, β v * g (tupleProduct v) := by
    rw [← Finset.sum_coe_sort S (fun v => β v * g (tupleProduct v))]
    apply Finset.sum_congr rfl
    intro v hv
    simp only [g, dite_eq_left (hS v.val v.property), idealGaussRow]
  have hr : idealAddedZero (tupleColumns S) (tupleColumns_supported S hS) (tupleCoefficient S β) =
      ∑ I ∈ tupleColumns S, tupleCoefficient S β I * g I := by
    rw [← Finset.sum_coe_sort (tupleColumns S) (fun I => tupleCoefficient S β I * g I)]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [g, dite_eq_left (tupleColumns_supported S hS I.val I.property)]
  rw [hl, hr]
  symm
  simp only [tupleCoefficient, Finset.sum_mul]
  calc
    (∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g I) =
        ∑ I ∈ tupleColumns S, ∑ v ∈ S.filter (fun v => tupleProduct v = I), β v * g (tupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = ∑ v ∈ S, β v * g (tupleProduct v) :=
      Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v, hv, rfl⟩) _

end SevenEighths.CenteredMomentAddedZero

end

end OAI

end

