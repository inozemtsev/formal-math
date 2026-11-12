module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part023
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part006
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part007
public import Green64.Library.Analysis.NumberTheory.DirichletL.Moments.Part008

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Inversion / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyRetained -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialProfile CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

def retainedWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val)≤L)

def tailWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>L< radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val))

theorem window_sum_split (a b:Fin 4→ℝ)(Z D m L:ℝ)(f:Windows a b→ℂ) :
    (∑k,f k)=(∑k∈retainedWindows a b Z D m L,f k)+
      ∑k∈tailWindows a b Z D m L,f k := by
  simpa only [retainedWindows,tailWindows,not_le] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ:Finset (Windows a b))
      (fun k=>radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
        (exponent Z (k 0).val)≤L) f).symm

theorem retained_exponents_eventually (b R Λ:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D m L T:ℝ,D≤R→0≤ m→L≤Λ→0<T→
      ∀k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
        ∀i,exponent Z (k i).val∈Set.Icc 0 (3*R+Λ+1) := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro D m L T hD hm hL hT k hk
  have hs:radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
      (exponent Z (k 0).val)≤L := (Finset.mem_filter.mp hk).2
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hZ.1]) D)
  have h0:=hZ.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hZ.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  have h2:=hZ.2 (b*Z^D) D hp le_rfl (k 2).val (k 2).property
  have h3:=window_exponent_nonneg Z T hZ.1 hT (k 3).val (k 3).property
  unfold radialCenter at hs
  intro i
  fin_cases i
  · change exponent Z (k 0).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h0.1,by linarith [h0.2]⟩
  · change exponent Z (k 1).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h1.1,by linarith [h1.2]⟩
  · change exponent Z (k 2).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h2.1,by linarith [h2.2]⟩
  · change exponent Z (k 3).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h3,by linarith [h0.1,h1.2]⟩

theorem window_quotient_eventually (b R:ℝ)(hb:0<b) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D T η:ℝ,D≤R→0<T→η≤1→
      ∀k:Windows (fun _=>1) (physicalCaps b Z D T),
        exponent Z (k 0).val-exponent Z (k 1).val+2*η≤R+3 := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro D T η hD hT hη k
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hz.1]) D)
  have h0:=hz.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hz.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  linarith [h0.2,h1.1]

theorem retained_card_of_exponents (a b:Fin 4→ℝ)(Z D m L A:ℝ)(hZ:1<Z)
    (he:∀k∈retainedWindows a b Z D m L,∀i,exponent Z (k i).val∈Set.Icc 0 A) :
    (retainedWindows a b Z D m L).card≤
      Fintype.card (Windows (fun _=>1) (fun _=>Z^A)) := by
  have hZp:0<Z := by linarith
  let f:↥(retainedWindows a b Z D m L)→Windows (fun _=>1) (fun _=>Z^A) :=
    fun k i=>⟨(k.val i).val,(mem_indices_iff_scale 1 (Z^A) (by norm_num)
      (Real.rpow_pos_of_pos hZp A) (k.val i).val).mpr ⟨by
        rw [←exponent_scale Z hZ]
        simpa only [Real.rpow_zero] using
          (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).1,by
        have hh:(dyadicScale (k.val i).val)≤Z^A := by
          rw [←exponent_scale Z hZ]
          exact (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).2
        exact hh.trans (by nlinarith [Real.rpow_pos_of_pos hZp A])⟩⟩
  have hf:Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem retained_card_subpower (b R Λ ε:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in atTop,
      ∀D m L T:ℝ,D≤R→0≤ m→L≤Λ→0<T→
        ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤A*Z^ε := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower 1 (3*R+Λ+1) ε (by norm_num) (by positivity) hε
  refine ⟨A,hA,?_⟩
  filter_upwards [retained_exponents_eventually b R Λ hb hR hΛ,hcount] with Z hz hc
  intro D m L T hD hm hL hT
  have he:=hz.2 D m L T hD hm hL hT
  have hi:=retained_card_of_exponents (fun _=>1) (physicalCaps b Z D T) Z D m L
    (3*R+Λ+1) hz.1 he
  have hp:(1:ℝ)≤Z^(3*R+Λ+1) := Real.one_le_rpow (le_of_lt hz.1) (by positivity)
  exact (by exact_mod_cast hi :
    ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤
      (Fintype.card (Windows (fun _=>1) (fun _=>Z^(3*R+Λ+1))):ℝ)).trans
    (hc (fun _=>1) (fun _=>Z^(3*R+Λ+1)) (by intro i; norm_num)
      (fun _=>hp) (by intro i; simp))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyTail -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def windowMass {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) : ℝ :=
  ∑k∈F,∏i:Fin 4,dyadicWeight (k i).val (q i)

theorem windowMass_cast {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    (windowMass F q:ℂ)=∑k∈F,weight (fun i=>(k i).val) q := by
  simp only [windowMass,weight,Complex.ofReal_sum,Complex.ofReal_prod]

theorem windowMass_nonneg {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    0≤windowMass F q := by
  apply Finset.sum_nonneg
  intro k hk
  exact Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1)

theorem windowMass_univ (a b q:Fin 4→ℝ)(ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    windowMass (Finset.univ:Finset (Windows a b)) q=1 := by
  apply Complex.ofReal_injective
  rw [windowMass_cast,Complex.ofReal_one]
  exact weight_partition a b q ha hq

theorem windowMass_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : windowMass F q≤1 := by
  rw [←windowMass_univ a b q ha hq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun k hk hnot=>Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1))

theorem windowMass_norm_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : ‖(windowMass F q:ℂ)‖≤1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (windowMass_nonneg F q)]
    using windowMass_le_one F q ha hq

theorem windowMass_ne_zero_exists {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (h:windowMass F q≠0) : ∃k∈F,weight (fun i=>(k i).val) q≠0 := by
  have hc:(windowMass F q:ℂ)≠0:=by exact_mod_cast h
  rw [windowMass_cast] at hc
  exact Finset.exists_ne_zero_of_sum_ne_zero hc

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem windowBlock_eq_full
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)(k:Fin 4→ℤ) :
    windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m k =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*weight k (sourceNorms p x))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [source_weight_cutoff p Z D hZ]
  exact (physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m
    w Ψ j marks W₁ W₂ Φ).symm

theorem sum_windowBlock_eq_mass
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    (∑k∈F,windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
        Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [windowBlock_eq_full p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m hZ]
  unfold physicalBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply]
  rw [←Finset.sum_mul,←Finset.mul_sum,←windowMass_cast]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem mass_weight_bound
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(x:Source (ι:=ι) 0)
    (hx:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    ‖w x*(windowMass F (sourceNorms p x):ℂ)‖≤‖w x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (windowMass_norm_le_one F _ ha hx)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L< radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))≠0 := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  rwa [source_weight_cutoff p Z D hZ] at hne

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live_bounds (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L< radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      ∀i,sourceNorms p x i∈Set.Ioo (Z^(exponent Z (k i).val)/4) (Z^(exponent Z (k i).val)) := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  intro i
  have hi:(dyadicWeight (k i).val (sourceNorms p x i):ℂ)≠0 :=
    Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  have hr:dyadicWeight (k i).val (sourceNorms p x i)≠0 := by exact_mod_cast hi
  rw [exponent_scale Z hZ]
  exact dyadicWeight_support (k i).val hr

theorem physicalBlock_filter_of_live
    (source:Finset (Point ι))(P:Point ι→Prop)(w:Point ι→ℂ)
    (Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hP:∀x∈source,∀ρ:SecondRayIndex,
      w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m x ρ≠0→P x) :
    physicalBlock p hp hcop hg source w Ψ j marks W₁ W₂ Φ Z D m =
      physicalBlock p hp hcop hg (source.filter P) w Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hh:P x
  · rw [ite_eq_left hh]
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro ρ hρ
    by_contra hn
    exact hh (hP x hx ρ hn)

theorem physicalBlock_mass_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg
      (pointSource pool (S.filter (fun x=>windowMass F (sourceNorms p x)≠0)))
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hn:windowMass F (sourceNorms p x)=0
  · simp only [hn,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,
      erase_sourcePoint,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left hn]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem exists_source_frequency_cap (S:Finset (Source (ι:=ι) 0)) :
    ∃T:ℝ,0<T ∧ ∀x∈S,sourceNorms p x 3≤T := by
  have hn (x:Source (ι:=ι) 0) : 0≤ sourceNorms p x 3 := by
    change 0≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    positivity
  have hs:0≤∑x∈S,sourceNorms p x 3:=Finset.sum_nonneg (fun x hx=>hn x)
  refine ⟨1+∑x∈S,sourceNorms p x 3,by linarith,?_⟩
  intro x hx
  have he:sourceNorms p x 3≤∑y∈S,sourceNorms p y 3 :=
    Finset.single_le_sum (fun y hy=>hn y) hx
  linarith

theorem actual_physical_retained_tail
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T L:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    (∑k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) +
    physicalBlock p hp hcop hg
      (pointSource pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T)))
      ((fun x=>w x*(windowMass (tailWindows (fun _=>1) (physicalCaps b Z D T) Z D m L)
        (sourceNorms p x):ℂ))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  rw [actual_physical_partition p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ
    Z D m b T hZ hW₁ hW₂ hT]
  rw [window_sum_split (fun _=>1) (physicalCaps b Z D T) Z D m L]
  congr 1
  exact sum_windowBlock_eq_mass p hp hcop hg pool
    (cappedSource p S (fun _=>1) (physicalCaps b Z D T)) _ _ _ w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailGates -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialDyadicAssembly InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem pointSource_erase_mem (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (x : Point ι) (hx : x∈pointSource pool S) : erasePoint x∈S := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  simpa only [erase_sourcePoint] using hy

theorem pointSource_supports (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hC : ∀x∈S,x.common⊆pool) (hV : ∀x∈S,x.overlap⊆pool)
    (hdiv : ∀x∈S,x.divisor⊆x.common)
    (x : Point ι) (hx : x∈pointSource pool S) :
    ∀i,InverseInitialHighFrequencyTail.sourceKey x i⊆pool := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  intro i
  fin_cases i
  · exact hC y hy
  · exact (hdiv y hy).trans (hC y hy)
  · exact hV y hy
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).2).trans Finset.sdiff_subset

def idealIndex : Fin 5→Fin 6 := ![0,1,2,4,5]

omit [DecidableEq ι] in
theorem sourceKey_norm_coordinate (p : ι→O) (x : Point ι) (i : Fin 5) :
    primeProductNorm p (InverseInitialHighFrequencyTail.sourceKey x i)=coordinates p x (idealIndex i) := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  fin_cases i <;> simp [InverseInitialHighFrequencyTail.sourceKey,coordinates,physicalCoordinates,idealIndex,hn]

omit [DecidableEq ι] in
theorem sourceNorms_erase (p : ι→O) (x : Point ι) (i : Fin 4) :
    sourceNorms p (erasePoint x) i=coordinates p x (InverseSecondChildWindows.outerIndex i) := by
  have he : InverseInitialEnergyCallerModes.sourcePoint (erasePoint x) x.left x.right=x := by
    cases x
    rfl
  simpa only [he] using sourceNorms_fresh p (erasePoint x) x.left x.right i

omit [DecidableEq ι] in
theorem live_mass_radial_gate
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (a b : Fin 4→ℝ) (Z D m η τ bW : ℝ) (hZ : 1<Z) (hη : 0≤η)
    (hbW : 0<bW) (hfixed : 64*bW^2≤Z^η)
    (x : Point ι) (hx : Valid x)
    (hleft : coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D)
    (hright : coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D)
    (hmass : windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0) :
    Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2 := by
  obtain ⟨k,hk,hhigh,hbounds⟩ := tail_mass_live_bounds p a b Z D m (4*η+τ) hZ (erasePoint x) hmass
  have hc := coordinates_pos p hp x hx
  have h₀ := (hbounds 0).1.le
  have h₁ := (hbounds 1).2.le
  have h₃ := (hbounds 3).1.le
  rw [sourceNorms_erase] at h₀ h₁ h₃
  have hh := InverseInitialHighFrequencyTail.actual_annulus_high_gate Z D m
    (exponent Z (k 0).val) (exponent Z (k 1).val) (exponent Z (k 3).val) η τ bW
    (coordinates p x 0) (coordinates p x 1) (coordinates p x 2)
    (coordinates p x 4) (coordinates p x 5) (coordinates p x 3)
    hZ.le hη hbW (hc 1) (hc 2) (hc 4) (hc 5) h₀ h₁ h₃ hleft hright hfixed hhigh.le
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  simpa [coordinates,physicalCoordinates,hn] using hh

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailBound -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialDyadicAssembly InverseInitialProfile
open InverseInitialRetainedSupport InverseInitialHighFrequencyTail
local notation "O"=>ActualEisensteinCubic.O

theorem actual_high_mass_tail (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (weights : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m η bW Γ B₁ B₂ : ℝ),
    1<Z → 0≤η → 0<bW → 64*bW^2≤Z^η →
    0≤Lcap → bW*Z^D≤Z^Lcap → -m≤Lcap → m-D≤Lcap →
    0≤Γ → 0≤B₁ → 0≤B₂ → (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    Function.support W₁⊆Set.Iic bW → Function.support W₂⊆Set.Iic bW →
    ∀ (pool : Finset ι) (S : Finset (Source (ι:=ι) 0)) (w : Source (ι:=ι) 0→ℂ),
    (∀x∈S,x.common⊆pool) → (∀x∈S,x.overlap⊆pool) →
    (∀x∈S,x.divisor⊆x.common) → (∀x∈S,x.frequency≠0) → (∀x∈S,‖w x‖≤Γ) →
    ∀ (a b : Fin 4→ℝ), (∀i,0<a i) → (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) →
    ‖physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨s,C,hC,hrapid⟩ := original_physical_tail_rapid Lcap saving τ hτ
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  let wt : Point ι→ℂ := ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ))
    (sourceNorms p x):ℂ))∘erasePoint)
  let live (x : Point ι) : Prop := ∃ρ : SecondRayIndex,
    wt x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m x ρ≠0
  let F := (pointSource pool S).filter live
  have hmem (x) (hx : x∈F) : x∈pointSource pool S := (Finset.mem_filter.mp hx).1
  have hvalid (x) (hx : x∈F) : Valid x := pointSource_valid pool S hdiv hfreq x (hmem x hx)
  have hold (x) (hx : x∈F) : erasePoint x∈S := pointSource_erase_mem pool S x (hmem x hx)
  have hgeometry (x) (hx : x∈F) :
      (coordinates p x 0≤bW*Z^D ∧ coordinates p x 1≤bW*Z^D ∧
       coordinates p x 2≤bW*Z^D ∧ coordinates p x 4≤bW*Z^D ∧ coordinates p x 5≤bW*Z^D) ∧
      (coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D ∧
       coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D) ∧
      windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0 := by
    obtain ⟨ρ,hρ⟩ := (Finset.mem_filter.mp hx).2
    have hpterm := (mul_ne_zero_iff.mp hρ).2
    refine ⟨live_ideal_caps p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,
      live_whole_columns p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,?_⟩
    intro hz
    apply (mul_ne_zero_iff.mp hρ).1
    simp only [wt,Function.comp_apply,hz,Complex.ofReal_zero,mul_zero]
  have hn (x : Point ι) (i : Fin 5) := sourceKey_norm_coordinate p x i
  have hwhole (x) (hx : x∈F) :
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤bW*Z^D ∧
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤bW*Z^D := by
    have he := (hgeometry x hx).2.1
    have hn0 := hn x 0
    have hn2 := hn x 2
    have hn3 := hn x 3
    have hn4 := hn x 4
    simp [sourceKey,idealIndex] at hn0 hn2 hn3 hn4
    rw [←hn0,←hn2,←hn3,←hn4] at he
    exact he
  have hfilter := physicalBlock_filter_of_live p hp hcop hg (pointSource pool S) live wt Ψ j
    (primeMark slots lists weights) W₁ W₂ Φ Z D m (fun x hx ρ hn=>⟨ρ,hn⟩)
  change ‖physicalBlock p hp hcop hg (pointSource pool S) wt Ψ j _ W₁ W₂ Φ Z D m‖≤_
  rw [hfilter]
  have hr := hrapid p hp hcop hg hinj hc Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m (max 1 (bW*Z^D)) Γ B₁ B₂ hZ.le (le_max_left _ _) hcap
    (max_le (Real.one_le_rpow hZ.le hcap) hsize) hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool F wt hvalid
  suffices hbound : ‖physicalBlock p hp hcop hg F wt Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) by
    have hset : @Finset.filter (Point ι) live (fun x=>Classical.propDecidable (live x))
        (pointSource pool S)=F := by
      ext x
      simp only [Finset.mem_filter,F]
    rw [hset]
    exact hbound
  refine hr ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (mass_weight_bound p a b _ ha w (erasePoint x) (hrange _ (hold x hx))).trans (hw _ (hold x hx))
  · intro x hx
    exact pointSource_supports pool S hcommon hoverlap hdiv x (hmem x hx)
  · intro x hx i
    rw [sourceKey_norm_coordinate]
    have he := (hgeometry x hx).1
    apply le_trans _ (le_max_right 1 (bW*Z^D))
    fin_cases i
    · exact he.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2
  · intro x hx
    exact (hwhole x hx).1.trans (le_max_right _ _)
  · intro x hx
    exact (hwhole x hx).2.trans (le_max_right _ _)
  · intro x hx
    exact live_mass_radial_gate p hp a b Z D m η τ bW hZ hη hbW hfixed x
      (hvalid x hx) (hgeometry x hx).2.1.1 (hgeometry x hx).2.1.2 (hgeometry x hx).2.2

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSum -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedSum
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseSecondChildWindows Filter
local notation "O"=>ActualEisensteinCubic.O

theorem retained_sum_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(D m r T:ℝ),0≤ m→0<T→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          (cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)) w Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0< max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨J,Btree,Tclip,hBtree,hTclip,hwindow⟩:=
    InverseInitialRetainedWindow.retained_window_bound W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
      (fun _=>1/4) (fun _=>1) (by intros;norm_num) (by intros;norm_num)
      cap gap eps (cap+3) π hcap hgap heps (by linarith) hπ K
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 hb (by norm_num)
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and hevent)))
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Zq,hC,hZq,hw⟩:=hwindow q hq
  refine ⟨A*C,max Zq Zaux,mul_pos hA hC,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf D m r T hm hT
    hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hweight
  have hZq':Zq≤Z:=(le_max_left _ _).trans hZ
  obtain ⟨hcZ,hpow,hlog,hexp⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hZp:1<Z:=hZq.trans_le hZq'
  have hDcap:D≤ cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq]
    linarith
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hlo:Z^(-η)≤(1/4:ℝ):=by
    rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
  have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
      (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
      ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
        (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    have hsize:0< max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
    have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
    have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
    apply hw Z hZq' Dpool hD all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
      qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod Sc hdivc hfc cutoff
      (fun i x hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx))
      D (exponent Z (k 0).val) (exponent Z (k 2).val) (exponent Z (k 1).val)
      (exponent Z (k 3).val) m r η τ hη.le hηsmall hτsmall
      (fun _=>by linarith) hlo hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent
      (by linarith [h0.2,h1.1]) (Finset.mem_filter.mp hk).2 c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂
      (fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))) ?_
    intro x hx
    rw [norm_mul]
    have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb₀ ha).trans hb
    apply hmul (hweight x (Finset.mem_filter.mp hx).1) (by positivity)
    unfold outerCutoff
    simp only [norm_mul]
    exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
      (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hnorm).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _≤(A*Z^loss)*(C*Z^(m+15*η+π+eps)*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
      mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
    _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];ring

end SevenEighths.InverseInitialRetainedSum

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialFiniteEnergy -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialFiniteEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

theorem finite_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ
        (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨J,Btree,hBtree,hretained⟩:=InverseInitialRetainedSum.retained_sum_bound
    W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨ss,Ct,hCt,htail⟩:=InverseInitialDyadicTailBound.actual_high_mass_tail (2*cap+2) 1 τ hτ
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC:0≤tailC:=by dsimp [tailC];positivity
  have hevent:∀ᶠZ:ℝ in atTop,max 1 b₀≤Z ∧ 64*(max 1 b₀)^2≤Z^η:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp hevent
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cr,Zr,hCr,hZr,hretained⟩:=hretained q hq
  refine ⟨Cr+tailC,max Zr Zaux,by linarith,lt_max_of_lt_left hZr,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZr':Zr≤Z:=(le_max_left _ _).trans hZ
  have hZp:1<Z:=hZr.trans_le hZr'
  obtain ⟨hbZ,h64⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hDcap:D≤ cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z^D≤Z^(2*cap+2):=by
    calc
      _≤Z*Z^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z^(D+1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  have hs₁':Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₁ a₀ b₀ c₁ θ₁ ha₀ hc₁ hs₁ hx) (le_max_right 1 b₀)
  have hs₂':Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₂ a₀ b₀ c₂ θ₂ ha₀ hc₂ hs₂ hx) (le_max_right 1 b₀)
  obtain ⟨T,hT,hfreqcap⟩:=exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hret:=hretained Z hZr' Dpool hD all assigned hassigned hK lists Hslot coeff
    hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf
    D m r T hm hT hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hheight:1≤((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂]))
  have hpow:Z^(-1:ℝ)≤Z^(m+15*η+π+eps+loss):=
    Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  apply (add_le_add hret ht).trans
  change Cr*Z^(m+15*η+π+eps+loss)*_+(Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-1:ℝ))≤_
  have hh:tailC*Z^(-1:ℝ)≤tailC*Z^(m+15*η+π+eps+loss)*
      ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤tailC*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left hpow htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert add_le_add_left hh (Cr*Z^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

end SevenEighths.InverseInitialFiniteEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialTotalEnergy -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(c θ:ℝ),1≤ c→c≤bcap→
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists coeff)
            (clippedSource W c θ) Z D) u‖^2:ℝ)‖≤
        C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*degree)) := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc a₀ b₀:=by
    intro x hx
    apply hs
    simpa only [Function.mem_support,star_ne_zero] using hx
  have hbStar:∀x,‖star (W x)‖≤B₀:=by intro x;simpa only [norm_star] using hb x
  obtain ⟨J,Btree,hBtree,hfinite⟩:=InverseInitialFiniteEnergy.finite_physical_bound
    (fun x=>star (W x)) W a₀ b₀ bcap ha₀ hbcap hsstar hs
    (Complex.conjCLE.contDiff.comp hW) hW Φ B₀ hB₀ hbStar hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cz,hCz,hzero⟩:=InverseInitialZeroMode.physical_marked_zero_bound
    loss cap (max 1 b₀) B₀ hloss hcap (by positivity) hB₀ Φ
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cf,Z₀,hCf,hZ₀,hfinite⟩:=hfinite q hq
  refine ⟨Cf+Cz,Z₀,by linarith,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent c θ hc hbc
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hDcap:D≤ cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hconj:(fun x=>star (clippedSource W c θ x))=clippedSource (fun x=>star (W x)) c (-θ):=
    funext (clippedSource_conjugate W c θ)
  have hn:=nonzero_frequency_norm_le p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m
    (Cf*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)))
    (by linarith : 0<Z) (by
      intro freqT hzero
      rw [hconj]
      have h:=hfinite Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        (finiteSource Finset.univ freqT)
        (finiteSource_divisor Finset.univ freqT) (finiteSource_nonzero Finset.univ freqT hzero)
        (fun x hx=>Finset.subset_univ _) (fun x hx=>Finset.subset_univ _)
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
        c c (-θ) θ hc hbc hc hbc (fun _=>1) (by intros;norm_num)
      simpa only [Function.comp_def,norm_neg,pow_mul,pow_two,mul_pow] using h)
  have hz0:=hzero p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa)
    Finset.univ Ψ hΨ (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W c θ) (clipped_bound W B₀ hb c θ)
    (fun x hx=>le_trans (clipped_support_upper W a₀ b₀ c θ ha₀ hc hs hx) (le_max_right 1 b₀))
    Z D m hZp.le hDcap
  rw [original_input_zero_nonzero p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m (by linarith)]
  apply (norm_add_le _ _).trans
  have hh:1≤(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=one_le_pow₀ (by linarith [norm_nonneg θ])
  have hz1:Cz*Z^(m+loss)≤Cz*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤Cz*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)) hCz.le
      _≤_:=le_mul_of_one_le_right (by positivity) hh
  change ‖physicalFrequency _ _ _ _ _ _ _ _ _ _ _ _ _ 0‖+_≤_
  exact (add_le_add (hz0.trans hz1) hn).trans_eq (by ring)

end SevenEighths.InverseInitialTotalEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Dictionary.InverseRawInputBound -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawInputBound
open ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT CompletedGauss SecondPassArithmetic CanonicalQuadraticSieve CanonicalRowCompletion
open CanonicalCoefficientClass InverseMoment InverseInitialProfile InverseInitialRayAttachment
open InverseInitialQuotientGeometry InverseInitialProfileBounds
local notation "O"=>ActualEisensteinCubic.O

theorem raw_input_bound
    (W:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support W⊆Set.Icc a b)
    (Φ:𝓢(ℝ,ℂ))(gap eps π η τ loss:ℝ)
    (hgap:0<gap)(heps:0<eps)(hπ:0<π)(hη:0<η)(hηone:η≤1)
    (hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss):
    ∃J:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^3≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hg:=poolPrimary_good F hF;
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀ (r t : ℝ), (-2 : ℝ) ≤ r → r ≤ 1 - 2 * gap → 2 * r ≤ 3 - 2 * gap → r + 7 * η ≤ 2 →
    ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z)*
      (‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ 1 1 1
        (initialTest p (fun _=>1) (childLogTest W t) Z r) u‖^2:ℝ)‖≤
      C*Z^(1+15*η+π+eps+loss)*(1+‖t‖)^(2*J) := by
  have hB:0≤SchwartzMap.seminorm ℝ 0 0 W:=apply_nonneg _ _
  have hb:∀x,‖W x‖≤SchwartzMap.seminorm ℝ 0 0 W:=fun x=>by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using W.le_seminorm ℝ 0 0 x
  obtain ⟨degree,Btree,hBtree,hbound⟩:=InverseInitialTotalEnergy.original_input_bound
    W a b 1 ha le_rfl hs (W.smooth ⊤) Φ _ hB hb 2 gap eps π η τ loss
    (by norm_num) hgap heps hπ hη hηone hηsmall hτ hτsmall hloss 0
  refine ⟨InverseClippingProfiles.momentOrder (4*degree),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hpool F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro p hg Ψ hΨ hperiod r t hrlo hr₁ hr₂ hrcap
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hpool':Btree*Z^((2:ℝ)+1)≤Dpool:=by norm_num;exact hpool
  have hp:=Real.one_le_rpow hZp.le hη.le
  have h:=hbound Z hZ Dpool hpool' (σ:=Fin 0) ∅ ∅ (by simp) (by simp)
    (fun _=>∅) (fun _=>1) (fun _ _=>0) (by simp) (by simp) (by simp) (by simp)
    (fun _=>1) (fun _=>0) (fun _=>1) (fun _=>1) (fun _ _=>0)
    (by simp) (by simp) (by simp) (by simp) Ψ hΨ hperiod r 1 r
    (by norm_num) (by norm_num) hrlo (by simpa using hp) (by simpa [assignedCenter] using hp)
    (by simp [assignedCenter]) (by simpa [assignedCenter] using hr₁)
    (by simpa [assignedCenter] using hr₂) (by simpa [assignedCenter] using hrcap)
    1 t le_rfl le_rfl
  simp only [Finset.sdiff_self,assignedElement,Finset.prod_empty] at h
  have hemark : primeMark (∅:Finset (Fin 0)) (fun _=> (∅:Finset (primePool F)))
      (fun _ _=> (0:ℂ))=(fun _=>1) := by
    funext A
    exact primeMark_empty _ _ A
  rw [hemark] at h
  simpa only [
    Real.rpow_one,←childLogTest_eq_clipped] using h

end SevenEighths.DetectorDictionaryInverseRawInputBound

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialInputRadial -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialInputRadial
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT
open InverseInitialConjugateEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_energy_summable (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(Y:ℝ)(hY:0<Y):
    Summable (fun u:O=>Φ (‖eisEmbedding u‖^2/Y)*
      (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)):=by
  let c:Finset ι→ℂ:=fun S=>a*supportMobius (fun i=>Ideal.span {p i}) S*
    secondInputCoefficient p hg Ψ j 1 1 test S
  have he (u:O):a*inputConjugateRow p hg pool Ψ j 1 1 test u=
      star (∑S∈pool.powerset,star (c S)*finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u):=by
    simp only [inputConjugateRow,supportConjugateSum,Finset.mul_sum,star_sum,star_mul,star_star,c]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  simp_rw [he,norm_star]
  exact finiteSquarefreeRow_smoothed_mean_square_summable (fun i=>Ideal.span {p i}) hg
    pool.powerset id (fun S=>star (c S)) Φ Y hY

theorem finite_rows_le_input_norm (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)
    (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (Y:ℝ)(hY:0<Y)(rows:Finset O)(hrows:∀u∈rows,‖eisEmbedding u‖^2≤Y):
    (∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)≤
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)‖:=by
  have hs:=input_energy_summable p hg pool Ψ j test a Φ Y hY
  have hr:=Complex.hasSum_re hs.hasSum
  have hfin:(∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)=
      ∑u∈rows,(Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)).re:=by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hone _ ⟨div_nonneg (sq_nonneg _) hY.le,(div_le_one hY).mpr (hrows u hu)⟩]
    simp only [one_mul,Complex.ofReal_re]
  rw [hfin]
  apply (hr.summable.sum_le_tsum rows (fun u _=>?_)).trans
  · rw [hr.tsum_eq]
    exact Complex.re_le_norm _
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (hΦ _) (sq_nonneg _)

end SevenEighths.InverseInitialInputRadial

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialTotalRows -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalRows
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_rows_fourier_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(θ:ℝ),
      (∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)))
            (childLogTest W θ) Z D) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalEnergy.original_input_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨InverseClippingProfiles.momentOrder (4*J),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y θ
  have hZp:1<Z:=hZ₀.trans_le hZ
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot
    (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)) hdis hHs hPs
    (by intro i hi P hP;simpa only [norm_mul,FourierBridge.logPhase_norm,mul_one] using hac i hi P hP)
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent 1 θ le_rfl hbcap
  have hr:=InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ Ψ
    (assignedElement assigned qelem)
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P))) (childLogTest W θ) Z D)
    ((Z^(-D/2):ℝ):ℂ) Φ hΦ hone (Z^m) (Real.rpow_pos_of_pos (by linarith) _) rows hrows
  apply hr.trans
  simpa only [InverseInitialProfileBounds.childLogTest_eq_clipped,pow_mul,pow_two,mul_pow] using he

end SevenEighths.InverseInitialTotalRows

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialTotalFourier -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalFourier
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
theorem original_fourier_energy_bound
    (g:𝓢(ℝ,ℂ))(W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(xj θ:ℝ),
      (∑u∈rows,‖∫t:ℝ,density (frequencyTwist g θ) xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-t) (y i P)))
            (childLogTest W t) Z D) u)‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalRows.original_input_rows_fourier_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cm,hCm,hmeasure⟩:=InverseInitialOverlapHeight.twisted_polynomial_measure_energy g J
  refine ⟨J+(volume:Measure ℝ).integrablePower,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y xj θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  let φ:O→ℝ→ℂ:=fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*logPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht:=hmeasure θ xj (fun u:rows=>φ u.val) (C*Z^(m+15*η+π+eps+loss))
    (by positivity)
    (fun u=>InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ Ψ (assignedElement assigned qelem) u.val
      (all\assigned) lists coeff y W Z D xj)
    (fun t=>by
      apply (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans
      exact henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y t)
  apply (Finset.sum_coe_sort rows (fun u=>‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t‖^2)).symm.le.trans
  apply ht.trans
  have hh:0≤C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)):=by positivity
  have he:=mul_le_mul_of_nonneg_right (show Cm≤Cm+1 by linarith) hh
  convert he using 1 <;> simp only [pow_mul,pow_two,mul_pow] <;> ring

end SevenEighths.InverseInitialTotalFourier

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialInputReindex -/

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

theorem primeMark_subtype {σ ι:Type*}[DecidableEq σ][DecidableEq ι]
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:I=>L i.val) (fun i:I=>a i.val) A=
      primeMark I L a A:=by
  exact Finset.prod_coe_sort I (fun i=>primeSlot (L i) (a i) A)

theorem primeMark_remaining {σ ι:Type*}[Fintype σ][DecidableEq σ][DecidableEq ι]
    (J:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:{i:σ//i∉J}=>L i.val) (fun i:{i:σ//i∉J}=>a i.val) A=
      primeMark (Finset.univ\J) L a A:=by
  classical
  unfold primeMark
  exact (Finset.prod_subtype (Finset.univ\J) (by intro i;simp)
    (fun i=>primeSlot (L i) (a i) A)).symm

end SevenEighths.InverseInitialInputReindex

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOriginalHeight -/

section

namespace OAI

noncomputable section

open scoped Classical SchwartzMap ContDiff FourierTransform
namespace SevenEighths.InverseInitialOriginalHeight
open InverseMoment InverseInitialProfile InverseInitialProfileBounds FourierBridge
open JointLogSeparation CompletedHeight

theorem child_eq_normTwisted (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=normTwistedSource W θ:=by
  rw [childLogTest_eq_clipped]
  funext x
  simp only [clippedSource,normTwistedSource,one_mul]

theorem child_support (W:ℝ→ℂ)(θ:ℝ):
    Function.support (childLogTest W θ)⊆Function.support W:=by
  rw [child_eq_normTwisted]
  exact normTwistedSource_support W θ

theorem child_smooth (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    ContDiff ℝ ∞ (childLogTest W θ):=by
  rw [child_eq_normTwisted]
  exact CanonicalRowCompletion.normTwistedSource_contDiff W a b ha hs hW θ

theorem logSchwartz_child (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    CubicReflectionKernel.logSchwartz (childLogTest W θ) a b ha
      ((child_support W θ).trans hs) (child_smooth W a b ha hs hW θ)=
    frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) θ:=by
  ext x
  simp only [CubicReflectionKernel.logSchwartz_apply,childLogTest,
    frequencyTwist_apply,Real.log_exp]
  ring

end SevenEighths.InverseInitialOriginalHeight

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstDiscarded -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscarded
open SevenEighths CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem actual_first_kernel_reference (I J E : Ideal O)
    (hI : I≠0) (hJ : J≠0) (hE : E≠0) (K X HN Tsec : ℝ)
    (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤Tsec) :
    kernelReference Tsec HN ≤
      K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  simpa only [kernelReference,mul_one] using
    first_kernel_sector_lower I J E hI hJ hE K X 1 HN Tsec hK hX zero_le_one hi hj hsec

theorem canonical_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J E : Ideal O) (hI : Supported I) (hJ : Supported J), E≠0 →
      ∀ K X HN Tsec Z Csec ξ : ℝ, 0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      firstNominalScale I J E K X≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W
          ((K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
            (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)))*normValue h)‖ ≤
      (‖eisEmbedding (activeConductor I J)‖*(Ideal.absNorm (residualPart I J):ℝ)*
        (Ideal.absNorm (residualPart J I):ℝ))*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W I J E hI hJ hE K X HN Tsec Z Csec ξ hK hX hZ hCsec hi hj hsec hthreshold
  have hT : 0<Tsec := (firstNominalScale_pos I J E hE K X hK hX).trans_le hsec
  apply ht W Tsec Z Csec HN ξ _ _ hT hZ hCsec hthreshold
    (actual_first_kernel_reference I J E hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec)
    (by positivity)
  intro h
  apply (canonical_tripleFourier_norm_le I J hI hJ h).trans
  have ha := CenteredMomentTail.residueGauss_norm_le (residualGenerator I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (residualCharacter I J hI) (Ideal.Quotient.mk _ h)
  have hb := CenteredMomentTail.residueGauss_norm_le (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)
  have ha' := ha.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span I J hI))
  have hb' := hb.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span J I hJ))
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha' (norm_nonneg _)) hb' (norm_nonneg _) (by positivity)

end SevenEighths.CenteredMomentFirstDiscarded

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscardedEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem tripleRow_norm_le_one (a b r : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (z : O) :
    ‖tripleRow a b r χa χb G z‖≤1 := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleRow,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_finite_character_le_one χa _)).trans
      (QuadraticInitialBound.norm_finite_character_le_one χb _))).trans (hG _)

theorem tripleFourier_norm_le_full (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (h : O) :
    ‖tripleFourier a b r ha hb hr χa χb G h‖≤normValue (a*(b*r)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  rw [tripleFourier,tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a*(b*r)),‖tripleResidue a b r χa χb G x*
      quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a*(b*r)),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [norm_mul,(quotientTrace _ _).norm_apply,mul_one,tripleResidue_mk]
      exact tripleRow_norm_le_one a b r ha hb χa χb G hG z
    _ = _ := by simp [normValue,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem activeFunction_norm_le_one (I J : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (x : Residue (activeConductor I J)) : ‖activeFunction I J hI x‖≤1 := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    _ = ‖finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z‖ :=
      congrArg norm (principalSexticRow_mk (activePrime I J) (activeCoprime I J)
        (activeGood I J hI) (CenteredMomentCanonicalFirst.activeExponent I J)
        (activeConductor I J) (span_finitePrimeModulus _) z)
    _ ≤ 1 := QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ z

theorem scaled_discarded_triple_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ k : ℝ),
      0<Tsec → 1<Z → 1≤Csec → 0<k →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ∀ (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
        (G : Residue r → ℂ), (∀ x,‖G x‖≤1) →
      kernelReference Tsec H≤k/normValue (a*(b*r)) →
      ‖((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
        (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h)‖ ≤
      k*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ k hT hZ hCs hk hthreshold a b r ha hb hr χa χb G hG hscale
  have hN : 0<normValue (a*(b*r)) := norm_pos _
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr)))
  have hh := ht W Tsec Z Csec H ξ (k/normValue (a*(b*r))) (normValue (a*(b*r)))
    hT hZ hCs hthreshold hscale hN.le (tripleFourier a b r ha hb hr χa χb G)
    (tripleFourier_norm_le_full a b r ha hb hr χa χb G hG)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hk hN)]
  apply (mul_le_mul_of_nonneg_left hh (div_pos hk hN).le).trans_eq
  field_simp

def canonicalDiscardedTerm (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem canonical_kernel_scale (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (K : ℝ) :
    (K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/
      normValue (residualGenerator I J*(residualGenerator J I*activeConductor I J)) =
      K/((Ideal.absNorm (∏ P∈E,P.val):ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart I J):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart J I):ℝ)) := by
  rw [normValue_mul,normValue_mul]
  unfold normValue
  rw [primeSubsetGenerator,span_idealGenerator,residualGenerator_span I J hI,residualGenerator_span J I hJ,div_div]
  congr 1
  ring

theorem canonical_discarded_term_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (E : Finset (CommonIndex I J)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ ≤
      K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := scaled_discarded_triple_bound A
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hE : (∏ P∈E,P.val)≠(0:Ideal O) := by
    have hh := Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [e,primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
  have hNe : 0<normValue e := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)
  have hNe1 : 1≤normValue e := by
    change (1:ℝ)≤(Ideal.absNorm (Ideal.span {e}):ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr he))
  have hk := div_pos hK hNe
  have hkK : K/normValue e≤K := div_le_self hK.le hNe1
  have hT := (firstNominalScale_pos I J _ hE K X hK hX).trans_le hsec
  have hscale := actual_first_kernel_reference I J _ hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec
  rw [← canonical_kernel_scale I J hI hJ E K] at hscale
  have hb := ht W Tsec Z Csec HN ξ (K/normValue e) hT hZ hCs hk hthreshold
    (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
    (activeFunction_norm_le_one I J hI) hscale
  have hm : ‖(UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e‖≤1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_ideal_moebius_le_one _)).trans
      (tripleRow_norm_le_one _ _ _ (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) _ _ _ (activeFunction_norm_le_one I J hI) e)
  change ‖_ * _‖≤_
  rw [norm_mul]
  apply (mul_le_mul hm hb (norm_nonneg _) zero_le_one).trans
  rw [one_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkK (by positivity)) (by positivity)

def inactiveSubsets (I J : Ideal O) : Finset (Finset (CommonIndex I J)) :=
  (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset

theorem inactiveSubsets_card (I J : Ideal O) :
    (inactiveSubsets I J).card≤2^(primeSupport I).card := by
  rw [inactiveSubsets,Finset.card_powerset]
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    _ ≤ (Finset.univ : Finset (CommonIndex I J)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = (commonSupport I J).card := by simp [CommonIndex]
    _ ≤ _ := Finset.card_le_card Finset.inter_subset_left

def canonicalDiscardedPair (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ

theorem canonical_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      (∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedPair I J hI hJ W K Tsec Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => ht W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec E hE) hthreshold)
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentFirstDiscardedEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O))
        (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,(Ideal.absNorm I:ℝ)≤Real.exp HN*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,∀ E∈inactiveSubsets I J,
        firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖ ≤
      (∑ I∈S,‖c I‖)^2*(Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X HN Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤B := by
    have hi := hN I (Finset.mem_filter.mp I.property).1
    have hj := hN J (Finset.mem_filter.mp J.property).1
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec I J) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hi hε.le) hK.le
  have hcoeff (I : supportedColumns S) : ‖c I*rowWeight η m A 1 t I‖≤‖c I‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1)
  have hmass : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  have he : (∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B)=
      (∑ I : supportedColumns S,‖c I‖)^2*B := by
    rw [pow_two,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.mul_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ I : supportedColumns S,‖∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B := by
      apply Finset.sum_le_sum
      intro I hI
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (hcoeff I) (hcoeff J) (norm_nonneg _) (norm_nonneg _))
        (hpair I J) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ I : supportedColumns S,‖c I‖)^2*B := he
    _ ≤ (∑ I∈S,‖c I‖)^2*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass 2) hB
    _ = _ := by dsimp only [B];ring

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstLocalization -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (retainedWeight_nonneg R q)]
  exact (retainedWeight_bounds R q).2

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg R q)]
  exact (discardedWeight_bounds R q).2

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  have hr := weighted_fourier_summable W k hk c (fun h => (retainedWeight R (normValue h):ℂ)) B hc
    (fun h => retained_complex_norm R _)
  have hd := weighted_fourier_summable W k hk c (fun h => (discardedWeight R (normValue h):ℂ)) B hc
    (fun h => discarded_complex_norm R _)
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [ite_eq_right hh]
    have hp : 0<normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    rw [← add_mul,← add_mul,he,one_mul]

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

theorem reducedFirstSum_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      canonicalRetainedPair I J hI hJ W K Tsec Z ξ+canonicalDiscardedPair I J hI hJ W K Tsec Z ξ := by
  unfold reducedFirstSum canonicalZeroPair canonicalRetainedPair canonicalDiscardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

theorem finiteHeckeEnergy_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K Tsec Z ξ+
        discardedEnergy η m A t S c W K Tsec Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_split _ _ _ _ W K Tsec Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstSectorLocalization -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstLocalization

def retainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

def discardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

theorem reducedFirstSum_sector_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      retainedPair I J hI hJ W K X Z ξ+discardedPair I J hI hJ W K X Z ξ := by
  unfold reducedFirstSum canonicalZeroPair retainedPair discardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  let Tsec:=firstNominalScale I J (∏ P∈E,P.val) K X
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

theorem finiteHeckeEnergy_sector_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K X Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K X Z ξ+
        discardedEnergy η m A t S c W K X Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_sector_split _ _ _ _ W K X Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstSectorLocalization

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstCommonTransport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstCommonTransport
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstSectorEnergy CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem extracted_support (I J:Ideal O):
    commonSupport (commonPart I J) (commonPart J I)=commonSupport I J:=by
  rw [commonSupport,commonPart_support,commonPart_support,commonSupport_comm J I,Finset.inter_self]

def commonEquiv (I J:Ideal O):CommonIndex I J ≃ CommonIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨P.val,by rw [extracted_support];exact P.property⟩
  invFun P:=⟨P.val,by rw [←extracted_support I J];exact P.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem commonEquiv_val (I J:Ideal O)(P:CommonIndex I J):
    (commonEquiv I J P).val=P.val:=rfl

@[simp] theorem extracted_left (I J:Ideal O)(P:CommonIndex I J):
    leftExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=leftExponent I J P:=by
  simp only [leftExponent,commonEquiv_val,commonPart_valuation,ite_eq_left P.property]

@[simp] theorem extracted_right (I J:Ideal O)(P:CommonIndex I J):
    rightExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=rightExponent I J P:=by
  have hp:P.val∈commonSupport J I:=by rw [commonSupport_comm];exact P.property
  simp only [rightExponent,commonEquiv_val,commonPart_valuation,ite_eq_left hp]

def activeEquiv (I J:Ideal O):ActiveIndex I J ≃ ActiveIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨commonEquiv I J P.val,by
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using P.property⟩
  invFun P:=⟨(commonEquiv I J).symm P.val,by
    have hp:=P.property
    have he:(commonEquiv I J) ((commonEquiv I J).symm P.val)=P.val:=(commonEquiv I J).apply_symm_apply _
    rw [←he] at hp
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp⟩
  left_inv P:=by apply Subtype.ext;exact (commonEquiv I J).symm_apply_apply _
  right_inv P:=by apply Subtype.ext;exact (commonEquiv I J).apply_symm_apply _

@[simp] theorem activeEquiv_prime (I J:Ideal O)(P:ActiveIndex I J):
    activePrime (commonPart I J) (commonPart J I) (activeEquiv I J P)=activePrime I J P:=rfl

@[simp] theorem activeEquiv_exponent (I J:Ideal O)(P:ActiveIndex I J):
    activeExponent (commonPart I J) (commonPart J I) (activeEquiv I J P)=activeExponent I J P:=by
  change netExponent (leftExponent _ _ (commonEquiv I J P.val))
    (rightExponent _ _ (commonEquiv I J P.val))=_
  rw [extracted_left,extracted_right]
  rfl

theorem activeConductor_extracted (I J:Ideal O):
    activeConductor (commonPart I J) (commonPart J I)=activeConductor I J:=by
  unfold activeConductor finitePrimeModulus
  congr 1
  exact (Fintype.prod_equiv (activeEquiv I J) _ _ (fun P=>by rw [activeEquiv_prime])).symm

theorem activeRow_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    finiteSexticRow (activePrime (commonPart I J) (commonPart J I))
      (activeGood _ _ (commonPart_supported I J hI))
      (activeExponent (commonPart I J) (commonPart J I)) z=
    finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) z:=by
  unfold finiteSexticRow
  apply (Fintype.prod_equiv (activeEquiv I J) _ _ ?_).symm
  intro P
  rw [activeEquiv_exponent]
  rfl

theorem activeFunction_mk_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (Ideal.Quotient.mk _ z)=activeFunction I J hI (Ideal.Quotient.mk _ z):=by
  simp only [activeFunction]
  exact activeRow_extracted I J hI z

def mappedSubset (I J:Ideal O)(E:Finset (CommonIndex I J)):
    Finset (CommonIndex (commonPart I J) (commonPart J I)):=E.map (commonEquiv I J).toEmbedding

theorem mappedSubset_product (I J:Ideal O)(E:Finset (CommonIndex I J)):
    (∏P∈mappedSubset I J E,P.val)=∏P∈E,P.val:=by
  simp only [mappedSubset,Finset.prod_map,Equiv.toEmbedding_apply,commonEquiv_val]

theorem mappedSubset_generator (I J:Ideal O)(E:Finset (CommonIndex I J)):
    primeSubsetGenerator (fun P:CommonIndex (commonPart I J) (commonPart J I)=>P.val)
      (mappedSubset I J E)=primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E:=by
  unfold primeSubsetGenerator
  rw [mappedSubset_product]

theorem mappedSubset_inactive (I J:Ideal O)(E:Finset (CommonIndex I J)):
    mappedSubset I J E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I) ↔
      E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J:=by
  simp only [CenteredMomentFirstDiscardedEnergy.inactiveSubsets,Finset.mem_powerset]
  constructor
  · intro h P hP
    have hp:=h (Finset.mem_map.mpr ⟨P,hP,rfl⟩)
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp
  · intro h P hP
    obtain ⟨R,hR,rfl⟩:=Finset.mem_map.mp hP
    have hr:=h hR
    simpa only [Equiv.toEmbedding_apply,principalSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hr

theorem nominal_extracted (I J:Ideal O)(E:Finset (CommonIndex I J))(K X:ℝ):
    CenteredMomentFirstScale.firstNominalScale (commonPart I J) (commonPart J I)
      (∏P∈mappedSubset I J E,P.val) K X=
    CenteredMomentFirstScale.firstNominalScale I J (∏P∈E,P.val) K X:=by
  obtain ⟨hc,hd⟩:=fixed_common_parts (commonPart I J) (commonPart J I)
    (commonPart_ne_zero I J) (commonPart_ne_zero J I) (commonParts_equal_support I J)
  unfold CenteredMomentFirstScale.firstNominalScale
  rw [mappedSubset_product,activeConductor_extracted,hc,hd]

end SevenEighths.CenteredMomentFirstCommonTransport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.FirstCommonFourierTransport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonFourierTransport
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentFirstLocalization CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentFirstCommonTransport
local notation "O"=>ActualEisensteinCubic.O

theorem quotient_function_heq (r r':O)(hr:r'=r)
    (G:Residue r→ℂ)(G':Residue r'→ℂ)
    (hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z)):
    HEq G' G:=by
  subst r'
  apply heq_of_eq
  funext x
  obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
  exact hG z

def retainedFourierTerm (a b r:O)(ha:a≠0)(hb:b≠0)(hr:r≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):ℂ:=
  let k:=K/normValue e
  (UniqueFactorizationMonoid.moebius E:ℂ)*tripleRow a b r χa χb G e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑'h:O,
      (retainedWeight R (normValue h):ℂ)*tripleFourier a b r ha hb hr χa χb G h*
        EisensteinSchwartzPoisson.paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem retainedFourierTerm_transport (a b r r':O)(ha:a≠0)(hb:b≠0)(hr:r≠0)(hr':r'≠0)
    (χa:MulChar (Residue a) ℂ)(χb:MulChar (Residue b) ℂ)(G:Residue r→ℂ)(G':Residue r'→ℂ)
    (he:r'=r)(hG:∀z:O,G' (Ideal.Quotient.mk _ z)=G (Ideal.Quotient.mk _ z))
    (e:O)(E:Ideal O)(W:𝓢(ℝ,ℂ))(K R:ℝ):
    retainedFourierTerm a b r' ha hb hr' χa χb G' e E W K R=
      retainedFourierTerm a b r ha hb hr χa χb G e E W K R:=by
  subst r'
  have hg:G'=G:=eq_of_heq (quotient_function_heq r r rfl G G' hG)
  subst G'
  rfl

def fixedRetainedTerm (C D:Ideal O)(hC:Supported C)(a b:O)
    (ha:Supported (Ideal.span {a}))(hb:Supported (Ideal.span {b}))
    (E:Finset (CommonIndex C D))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):ℂ:=
  retainedFourierTerm a b (activeConductor C D)
    (supported_element_ne_zero _ ha) (supported_element_ne_zero _ hb) (finitePrimeModulus_ne_zero _)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K X) Z ξ)

theorem canonicalRetainedTerm_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (E:Finset (CommonIndex I J))(W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    canonicalRetainedTerm I J hI hJ E W K
      (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ=
    fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
      (residualGenerator I J) (residualGenerator J I)
      (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ)
      (mappedSubset I J E) W K X Z ξ:=by
  unfold fixedRetainedTerm
  rw [nominal_extracted,mappedSubset_generator,mappedSubset_product]
  have hh:=retainedFourierTerm_transport (residualGenerator I J) (residualGenerator J I)
    (activeConductor I J) (activeConductor (commonPart I J) (commonPart J I))
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (finitePrimeModulus_ne_zero _) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹
    (activeFunction I J hI) (activeFunction (commonPart I J) (commonPart J I) (commonPart_supported I J hI))
    (activeConductor_extracted I J) (activeFunction_mk_extracted I J hI)
    (primeSubsetGenerator (fun P:CommonIndex I J=>P.val) E) (∏P∈E,P.val) W K
    (frequencyRadius (firstNominalScale I J (∏P∈E,P.val) K X) Z ξ)
  exact hh.symm

def inactiveEquiv (I J:Ideal O):
    CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J ≃
      CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I):=
  (Equiv.finsetCongr (commonEquiv I J)).subtypeEquiv (fun E=>(mappedSubset_inactive I J E).symm)

@[simp] theorem inactiveEquiv_val (I J:Ideal O)
    (E:CenteredMomentFirstDiscardedEnergy.inactiveSubsets I J):
    (inactiveEquiv I J E).val=mappedSubset I J E.val:=rfl

theorem canonicalRetainedPair_fixed (I J:Ideal O)(hI:Supported I)(hJ:Supported J)
    (W:𝓢(ℝ,ℂ))(K X Z ξ:ℝ):
    CenteredMomentFirstSectorLocalization.retainedPair I J hI hJ W K X Z ξ=
    ∑E∈CenteredMomentFirstDiscardedEnergy.inactiveSubsets (commonPart I J) (commonPart J I),
      fixedRetainedTerm (commonPart I J) (commonPart J I) (commonPart_supported I J hI)
        (residualGenerator I J) (residualGenerator J I)
        (residualGenerator_supported I J hI) (residualGenerator_supported J I hJ) E W K X Z ξ:=by
  unfold CenteredMomentFirstSectorLocalization.retainedPair
  apply Finset.sum_bij (fun E _=>mappedSubset I J E)
  · intro E hE
    exact (mappedSubset_inactive I J E).mpr hE
  · intro E hE F hF he
    exact (Equiv.finsetCongr (commonEquiv I J)).injective he
  · intro F hF
    obtain ⟨E,he⟩:=(Equiv.finsetCongr (commonEquiv I J)).surjective F
    change mappedSubset I J E=F at he
    exact ⟨E,(mappedSubset_inactive I J E).mp (he.symm ▸ hF),he⟩
  · intro E hE
    exact canonicalRetainedTerm_fixed I J hI hJ E W K X Z ξ

end SevenEighths.CenteredMomentFirstCommonFourierTransport

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputFirstTailScale -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSourceInputFirstTailUniform
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstScale
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma common_subset_product_dvd_right (I J : Ideal O) (E : Finset (CommonIndex I J)) :
    (∏P∈E,P.val)∣commonPart J I := by
  apply (Finset.prod_dvd_prod_of_subset E Finset.univ
    (fun P : CommonIndex I J=>P.val) (Finset.subset_univ _)).trans
  rw [commonPart_right_product]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  simpa only [pow_one] using pow_dvd_pow P.val (rightExponent_pos I J P)

theorem first_nominal_scale_le (I J : Ideal O) (E : Finset (CommonIndex I J))
    (K X : ℝ) (hK : 0<K) :
    firstNominalScale I J (∏P∈E,P.val) K X≤X^2/K := by
  have hC := norm_pos (commonPart I J) (commonPart_ne_zero I J)
  have hD := norm_pos (commonPart J I) (commonPart_ne_zero J I)
  have hE : (Ideal.absNorm (∏P∈E,P.val):ℝ)≤Ideal.absNorm (commonPart J I) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
      (map_dvd Ideal.absNorm (common_subset_product_dvd_right I J E))
  have hA : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤Ideal.absNorm (commonPart I J) := by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J)))
      (map_dvd Ideal.absNorm (activeConductor_span_dvd I J))
  unfold firstNominalScale
  apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hE hA (by positivity) hD.le) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hK.le hC.le) hD.le)).trans_eq
  field_simp

end SevenEighths.CenteredMomentSourceInputFirstTailUniform

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailPair -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum CenteredMomentFirstDiscardedEnergy
open CenteredMomentSourceInputFirstTailUniform
local notation "O"=>ActualEisensteinCubic.O

lemma local_tail_denominator_mono (Tlocal Tupper H Z ξ:ℝ)(A:ℕ)(B:ℝ)
    (hT:0<Tlocal)(hupper:Tlocal≤Tupper)(hB:0≤B)(hZ:0≤Z):
    B/((min 1 (kernelReference Tlocal H))^2*(1+Z^(ξ/4))^A)≤
      B/((min 1 (kernelReference Tupper H))^2*(1+Z^(ξ/4))^A):=by
  have hu:0<Tupper:=hT.trans_le hupper
  have hk:kernelReference Tupper H≤kernelReference Tlocal H:=by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT hupper
  have hm:0< min 1 (kernelReference Tupper H):=lt_min zero_lt_one (kernelReference_pos _ _ hu)
  have hp:0≤Z^(ξ/4):=Real.rpow_nonneg hZ _
  apply div_le_div_of_nonneg_left hB (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ hm.le (min_le_min_left 1 hk) 2

theorem local_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      X^2/K≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K
        (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => by
        let Tlocal:=firstNominalScale I J (∏ P∈E,P.val) K X
        have hE0:(∏ P∈E,P.val)≠(0:Ideal O):=by
          have he:=primeSubsetGenerator_ne_zero (fun P:CommonIndex I J=>P.val) E
          have hh:=Ideal.span_singleton_eq_bot.not.mpr he
          simpa only [primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
        have hTl:0<Tlocal:=firstNominalScale_pos I J _ hE0 K X hK hX
        have hTu:Tlocal≤Tsec:=(first_nominal_scale_le I J E K X hK).trans hsec
        have hh:=ht W I J hI hJ E K X HN Tlocal Z Csec ξ hK hX hZ hCs hi hj le_rfl hthreshold
        exact hh.trans (local_tail_denominator_mono Tlocal Tsec HN Z ξ A
          (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) hTl hTu (by positivity) (zero_lt_one.trans hZ).le))
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI

end

