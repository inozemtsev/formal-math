module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part012
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part010
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part011
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part009
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileWindows -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
local notation "O" => ActualEisensteinCubic.O
theorem original_cell_windows (g₁ g₂ : 𝓢(ℝ,ℂ)) (m₁ m₂ bcap : ℝ)
    (Bρ : Fin 9→ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂)
    (hBρ : ∀i,0≤Bρ i) :
    ∃(w₁ w₂ : 𝓢(ℝ,ℂ))(U₀ : Fin 9→𝓢(ℝ,ℂ))(M₀ : Fin 9→ℝ)(a b : ℝ),
      0<a ∧ a≤b ∧ HasCompactSupport (w₁ : ℝ→ℂ) ∧ HasCompactSupport (w₂ : ℝ→ℂ) ∧
      tsupport (w₁ : ℝ→ℂ)⊆Set.Icc a b ∧ tsupport (w₂ : ℝ→ℂ)⊆Set.Icc a b ∧
      (∀i,0≤M₀ i) ∧ (∀i,HasCompactSupport (U₀ i : ℝ→ℂ)) ∧
      (∀i,Function.support (U₀ i)⊆Set.Icc (-M₀ i) (M₀ i)) ∧
      ∀{ι : Type*}[DecidableEq ι]
      (p : ι→O)(_hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
      (C₁ C₂ : OriginalIndex ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
      (ρ : Fin 9→ℝ)(c₁ c₂ θ₁ θ₂ : ℝ),
      0<T₁ → 0<T₂ → (∀i,|ρ i|≤Bρ i) →
      1≤ c₁ → c₁≤bcap → 1≤ c₂ → c₂≤bcap →
      let source := sourceCell (originalNorms p)
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k
      let F := pool
      let selector : OriginalIndex ι→Finset ι→ℂ := fun _=>commonSelector p (fun _=>1) l
      let A₁ := leftNorm p
      let A₂ := rightNorm p
      let C := commonNorm p
      let R := activeNorm p
      let d := fun x : OriginalIndex ι=>divisorElement p x.1
      let h := fun x : OriginalIndex ι=>x.2.2
      let s := rawScales k l T₁ T₂
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
  obtain ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,he⟩ :=
    actual_first_child_windows g₁ g₂ m₁ m₂ bcap (fun _=>1) (fun _=>2) Bρ
      hm₁ hm₂ hg₁ hg₂ (by intro i;norm_num) (by intro i;norm_num) hBρ
  refine ⟨w₁,w₂,U,M,a,b,ha,hab,hwc₁,hwc₂,hws₁,hws₂,hM,hUc,hUs,?_⟩
  intro ι _ p hp _ hg pool Q labels Y C₁ C₂ k l T₁ T₂ ρ c₁ c₂ θ₁ θ₂
    hT₁ hT₂ hρ hc₁ hcb₁ hc₂ hcb₂ source F selector A₁ A₂ C R d h s
  apply he p hp hg source F selector C₁ C₂ A₁ A₂ C R d h s ρ c₁ c₂ θ₁ θ₂
    (rawScales_pos k l T₁ T₂ hT₁ hT₂) hρ hc₁ hcb₁ hc₂ hcb₂
  intro x hx j hj hn
  exact actual_original_cell_ratios p hp hg _ (fun _ _=>1) C₁ C₂
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    (fun x=>divisorElement p x.1) (fun x=>x.2.2)
    (original_source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileCellEnergy -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def originalChildEnergy (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) : ℝ :=
  ∑x∈originalOuterCell p pool Q k,
    firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
      (mark (if negative then x.1.rightExponent else x.1.leftExponent))
      (commonSelector p (fun _=>1) l) omega T t Y

def originalCellRows (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
    (sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k)
    pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) W₁ W₂ Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s

theorem original_cell_physical_budget (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ : ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) :
    ∃(omega₁ omega₂ : 𝓢(ℝ,ℂ))(lo hi : ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁ : ℝ→ℂ) ∧ HasCompactSupport (omega₂ : ℝ→ℂ) ∧
      tsupport (omega₁ : ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂ : ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀(ε : ℝ),0<ε→∀(Aker J : ℕ),∃ Cprofile Kpush : ℝ,0≤Cprofile ∧ 0<Kpush ∧
    ∀{ι : Type*}[DecidableEq ι](p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
      (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Γ Y : ℝ)
      (_hΨ : ∀u,‖Ψ u‖≤1) (_hΓ : 0≤Γ) (_hY : 0<Y)
      (_hsf : ∀I∈labels,Squarefree I) (_hn : ∀I∈labels,I≠0)
      (_hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (k : SourceIndex) (l : ℕ) (T₁ T₂ K theta L : ℝ)
      (_hT₁ : 0<T₁) (_hT₂ : 0<T₂) (_hK : 0<K) (_hL : 0≤L)
      (Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta : ℝ)
      (_hB : 0≤Benergy) (_hZ : 0<Z)
      (_hscale : rawScales k l T₁ T₂=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
      (_hLe : L=eta*Real.log Z)
      (_hleft : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          originalChildEnergy p hp hg hinj pool Q k l true Ψ m mark omega₁ T₁
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
      (_hright : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          originalChildEnergy p hp hg hinj pool Q k l false Ψ m mark omega₂ T₂
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
      (Z^(-r-2*ell-V)*Z^M)*‖originalCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Y (rawScales k l T₁ T₂)‖≤
        ((Γ^2*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖-theta‖)^InverseClippingProfiles.momentOrder J*
          (1+‖theta‖)^InverseClippingProfiles.momentOrder J)/
          (1+K*(rawScales k l T₁ T₂) 6/((rawScales k l T₁ T₂) 3*(rawScales k l T₁ T₂) 4*
            ((rawScales k l T₁ T₂) 5)^2*T₁*T₂))^Aker)) := by
  obtain ⟨w₁,w₂,U,M₀,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,hM,hUc,hUs,hwin⟩ :=
    original_cell_windows g₁ g₂ m₁ m₂ 1 (fun _=>0) hm₁ hm₂ hg₁ hg₂ (fun _=>le_rfl)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro ε hε Aker J
  obtain ⟨Cprofile,Kpush,hC,hKp,he⟩ := actual_first_original_subset_physical_budget
    ε hε U g₁ g₂ Φ M₀ (fun _=>0) m₁ m₂ 1
    hM (fun _=>le_rfl) hUs hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hC,hKp,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y hΨ hΓ hY hsf hn hβ
    k l T₁ T₂ K theta L hT₁ hT₂ hK hL Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hB hZ hscale hLe hleft hright
  let source := sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k
  have hgates := hwin p hp hg pool Q labels Y (coefficient p hp hcop hg Ψ m mark true)
    (coefficient p hp hcop hg Ψ m mark false) k l T₁ T₂ (fun _=>0) 1 1 (-theta) theta
    hT₁ hT₂ (by intro i;simp) le_rfl le_rfl le_rfl le_rfl
  have hb := he p hp hg hinj hcop hc hpr pool (originalOuterCell p pool Q k) (fun x=>x.1) (fun x=>x.2.1)
    Ψ Ψ m m (divisorElement p) (fun x=>mark x.1.rightExponent) (fun x=>mark x.1.leftExponent)
    (fun _=>commonSelector p (fun _=>1) l) (fun _=>labels) (firstOriginalWeight p β cutoff) (Γ^2) Y
    hΨ hΨ (sq_nonneg _) hY (fun _ _=>hsf) (fun _ _=>hn)
    (fun x hx=>original_weight_bound p pool Q labels β cutoff Γ Y hΓ hβ x (original_outer_cell_subset p pool Q k hx))
    w₁ w₂ (fun _=>0) 1 1 (-theta) theta (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    K L hK (rawScales k l T₁ T₂) (rawScales_pos k l T₁ T₂ hT₁ hT₂)
    source (original_cell_subset p pool Q labels Y k)
    (fun x hx=>original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp hx).1)
    (by intro i;simp) le_rfl le_rfl le_rfl le_rfl hL hgates.1 hgates.2.1 hgates.2.2
    Benergy hB Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe
    (by simpa [originalChildEnergy,rawScales] using hleft)
    (by simpa [originalChildEnergy,rawScales] using hright)
  unfold originalCellRows
  unfold SevenEighths.InverseMomentFirstOriginalProfile.coefficient SevenEighths.InverseMomentFirstOriginalProfile.weight
  simpa [source,rawScales] using hb

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

def secondCellColumnExponent (Z X:ℝ) (d:BlockIndex):ℝ :=
  Real.logb Z (X/(scales d 0*scales d 2))

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

theorem second_cell_physical_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)=X := by
  rw [second_cell_column_scale Z X d hZ hX]
  field_simp [scales,ne_of_gt (dyadScale_pos (d 0)),ne_of_gt (dyadScale_pos (d 2))]

theorem second_cell_clipping_ratio (Z X b:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X)
    (hb:1≤b) (hsource:scales d 0*scales d 2≤b*X) :
    1≤Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d) ∧
    Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d)≤b := by
  let N:=secondCellColumnExponent Z X d
  have hz:0<Z:=lt_trans zero_lt_one hZ
  have hn:Z^N=X/(scales d 0*scales d 2):=second_cell_column_scale Z X d hZ hX
  constructor
  · exact Real.one_le_rpow hZ.le (sub_nonneg.mpr (le_max_right _ _))
  · by_cases hN:0≤N
    · rw [max_eq_right hN,sub_self,Real.rpow_zero];exact hb
    · have hN':N≤0:=le_of_not_ge hN
      rw [max_eq_left hN',zero_sub,Real.rpow_neg hz.le,hn,inv_div]
      exact (div_le_iff₀ hX).mpr hsource

theorem actual_priority_cell_profile {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) (d:BlockIndex) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
        (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d)) := by
  rw [second_cell_physical_scale Z X d hZ hX]
  exact actual_priority_profile_common p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    om lo hi hlo hs negative t Φ Y X hX

theorem actual_priority_cells {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo:ℕ} (source:Finset (MarkedSecondSource ι Jo 0))
    (pool:Finset ι) (Ψ:O→*ℂ) (m:O) (ray:SecondRayIndex)
    (slots₁ slots₂:Finset σ) (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (deleted₁ deleted₂:MarkedSecondSource ι Jo 0→Finset ι)
    (w:MarkedSecondSource ι Jo 0→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X Z:ℝ) (hX:0<X) (hZ:1<Z) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    (Y:ℂ)*secondRayCoefficient ray *
      (∑x∈source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X) =
    ∑d∈keys p source,(Y:ℂ)*secondRayCoefficient ray *
      (∑x∈cell p source d,(w x*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x)*
        actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
          slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y
          (scales d 0*scales d 2*Z^(secondCellColumnExponent Z X d))) := by
  intro g θ
  refine (physical_source_partition p hp hcop hg source pool Ψ m ray slots₁ slots₂ lists₁ lists₂
    a₁ a₂ deleted₁ deleted₂ w (principalWindow om lo hi hlo hs negative t)
    (principalWindow om lo hi hlo hs negative t) Φ Y X).trans ?_
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg ((Y : ℂ) * secondRayCoefficient ray * ·)
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg ((w x * actualSecondSignedWeight p hp hcop hg Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) ray x) * ·)
    (actual_priority_cell_profile p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hs negative t Φ Y X Z hX hZ d)

theorem actual_source_block_ratios {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (d:BlockIndex)
    (hcell:∀x∈source,index p x=d) (hk:∀x∈source,x.second.frequency≠0) :
    ∀x∈source,∀i,InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i∈Set.Icc 1 2 := by
  intro x hx i
  have hxcell:x∈cell p source d:=(mem_cell p source d x).mpr ⟨hx,hcell x hx⟩
  have hr:=cell_ratios p hp source hk d x hxcell i
  have he:InverseSecondChildWindows.actualOuterRatios p x
      (scales d 0) (scales d 1) (scales d 2) (scales d 3) i=outerNorms p x i/scales d i := by
    fin_cases i <;> simp [InverseSecondChildWindows.actualOuterRatios,outerNorms,
      primeSubsetGenerator_norm_eq_productNorm]
  rw [he]
  exact ⟨hr.1,hr.2.le⟩

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityCellEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_cell_recursive
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (Aker J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
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
    (_hs : ActualSecondSourceConditions p source) (d:InverseSecondSourceBlocks.BlockIndex)
    (_hcell:∀x∈source,InverseSecondSourceBlocks.index p x=d),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
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
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^Aker)) := by
  let g:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤ mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg:Function.support g⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile g)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_second_fixed_block_recursive (ι:=ι) (σ:=σ) (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X Vlabel εchild ell Ractive j tcount gcount theta eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY hrows hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hblock:=actual_source_block_ratios p hp source d hcell
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx))
  have he:=henergy p hp hcop hg₀ hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (scales d 0) (scales d 1) (scales d 2) (scales d 3) Y R L Z
    (secondCellColumnExponent Z X d) Vlabel εchild ell Ractive j tcount gcount theta eta ρ
    1 1 (-priorityHeight negative t) (priorityHeight negative t) w labels A
    hd₁ hd₂ hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL (lt_trans zero_lt_one hZ)
    (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _) hY hrows hblock
    hcube₁ hcube₂ hactive hj hquot hcommon hdiv hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  rw [second_cell_physical_scale Z X d hZ hX] at he
  refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) he
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hp hcop hg₀ Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) z x) * v)
    (actual_priority_profile_common p hp hcop hg₀ pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityCellEnergyWindowOrder -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_cell_recursive_window_order
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (Aker K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
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
    (_hs : ActualSecondSourceConditions p source) (d:InverseSecondSourceBlocks.BlockIndex)
    (_hcell:∀x∈source,InverseSecondSourceBlocks.index p x=d),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
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
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^Aker)) := by
  let g:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤ mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg:Function.support g⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile g)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_second_fixed_block_recursive_window_order (ι:=ι) (σ:=σ) (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X Vlabel εchild ell Ractive j tcount gcount theta eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY hrows hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hblock:=actual_source_block_ratios p hp source d hcell
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx))
  have he:=henergy p hp hcop hg₀ hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (scales d 0) (scales d 1) (scales d 2) (scales d 3) Y R L Z
    (secondCellColumnExponent Z X d) Vlabel εchild ell Ractive j tcount gcount theta eta ρ
    1 1 (-priorityHeight negative t) (priorityHeight negative t) w labels A
    hd₁ hd₂ hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL (lt_trans zero_lt_one hZ)
    (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _) hY hrows hblock
    hcube₁ hcube₂ hactive hj hquot hcommon hdiv hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  rw [second_cell_physical_scale Z X d hZ hX] at he
  refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) he
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hp hcop hg₀ Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) z x) * v)
    (actual_priority_profile_common p hp hcop hg₀ pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityCellEnergyWindowOrderUniform -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_cell_recursive_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (Aker K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
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
    (_hs : ActualSecondSourceConditions p source) (d:InverseSecondSourceBlocks.BlockIndex)
    (_hcell:∀x∈source,InverseSecondSourceBlocks.index p x=d),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (Y R L Z X Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
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
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+Vlabel) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^Aker)) := by
  let g:=priorityLogWindow om lo hi hlo hsupport negative
  let mg:=|Real.log lo|+|Real.log hi|
  have hm:0≤ mg:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg:Function.support g⊆Set.Icc (-mg) mg:=priorityLogWindow_support om lo hi hlo hsupport negative
  have hcg:Function.support (conjugateProfile g)⊆Set.Icc (-mg) mg:=by
    intro x hx
    apply hg
    simpa only [Function.mem_support,conjugateProfile_apply,star_ne_zero] using hx
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_second_fixed_block_recursive_window_order_uniform_types  (conjugateProfile g) g Φ mg mg 1
      (fun _=>1) (fun _=>2) B₀ hm hm (le_refl 1) (fun _=>zero_lt_one)
      (fun _=>by norm_num) hB₀ hcg hg Aker K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg₀ hpr hinj hc Jo source hs d hcell pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X Vlabel εchild ell Ractive j tcount gcount theta eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY hrows hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hblock:=actual_source_block_ratios p hp source d hcell
    (fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx))
  have he:=henergy p hp hcop hg₀ hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (scales d 0) (scales d 1) (scales d 2) (scales d 3) Y R L Z
    (secondCellColumnExponent Z X d) Vlabel εchild ell Ractive j tcount gcount theta eta ρ
    1 1 (-priorityHeight negative t) (priorityHeight negative t) w labels A
    hd₁ hd₂ hρ (le_refl 1) (le_refl 1) (le_refl 1) (le_refl 1) hL (lt_trans zero_lt_one hZ)
    (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _) (dyadScale_pos _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hZ) _) hY hrows hblock
    hcube₁ hcube₂ hactive hj hquot hcommon hdiv hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  rw [second_cell_physical_scale Z X d hZ hX] at he
  refine le_trans (le_of_eq (congrArg (fun v : ℂ => ‖(Y : ℂ) * secondRayCoefficient z * v‖) ?_)) he
  apply Finset.sum_congr rfl
  intro x _hx
  exact congrArg (fun v : ℂ => (w x * actualSecondSignedWeight p hp hcop hg₀ Ψ
    (m * ConcretePrimeRowBridge.idealGenerator x.quotient) z x) * v)
    (actual_priority_profile_common p hp hcop hg₀ pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ _ _ a₁ a₂ om lo hi hlo hsupport negative t Φ Y X hX)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondCellParameters -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def secondCellExponent (Z:ℝ) (d:BlockIndex) (i:Fin 4):ℝ:=Real.logb Z (scales d i)

theorem secondCellExponent_nonneg (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    0≤ secondCellExponent Z d i := by
  apply Real.logb_nonneg hZ
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

theorem second_cell_formal_column (Z r A B t:ℝ) (d:BlockIndex) (hZ:1<Z):
    secondCellColumnExponent Z (Z^(r-A-B-t)) d=
      secondFormalColumn r A B t (secondCellExponent Z d 0) (secondCellExponent Z d 2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  apply (Real.rpow_right_inj hz (ne_of_gt hZ)).mp
  rw [second_cell_column_scale Z _ d hZ (Real.rpow_pos_of_pos hz _)]
  rw [←second_cell_scale_rpow Z d 0 hZ,←second_cell_scale_rpow Z d 2 hZ,
    ←Real.rpow_add hz,←Real.rpow_sub hz]
  congr 1
  unfold secondFormalColumn
  ring

theorem actual_second_child_label_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (x:MarkedSecondSource ι Jo Jn) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)=
      ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*primeProductNorm p x.second.divisor*
      primeProductNorm p x.second.overlap := by
  have hn(S:Finset ι):(Ideal.absNorm (sourceIdeal p S):ℝ)=primeProductNorm p S:=by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈S,p i)).symm
  change (Ideal.absNorm (Ideal.span {(jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)} *
      sourceIdeal p x.firstCommon * sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap):ℝ)=_
  simp only [map_mul,Nat.cast_mul,hn,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem actual_cell_child_label_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      4*‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*scales d 1*scales d 2 := by
  have hE:= (cell_ratios p hp source hk d x hx 1).2.le
  have hV:= (cell_ratios p hp source hk d x hx 2).2.le
  have he:primeProductNorm p x.second.divisor≤2*scales d 1:=
    (div_le_iff₀ (dyadScale_pos _)).mp hE
  have hv:primeProductNorm p x.second.overlap≤2*scales d 2:=
    (div_le_iff₀ (dyadScale_pos _)).mp hV
  rw [actual_second_child_label_norm]
  calc
    _ ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*(2*scales d 1)*(2*scales d 2) := by
      have hc0 := (primeProductNorm_pos p hp x.firstCommon).le
      have hv0 := (primeProductNorm_pos p hp x.second.overlap).le
      have hs0 := (dyadScale_pos (d 1)).le
      gcongr
    _ = _ := by ring

theorem actual_cell_child_label_power {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ)
    (Z B j eta:ℝ) (hZ:1<Z) (hbin:2≤Z^eta)
    (hC:primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ:‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      Z^(secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hfour:(4:ℝ)≤Z^(2*eta):=by
    have hh:=mul_le_mul hbin hbin (by norm_num) (Real.rpow_nonneg hz.le _)
    norm_num only [←Real.rpow_add hz,show eta+eta=2*eta by ring] at hh
    exact hh
  apply (actual_cell_child_label_bound p hp source hk d x hx u v).trans
  calc
    _≤Z^(2*eta)*Z^(j+eta)*Z^(B+eta)*scales d 1*scales d 2:=by
      have hc0:0≤primeProductNorm p x.firstCommon:=(primeProductNorm_pos p hp _).le
      have hs1:0≤ scales d 1:=(dyadScale_pos _).le
      have hs2:0≤ scales d 2:=(dyadScale_pos _).le
      gcongr
    _= _:=by
      rw [←second_cell_scale_rpow Z d 1 hZ,←second_cell_scale_rpow Z d 2 hZ,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      unfold secondFormalLabel
      ring

theorem second_cell_clipping_width (Z X b eta:ℝ) (d:BlockIndex)
    (hZ:1<Z) (hX:0<X) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*X) (hthreshold:b≤Z^(6*eta)) :
    max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d≤6*eta := by
  exact (Real.rpow_le_rpow_left_iff hZ).mp
    ((second_cell_clipping_ratio Z X b d hZ hX hb hsource).2.trans hthreshold)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityCellBudget -/

section

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment
open InverseSecondSourceBlocks

theorem priority_cell_physical_budget
    (Z:ℝ) (hZ:1<Z) (d:BlockIndex)
    (M r ell V delta A B R j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ) (hC:0≤C) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*Z^(r-A-B-t))
    (hthreshold:b≤Z^(6*eta))
    (hmass:epsmass*(secondCount ell R j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) :
    let N:=secondCellColumnExponent Z (Z^(r-A-B-t)) d
    let Vchild:=secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta
    C*Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.exp (6*(eta*Real.log Z))*
        ‖((Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau):ℝ):ℂ)*ray*
          ((scales d 1*scales d 2*Z^N:ℝ):ℂ)⁻¹‖)*
      Z^((secondCount ell R j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
      Z^(2*(max 0 N+Vchild)+eps)≤
    C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  intro N Vchild
  have hz:0<Z:=zero_lt_one.trans hZ
  have hclip:=second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos hz _) hb hsource hthreshold
  rw [second_cell_formal_column Z r A B t d hZ] at hclip
  have he:=physical_block_scalar_budget Z hZ.le M r ell V delta A B R j t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) (secondCellExponent Z d 2)
    eta tau pi (eps+8*eta) epsmass ray C hC hclip hmass
  dsimp only [N,Vchild]
  rw [second_cell_formal_column Z r A B t d hZ]
  rw [second_cell_scale_rpow Z d 1 hZ,second_cell_scale_rpow Z d 2 hZ] at he
  convert he using 1 <;> congr 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityMovingRadius -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_source_moving_radius
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
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
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,henergy⟩:=
    actual_priority_cell_recursive (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ 0 J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤ scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y (R d) L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>by simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityMovingRadiusWindowOrder -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_priority_source_moving_radius_window_order
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
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
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_cell_recursive_window_order (ι:=ι) (σ:=σ) om Φ lo hi hlo hsupport negative B₀ hB₀ 0 K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤ scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y (R d) L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>by simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PriorityMovingRadiusWindowOrderUniform -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers
local notation "Eis" => ActualEisensteinCubic.O
theorem actual_priority_source_moving_radius_window_order_uniform_types
    (om Φ:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
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
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t) Φ Y X)‖ ≤
      ∑d∈keys p source,(Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*(((scales d 1)*(scales d 2)*(Z^(secondCellColumnExponent Z X d)) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 (secondCellColumnExponent Z X d)+(Vlabel d))+εchild))*
          Z^((ell+Ractive/2-j+tcount+(secondCellExponent Z d 0)-(secondCellExponent Z d 1)+11*eta/2)*(1+εmass)))*
          (C*((1+‖(-priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J *
            (1+‖(priorityHeight negative t)‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*(scales d 3)/((scales d 1)*(scales d 2)^2*(Z^(secondCellColumnExponent Z X d))^2))^0)) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_cell_recursive_window_order_uniform_types  om Φ lo hi hlo hsupport negative B₀ hB₀ 0 K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,hC,henergy⟩:=hordered J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y R L Z X εchild Vlabel ell Ractive j tcount eta ρ t w labels A
    hd₁ hd₂ hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hk:∀x∈source,x.second.frequency≠0:=fun x hx=>frequency_ne_zero_of_gate _ _ (hrows x hx)
  rw [physical_source_partition p hp hcop hg source pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ w]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  have hin : cell p source d⊆source:=cell_subset p source d
  have hcommon:∀x∈cell p source d,primeProductNorm p x.second.sourceCommon≤Z^(secondCellExponent Z d 0+eta):=by
    intro x hx
    have hr:primeProductNorm p x.second.sourceCommon≤2*scales d 0:=
      (div_le_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).2.le
    apply hr.trans
    rw [Real.rpow_add hz,second_cell_scale_rpow Z d 0 hZ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbin (show 0≤ scales d 0 from (dyadScale_pos _).le)
  have hdiv:∀x∈cell p source d,Z^(secondCellExponent Z d 1-eta)≤primeProductNorm p x.second.divisor:=by
    intro x hx
    have hr:scales d 1≤primeProductNorm p x.second.divisor:=by
      simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 1).1
    have hh:Z^(secondCellExponent Z d 1-eta)≤Z^(secondCellExponent Z d 1):=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    rw [second_cell_scale_rpow Z d 1 hZ] at hh
    exact hh.trans hr
  exact henergy p hp hcop hg hpr hinj hc (cell p source d) (cell_conditions p source hs d) d
    (fun x hx=>(mem_cell p source d x).mp hx |>.2) pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
    deleted₁ deleted₂ Y (R d) L Z X (Vlabel d) εchild ell Ractive j tcount
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta ρ t w (labels d) A
    (fun x hx=>hd₁ x (hin hx)) (fun x hx=>hd₂ x (hin hx)) hρ hL hZ hX hY
    (fun x hx=>by simpa only [(mem_cell p source d x).mp hx |>.2] using hrows x (hin hx)) (fun x hx=>hcube₁ x (hin hx)) (fun x hx=>hcube₂ x (hin hx))
    (fun x hx=>hactive x (hin hx)) (fun x hx=>hj x (hin hx)) (fun x hx=>hquot x (hin hx))
    hcommon hdiv hΨ (fun x hx=>hw x (hin hx)) ha₁ ha₂ (hlabels d hd) ho hslots₁ hslots₂ hA
    (hleft d hd) (hright d hd)

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.PrioritySourceBudget -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def priorityCellScalar (Z Y L X ell Ractive j t eta eps epsmass B:ℝ) (ray:ℂ) (d:BlockIndex):ℝ :=
  (Real.exp (6*L)*‖(Y:ℂ)*ray*((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
    Z^((secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
    Z^(2*(max 0 (secondCellColumnExponent Z X d)+
      (secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta))+eps)

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

theorem priority_source_scalar_budget (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) :
    ∃ Cbin:ℝ,0≤Cbin ∧ ∀ {ι:Type*} [DecidableEq ι]
    (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ), 2≤Z → 0≤C → 1≤b → b≤Z^(6*eta) →
    (∀x∈source,x.second.frequency≠0) →
    (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
    (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t)) →
    (∀d∈keys p source,epsmass*(secondCount ell Ractive j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) →
    C*Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (∑d∈keys p source,priorityCellScalar Z (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
        (eta*Real.log Z) (Z^(r-A-B-t)) ell Ractive j t eta eps epsmass B ray d) ≤
    C*‖ray‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  refine ⟨capConstant caps,capConstant_nonneg caps hcaps,?_⟩
  intro ι _ p hp _ Jo Jn source Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
    ray hZ hC hb hthreshold hk hnorm hgeom hmass
  have hZ':1<Z:=lt_of_lt_of_le (by norm_num) hZ
  have hz:0<Z:=zero_lt_one.trans hZ'
  have hcard:((keys p source).card:ℝ)≤(1+capConstant caps*Real.log Z)^4:=by
    have h:=keys_card_le_product p hp source hk caps Z hnorm
    have hr:((keys p source).card:ℝ)≤∏i:Fin 4,((dyadIndex (Z^(caps i)):ℝ)+1):=by exact_mod_cast h
    apply hr.trans
    calc
      _≤∏_i:Fin 4,(1+capConstant caps*Real.log Z):=
        Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>cap_bin_bound caps hcaps Z hZ i)
      _= _:=by simp
  rw [Finset.mul_sum]
  calc
    _≤∑_d∈keys p source,C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps):=by
      apply Finset.sum_le_sum
      intro d hd
      have he:=priority_cell_physical_budget Z hZ' d M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
        ray hC hb (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold (hmass d hd)
      convert he using 1 ; dsimp only [priorityCellScalar] ; ring
    _= ((keys p source).card:ℝ)*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=by simp
    _≤ (1+capConstant caps*Real.log Z)^4*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _= _:=by ring

end SevenEighths.InverseMoment

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildState -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellLabelExponent (Z B j eta : ℝ) (d : BlockIndex) : ℝ :=
  secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta

def actualCellTotalExponent (Z X B j eta : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)+actualCellLabelExponent Z B j eta d

def actualCellClipping (Z X : ℝ) (d : BlockIndex) : ℝ :=
  max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d

lemma actual_cell_total_transition (Z r ell V A B t j eta : ℝ) (d : BlockIndex) (hZ : 1<Z) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d=
      childF (r+3*ell+V) ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j
        (actualCellClipping Z (Z^(r-A-B-t)) d+4*eta) := by
  unfold actualCellTotalExponent actualCellLabelExponent actualCellClipping
  rw [second_cell_formal_column Z r A B t d hZ]
  unfold childF decrease secondFormalColumn secondFormalLabel
  ring

lemma actual_cell_label_nonneg (Z B j eta : ℝ) (d : BlockIndex)
    (hZ : 1<Z) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) :
    0≤actualCellLabelExponent Z B j eta d := by
  have h1 := secondCellExponent_nonneg Z d 1 hZ
  have h2 := secondCellExponent_nonneg Z d 2 hZ
  unfold actualCellLabelExponent secondFormalLabel
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

omit [DecidableEq ι] in
theorem actual_cell_norm_centers {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (i : Fin 4) :
    Z^(secondCellExponent Z d i-eta)≤outerNorms p x i ∧
      outerNorms p x i≤Z^(secondCellExponent Z d i+eta) := by
  have hr := cell_ratios p hp source hk d x hx i
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlo := (le_div_iff₀ (dyadScale_pos (d i))).mp hr.1
  have hhi := (div_le_iff₀ (dyadScale_pos (d i))).mp hr.2.le
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : secondCellExponent Z d i-eta≤ secondCellExponent Z d i)).trans
    simpa only [second_cell_scale_rpow Z d i hZ,one_mul,scales] using hlo
  · calc
      _ ≤ 2*scales d i := hhi
      _ ≤ Z^eta*scales d i := mul_le_mul_of_nonneg_right hbin (dyadScale_pos _).le
      _ = _ := by rw [←second_cell_scale_rpow Z d i hZ,←Real.rpow_add hz];congr 1;ring

theorem actual_cell_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (u v : Oˣ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta)) :
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  apply actual_second_child_margins_from_cubes p hp hpr x (hs.second_divisor x hxs)
    (hs.quotient_nonzero x hxs) u v m hm Z (r+3*ell+V) M Q z c ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j _ eta hZ hparent hA ht hV hj
    (by unfold actualCellClipping;have := le_max_right 0 (secondCellColumnExponent Z (Z^(r-A-B-t)) d);linarith)
    heta hQ h1 h2 hT
  · simpa only [outerNorms,Matrix.cons_val_zero] using hG
  · simpa only [outerNorms,Matrix.cons_val_one,Matrix.cons_val_zero] using hD

theorem actual_cell_child_total_upper {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z r ell V A B t j eta b : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hb : 1≤b) (hthreshold : b≤Z^(6*eta))
    (hgeom : ∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t))
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d≤(r+3*ell+V)+15*eta := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hgt := actual_second_common_center p hp x (hs.second_divisor x hxs) Z
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta hZ
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD)
  have hj := actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ
  have hd : d∈keys p source := (mem_keys_iff p source d).mpr ⟨x,hx⟩
  have hc := second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hb
    (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  unfold childF decrease actualCellClipping
  linarith

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildStateLabels -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def actualCellLabels {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : Finset (Ideal O) :=
  (cell p source d).image (fun x=>(actualSecondChild p 1 1 x).2.1)

lemma actual_cell_labels_cover {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) :
    (actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem actual_cell_labels_bound (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈actualCellLabels p source d,(Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hI
  exact actual_cell_child_label_power p hp source hk d x hx 1 1 Z B j eta hZ hbin
    (hC x (cell_subset p source d hx)) (hJ x (cell_subset p source d hx))

theorem actual_cell_squarefree_labels (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,hi.2.ne_zero,actual_cell_labels_bound p hp source hk d Z B j eta hZ hbin hC hJ I hi.1⟩

theorem actual_cell_nonzero_weight_label (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m ray x≠0) :
    (actualSecondChild p 1 1 x).2.1∈(actualCellLabels p source d).filter Squarefree := by
  have hxs := cell_subset p source d hx
  exact Finset.mem_filter.mpr ⟨actual_cell_labels_cover p source d x hx,
    actual_second_nonzero_weight_squarefree p hp hcop hg Ψ m ray x
      (hs.common_disjoint x hxs) (hs.second_divisor x hxs) hw 1 1⟩

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_label_support {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) :=
  actual_cell_child_label_power p hp source hk d x hx u v Z B j eta hZ hbin hC hJ

theorem actual_cell_correlated_row_support
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (u v : Oˣ)
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    (actualSecondChild p u v x).2.2∈nonzeroChildFrequencyBall 1
      (Z^(childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)) := by
  have hE := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr := second_correlated_radius_childM p hp
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor) x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 hd (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  apply (actual_second_row_ball p hp hpr x u v _).mp
  have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hgate
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

omit hp in

lemma actual_child_row_length_nonneg (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) : 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^M) k).mp hk
  simp only [one_mul] at hb
  have hk0 : k≠0 := (Finset.mem_erase.mp hk).1
  have hn := EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq k hk0
  have hpow : Z^(0:ℝ)≤Z^M := by simpa only [Real.rpow_zero,one_mul] using hn.trans hb.2
  exact (Real.rpow_le_rpow_left_iff hZ).mp hpow

theorem actual_cell_row_decrease {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hs : ActualSecondSourceConditions p source)
    (hk : ∀x∈source,x.second.frequency≠0) (d : BlockIndex)
    (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z M ell A t V j eta cutoff : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : cutoff≤ell+V) (hsmall : eta≤ cutoff/16)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta+3*cutoff/2≤M := by
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  have hh := actual_second_row_decrease p hp x (hs.second_divisor x (cell_subset p source d hx)) Z M ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta cutoff hZ hA ht hterminal hsmall
    (by simpa [outerNorms] using hG) (by simpa [outerNorms] using hD) h1 h2 hJ
  linarith

theorem actual_cell_triple_puncture_nonzero
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) (m : O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildStateDepth -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem actual_cell_path_lengths {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (Jo Jn : ℕ→ℕ) (source : (k : ℕ)→Finset (MarkedSecondSource ι (Jo k) (Jn k)))
    (cellIndex : ℕ→BlockIndex) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M r ell V A B t j b : ℕ→ℝ) (Z eta cutoff : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hsmall : eta≤ cutoff/16) (n : ℕ)
    (hsource : ∀k<n,
      ActualSecondSourceConditions p (source k) ∧
      (∀y∈source k,y.second.frequency≠0) ∧ x k∈cell p (source k) (cellIndex k) ∧
      F k=r k+3*ell k+V k ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ cutoff≤ell k+V k ∧
      1≤b k ∧ b k≤Z^(6*eta) ∧
      (∀y∈source k,primeProductNorm p y.second.sourceCommon*primeProductNorm p y.second.overlap≤
        b k*Z^(r k-A k-B k-t k)) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀k<n,F (k+1)=actualCellTotalExponent Z (Z^(r k-A k-B k-t k)) (B k) (j k) eta (cellIndex k))
    (hM : ∀k<n,M (k+1)=childM (M k) (ell k) (A k) (t k)
      (secondCellExponent Z (cellIndex k) 0) (secondCellExponent Z (cellIndex k) 1) (V k) (j k) eta) :
    F n≤F 0+15*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*cutoff/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    obtain ⟨hs,hk,hx,hparent,hA,ht,hell,hV,hterm,hb,hthreshold,hgeom,h1,h2,hj⟩ := hsource n hn
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hn))
      (fun k hk=>hF k (Nat.lt_trans hk hn)) (fun k hk=>hM k (Nat.lt_trans hk hn))
    have hf := actual_cell_child_total_upper p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (r n) (ell n) (V n) (A n) (B n) (t n) (j n) eta (b n) hZ hA ht hell hV heta hbin
      hb hthreshold hgeom h1 h2 hj
    have hm := actual_cell_row_decrease p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (M n) (ell n) (A n) (t n) (V n) (j n) eta cutoff hZ hA ht heta hbin hterm hsmall h1 h2 hj
    rw [←hF n hn,←hparent] at hf
    rw [←hM n hn] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem actual_cell_depth_caps (F M N V F0 M0 eta : ℝ) (n depth : ℕ)
    (hn : n≤depth) (heta : 0≤eta) (hF : F≤F0+15*(n:ℝ)*eta)
    (hM : M≤M0) (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+15*(depth:ℝ)*eta ∧ V≤F0+15*(depth:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hM

theorem actual_cell_depth_bound (M M0 cutoff : ℝ) (n : ℕ) (hcutoff : 0<cutoff)
    (hM : 0≤M) (hpath : M+3*(n:ℝ)*cutoff/2≤M0) :
    (n:ℝ)≤2*M0/(3*cutoff) := by
  apply (le_div_iff₀ (by positivity : 0<3*cutoff)).mpr
  nlinarith

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildStatePuncture -/

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic InverseSecondFibers CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma actual_inherited_puncture_dvd (m : O) (γ : OuterTriple) :
    m∣actualSecondInheritedPuncture m γ := by
  refine ⟨ConcretePrimeRowBridge.idealGenerator γ.quotient*primaryGenerator γ.q0*
    primaryGenerator γ.residual,?_⟩
  unfold actualSecondInheritedPuncture actualSecondPuncture
  ring

lemma actual_inherited_radical_puncture_span (m : O) (γ : OuterTriple) :
    Ideal.span {actualSecondInheritedRadicalPuncture m γ}=
      (Ideal.span {actualSecondInheritedPuncture m γ}:Ideal O).radical :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma actual_inherited_radical_preserves_support (m : O) (γ : OuterTriple) :
    (Ideal.span {m}:Ideal O).radical∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.dvd_iff_le]
  apply Ideal.radical_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact actual_inherited_puncture_dvd m γ

lemma actual_inherited_radical_preserves_fixed (m : O) (γ : OuterTriple) (Q : Ideal O)
    (hQ : Q.radical=Q) (hparent : Q∣Ideal.span {m}) :
    Q∣Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  apply dvd_trans _ (actual_inherited_radical_preserves_support m γ)
  rw [Ideal.dvd_iff_le,←hQ]
  exact Ideal.radical_mono (Ideal.dvd_iff_le.mp hparent)

lemma actual_inherited_radical_is_radical (m : O) (γ : OuterTriple) :
    (Ideal.span {actualSecondInheritedRadicalPuncture m γ}:Ideal O).radical=
      Ideal.span {actualSecondInheritedRadicalPuncture m γ} := by
  rw [actual_inherited_radical_puncture_span,Ideal.radical_idem]

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildStateRadius -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def actualCellRowExponent (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta

def actualCellRowRadius (Z M ell A t V j eta : ℝ) (d : BlockIndex) : ℝ :=
  Z^(actualCellRowExponent Z M ell A t V j eta d)

lemma actual_cell_row_radius_pos (Z M ell A t V j eta : ℝ) (d : BlockIndex) (hZ : 0<Z) :
    0<actualCellRowRadius Z M ell A t V j eta d := Real.rpow_pos_of_pos hZ _

theorem actual_cell_correlated_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hd : ∀x∈source,‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)‖^2≤Z^(delta+eta))
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (correlatedSecondRadius p (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
        x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs := cell_subset p source d hx
  exact (actual_second_row_ball p hp hpr x 1 1 _).mpr
    (actual_cell_correlated_row_support p hp hpr source hk d x hx 1 1
      Z M r ell V delta A B j t eta tau L hZ heta hbin hL0 (hd x hxs) hL (hgate x hxs))

theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1<Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hr := actual_second_row_radius_one p (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) ⟨x,hx⟩ (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero,actualCellRowRadius] using hr)

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualChildStateTriples -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_triple_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀x∈source,(Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta))
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 ∧
    0≤actualSecondPunctureWidth Z m γ ∧
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  have hn := actual_cell_triple_puncture_nonzero p hp hpr source hs d m hm γ hγ
  refine ⟨hn,?_,?_,?_⟩
  · exact Real.logb_nonneg hZ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn)
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)))).symm
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    have hxs := cell_subset p source d hx
    exact actual_cell_child_margins p hp hpr source hs hk d x hx 1 1 m hm
      Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ
      (h1 x hxs) (h2 x hxs) (hT x hxs)

omit hp in

theorem actual_child_enlarged_row_bounds (Z M : ℝ) (hZ : 1<Z) (k : O)
    (hk : k∈nonzeroChildFrequencyBall 1 (Z^M)) :
    k≠0 ∧ ‖eisEmbedding k‖^2≤Z^M ∧ 0≤M := by
  have hb := (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ k).mp hk
  simp only [one_mul] at hb
  exact ⟨(Finset.mem_erase.mp hk).1,hb.2,actual_child_row_length_nonneg Z M hZ k hk⟩

omit hp in

theorem actual_child_size_caps (F M Q z c cap : ℝ)
    (hinv : CanonicalMargins F M Q z c) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hc : 0≤ c) (hF : F≤ cap) : M≤ cap ∧ Q≤ cap ∧ z≤ cap := by
  obtain ⟨h1,h2⟩ := hinv
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.ActualDepthBudget -/

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment

def actualDepth (Mmax cutoff : ℝ) : ℕ := ⌈2*Mmax/(3*cutoff)⌉₊+1

lemma actualDepth_pos (Mmax cutoff : ℝ) : 0<actualDepth Mmax cutoff := by
  exact Nat.succ_pos _

lemma actualDepth_strict (Mmax cutoff : ℝ) :
    2*Mmax/(3*cutoff)<(actualDepth Mmax cutoff:ℝ) := by
  have h := Nat.le_ceil (2*Mmax/(3*cutoff))
  unfold actualDepth
  push_cast
  linarith

theorem actual_depth_parameters (depth : ℕ) (cutoff c eps : ℝ)
    (hd : 0<cutoff) (hc : 0<c) (heps : 0<eps) :
    ∃eta tau pi : ℝ,0<eta ∧ 0<tau ∧ 0<pi ∧ eta≤ cutoff/16 ∧
      (depth:ℝ)*7*eta≤ c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4 := by
  let D : ℝ := (depth:ℝ)+1
  have hD : 0<D := by dsimp [D];positivity
  have hn : 0≤(depth:ℝ) := Nat.cast_nonneg _
  have hnD : (depth:ℝ)≤D := by dsimp [D];linarith
  let eta := min (cutoff/16) (min (c/(28*D)) (min (1/(30*D)) (eps/(1600*D))))
  let tau := eps/(128*D)
  have heta : 0<eta := by dsimp [eta];positivity
  have htau : 0<tau := by dsimp [tau];positivity
  have he1 : eta≤ cutoff/16 := min_le_left _ _
  have he2 : eta≤ c/(28*D) := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : eta≤1/(30*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he4 : eta≤eps/(1600*D) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hb2 : eta*(28*D)≤ c := (le_div_iff₀ (by positivity)).mp he2
  have hb3 : eta*(30*D)≤1 := (le_div_iff₀ (by positivity)).mp he3
  have hb4 : eta*(1600*D)≤eps := (le_div_iff₀ (by positivity)).mp he4
  have ht : tau*(128*D)=eps := by dsimp [tau];field_simp
  have hne : (depth:ℝ)*eta≤D*eta := mul_le_mul_of_nonneg_right hnD heta.le
  have hnt : (depth:ℝ)*tau≤D*tau := mul_le_mul_of_nonneg_right hnD htau.le
  refine ⟨eta,tau,tau,heta,htau,htau,he1,?_,?_,?_⟩ <;> nlinarith

theorem actual_depth_margin_size (depth n : ℕ) (hn : n≤depth)
    (c eta F0 : ℝ) (heta : 0≤eta)
    (hmargin : (depth:ℝ)*7*eta≤ c/2) (hsize : (depth:ℝ)*15*eta≤1) :
    c/2≤ c-7*(n:ℝ)*eta ∧ F0+15*(n:ℝ)*eta≤F0+1 := by
  have hnn : (n:ℝ)≤depth := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_right hnn heta
  constructor <;> nlinarith

theorem actual_depth_uniform_caps (depth n : ℕ) (hn : n≤depth)
    (F M N V Q z c F0 M0 eta : ℝ) (heta : 0≤eta) (hc : 0<c)
    (hmargin : (depth:ℝ)*7*eta≤ c/2) (hsize : (depth:ℝ)*15*eta≤1)
    (hF : F≤F0+15*(n:ℝ)*eta) (hM0 : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hM : 0≤M) (hQ : 0≤Q) (hz : 0≤z)
    (hsum : F=N+V) (hinv : CanonicalMargins F M Q z (c-7*(n:ℝ)*eta)) :
    N≤F0+1 ∧ V≤F0+1 ∧ M≤ min M0 (F0+1) ∧ Q≤F0+1 ∧ z≤F0+1 := by
  have hh := actual_depth_margin_size depth n hn c eta F0 heta hmargin hsize
  have hFcap : F≤F0+1 := hF.trans hh.2
  have hcaps := actual_child_size_caps F M Q z (c-7*(n:ℝ)*eta) (F0+1)
    hinv hM hQ hz (by linarith [hh.1]) hFcap
  refine ⟨?_,?_,le_min hM0 hcaps.1,hcaps.2.1,hcaps.2.2⟩ <;> linarith

theorem actual_depth_retained_loss (depth n : ℕ) (hn : n≤depth)
    (eta tau pi epsChild eps : ℝ) (he : 0≤eta) (ht : 0≤tau) (hp : 0≤pi)
    (hc : 0≤epsChild) (hbudget : (depth:ℝ)*(100*eta+4*tau+4*pi)≤eps/4)
    (hchild : (depth:ℝ)*epsChild≤eps/4) :
    (n:ℝ)*(48*eta+tau+pi+epsChild)≤eps/2 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have h1 := mul_le_mul_of_nonneg_right hn' (show 0≤48*eta+tau+pi+epsChild by positivity)
  have h2 : (depth:ℝ)*(48*eta+tau+pi)≤(depth:ℝ)*(100*eta+4*tau+4*pi) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  nlinarith

theorem actual_depth_row_negative (M Mmax cutoff : ℝ) (n : ℕ) (hd : 0<cutoff)
    (hn : actualDepth Mmax cutoff≤n)
    (hpath : M+3*(n:ℝ)*cutoff/2≤Mmax) : M<0 := by
  have hn' : (actualDepth Mmax cutoff:ℝ)≤n := by exact_mod_cast hn
  have hs := (actualDepth_strict Mmax cutoff).trans_le hn'
  have hs' := (div_lt_iff₀ (by positivity : 0<3*cutoff)).mp hs
  nlinarith

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMask -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge CanonicalQuadraticSieve
open InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

section General
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
theorem rowCoprimeMask_redundant_mul (S : Finset ι) (m c : Eis)
    (hc : ∀ i∈S,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (m*c)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) S m := by
  have he : (∃i∈S,m*c∈Ideal.span {p i}) ↔ ∃i∈S,m∈Ideal.span {p i} := by
    constructor
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,((inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hm).elim id (hc i hi)⟩
    · rintro ⟨i,hi,hm⟩
      exact ⟨i,hi,Ideal.mul_mem_right _ _ hm⟩
  simp only [rowCoprimeMask,he]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c f k : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ (m*c) f k slots lists a W X=
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro S hS
  have hm := rowCoprimeMask_redundant_mul p S m c
    (fun i hi=>hc i (Finset.mem_powerset.mp hS hi))
  simp only [secondChildColumn,hm]

omit [DecidableEq σ] in
theorem normalizedColumnEnergy_redundant_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m c : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z F : ℝ)
    (hc : ∀ i∈pool,c∈Ideal.span {p i}→m∈Ideal.span {p i}) :
    normalizedColumnEnergy p hp hcop hg pool Ψ (m*c) slots lists a labels rows D W X Z F=
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F := by
  simp only [normalizedColumnEnergy,finiteCanonicalMarkedRow_redundant_puncture
    p hp hcop hg pool Ψ m c _ _ slots lists a W X hc]

omit [DecidableEq ι] in
theorem puncture_mem_of_radical_dvd (m c : Eis)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣(Ideal.span {m}:Ideal Eis).radical)
    (i : ι) (hi : c∈Ideal.span {p i}) : m∈Ideal.span {p i} := by
  rw [←Ideal.span_singleton_le_iff_mem]
  apply Ideal.le_radical.trans
  apply (Ideal.dvd_iff_le.mp hc).trans
  exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.mpr
    (by rwa [Ideal.span_singleton_le_iff_mem])

omit [DecidableEq ι] in
theorem inherited_puncture_redundant_mem (m c : Eis)
    (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (i : ι) (hi : c∈Ideal.span {p i}) :
    actualSecondInheritedRadicalPuncture m γ∈Ideal.span {p i} := by
  have hd := actual_inherited_radical_preserves_fixed m γ (Ideal.span {c}).radical
    (Ideal.radical_idem _) hc
  apply puncture_mem_of_radical_dvd p _ c _ i hi
  rw [actual_inherited_radical_is_radical]
  exact hd

end General

theorem outside_pool_redundant_puncture {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m f k : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) f k slots lists a W X=
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ m f k slots lists a W X := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply finiteCanonicalMarkedRow_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

end SevenEighths.InverseMoment
end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.CanonicalPunctureMaskEnergy -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

theorem outside_pool_redundant_energy {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (m*excludedGenerator S) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  apply normalizedColumnEnergy_redundant_puncture
  intro i hi hc
  rw [poolPrimary_span F hF i] at hc
  exact False.elim (excludedGenerator_not_mem_pool S D hSp i hc)

theorem reflection_pool_mask_energy {σ : Type*} [DecidableEq σ]
    (q D : ℕ)
    (pool : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (Ψ : Eis →* ℂ) (m : Eis) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      (ActualFiber.maskElement q m) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) pool Ψ
      m slots lists a labels rows weight W X Z Fexp :=
  outside_pool_redundant_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) (reflectionExcludedPrimes_prime q)
    pool Ψ m slots lists a labels rows weight W X Z Fexp

theorem inherited_radical_mask_energy {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι→Eis) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Ψ : Eis→*ℂ) (m c : Eis) (γ : InverseSecondFibers.OuterTriple)
    (hc : (Ideal.span {c}:Ideal Eis).radical∣Ideal.span {m})
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (weight : Ideal Eis→ℝ)
    (W : ℝ→ℂ) (X Z Fexp : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ*c) slots lists a labels rows weight W X Z Fexp=
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (actualSecondInheritedRadicalPuncture m γ) slots lists a labels rows weight W X Z Fexp :=
  normalizedColumnEnergy_redundant_puncture p hp hcop hg pool Ψ _ c
    slots lists a labels rows weight W X Z Fexp
    (fun i _=>inherited_puncture_redundant_mem p m c γ hc i)

end SevenEighths.InverseMoment
end

end OAI

end

