module

public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part008
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part002
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part007
public import Green64.Library.OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower
public import Green64.Library.Analysis.NumberTheory.DirichletL.IdealEuler.Part001
public import Green64.Library.Analysis.NumberTheory.DirichletL.Inversion.Part003
public import Green64.Library.Analysis.NumberTheory.DirichletL.Descent.Part004
public import Green64.Library.Analysis.NumberTheory.DirichletL.CubicSieve.Part016

@[expose] public section

/-!
# Analysis / NumberTheory / DirichletL / Descent / Part009

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondDeletedModeEnergy -/

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

theorem actual_second_deleted_mode_branch_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
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
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
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
  have he := actual_second_supported_varying_lists_energy p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*ConcretePrimeRowBridge.idealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)
    (fun _ _ _ _=>Finset.sdiff_subset) (fun _ _ _ _=>Finset.sdiff_subset) a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [secondModeBranch_parent_lists_restore p hp hcop hg hpr x (hs.admissible x hx)
    (hs.second_divisor x hx) u v (deleted₁ x) (deleted₂ x) (hd₁ x hx) (hd₂ x hx)]
  dsimp only [phase]
  ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondWholeMass -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem actualSecondChild_outer_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).1 = (actualSecondChild p 1 1 x).1 := rfl

theorem actualSecondChild_label_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).2.1 = (actualSecondChild p 1 1 x).2.1 := rfl

theorem actualSecondTriples_units {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) :
    actualSecondTriples p u v source = actualSecondTriples p 1 1 source := rfl

theorem assigned_second_triples_subset {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂) ⊆
      actualSecondTriples p 1 1 source := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

theorem assigned_second_mass_le_original {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (K : ℕ) :
    (∑ γ∈actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),tripleDivisorWeight K γ) ≤
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (assigned_second_triples_subset p u v source J₁ J₂ L₁ L₂)
    (fun γ _ _ => tripleDivisorWeight_nonneg K γ)

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondDeletedOriginalBound -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈J₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈J₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖∑ x∈source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := (actualSecondTriples_mono p u v
    (show varyingAssignedSource source J₁ J₂ lists₁ lists₂
      (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)⊆
      assignedSecondSource source J₁ J₂ lists₁ lists₂ from Finset.filter_subset _ _)).trans
      (assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂)
  apply (actual_second_deleted_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hΓ (fun γ _ _=>tripleDivisorWeight_nonneg K γ)) hA

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondDeletedAllModes -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondDeletedFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondDeletedFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondDeletedFullModeSum
  apply Finset.sum_congr rfl
  intro uv huv
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem actual_second_deleted_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_deleted_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      (fun x hx=>hd₁ x (hsub hx)) (fun x hx=>hd₂ x (hsub hx))
      (fun i hi => ha₁ i (Finset.mem_powerset.mp hJ₁ hi))
      (fun i hi => ha₂ i (Finset.mem_powerset.mp hJ₂ hi)) ω₁ ω₂ G E V B X R t labels
      (fun x hx => hlabels x (hsub hx)) (fun x hx => hrows x (hsub hx)) K ho
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₁)).trans hslots₁)
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₂)).trans hslots₂)
      w (fun x hx => hw x (hsub hx)) A hA
      (fun γ hγ => hleft J₁ hJ₁ γ (ht hγ)) (fun γ hγ => hright J₂ hJ₂ γ (ht hγ))
    exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun γ _ _ => tripleDivisorWeight_nonneg K γ)) hA)
  calc
    _ ≤ ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
        ‖∑ x∈secondSourceSector source sector uv,
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
              ω₁ ω₂ G E V B X t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro uv huv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact norm_sum_le _ _
    _ ≤ ∑ _uv : Eisˣ × Eisˣ,∑ _J₁∈slots₁.powerset,∑ _J₂∈slots₂.powerset,A*mass := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact Finset.sum_le_sum (fun J₂ hJ₂ => hbound uv J₁ hJ₁ J₂ hJ₂)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,
        second_unit_sector_card,Nat.cast_pow,Nat.cast_ofNat,mass]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondDeletedAllIntegral -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ)
    (hDensity : Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J t.1*coordinateHeight J t.2*‖density t‖))
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_deleted_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
      K ho hslots₁ hslots₂ w hw (A*(tripleHeight J t.1*coordinateHeight J t.2))
      (by unfold tripleHeight coordinateHeight; positivity) (hleft t) (hright t)
    exact hh.trans_eq (by dsimp only [C]; ring)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),C*(tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul C)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondOriginalBound -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈J₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖∑ x∈source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂
  apply (actual_second_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left (assigned_second_mass_le_original p u v source J₁ J₂ lists₁ lists₂ K) hA

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondAllModes -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondFullModeSum
  apply Finset.sum_congr rfl
  intro uv huv
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem actual_second_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
      (fun i hi => ha₁ i (Finset.mem_powerset.mp hJ₁ hi))
      (fun i hi => ha₂ i (Finset.mem_powerset.mp hJ₂ hi)) ω₁ ω₂ G E V B X R t labels
      (fun x hx => hlabels x (hsub hx)) (fun x hx => hrows x (hsub hx)) K ho
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₁)).trans hslots₁)
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₂)).trans hslots₂)
      w (fun x hx => hw x (hsub hx)) A hA
      (fun γ hγ => hleft J₁ hJ₁ γ (ht hγ)) (fun γ hγ => hright J₂ hJ₂ γ (ht hγ))
    exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun γ _ _ => tripleDivisorWeight_nonneg K γ)) hA)
  calc
    _ ≤ ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
        ‖∑ x∈secondSourceSector source sector uv,
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro uv huv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact norm_sum_le _ _
    _ ≤ ∑ _uv : Eisˣ × Eisˣ,∑ _J₁∈slots₁.powerset,∑ _J₂∈slots₂.powerset,A*mass := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact Finset.sum_le_sum (fun J₂ hJ₂ => hbound uv J₁ hJ₁ J₂ hJ₂)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,
        second_unit_sector_card,Nat.cast_pow,Nat.cast_ofNat,mass]
      ring

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondAllIntegral -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ)
    (hDensity : Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J t.1*coordinateHeight J t.2*‖density t‖))
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
      K ho hslots₁ hslots₂ w hw (A*(tripleHeight J t.1*coordinateHeight J t.2))
      (by unfold tripleHeight coordinateHeight; positivity) (hleft t) (hright t)
    exact hh.trans_eq (by dsimp only [C]; ring)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),C*(tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul C)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SourceDepth -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in

theorem actual_second_childF_upper {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (Z F ell A t g theta V j delta eta : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (hdelta : delta≤6*eta)
    (hG : primeProductNorm p x.second.sourceCommon≤Z^(g+eta))
    (hD : Z^(theta-eta)≤primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childF F ell A t g theta V j delta≤F+11*eta :=
  childF_upper hA ht hell hV
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hdelta

include hp in

theorem actual_source_path_lengths
    (Jo Jn : ℕ→ℕ) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M ell A t g theta V j delta : ℕ→ℝ) (Z eta d : ℝ) (hZ : 1<Z)
    (n : ℕ) (heta : eta≤d/16)
    (hsource : ∀ k<n,
      (x k).second.divisor⊆(x k).second.sourceCommon ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ delta k≤6*eta ∧ d≤ell k+V k ∧
      primeProductNorm p (x k).second.sourceCommon≤Z^(g k+eta) ∧
      Z^(theta k-eta)≤primeProductNorm p (x k).second.divisor ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀ k<n,F (k+1)=childF (F k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) (delta k))
    (hM : ∀ k<n,M (k+1)=childM (M k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) eta) :
    F n≤F 0+11*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*d/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n<n+1 := Nat.lt_succ_self n
    obtain ⟨he,ha,ht,hl,hv,hd,hterm,hg,hdiv,h1,h2,hj⟩ := hsource n hlt
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hlt))
      (fun k hk=>hF k (Nat.lt_trans hk hlt)) (fun k hk=>hM k (Nat.lt_trans hk hlt))
    have hf := actual_second_childF_upper p hp (x n) he Z (F n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) (delta n) eta hZ ha ht hl hv hd hg hdiv h1 h2 hj
    have hm := actual_second_row_decrease p hp (x n) he Z (M n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) eta d hZ ha ht hterm heta hg hdiv h1 h2 hj
    rw [←hF n hlt] at hf
    rw [←hM n hlt] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem source_depth_caps (F M N V F0 M0 eta : ℝ) (n D : ℕ) (hn : n≤D)
    (heta : 0≤eta) (hF : F≤F0+11*(n:ℝ)*eta) (_hM : 0≤M) (hMm : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+11*(D:ℝ)*eta ∧ V≤F0+11*(D:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤D := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hMm

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

theorem clippedTest_eq_source (w : ℝ → ℂ) (c h x : ℝ) :
    clippedTest w c h x = InverseInitialProfile.clippedSource w c h x := by
  unfold clippedTest childLogTest InverseInitialProfile.clippedSource
  ring

theorem child_test_clipping (w : ℝ → ℂ) {Z q : ℝ} (hZ : 0 < Z) (hq : 0 < q)
    (N h : ℝ) :
    childLogTest w h (q/Z^N) = logPhase h (Real.log (Z^(max 0 N-N))) *
      clippedTest w (Z^(max 0 N-N)) h (q/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,mul_comm] using
    InverseInitialProfile.clipped_column_source_identity w hZ hq N h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) : Finset (Finset ι) :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) (U : Finset ι) :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem clippedTest_support_of_freshColumns (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N h : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hZ : 1 < Z)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    Function.support (clippedTest w (Z^(max 0 N-N)) h) ⊆ Set.Icc (a/b) b := by
  obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hs := InverseClippingProfiles.clipped_positive_support w a b _ ha hc hcb hw
  intro x hx
  exact hs (mul_ne_zero_iff.mp hx).1

theorem canonical_row_zero_of_freshColumns_empty
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ) (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_eq_zero
  intro U hU
  have hw : w (primeProductNorm p U/X) = 0 := by
    by_contra hw
    have hu : U ∈ freshColumns p pool w X := Finset.mem_filter.mpr ⟨hU,hw⟩
    rw [he] at hu
    exact Finset.notMem_empty U hu
  simp only [secondChildColumn,childLogTest,hw,zero_mul,mul_zero]

theorem canonical_row_nonzero_freshColumns
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ)
    (hn : finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X ≠ 0) : (freshColumns p pool w X).Nonempty := by
  by_contra he
  exact hn (canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m f k
    slots lists a w X h (Finset.not_nonempty_iff_eq_empty.mp he))

theorem canonical_row_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      logPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem canonical_row_clipping_norm
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots lists a w hZ N h,
    norm_mul,logPhase_norm,one_mul]

def columnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots lists a W X‖^2

theorem columnEnergy_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold columnEnergy
  simp_rw [canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _ slots lists a w hZ N h]

theorem canonical_pair_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ h₁) (Z^N) *
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ (-h₂)) (Z^N)) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) h₁) (Z^(max 0 N)) *
      star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) (-h₂)) (Z^(max 0 N)))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

theorem canonical_pair_clipping_left_conjugate
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ (-h₁)) (Z^N)) *
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ h₂) (Z^N) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) (-h₁)) (Z^(max 0 N))) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) h₂) (Z^(max 0 N))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

def normalizedColumnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

theorem columnEnergy_normalization
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) {Z : ℝ} (hZ : 0 < Z) (F : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

theorem initial_columnEnergy_clipping_normalized
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N V h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z (max 0 N+V) := by
  rw [columnEnergy_clipping p hp hcop hg pool Ψ m slots lists a labels rows D w hZ N h]
  exact columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows D
    _ _ hZ _

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 5+z.1.2.1-z.1.2.2

theorem leftHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    leftHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 4 := by
  simp [leftHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

theorem rightHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    rightHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 5 := by
  simp [rightHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

def clippingPhase (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) : ℂ :=
  logPhase (leftHeight z+rightHeight z) (Real.log c)

theorem clippingPhase_norm (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) :
    ‖clippingPhase c z‖ = 1 := logPhase_norm _ _

theorem clippingPhase_continuous (c : ℝ) : Continuous (clippingPhase c) := by
  unfold clippingPhase leftHeight rightHeight logPhase
  fun_prop

theorem fresh_pair_mode_clipping (w₁ w₂ : ℝ → ℂ)
    {Z q₁ q₂ : ℝ} (hZ : 0 < Z) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (N : ℝ) (y : Fin 6 → ℝ) (z : Frequency × (Fin 6 → ℝ))
    (hy₁ : y 4 = Real.log (q₁/Z^N)) (hy₂ : y 5 = Real.log (q₂/Z^N)) :
    (w₁ (q₁/Z^N)*star (w₂ (q₂/Z^N))) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y z.1 z.2 =
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
      clippingPhase (Z^(max 0 N-N)) z *
      (clippedTest w₁ (Z^(max 0 N-N)) (leftHeight z) (q₁/Z^(max 0 N)) *
      star (clippedTest w₂ (Z^(max 0 N-N)) (-rightHeight z) (q₂/Z^(max 0 N)))) := by
  rw [second_mode_split,← leftHeight_eq,← rightHeight_eq,hy₁,hy₂]
  have h1 := child_test_clipping w₁ hZ hq₁ N (leftHeight z)
  have h2 := child_test_clipping w₂ hZ hq₂ N (-rightHeight z)
  calc
    _ = secondOuterPhase
        (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
        (childLogTest w₁ (leftHeight z) (q₁/Z^N) *
          star (childLogTest w₂ (-rightHeight z) (q₂/Z^N))) := by
      simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg]
      ring
    _ = _ := by
      rw [h1,h2]
      simp only [clippingPhase,star_mul,SecondPassIntegration.logPhase_conjugate,
        neg_neg,logPhase_add_frequency]
      ring

theorem child_height_moment_bound (K : ℕ) (z : Frequency × (Fin 6 → ℝ)) :
    (1+‖leftHeight z‖)^K * (1+‖rightHeight z‖)^K ≤
      tripleHeight (2*K) z.1 * coordinateHeight (2*K) z.2 := by
  have hh := InverseAmbientProfileTower.inherited_pair_weight_bound 4 5 0 K z
  simpa only [InverseAmbientProfileTower.ambientWeight,
    InverseAmbientProfileTower.inheritedLeft,InverseAmbientProfileTower.inheritedRight,
    leftHeight,rightHeight,norm_neg,pow_zero,Finset.prod_const_one,
    mul_one,one_mul,zero_add,tripleHeight,coordinateHeight] using hh

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ) : ℂ :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

def retainedCutoffs (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![ψ 0,ψ 1,ψ 2,ψ 3,w₁,w₂]

theorem retainedCutoffs_nonzero (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (x : Fin 6 → ℝ) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, retainedCutoffs ψ w₁ w₂ i (x i) ≠ 0 := by
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  intro i
  fin_cases i <;> simp only [retainedCutoffs]
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2
  · exact h₁
  · exact h₂

theorem larger_windows_one (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (Ω : Fin 6 → ℝ → ℂ)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, Ω i (Real.exp (Real.log (x i))) = 1 := by
  intro i
  rw [Real.exp_log (hx i)]
  exact hΩ i (x i) (retainedCutoffs_nonzero ψ w₁ w₂ x ho h₁ h₂ i)

theorem retained_physical_kernel_restore
    (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (ψ : Fin 4 → ℝ → ℂ) (Ω : Fin 6 → ℝ → ℂ)
    (a b A₀ B₀ A₂ B₂ : ℝ) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂)
    (hW₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hψ₀ : ∀ x, ψ 0 x ≠ 0 → x ∈ Set.Icc A₀ B₀)
    (hψ₂ : ∀ x, ψ 2 x ≠ 0 → x ∈ Set.Icc A₂ B₂)
    (hw₁ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₁ x = 1)
    (hw₂ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₂ x = 1)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    let x := InverseInitialProfile.relativeNorm q Z D B v θ H
    outerCutoff ψ x * InverseInitialProfile.physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(InverseInitialProfile.prefactorCenter m D B θ+3*η) : ℝ) *
        outerCutoff ψ x * (w₁ (x 4)*w₂ (x 5)) *
        InverseInitialProfile.normalizedProfile W₁ W₂ Φ (fun i y => Ω i (Real.exp y))
          (Z^(InverseInitialProfile.radialCenter m H θ D B)) (η*Real.log Z)
          (InverseInitialProfile.relativeLog q Z D B v θ H) := by
  dsimp only
  let x := InverseInitialProfile.relativeNorm q Z D B v θ H
  have hx : ∀ i, 0 < x i := InverseInitialProfile.relativeNorm_pos q hq hZ D B v θ H
  by_cases ho : outerCutoff ψ x = 0
  · change outerCutoff ψ x * _ = _ * outerCutoff ψ x * _ * _
    simp only [ho,zero_mul,mul_zero]
  have hc : ψ 0 (x 0) ≠ 0 := ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).1 |> mul_ne_zero_iff.mp).1
  have hs : ψ 2 (x 2) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).2
  have h1 : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1 :=
    fresh_window_eq_one W₁ w₁ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 4)
      hW₁ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 4).le hw₁
  have h2 : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1 :=
    fresh_window_eq_one W₂ w₂ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 5)
      hW₂ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 5).le hw₂
  have hcut : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 →
      ∀ i, Ω i (Real.exp (InverseInitialProfile.relativeLog q Z D B v θ H i)) = 1 := by
    intro hleft hright
    exact larger_windows_one ψ w₁ w₂ Ω hΩ x hx ho hleft hright
  have he := InverseInitialProfile.initial_kernel_restore W₁ W₂ w₁ w₂ Φ
    (fun i y => Ω i (Real.exp y)) hZ D B v m θ H η q hq h1 h2 hcut
  rw [he]
  ring

end SevenEighths.InverseInitialClippedColumns

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy -/

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open JointLogSeparation IdealMobiusDivisorSum InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma child_ball_neg (R : ℝ) (k : Eis) :
    -k ∈ nonzeroChildFrequencyBall 1 R ↔ k ∈ nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,map_neg,norm_neg]

lemma child_ball_sum_neg {β : Type*} [AddCommMonoid β] (R : ℝ) (F : Eis → β) :
    ∑ k ∈ nonzeroChildFrequencyBall 1 R,F (-k) =
      ∑ k ∈ nonzeroChildFrequencyBall 1 R,F k := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    exact (child_ball_neg R k).mpr hk
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,(child_ball_neg R b).mpr hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondLabelWeight (K : ℕ) (f : Ideal Eis) : ℝ := ((idealDivisors f).card : ℝ)^(9+4*K)

theorem second_left_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels rows (secondModeLeft p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K) ω hZ N V _

theorem second_right_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (R : ℝ) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  have he : secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      columnEnergy p hp hcop hg pool (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ)
        slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N) := by
    unfold secondLabelEnergy columnEnergy
    apply Finset.sum_congr rfl
    intro f hf
    simp only [secondLabelWeight,secondModeRight,secondCanonicalPolynomial]
    apply congrArg (fun a : ℝ => ((idealDivisors f).card : ℝ)^(9+4*K)*a)
    exact child_ball_sum_neg (β:=ℝ) R (fun k => ‖finiteCanonicalMarkedRow p hp hcop hg pool
      (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ) (primaryGenerator f) k
      slots lists a (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N)‖^2)
  rw [he]
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R)
    (secondLabelWeight K) ω hZ N V _

omit [DecidableEq σ] in
theorem normalized_child_energy_radical_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical)
      slots lists a labels rows D W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_congr rfl
  intro f hf
  apply congrArg (fun x : ℝ => D f*x)
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteCanonicalMarkedRow_radical_puncture p hp hcop hg pool Ψ m (primaryGenerator f) k slots lists a W X]

end
end SevenEighths.InverseMoment

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialOverlapInputFourier
open InverseMoment InverseInitialOverlapFourier InverseInitialArithmetic InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_integral (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (H : Finset ι→ℝ→ℂ) (hH : ∀A∈F.powerset,Integrable (H A)) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∫t:ℝ,H A t) u =
      ∫t:ℝ,inputConjugateRow p hg F Ψ j 1 1 (fun A=>H A t) u := by
  rw [initial_input_row p hg]
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  have he (A:Finset ι) (t:ℝ) :
      supportMobius (fun i=>Ideal.span {p i}) A*
        (Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*H A t)*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)=
      (supportMobius (fun i=>Ideal.span {p i}) A*Ψ (∏i∈A,p i)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u))*H A t := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA=>(hH A hA).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem original_overlap_input
    (hp : ∀i,p i≠0) (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (hy : ∀i∈slots,∀q∈lists i,0<y i q)
    (wFresh : ℝ→ℂ) (Z D yj : ℝ) (hZ : 0<Z) (hj : 0<yj) :
    ((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
      (fun A=>wFresh (primeProductNorm p A/Z^D)*
        ∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) u =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p
            (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))))
            (childLogTest wFresh t) Z D) u) := by
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset ι→ℝ→ℂ := fun A t=>density g (Real.log yj) t*
    (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))) A*
      childLogTest wFresh t (primeProductNorm p A/Z^D))
  have hH (A:Finset ι) : Integrable (H A) := by
    have hi := (overlap_mode_integrable g slots lists a (fun i q=>Real.log (y i q))
      A (Real.log yj) (Real.log (primeProductNorm p A/Z^D))).const_mul
      (wFresh (primeProductNorm p A/Z^D))
    convert hi using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have he (A:Finset ι) :
      wFresh (primeProductNorm p A/Z^D)*
        (∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) =
      ∫t:ℝ,H A t := by
    rw [actual_overlap_separation W a₀ b₀ ha₀ hs hW slots lists a y hy A yj
      (primeProductNorm p A/Z^D) hj
      (div_pos (primeProductNorm_pos p hp A) (Real.rpow_pos_of_pos hZ D)),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H,childLogTest,g]
    ring
  simp_rw [he]
  rw [input_integral p hg F Ψ j u H (fun A _=>hH A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialOverlapInputFourier

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlapEnergy -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapEnergy
open InverseInitialOverlapFourier InverseMoment

theorem polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density g xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density g xj t*φ k t‖^2)≤C*E := by
  obtain ⟨C,hC,hint⟩ := density_moment g J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro κ inst xj φ E hE hφ hbound
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density g xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density g xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density g xj t‖ := by
    rw [show b t=density g xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h]
      using (hint xj).1
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C := by
    simpa only [hbnorm,h]
      using (hint xj).2
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialMarkedInputEnergy -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialMarkedInputEnergy
open InverseMoment InverseInitialOverlapFourier InverseInitialOverlapEnergy
open InverseInitialRayAttachment InverseInitialArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem marked_input_integrable (g:𝓢(ℝ,ℂ))(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
    (wFresh:ℝ→ℂ)(Z D xj:ℝ) :
    Integrable (fun t:ℝ=>density g xj t*
      (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u)) := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro A hA
  have hh := (overlap_mode_integrable g I L a y A xj
    (Real.log (primeProductNorm p A/Z^D))).const_mul
    (((Z^(-D/2):ℝ):ℂ)*supportMobius (fun i=>Ideal.span {p i}) A*
      Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)*
      wFresh (primeProductNorm p A/Z^D))
  convert hh using 1
  funext t
  unfold initialTest childLogTest
  ring

theorem marked_input_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(rows:Finset Eis)
      (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
      (wFresh:ℝ→ℂ)(Z D xj E:ℝ),0≤E→
      (∀t,(∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑u∈rows,‖∫t:ℝ,density g xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
            (childLogTest wFresh t) Z D) u)‖^2)≤C*E := by
  obtain ⟨C,hC,htransfer⟩ := polynomial_measure_energy g J
  refine ⟨C,hC,?_⟩
  intro F Ψ j rows I L a y wFresh Z D xj E hE henergy
  let ψ : Eis→ℝ→ℂ := fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
    (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
      (childLogTest wFresh t) Z D) u
  let φ : rows→ℝ→ℂ := fun u t=>ψ u.val t
  have hh := htransfer xj φ E hE
    (fun u=>marked_input_integrable p hg g F Ψ j u.val I L a y wFresh Z D xj)
    (fun t=>by
      exact (Finset.sum_coe_sort rows (fun u=>‖ψ u t‖^2)).le.trans (henergy t))
  exact (Finset.sum_coe_sort rows
    (fun u=>‖∫t:ℝ,density g xj t*ψ u t‖^2)).symm.le.trans hh

end SevenEighths.InverseInitialMarkedInputEnergy

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialOverlapHeight -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapHeight
open InverseInitialOverlapFourier InverseMoment JointLogSeparation

theorem twisted_polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(θ:ℝ),∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density (frequencyTwist g θ) xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ k t‖^2)≤C*E*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨C,hC,hboundMoment⟩ := frequencyTwist_fourier_moment J g
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro θ κ inst xj φ E hE hφ hbound
  have hint:=AnalyticBridge.schwartz_fourier_one_plus_integrable (frequencyTwist g θ) J
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density (frequencyTwist g θ) xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density (frequencyTwist g θ) xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density (frequencyTwist g θ) xj t‖ := by
    rw [show b t=density (frequencyTwist g θ) xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h,density_norm]
      using hint
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C*(1+‖θ‖)^(J+(volume:Measure ℝ).integrablePower) := by
    simpa only [hbnorm,h,density_norm]
      using hboundMoment θ
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_pow,←pow_mul,Nat.mul_comm,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapHeight

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure -/

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseInitialPhysicalMeasure
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialRayAttachment
open InverseInitialKernelBridge InverseInitialProfile InverseInitialClippedColumns
open MeasureTheory FourierBridge JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Point (ι : Type*) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  left : Finset ι
  right : Finset ι
  frequency : O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

def divisor (x : Point ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) x.divisor

def quotient (x : Point ι) : O := primaryGenerator (sourceIdeal p (x.common\x.divisor))

def coordinates (x : Point ι) : Fin 6 → ℝ :=
  physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor)
    (sourceIdeal p x.overlap) (sourceIdeal p x.left) (sourceIdeal p x.right) x.frequency

structure Valid (x : Point ι) : Prop where
  divisor_subset : x.divisor⊆x.common
  overlap_left : Disjoint x.overlap x.left
  overlap_right : Disjoint x.overlap x.right
  frequency_nonzero : x.frequency≠0

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem coordinates_pos (x : Point ι) (hx : Valid x) : ∀ i,0<coordinates p x i :=
  physicalCoordinates_pos _ _ _ _ _ _ (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) hx.frequency_nonzero

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem divisor_span (x : Point ι) : Ideal.span {divisor p x}=sourceIdeal p x.divisor := by
  simpa only [divisor,sourceIdeal,FiniteGaussPhase.span_finset_prod] using
    pairDivisor_span (fun i=>Ideal.span {p i}) x.divisor

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem quotient_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) := by
  rw [quotient,sourceIdeal_gen p hp hpr]
  rfl

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem common_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) (hx : Valid x) :
    Ideal.span {divisor p x*quotient p x}=sourceIdeal p x.common := by
  rw [←Ideal.span_singleton_mul_span_singleton,divisor_span p,quotient_span p hp hpr,
    ←sourceIdeal_union p _ _ (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hx.divisor_subset]

include hp in
def unitSector (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) : Oˣ :=
  Classical.choose (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unitSector_spec (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    divisor p x=(unitSector p hp hpr x:O)*primaryGenerator (sourceIdeal p x.divisor) :=
  Classical.choose_spec (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

theorem child_normalized (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι)
    (Ψ : O →* ℂ) (j h : O) (H : Finset ι→ℂ) (N : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (divisor p x*∏ i∈x.overlap,p i) (divisor p x*h) H N =
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h)) H N := by
  obtain ⟨u,hu,he⟩ := initial_poisson_child_normalized p hp hcop hg hpr
    x.common x.divisor x.overlap Ψ j (divisor p x) (quotient p x) h
    (divisor_span p x) (quotient_span p hp hpr x)
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr];exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hu' : u=unitSector p hp hpr x := Units.val_injective
    (mul_right_cancel₀ hgen (hu.symm.trans (unitSector_spec p hp hpr x)))
  simpa only [hu',quotient] using he H N

include hp hcop hg in
theorem column_extraction (hpr : ∀ i,goodLambda^2∣p i-1)
    (x : Point ι) (hx : Valid x) (Ψ : O →* ℂ) (j h : O)
    (σ : Finset ι→ℂ) (N : Finset ι) (hN : Disjoint x.overlap N) :
    initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h
      (fun A=>σ (x.common∪A)) (x.overlap∪N) =
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h (fun _=>1) x.overlap *
      secondChildColumn p hp hcop hg Ψ (j*quotient p x)
        (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
        (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
        (fun A=>σ (x.common∪(x.overlap∪A))) N := by
  have hm (A : Finset ι) :
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*∏ i∈x.common,p i)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*(divisor p x*quotient p x)) :=
    rowCoprimeMask_mul_eq_of_span_eq _ A j (common_span p hp hpr x hx).symm
  have hc (H : Finset ι→ℂ) (A : Finset ι) :
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h H A =
      initialColumn p hp hcop hg Ψ j (divisor p x*quotient p x) (divisor p x) h H A := by
    simp only [initialColumn,hm]
  rw [hc,initial_common_extraction p hp hcop hg hpr Ψ j (quotient p x) (divisor p x) h _ _ _ hN,
    ←hc,child_normalized p hp hcop hg hpr]

def outerCoefficient (Ψ : O →* ℂ) (j : O) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ *
    star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) x.frequency (fun _=>1) x.overlap) *
    initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) (-x.frequency) (fun _=>1) x.overlap

def canonicalColumn (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (x : Point ι) (h : O)
    (H : Finset ι→ℂ) (N : Finset ι) : ℂ :=
  secondChildColumn p hp hcop hg Ψ (j*quotient p x)
    (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
    (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
    (fun A=>σ (x.common∪(x.overlap∪A))*H A) N

def physicalTerm (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>σ (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>σ (x.common∪A)) (x.overlap∪x.right) *
  physicalKernel W₁ W₂ Φ Z D m
    (physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor) 1
      (sourceIdeal p (x.overlap∪x.left)) (sourceIdeal p (x.overlap∪x.right)) x.frequency)

include hp hcop hg in
theorem physicalTerm_extracted (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ =
      outerCoefficient p hp hcop hg Ψ j x ρ *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_left,
    column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_right,
    sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  simp only [canonicalColumn,mul_one,star_mul,outerCoefficient,coordinates]
  ring

def barePair (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j x ρ *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right

def columnRatio (N : Finset ι) (Z D B v : ℝ) : ℝ :=
  (Ideal.absNorm (sourceIdeal p N):ℝ)/Z^(columnCenter D B v)

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_left (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 4=columnRatio p x.left Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem relative_column_right (x : Point ι) (Z D B v θ H : ℝ) :
    relativeNorm (coordinates p x) Z D B v θ H 5=columnRatio p x.right Z D B v := rfl

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem columnRatio_actual (N : Finset ι) (Z D B v : ℝ) :
    columnRatio p N Z D B v=primeProductNorm p N/Z^(columnCenter D B v) := by
  unfold columnRatio sourceIdeal primeProductNorm
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]

def canonicalPairMode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  let height :=  profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  outerCoefficient p hp hcop hg Ψ j x ρ *
    secondOuterPhase height (relativeLog (coordinates p x) Z D B v θ H) *
    star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency
      (fun A=>childLogTest ω₁ (-height 4) (columnRatio p A Z D B v)) x.left) *
    canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency)
      (fun A=>childLogTest ω₂ (height 5) (columnRatio p A Z D B v)) x.right

theorem canonical_pair_mode (hpr : ∀ i,goodLambda^2∣p i-1) (Ψ : O →* ℂ) (j : O)
    (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) (z : Frequency × (Fin 6→ℝ)) :
    barePair p hp hcop hg hpr Ψ j σ x ρ *
      (star (ω₁ (columnRatio p x.left Z D B v))*ω₂ (columnRatio p x.right Z D B v)) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
        (relativeLog (coordinates p x) Z D B v θ H) z.1 z.2 =
      canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z := by
  rw [second_mode_split]
  simp only [canonicalPairMode,barePair,canonicalColumn,secondChildColumn,childLogTest,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,relativeLog,
    relative_column_left,relative_column_right,mul_one]
  ring

theorem family_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ)) (c₁ c₂ θ₁ θ₂ L : ℝ)
    (c : κ→ℂ) (y : κ→Fin 6→ℝ) :
    (∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
      familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2) =
    ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z *
      ∑ k∈s,c k*pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
  simp only [familyDensity,mul_assoc,integral_const_mul]
  have he := full_density_finite_sum s g (𝓕 (clippedTwist g₁ c₁ θ₁))
    (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ secondLeftSlope secondRightSlope secondKernelSlope c y
  calc
    _ = (Real.exp (-3*L):ℂ)*∑ k∈s,c k*∫ z : Frequency × (Fin 6→ℝ),
        fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y k) z.1 z.2 := by
      rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro k hk;ring
    _ = _ := by rw [he]

def physicalBlock (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ

def canonicalBlock (hpr : ∀ i,goodLambda^2∣p i-1)
    (source : Finset (Point ι)) (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (Z D B v θ H : ℝ) (z : Frequency × (Fin 6→ℝ)) : ℂ :=
  ∑ x∈source,∑ ρ : SecondRayIndex,w x*canonicalPairMode p hp hcop hg hpr Ψ j σ ω₁ ω₂ Z D B v θ H x ρ z

theorem physicalBlock_integral
    (hpr : ∀ i,goodLambda^2∣p i-1)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ)
    (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ)
    (hid : PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂)
    (source : Finset (Point ι)) (hs : ∀ x∈source,Valid x)
    (w : Point ι→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hω₁ : ∀ x∈source,clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1)
    (hω₂ : ∀ x∈source,clippedSource W₂ c₂ θ₂
      (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1)
    (hcut : ∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
      ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1) :
    physicalBlock p hp hcop hg source w Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
      ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
        canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z := by
  let S := source ×ˢ (Finset.univ : Finset SecondRayIndex)
  let c := fun a : Point ι × SecondRayIndex => w a.1*barePair p hp hcop hg hpr Ψ j σ a.1 a.2 *
    (star (ω₁ (columnRatio p a.1.left Z D B v))*ω₂ (columnRatio p a.1.right Z D B v))
  let y := fun a : Point ι × SecondRayIndex => relativeLog (coordinates p a.1) Z D B v θ H
  have he := family_density_finite_sum S g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) c y
  have hpnt (x : Point ι) (hx : x∈source) (ρ : SecondRayIndex) :
      w x*physicalTerm p hp hcop hg Ψ j σ (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m x ρ =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*c (x,ρ)*
        ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y (x,ρ)) z.1 z.2 := by
    rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ _ _ Φ Z D m x (hs x hx) ρ]
    rw [hid (fun r=>star (ω₁ r)) ω₂ (coordinates p x) (coordinates_pos p hp x (hs x hx))
      (hω₁ x hx) (hω₂ x hx) (hcut x hx)]
    dsimp only [c,y,barePair]
    rw [relative_column_left,relative_column_right]
    ring
  have hsumeq : physicalBlock p hp hcop hg source w Ψ j σ
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
      (Z^(prefactorCenter m D B θ+3*η):ℝ)*
        ∑ a∈S,c a*∫ z : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope (y a) z.1 z.2 := by
    simp only [physicalBlock,S,Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hpnt x hx ρ]
    ring
  rw [hsumeq,he]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  simp only [S,Finset.sum_product,canonicalBlock,c,y]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mul_assoc (w x),mul_assoc (w x),canonical_pair_mode]

theorem original_ray_common_insertion
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F G E : Finset ι) (h : O) (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    (∑ U∈F.powerset,∑ T∈F.powerset,if Disjoint U T then
      initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0) =
    ∑ V∈F.powerset,∑ N₁∈(F\V).powerset,∑ N₂∈(F\V).powerset,
      ∑ ρ : SecondRayIndex,physicalTerm p hp hcop hg Ψ j σ (fun x=>star (W x)) W Φ Z D m
        ⟨G,E,V,N₁,N₂,h⟩ ρ := by
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [←prime_product_moebius (fun i=>Ideal.span {p i})
    (fun i=>Ideal.prime_of_isPrime (NeZero.ne _) inferInstance) hinj V]
  simp only [Finset.mul_sum,initialPhysicalMode,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro N₁ hN₁
  apply Finset.sum_congr rfl
  intro N₂ hN₂
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [physicalTerm,divisor,supportMobius]
  ring

theorem physicalBlock_zero (source : Finset (Point ι)) (w : Point ι→ℂ)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (hw : ∀ x∈source,w x=0) : physicalBlock p hp hcop hg source w Ψ j σ W₁ W₂ Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  simp only [hw x hx,zero_mul,Finset.sum_const_zero]

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem child_test_clipping (w₀ : ℝ→ℂ) {Z : ℝ} (hZ : 0<Z)
    (N t : ℝ) (A : Finset ι) :
    childLogTest w₀ t ((Ideal.absNorm (sourceIdeal p A):ℝ)/Z^N) =
      logPhase t ((max 0 N-N)*Real.log Z) *
        clippedTest w₀ (Z^(max 0 N-N)) t
          ((Ideal.absNorm (sourceIdeal p A):ℝ)/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,Real.log_rpow hZ,mul_comm] using
    clipped_column_source_identity w₀ hZ
      (QuadraticMainBoundary.norm_pos (sourceIdeal_ne_zero p hp A)) N t

def BlockSupport (source : Finset (Point ι)) (W₁ W₂ ω₁ ω₂ : ℝ→ℂ)
    (V : Fin 6→ℝ→ℂ) (Z D B v θ H c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  (∀ x∈source,clippedSource W₁ c₁ θ₁
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 4)≠0 → star (ω₁ (columnRatio p x.left Z D B v))=1) ∧
  (∀ x∈source,clippedSource W₂ c₂ θ₂
    (relativeNorm (coordinates p x) Z D B v θ H 0 * relativeNorm (coordinates p x) Z D B v θ H 2 *
      relativeNorm (coordinates p x) Z D B v θ H 5)≠0 → ω₂ (columnRatio p x.right Z D B v)=1) ∧
  (∀ x∈source,star (ω₁ (columnRatio p x.left Z D B v))≠0 →
    ω₂ (columnRatio p x.right Z D B v)≠0 → ∀ i,V i (relativeLog (coordinates p x) Z D B v θ H i)=1)

theorem actual_initial_block_common_measure
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6→ℝ→ℂ) (M : Fin 6→ℝ)
    (hV : ∀ i,ContDiff ℝ ∞ (V i)) (hS : ∀ i,HasCompactSupport (V i))
    (hM : ∀ i,0≤M i) (hbox : ∀ i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ,0≤C ∧ ∀ Z D B v m θ H η : ℝ,0<Z → 0≤η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ,ℂ),∀ c₁ c₂ θ₁ θ₂ : ℝ,0<c₁ → 0<c₂ →
      (∀ {κ : Type*} [DecidableEq κ] (p : κ→O) (hp : ∀ i,p i≠0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg : ∀ i,goodLambda∉Ideal.span {p i}) (hpr : ∀ i,goodLambda^2∣p i-1)
        (source : Finset (Point κ)) (_hs : ∀ x∈source,Valid x)
        (w : Point κ→ℂ) (Ψ : O →* ℂ) (j : O) (σ : Finset κ→ℂ) (ω₁ ω₂ : ℝ→ℂ),
        BlockSupport p source W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂ →
        physicalBlock p hp hcop hg source w Ψ j σ
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m =
          (Z^(prefactorCenter m D B θ+3*η):ℝ)*
            ∫ z : Frequency × (Fin 6→ℝ),familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z *
              canonicalBlock p hp hcop hg hpr source w Ψ j σ ω₁ ω₂ Z D B v θ H z) ∧
      Integrable (fun z : Frequency × (Fin 6→ℝ)=>tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖) ∧
      (1+Z^(radialCenter m H θ D B))^A *
        (∫ z : Frequency × (Fin 6→ℝ),tripleHeight J z.1*coordinateHeight J z.2*
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖) ≤
        C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*(1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
  dsimp only
  obtain ⟨C,hC,hfamily⟩ := initial_physical_family_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨C,hC,?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃,hb₃⟩ := hfamily Z D B v m θ H η hZ hL
  refine ⟨b₃,?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨hid,hi,hb⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  refine ⟨?_,hi,hb⟩
  intro κ _ p hp _ hcop hg hpr source hs w Ψ j σ ω₁ ω₂ hsupport
  exact physicalBlock_integral p hp hcop hg hpr W₁ W₂ Φ V _ _ _ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid source hs w Ψ j σ ω₁ ω₂
    hsupport.1 hsupport.2.1 hsupport.2.2

open InverseInitialOverlap InverseInitialPoissonBridge CanonicalQuadraticSieve

def overlapDilation (P j : Ideal O) (Z z G : ℝ) : ℝ :=
  ((Ideal.absNorm j:ℝ)/Z^G)/((Ideal.absNorm (residual P j):ℝ)/Z^(z-G))

theorem residualWindow_eq_clipped (P j : Ideal O) (W : ℝ→ℂ) (Z z G : ℝ) :
    residualOverlapWindow P j W Z z G=clippedSource W (overlapDilation P j Z z G) 0 := by
  funext x
  simp only [residualOverlapWindow,clippedSource,logPhase,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul,overlapDilation]
  congr 1
  ring

theorem overlapDilation_pos {P j : Ideal O} (hP : Admissible P) (hj : j∣P)
    {Z : ℝ} (hZ : 0<Z) (z G : ℝ) : 0<overlapDilation P j Z z G := by
  exact div_pos (div_pos (QuadraticMainBoundary.norm_pos (admissible_of_dvd hP hj).2.1.ne_zero)
      (Real.rpow_pos_of_pos hZ _))
    (div_pos (QuadraticMainBoundary.norm_pos (residual_squarefree hP.2.1 hj).ne_zero)
      (Real.rpow_pos_of_pos hZ _))

theorem clippedSource_zero_star (W : ℝ→ℂ) (c : ℝ) :
    (fun x=>star (clippedSource W c 0 x))=clippedSource (fun x=>star (W x)) c 0 := by
  funext x
  simp [clippedSource,logPhase]

def originalBlock (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z r z G m : ℝ) (source : Finset (Point (primePool (columns S P j))))
    (w : Point (primePool (columns S P j))→ℂ) : ℂ :=
  let F := columns S P j
  let hF : ∀ I∈F,Admissible I := fun I hI=>columns_admissible S hP hj hS hI
  letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  physicalBlock (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) source w (elementCharacter η) (primaryGenerator j)
    (reconstructedSelector S P j a) (fun x=>star (residualOverlapWindow P j W Z z G x))
    (residualOverlapWindow P j W Z z G) Φ Z (r+z-2*G) m

theorem originalBlock_integral
    (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Admissible P) (hj : j∣P) (hS : ∀ n∈S,Squarefree n → Supported n)
    (η : Ideal O →* ℂ) (a : Ideal O→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6→ℝ→ℂ) (g : Fin 6→𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (Z r z G B v m θ H ε : ℝ)
    (hid : PhysicalIdentityAt (fun x=>star (W x)) W Φ V g g₁ g₂ b₃
      Z (r+z-2*G) B v m θ H ε (overlapDilation P j Z z G) (overlapDilation P j Z z G) 0 0)
    (source : Finset (Point (primePool (columns S P j)))) (hs : ∀ x∈source,Valid x)
    (w : Point (primePool (columns S P j))→ℂ) (ω₁ ω₂ : ℝ→ℂ)
    (hcut : BlockSupport (poolPrimary (columns S P j)) source (fun x=>star (W x)) W ω₁ ω₂ V
      Z (r+z-2*G) B v θ H (overlapDilation P j Z z G) (overlapDilation P j Z z G) 0 0) :
    let F := columns S P j
    let hF : ∀ I∈F,Admissible I := fun I hI=>columns_admissible S hP hj hS hI
    letI : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    originalBlock S hP hj hS η a W Φ Z r z G m source w =
      (Z^(prefactorCenter m (r+z-2*G) B θ+3*ε):ℝ)*
        ∫ q : Frequency × (Fin 6→ℝ),
          familyDensity g g₁ g₂ b₃ (overlapDilation P j Z z G) (overlapDilation P j Z z G)
            0 0 (ε*Real.log Z) q *
          canonicalBlock (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
            (poolPrimary_good F hF) (poolPrimary_primary F hF) source w (elementCharacter η)
            (primaryGenerator j) (reconstructedSelector S P j a) ω₁ ω₂ Z (r+z-2*G) B v θ H q := by
  intro F hF
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  unfold originalBlock
  rw [residualWindow_eq_clipped,clippedSource_zero_star]
  exact physicalBlock_integral (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (poolPrimary_primary F hF) _ _ Φ V g g₁ g₂ b₃
    Z (r+z-2*G) B v m θ H ε _ _ 0 0 hid source hs w (elementCharacter η)
    (primaryGenerator j) (reconstructedSelector S P j a) ω₁ ω₂ hcut.1 hcut.2.1 hcut.2.2

end SevenEighths.InverseInitialPhysicalMeasure

end

end OAI

end

/-! ## OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights -/

section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPhysicalMeasure
namespace SevenEighths.InverseInitialEnergyCallerWeights
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem initialColumn_norm_le
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (Ψ : Eis →* ℂ) (j C d h : Eis) (V : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V‖ ≤ ‖Ψ (∏ i∈V,p i)‖ := by
  rw [initialColumn_eq_secondPre]
  exact secondPreColumn_norm_le p hp hcop hg hc Ψ (j*C) 1 1 d h V

omit hp hcop hg in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem initialBeta_norm_le_one (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖≤1)
    (j : Eis) (G : Finset ι) : ‖initialBeta p Ψ j G‖≤1 := by
  have hm : ‖rowCoprimeMask (fun i=>Ideal.span {p i}) G j‖≤1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  have h := (mul_le_of_le_one_left (norm_nonneg _) (hΨ (∏ i∈G,p i))).trans hm
  simp only [initialBeta,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _),norm_mul]
  nlinarith [mul_nonneg (norm_nonneg (Ψ (∏ i∈G,p i)))
    (norm_nonneg (rowCoprimeMask (fun i=>Ideal.span {p i}) G j))]

theorem outerCoefficient_norm_le
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖≤1)
    (j : Eis) (x : Point ι) (ρ : SecondRayIndex) :
    ‖outerCoefficient p hp hcop hg Ψ j x ρ‖ ≤ ‖secondRayCoefficient ρ‖ := by
  have hβ := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hV : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  have hL := (initialColumn_norm_le p hp hcop hg hc (secondRayMinus Ψ ρ)
    j (∏ i∈x.common,p i) (divisor p x) x.frequency x.overlap).trans
      ((secondRayMinus_norm_le Ψ ρ _).trans (hΨ _))
  have hR := (initialColumn_norm_le p hp hcop hg hc (secondRayPlus Ψ ρ)
    j (∏ i∈x.common,p i) (divisor p x) (-x.frequency) x.overlap).trans
      ((secondRayPlus_norm_le Ψ ρ _).trans (hΨ _))
  simp only [outerCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*1*1 := by
      gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialEnergyCallerWeights

end

end OAI

end

