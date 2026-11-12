module

public import Green64.Library.Weights.Part089

@[expose] public section

/-!
# Weights / UnfilteredEvolutionGhostFullColumn

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEvolutionGhostFullColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 300000
private theorem sum_fintype (A : Type) (i j : Fintype A) (f : A → ℝ) :
    @Finset.sum A ℝ _ (@Finset.univ A i) f =
      @Finset.sum A ℝ _ (@Finset.univ A j) f := by
  have h : i=j := Subsingleton.elim _ _
  cases h
  rfl

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- The true density column bound for the COMPLETE original physical G
positive witness kernel, with every birth weighted by 2. No reachability,
Nodup OLD inventory, V^OLD correction, or changed density is used. -/
theorem source_original_evolution_PHYSICAL_G_gamma_column434
    (q rho W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (V : BG → ℝ) (hV : ∀ g,0 ≤ V g) (hVW : ∀ g,V g ≤ W)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (hmass : ∀ g,∑ p,mu g p ≤ 2)
    (Y : FullPhysicalOutput SP sm BP bm M) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    (∑ x : FullPhysicalState SP sm BP bm M cap,
      ∑ y : FullPhysicalState SP sm BP bm M cap,
        (fullPhysicalMass SP sm BP bm M cap Vs mu x*w^(∑ g,((x.2 g).2).1.val))*
          (∑ c : FullGhostWitness SP sm BP bm M cap x,
            (2:ℝ)^(∑ g,(c g).2.1.val)*
              ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖)*
          (if physicalFockProjection SP sm BP bm M cap y=Y then 1 else 0)) ≤
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*
        physicalOrbitMass SP sm BP bm M cap Vs mu Y*w^(∑ g,((Y.2 g).2).card) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  change (∑ x : FullPhysicalState SP sm BP bm M cap,
      ∑ y : FullPhysicalState SP sm BP bm M cap,
        (fullPhysicalMass SP sm BP bm M cap Vs mu x*w^(∑ g,((x.2 g).2).1.val))*
          (∑ c : FullGhostWitness SP sm BP bm M cap x,
            (2:ℝ)^(∑ g,(c g).2.1.val)*
              ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖)*
          (if physicalFockProjection SP sm BP bm M cap y=Y then 1 else 0)) ≤
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*
        physicalOrbitMass SP sm BP bm M cap Vs mu Y*w^(∑ g,((Y.2 g).2).card)
  let d := Green64SmallHaar.groupStateMass SP sm M Vs
  let mass := fun g (x : BigState (bm g) M (cap g)) =>
    bigStateMass (bm g) M (cap g) (mu g) x*w^x.2.1.val
  let K := fun g => sourceOriginalUnfilteredEvolutionGhostBigPositive434
    (bm g) M (cap g) q rho (V g) N i (mu g)
  let proj := fun g (x : BigState (bm g) M (cap g)) => (x.1,fockMultiset x.2)
  have hw := source_original_evolution_weight_controls434 q rho W hr hW hg
  have hd : 0 ≤ d := by
    unfold d Green64SmallHaar.groupStateMass
    exact Finset.prod_nonneg (fun g _ =>
      (Green64SmallHaar.stateMass_positive (sm g) M (Vs g) (hVs g)).le)
  have hm (g : BG) (x : BigState (bm g) M (cap g)) : 0 ≤ mass g x :=
    mul_nonneg (bigStateMass_positive (bm g) M (cap g) (mu g) (hmu g) x).le
      (pow_nonneg hw.1.le _)
  have hk (g : BG) (x y : BigState (bm g) M (cap g)) : 0 ≤ K g x y := by
    dsimp only [K,sourceOriginalUnfilteredEvolutionGhostBigPositive434]
    split_ifs
    · exact Finset.sum_nonneg (fun c _ => norm_nonneg _)
    · exact le_rfl
  have hc (g : BG) :
      (∑ x : BigState (bm g) M (cap g),∑ y : BigState (bm g) M (cap g),
        mass g x*K g x y*(if proj g y=Y.2 g then 1 else 0)) ≤
      Real.exp (4*W*w/rho)*
        (∑ y : BigState (bm g) M (cap g),mass g y*(if proj g y=Y.2 g then 1 else 0)) :=
    source_original_evolution_SOURCE_BIG_GHOST_column434 (bm g) M (cap g)
      q rho (V g) W N i hq hq1 hr (hV g) (hVW g) hW hg
      (mu g) (fun p => (hmu g p).le) (hmass g) (Y.2 g)
  have hh := source_original_evolution_tensor_column_bound434
    proj mass K d hd hm hk (fun _ : BG => Real.exp (4*W*w/rho)) Y.1 Y.2 hc
  have hmass' (x : FullPhysicalState SP sm BP bm M cap) :
      fullPhysicalMass SP sm BP bm M cap Vs mu x*w^(∑ g,((x.2 g).2).1.val) =
      d*∏ g,mass g (x.2 g) := by
    dsimp only [d,mass,fullPhysicalMass,bigGroupStateMass]
    rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
    ring
  have hproj (y : FullPhysicalState SP sm BP bm M cap) :
      physicalFockProjection SP sm BP bm M cap y=Y ↔
      y.1=Y.1 ∧ ∀ g,proj g (y.2 g)=Y.2 g := by
    constructor
    · intro he
      exact ⟨congrArg Prod.fst he,fun g => congrFun (congrArg Prod.snd he) g⟩
    · rintro ⟨hs,hb⟩
      exact Prod.ext hs (funext hb)
  have hexp (n : ℕ) : Real.exp (4*W*w/rho)^n =
      Real.exp ((4*W*w/rho)*(n:ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,ih,←Real.exp_add]
      congr 1
      push_cast
      ring
  have hprod : (∏ _g : BG,Real.exp (4*W*w/rho)) =
      Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho) := by
    rw [Finset.prod_const,Finset.card_univ,hexp]
    congr 1
    ring
  rw [hprod] at hh
  change _ ≤ Real.exp (4*W*w*(Fintype.card BG:ℝ)/rho)*
    physicalOrbitMass SP sm BP bm M cap Vs mu Y*w^(∑ g,((Y.2 g).2).card)
  rw [mul_assoc,←source_original_evolution_PHYSICAL_weighted_fibre434 SP sm BP bm M cap Vs mu w Y]
  simp_rw [source_original_evolution_PHYSICAL_G_positive_kernel434 SP sm BP bm M cap q rho N i V mu,hmass',hproj]
  let oldInst : Fintype (FullPhysicalState SP sm BP bm M cap) := inferInstance
  let prodInst : Fintype (FullPhysicalState SP sm BP bm M cap) :=
    @instFintypeProd (Green64SmallHaar.GroupState SP sm M)
      ((g : BG) → BigState (bm g) M (cap g)) inferInstance
      (@Pi.instFintype BG (fun g => BigState (bm g) M (cap g))
        (Classical.decEq BG) inferInstance inferInstance)
  have hs (f : FullPhysicalState SP sm BP bm M cap → ℝ) :
      @Finset.sum (FullPhysicalState SP sm BP bm M cap) ℝ _
        (@Finset.univ (FullPhysicalState SP sm BP bm M cap) oldInst) f =
      @Finset.sum (FullPhysicalState SP sm BP bm M cap) ℝ _
        (@Finset.univ (FullPhysicalState SP sm BP bm M cap) prodInst) f :=
    sum_fintype _ oldInst prodInst f
  rw [hs]
  conv_lhs => arg 2; ext x; rw [hs]
  conv_rhs => arg 2; rw [hs]
  dsimp only [K] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

