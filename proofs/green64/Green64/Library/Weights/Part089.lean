module

public import Green64.Library.Weights.UnfilteredEvolutionGhostKernel
public import Green64.Library.Weights.Part087

@[expose] public section

/-!
# Weights / Part089

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalUnfilteredEvolutionGhostSourceColumn -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

/-- Actual source one-group G column, including a factor 2 per birth,
in the original prime/residue factorial measure. All repeated atoms remain. -/
theorem source_original_evolution_SOURCE_GHOST_doubled_column434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (B : ℕ)
    (q rho V W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hV : 0 ≤ V) (hVW : V ≤ W) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (hmass : ∑ p,mu p ≤ 2)
    (H : Multiset (Atom P modulus) → ℝ) (hH : ∀ m,0 ≤ H m) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    (∑ x : FockState (Atom P modulus) B,fockMass (sourceAtomMu mu) x*w^x.1.val*
      ∑ y : FockState (Atom P modulus) B,
        sourceOriginalUnfilteredEvolutionGhostPositive434 B (fun z => z.2=0)
          (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
          (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
          (2*(-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(rho:ℂ)))
          (sourceBirthNu (fun p => (mu p:ℂ))) x y * H (fockMultiset y)) ≤
    Real.exp (4*W*w/rho)*
      (∑ y : FockState (Atom P modulus) B,
        fockMass (sourceAtomMu mu) y*H (fockMultiset y)*w^y.1.val) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  change _ ≤ Real.exp (4*W*w/rho)*_
  have hwc := source_original_evolution_weight_controls434 q rho W hr hW hg
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hqi := source_original_evolution_visit_q_bounds434 q hq hq1 N i
  let eta := sourceVisitEta q N i
  let qi := sourceVisitQ q N i
  have hnA : ‖-((eta:ℝ):ℂ)/(rho:ℂ)‖=eta/rho := by
    simp [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he.1,abs_of_pos hr,eta]
  have hnX : ‖((qi:ℝ):ℂ)/(rho:ℂ)^2‖=qi/rho^2 := by
    simp [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hqi.1,abs_of_pos hr,qi]
  have hnC : ‖2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))‖=2*eta*V/rho := by
    simp [norm_div,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg he.1,abs_of_nonneg hV,abs_of_pos hr,eta]
    ring
  have hC : 2*eta*V/rho ≤ 2*W/rho := by
    apply div_le_div_of_nonneg_right _ hr.le
    have hh := mul_le_mul_of_nonneg_right he.2 hV
    nlinarith only [hh,hVW]
  have hc : ‖2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))‖/w+
      ‖((qi:ℝ):ℂ)/(rho:ℂ)^2‖ ≤ 1 := by
    rw [hnC,hnX]
    exact (add_le_add (div_le_div_of_nonneg_right hC hwc.1.le)
      (div_le_div_of_nonneg_right hqi.2 (sq_nonneg rho))).trans hwc.2.2.2
  have hh := source_original_evolution_GHOST_kernel_column434 B
    (fun z : Atom P modulus => z.2=0) (sourceAtomMu mu)
    (fun z => hmu z.1) (-((eta:ℝ):ℂ)/(rho:ℂ))
    (((qi:ℝ):ℂ)/(rho:ℂ)^2)
    (2*(-((eta:ℝ):ℂ)*(V:ℂ)/(rho:ℂ))) w hwc.1 hc H hH
  have hnu : (fun z : Atom P modulus => ((if z.2=0 then sourceAtomMu mu z else 0:ℝ):ℂ)) =
      sourceBirthNu (fun p => (mu p:ℂ)) := by
    funext z
    by_cases hz : z.2=0 <;> simp [sourceBirthNu,birthMass,sourceAtomMu,lambdaMass,hz]
  have hmass0 : (∑ z : Atom P modulus,if z.2=0 then sourceAtomMu mu z else 0)=∑ p,mu p := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro p _
    change (∑ r : ZMod (modulus p),if r=0 then mu p else 0)=mu p
    rw [Finset.sum_ite_eq']
    simp
  rw [hnu,hnA,hmass0] at hh
  have hm : 0 ≤ ∑ p,mu p := Finset.sum_nonneg (fun p _ => hmu p)
  have hexp : eta/rho*w*(∑ p,mu p) ≤ 4*W*w/rho := by
    have h1 := div_le_div_of_nonneg_right he.2 hr.le
    have h2 := mul_le_mul h1 hmass hm (by positivity : 0 ≤ 1/rho)
    have h3 := mul_le_mul_of_nonneg_left h2 hwc.1.le
    have h4 : 2*w/rho ≤ 4*W*w/rho := by
      apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [hwc.1]
    have h5 : eta/rho*w*(∑ p,mu p) ≤ 2*w/rho := by
      convert h3 using 1 <;> ring
    exact h5.trans h4
  apply hh.trans
  apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (mul_nonneg
    (div_nonneg (Finset.prod_nonneg (fun j _ => hmu (y.2 j).1)) (Nat.cast_nonneg _))
    (hH _)) (pow_nonneg hwc.1.le _)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostTensor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem source_original_evolution_tensor_pair_sum434
    {G : Type} [Fintype G] {A : G → Type} [∀ g,Fintype (A g)]
    (f : (g : G) → A g → A g → ℝ) :
    (∑ x : (g : G) → A g,∑ y : (g : G) → A g,∏ g,f g (x g) (y g)) =
    ∏ g,∑ x : A g,∑ y : A g,f g x y := by
  have hy (x : (g : G) → A g) :
      (∑ y : (g : G) → A g,∏ g,f g (x g) (y g)) =
      ∏ g,∑ y : A g,f g (x g) y :=
    (Fintype.prod_sum (fun g y => f g (x g) y)).symm
  simp_rw [hy]
  exact (Fintype.prod_sum (fun g x => ∑ y : A g,f g x y)).symm

theorem source_original_evolution_guarded_prod434
    {G : Type} [Fintype G] (p : G → Prop) [DecidablePred p] (f : G → ℝ) :
    (if ∀ g,p g then ∏ g,f g else 0) = ∏ g,if p g then f g else 0 := by
  by_cases h : ∀ g,p g
  · simp [h]
  · rw [if_neg h]
    obtain ⟨g,hg⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ g) (if_neg hg)

/-- Exact tensor column factorization with the original fixed SMALL
coordinate and independent per-group physical orbit projections. -/
theorem source_original_evolution_tensor_column_factor434
    {S G : Type} [Fintype S] [DecidableEq S] [Fintype G]
    {A : G → Type} [∀ g,Fintype (A g)]
    {O : G → Type} [∀ g,DecidableEq (O g)]
    (proj : (g : G) → A g → O g) (mass : (g : G) → A g → ℝ)
    (K : (g : G) → A g → A g → ℝ) (d : ℝ)
    (Ys : S) (Y : (g : G) → O g) :
    (∑ x : S × ((g : G) → A g),∑ y : S × ((g : G) → A g),
      d*(∏ g,mass g (x.2 g))*
        (if x.1=y.1 then ∏ g,K g (x.2 g) (y.2 g) else 0)*
        (if y.1=Ys ∧ ∀ g,proj g (y.2 g)=Y g then 1 else 0)) =
    d*∏ g,∑ x : A g,∑ y : A g,
      mass g x*K g x y*(if proj g y=Y g then 1 else 0) := by
  have hp (x y : (g : G) → A g) :
      (∏ g,mass g (x g))*(∏ g,K g (x g) (y g))*
        (if ∀ g,proj g (y g)=Y g then 1 else 0) =
      ∏ g,mass g (x g)*K g (x g) (y g)*
        (if proj g (y g)=Y g then 1 else 0) := by
    rw [←Finset.prod_mul_distrib]
    by_cases h : ∀ g,proj g (y g)=Y g
    · simp [h]
    · rw [if_neg h,mul_zero]
      obtain ⟨g,hg⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ g) (by simp [hg])
  have hs (x y : (g : G) → A g) :
      (∑ xs : S,∑ ys : S,
        d*(∏ g,mass g (x g))*
          (if xs=ys then ∏ g,K g (x g) (y g) else 0)*
          (if ys=Ys ∧ ∀ g,proj g (y g)=Y g then 1 else 0)) =
      d*∏ g,mass g (x g)*K g (x g) (y g)*
        (if proj g (y g)=Y g then 1 else 0) := by
    calc
      _ = d*((∏ g,mass g (x g))*(∏ g,K g (x g) (y g))*
          (if ∀ g,proj g (y g)=Y g then 1 else 0)) := by
        by_cases h : ∀ g,proj g (y g)=Y g <;>
          simp [h,mul_ite,ite_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',mul_assoc]
      _ = _ := congrArg (d*·) (hp x y)
  simp only [Fintype.sum_prod_type,Prod.fst,Prod.snd]
  rw [Finset.sum_comm]
  have he (x : (g : G) → A g) :
      (∑ xs : S,∑ ys : S,∑ y : (g : G) → A g,
        d*(∏ g,mass g (x g))*
          (if xs=ys then ∏ g,K g (x g) (y g) else 0)*
          (if ys=Ys ∧ ∀ g,proj g (y g)=Y g then 1 else 0)) =
      ∑ y : (g : G) → A g,d*∏ g,mass g (x g)*K g (x g) (y g)*
        (if proj g (y g)=Y g then 1 else 0) := by
    conv_lhs => arg 2; ext xs; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp_rw [hs]
  simp_rw [he,←Finset.mul_sum]
  rw [source_original_evolution_tensor_pair_sum434
    (fun g x y => mass g x*K g x y*(if proj g y=Y g then 1 else 0))]

/-- Exact target fibre mass for the full product projection. -/
theorem source_original_evolution_tensor_target_factor434
    {S G : Type} [Fintype S] [DecidableEq S] [Fintype G]
    {A : G → Type} [∀ g,Fintype (A g)]
    {O : G → Type} [∀ g,DecidableEq (O g)]
    (proj : (g : G) → A g → O g) (mass : (g : G) → A g → ℝ)
    (d : ℝ) (Ys : S) (Y : (g : G) → O g) :
    (∑ y : S × ((g : G) → A g),
      d*(∏ g,mass g (y.2 g))*
        (if y.1=Ys ∧ ∀ g,proj g (y.2 g)=Y g then 1 else 0)) =
    d*∏ g,∑ y : A g,mass g y*(if proj g y=Y g then 1 else 0) := by
  have hp (y : (g : G) → A g) :
      (∏ g,mass g (y g))*(if ∀ g,proj g (y g)=Y g then 1 else 0) =
      ∏ g,mass g (y g)*(if proj g (y g)=Y g then 1 else 0) := by
    simp only [mul_ite,mul_one,mul_zero]
    exact source_original_evolution_guarded_prod434 _ _
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hs (y : (g : G) → A g) :
      (∑ ys : S,d*(∏ g,mass g (y g))*
        (if ys=Ys ∧ ∀ g,proj g (y g)=Y g then 1 else 0)) =
      d*∏ g,mass g (y g)*(if proj g (y g)=Y g then 1 else 0) := by
    rw [←hp]
    by_cases h : ∀ g,proj g (y g)=Y g
    · simp [h,mul_ite,Finset.sum_ite_eq',mul_assoc]
    · simp [h]
  simp_rw [hs]
  rw [←Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum
    (fun g y => mass g y*(if proj g y=Y g then 1 else 0))).symm

/-- Tensorization of derived genuine density columns; applied below only
after the one-group column has been proved from the literal ghost terms. -/
theorem source_original_evolution_tensor_column_bound434
    {S G : Type} [Fintype S] [DecidableEq S] [Fintype G]
    {A : G → Type} [∀ g,Fintype (A g)]
    {O : G → Type} [∀ g,DecidableEq (O g)]
    (proj : (g : G) → A g → O g) (mass : (g : G) → A g → ℝ)
    (K : (g : G) → A g → A g → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hmass : ∀ g x,0 ≤ mass g x) (hK : ∀ g x y,0 ≤ K g x y)
    (C : G → ℝ) (Ys : S) (Y : (g : G) → O g)
    (hc : ∀ g,(∑ x : A g,∑ y : A g,
        mass g x*K g x y*(if proj g y=Y g then 1 else 0)) ≤
      C g*(∑ y : A g,mass g y*(if proj g y=Y g then 1 else 0))) :
    (∑ x : S × ((g : G) → A g),∑ y : S × ((g : G) → A g),
      d*(∏ g,mass g (x.2 g))*
        (if x.1=y.1 then ∏ g,K g (x.2 g) (y.2 g) else 0)*
        (if y.1=Ys ∧ ∀ g,proj g (y.2 g)=Y g then 1 else 0)) ≤
    (∏ g,C g)*
      (∑ y : S × ((g : G) → A g),d*(∏ g,mass g (y.2 g))*
        (if y.1=Ys ∧ ∀ g,proj g (y.2 g)=Y g then 1 else 0)) := by
  rw [source_original_evolution_tensor_column_factor434,
    source_original_evolution_tensor_target_factor434]
  calc
    _ ≤ d*∏ g,C g*(∑ y : A g,mass g y*(if proj g y=Y g then 1 else 0)) := by
      apply mul_le_mul_of_nonneg_left _ hd
      apply Finset.prod_le_prod₀
      · intro g _
        apply Finset.sum_nonneg
        intro x _
        apply Finset.sum_nonneg
        intro y _
        exact mul_nonneg (mul_nonneg (hmass g x) (hK g x y))
          (by split_ifs <;> norm_num)
      · intro g _
        exact hc g
    _ = _ := by rw [Finset.prod_mul_distrib];ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostActive -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem source_original_evolution_fixed_column_factor434
    {S A O : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq O]
    (proj : A → O) (smass : S → ℝ) (mass : A → ℝ) (K : A → A → ℝ)
    (Ys : S) (Y : O) :
    (∑ x : S × A,∑ y : S × A,
      (smass x.1*mass x.2)*
        (if x.1=y.1 then K x.2 y.2 else 0)*
        (if y.1=Ys ∧ proj y.2=Y then 1 else 0)) =
    smass Ys*(∑ x : A,∑ y : A,mass x*K x y*(if proj y=Y then 1 else 0)) := by
  have hs (x y : A) :
      (∑ xs : S,∑ ys : S,
        (smass xs*mass x)*(if xs=ys then K x y else 0)*
          (if ys=Ys ∧ proj y=Y then 1 else 0)) =
      smass Ys*(mass x*K x y*(if proj y=Y then 1 else 0)) := by
    by_cases h : proj y=Y <;>
      simp [h,mul_ite,ite_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',mul_assoc]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have he (x : A) :
      (∑ xs : S,∑ ys : S,∑ y : A,
        (smass xs*mass x)*(if xs=ys then K x y else 0)*
          (if ys=Ys ∧ proj y=Y then 1 else 0)) =
      ∑ y : A,smass Ys*(mass x*K x y*(if proj y=Y then 1 else 0)) := by
    conv_lhs => arg 2; ext xs; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp_rw [hs]
  simp_rw [he,←Finset.mul_sum]

theorem source_original_evolution_fixed_target_factor434
    {S A O : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq O]
    (proj : A → O) (smass : S → ℝ) (mass : A → ℝ) (Ys : S) (Y : O) :
    (∑ y : S × A,(smass y.1*mass y.2)*
        (if y.1=Ys ∧ proj y.2=Y then 1 else 0)) =
    smass Ys*(∑ y : A,mass y*(if proj y=Y then 1 else 0)) := by
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : proj y=Y <;>
    simp [h,mul_ite,Finset.sum_ite_eq',mul_assoc]

/-- The actual source ghost column extends to its unchanged active slots,
with exactly their original mu^M mass. No extra V^OLD is introduced. -/
theorem source_original_evolution_SOURCE_BIG_GHOST_column434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (q rho V W : ℝ) (N i : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 < rho)
    (hV : 0 ≤ V) (hVW : V ≤ W) (hW : 1 ≤ W)
    (hg : Real.sqrt q/rho^2 < 1)
    (mu : P → ℝ) (hmu : ∀ p,0 ≤ mu p) (hmass : ∑ p,mu p ≤ 2)
    (Y : (Fin M → P) × Multiset (Atom P modulus)) :
    let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
    let K := fun x y : BigState modulus M B =>
      if x.1=y.1 then
        sourceOriginalUnfilteredEvolutionGhostPositive434 B (fun z => z.2=0)
          (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
          (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
          (2*(-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(rho:ℂ)))
          (sourceBirthNu (fun p => (mu p:ℂ))) x.2 y.2
      else 0
    (∑ x : BigState modulus M B,∑ y : BigState modulus M B,
      (bigStateMass modulus M B mu x*w^x.2.1.val)*K x y*
        (if (y.1,fockMultiset y.2)=Y then 1 else 0)) ≤
    Real.exp (4*W*w/rho)*
      (∑ y : BigState modulus M B,
        (bigStateMass modulus M B mu y*w^y.2.1.val)*
          (if (y.1,fockMultiset y.2)=Y then 1 else 0)) := by
  let w := max 1 (4*W/(rho*(1-Real.sqrt q/rho^2)))
  dsimp only
  have hh := source_original_evolution_SOURCE_GHOST_doubled_column434
    modulus B q rho V W N i hq hq1 hr hV hVW hW hg mu hmu hmass
    (fun z => if z=Y.2 then 1 else 0) (fun z => by split_ifs <;> norm_num)
  change _ ≤ Real.exp (4*W*w/rho)*_ at hh
  have ha : 0 ≤ activeMass M mu Y.1 := activeMass_nonneg M mu hmu Y.1
  have hm (x : BigState modulus M B) :
      bigStateMass modulus M B mu x*w^x.2.1.val =
      activeMass M mu x.1*(fockMass (sourceAtomMu mu) x.2*w^x.2.1.val) := by
    unfold bigStateMass
    ring
  dsimp only [w] at hm
  have hy (y : BigState modulus M B) :
      (y.1,fockMultiset y.2)=Y ↔ y.1=Y.1 ∧ fockMultiset y.2=Y.2 := by
    constructor
    · intro h; exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
    · rintro ⟨ha,hb⟩; exact Prod.ext ha hb
  simp only [hm,hy]
  rw [source_original_evolution_fixed_column_factor434 fockMultiset (activeMass M mu)
    (fun x : FockState (Atom P modulus) B => fockMass (sourceAtomMu mu) x*w^x.1.val)
    (sourceOriginalUnfilteredEvolutionGhostPositive434 B (fun z => z.2=0)
      (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
      (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
      (2*(-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(rho:ℂ)))
      (sourceBirthNu (fun p => (mu p:ℂ)))) Y.1 Y.2,
    source_original_evolution_fixed_target_factor434 fockMultiset (activeMass M mu)
      (fun x : FockState (Atom P modulus) B => fockMass (sourceAtomMu mu) x*w^x.1.val) Y.1 Y.2]
  have he :
      (∑ y : FockState (Atom P modulus) B,
        fockMass (sourceAtomMu mu) y*(if fockMultiset y=Y.2 then 1 else 0)*w^y.1.val) =
      ∑ y : FockState (Atom P modulus) B,
        (fockMass (sourceAtomMu mu) y*w^y.1.val)*(if fockMultiset y=Y.2 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he] at hh
  convert mul_le_mul_of_nonneg_left hh ha using 1 <;>
    simp only [w,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostFullKernel -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64Fock Green64MemoryGhostOp Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 2400000

def sourceOriginalUnfilteredEvolutionGhostBigPositive434
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (M B : ℕ)
    (q rho V : ℝ) (N i : ℕ) (mu : P → ℝ)
    (x y : BigState modulus M B) : ℝ :=
  if x.1=y.1 then
    sourceOriginalUnfilteredEvolutionGhostPositive434 B (fun z => z.2=0)
      (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
      (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
      (2*(-((sourceVisitEta q N i:ℝ):ℂ)*(V:ℂ)/(rho:ℂ)))
      (sourceBirthNu (fun p => (mu p:ℂ))) x.2 y.2
  else 0

theorem source_original_evolution_GHOST_double_witness434
    {U : Type} [Fintype U] [DecidableEq U]
    (old next : List U) (zero : U → Prop) [DecidablePred zero] (B : ℕ)
    (alpha chi gamma : ℂ) (nu : U → ℂ) (c : GhostWitnessChoice old zero B) :
    ‖ghostWitnessTerm old next zero B alpha chi (2*gamma) nu c‖ =
      (2:ℝ)^c.2.1.val*‖ghostWitnessTerm old next zero B alpha chi gamma nu c‖ := by
  unfold ghostWitnessTerm
  split_ifs
  · exact source_original_evolution_double_birth_norm434 old zero c.1.1 c.2.2 alpha chi gamma nu
  · simp

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (cap : BG → ℕ)

/-- Exact all-group factorization of the ORIGINAL doubled positive physical
witness kernel. SMALL and BIG are independent types and repeated states remain. -/
theorem source_original_evolution_PHYSICAL_G_positive_kernel434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : FullPhysicalState SP sm BP bm M cap) :
    (∑ c : FullGhostWitness SP sm BP bm M cap x,
      (2:ℝ)^(∑ g,(c g).2.1.val)*
        ‖physicalGBranchTerm SP sm BP bm M cap q rho N i V mu x y c‖) =
    if x.1=y.1 then
      ∏ g,sourceOriginalUnfilteredEvolutionGhostBigPositive434 (bm g) M (cap g)
        q rho (V g) N i (mu g) (x.2 g) (y.2 g)
    else 0 := by
  by_cases hs : x.1=y.1
  · rw [if_pos hs]
    by_cases ha : ∀ g,(x.2 g).1=(y.2 g).1
    · simp only [physicalGBranchTerm,if_pos (And.intro hs ha),norm_prod]
      simp only [sourceOriginalUnfilteredEvolutionGhostBigPositive434,if_pos (ha _),
        sourceOriginalUnfilteredEvolutionGhostPositive434]
      simp_rw [source_original_evolution_GHOST_double_witness434]
      simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using (Fintype.prod_sum
        (fun g (c : GhostWitnessChoice (fockToList ((x.2 g).2))
          (fun z : Atom (BP g) (bm g) => z.2=0) (cap g)) =>
          (2:ℝ)^c.2.1.val*
            ‖ghostWitnessTerm (fockToList ((x.2 g).2)) (fockToList ((y.2 g).2))
              (fun z => z.2=0) (cap g)
              (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
              (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
              (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
              (sourceBirthNu (fun p => (mu g p:ℂ))) c‖)).symm
    · have hf : ¬(x.1=y.1 ∧ ∀ g,(x.2 g).1=(y.2 g).1) := fun h => ha h.2
      simp only [physicalGBranchTerm,if_neg hf,norm_zero,mul_zero,Finset.sum_const_zero]
      obtain ⟨g,hg⟩ := not_forall.mp ha
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ g)
        (by simp [sourceOriginalUnfilteredEvolutionGhostBigPositive434,hg])
  · simp [physicalGBranchTerm,sourceOriginalUnfilteredEvolutionGhostBigPositive434,hs]

theorem source_original_evolution_PHYSICAL_weighted_fibre434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) (w : ℝ)
    (Y : FullPhysicalOutput SP sm BP bm M) :
    (∑ y : FullPhysicalState SP sm BP bm M cap,
      (fullPhysicalMass SP sm BP bm M cap Vs mu y*w^(∑ g,((y.2 g).2).1.val))*
        (if physicalFockProjection SP sm BP bm M cap y=Y then 1 else 0)) =
    physicalOrbitMass SP sm BP bm M cap Vs mu Y*w^(∑ g,((Y.2 g).2).card) := by
  unfold physicalOrbitMass
  rw [Finset.sum_mul,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : physicalFockProjection SP sm BP bm M cap y=Y
  · simp only [hy,if_true,mul_one]
    rw [←source_original_evolution_projection_OLD434 SP sm BP bm M cap y,hy]
  · simp [hy]
end Green64Analytic.CorrelationSquare

end

end

