module

public import Green64.Library.Correlation.PhysicalReturnCoordinates
public import Green64.Library.Weights.ActualSignedGhostMatrix

@[expose] public section

/-!
# Correlation / PhysicalReturnGTensor

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalReturnGTensor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 300000

private theorem union_biUnion {I : Type} [Fintype I] [DecidableEq I]
    (S T : I → Finset ℕ) :
    Finset.univ.biUnion S ∪ Finset.univ.biUnion T =
      Finset.univ.biUnion (fun i => S i ∪ T i) := by
  ext n
  simp only [Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
  aesop

section Group
variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

private def restrictAll (S : Finset (Atom P modulus)) :
    SourceOriginalGroupPrimeBirthChoice434 modulus S ≃
      SourceOriginalRestrictedPrimeBirthChoice434 modulus S Finset.univ where
  toFun d := (d.1,⟨d.2,Finset.mem_powerset.mpr (Finset.subset_univ _)⟩)
  invFun d := (d.1,d.2.val)
  left_inv d := rfl
  right_inv d := by cases d; rfl

private def groupNext (s : SourceOriginalPrimeReturnProductState434 modulus)
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus
      ((sourceOriginalPrimeProductPending434 modulus 0 s).toFinset.filter (fun z => z.2=0))) :
    SourceOriginalPrimeReturnProductState434 modulus :=
  sourceOriginalPrimeProductNext434 modulus 0 s
    (sourceOriginalProductPrimeChoiceEquiv434 modulus 0 s (restrictAll modulus _ d))

private def groupWeight (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalPrimeReturnProductState434 modulus)
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus
      ((sourceOriginalPrimeProductPending434 modulus 0 s).toFinset.filter (fun z => z.2=0))) : ℂ :=
  if ∀ p ∈ d.2,p ∉ sourceOriginalPrimeProductSeen434 modulus s then
    sourceOriginalGroupPrimeBirthWeight434 modulus _
      (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ)) d
  else 0

private theorem group_output
    (s : SourceOriginalPrimeReturnProductState434 modulus)
    (d : SourceOriginalGroupPrimeBirthChoice434 modulus
      ((sourceOriginalPrimeProductPending434 modulus 0 s).toFinset.filter (fun z => z.2=0)))
    (hd : ∀ p ∈ d.2,p ∉ sourceOriginalPrimeProductSeen434 modulus s) :
    sourceOriginalGhostPiecePending434 modulus
        (sourceOriginalPrimeProductPending434 modulus 0 s).toFinset d.1.1 d.2 =
      sourceOriginalPrimeProductPending434 modulus 0 (groupNext modulus s d) ∧
    sourceOriginalPrimeProductSeen434 modulus s ∪ d.2 =
      sourceOriginalPrimeProductSeen434 modulus (groupNext modulus s d) := by
  let r := restrictAll modulus _ d
  have hg := (source_original_PRIME_PRODUCT_G_gate434 modulus 0 s r).mp hd
  have ho := source_original_PRIME_PRODUCT_choice_state_output434 modulus 0 s
    (sourceOriginalProductPrimeChoiceEquiv434 modulus 0 s r) hg
  exact ⟨(source_original_PRIME_PRODUCT_G_output434 modulus 0 s r).trans ho.1,
    (source_original_PRIME_PRODUCT_G_seen_output434 modulus 0 s r).trans ho.2⟩

private theorem group_row (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalPrimeReturnProductState434 modulus)
    (F : SourceOriginalPrimeReturnProductState434 modulus → ℂ) :
    (∑ d : SourceOriginalGroupPrimeBirthChoice434 modulus
        ((sourceOriginalPrimeProductPending434 modulus 0 s).toFinset.filter (fun z => z.2=0)),
      groupWeight modulus eta V mu s d * F (groupNext modulus s d)) =
    sourceOriginalPrimeProductReturnRow434 modulus 0 s eta V mu F := by
  let e := (restrictAll modulus _).trans (sourceOriginalProductPrimeChoiceEquiv434 modulus 0 s)
  calc
    _ = ∑ a : SourceOriginalProductPrimeLocalChoice434 modulus 0 s,
        (∏ p,sourceOriginalOnePrimeChoiceWeight434 modulus p 0 eta V mu (s p) (a p)) *
          F (sourceOriginalPrimeProductNext434 modulus 0 s a) := by
      apply Fintype.sum_equiv e
      intro d
      have hw := source_original_PRIME_PRODUCT_G_weight434 modulus 0 s
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (restrictAll modulus _ d)
      have hg := source_original_PRIME_PRODUCT_G_gate434 modulus 0 s (restrictAll modulus _ d)
      change (∀ p ∈ d.2,p ∉ sourceOriginalPrimeProductSeen434 modulus s) ↔
        (∀ p,(e d p).2.1=∅ ∨ sourceOriginalOnePrimeSeen434 (s p)=false) at hg
      change sourceOriginalGroupPrimeBirthWeight434 modulus _
          (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ)) d =
        ∏ p,sourceOriginalGroupPrimeBirthWeight434 modulus
          (sourceOriginalOnePrimeZero434 modulus p 0 (s p))
          (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
          (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ (e d p)) at hw
      unfold groupWeight
      simp only [sourceOriginalOnePrimeChoiceWeight434]
      rw [source_original_FINITE_product_gate434]
      by_cases h : ∀ p ∈ d.2,p ∉ sourceOriginalPrimeProductSeen434 modulus s
      · rw [if_pos h,if_pos (hg.mp h)]
        rw [hw]
        rfl
      · rw [if_neg h,if_neg (fun hh => h (hg.mpr hh)),zero_mul,zero_mul]
    _ = _ := by
      have ht := source_original_FINITE_product_pushforward434
        (fun p => SourceOriginalRestrictedPrimeBirthChoice434 modulus
          (sourceOriginalOnePrimeZero434 modulus p 0 (s p)) {p})
        (fun p => SourceOriginalGhostReturnState434 (ZMod (modulus p)))
        (fun p d => sourceOriginalOnePrimeNext434 modulus p 0 (s p) d.1.1 d.2.1)
        (fun p d => sourceOriginalOnePrimeChoiceWeight434 modulus p 0 eta V mu (s p) d) F
      refine ht.trans ?_
      unfold sourceOriginalPrimeProductReturnRow434
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      exact source_original_ONE_PRIME_choice_kernel434 modulus p 0 eta V mu (s p) (t p)
end Group

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)

def sourceOriginalFullReturnGKernel434 (eta : ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (s t : SourceOriginalFullReturnState434 BP bm) : ℂ :=
  ∏ g,∏ p,sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s g p) (t g p)

def sourceOriginalFullReturnG434 (eta : ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (F : SourceOriginalFullReturnState434 BP bm → ℂ)
    (s : SourceOriginalFullReturnState434 BP bm) : ℂ :=
  ∑ t,sourceOriginalFullReturnGKernel434 BP bm eta V mu s t * F t

/-- Literal original simultaneous G at rho=1, with the full SMALL state,
all BIG active arrays, numerical seen and an arbitrary joint continuation.
No bounded mask, independence, or artificial background restriction. -/
theorem source_original_PHYSICAL_G_full_return434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm M)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalPhysicalGhostUnseenPrimeRow434 SP sm BP bm M q 1 N i V mu
      (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1
      (sourceOriginalFullReturnDecode434 SP sm BP bm M x).2 F =
    sourceOriginalFullReturnG434 BP bm (sourceVisitEta q N i) V mu
      (fun t => F
        (sourceOriginalFullReturnDecode434 SP sm BP bm M (x.1,x.2.1,t)).1
        (sourceOriginalFullReturnDecode434 SP sm BP bm M (x.1,x.2.1,t)).2) x.2.2 := by
  let eta := sourceVisitEta q N i
  let A := fun g => SourceOriginalGroupPrimeBirthChoice434 (bm g)
    ((sourceOriginalPrimeProductPending434 (bm g) 0 (x.2.2 g)).toFinset.filter (fun z => z.2=0))
  let H := fun t : SourceOriginalFullReturnState434 BP bm => F
    (sourceOriginalFullReturnDecode434 SP sm BP bm M (x.1,x.2.1,t)).1
    (sourceOriginalFullReturnDecode434 SP sm BP bm M (x.1,x.2.1,t)).2
  have hh := source_original_GHOST_joint_exact_transfer434 A
    (fun g => SourceOriginalPrimeReturnProductState434 (bm g))
    (fun g => groupNext (bm g) (x.2.2 g))
    (fun g => groupWeight (bm g) eta (V g) (mu g) (x.2.2 g))
    (fun g t => ∏ p,sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g)
      (x.2.2 g p) (t p))
    (fun g f => group_row (bm g) eta (V g) (mu g) (x.2.2 g) f) H
  refine Eq.trans ?_ hh
  unfold sourceOriginalPhysicalGhostUnseenPrimeRow434
  apply Finset.sum_congr rfl
  intro d hd
  change (if ∀ g,∀ p ∈ (d g).2,bm g p ∉ sourceOriginalFullReturnSeen434 BP bm x.2.2 then
      sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q 1 N i V mu
        (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1 d *
        F _ _ else 0) =
    (∏ g,groupWeight (bm g) eta (V g) (mu g) (x.2.2 g) (d g)) *
      H (fun g => groupNext (bm g) (x.2.2 g) (d g))
  have hgate : (∀ g,∀ p ∈ (d g).2,bm g p ∉ sourceOriginalFullReturnSeen434 BP bm x.2.2) ↔
      (∀ g,∀ p ∈ (d g).2,p ∉ sourceOriginalPrimeProductSeen434 (bm g) (x.2.2 g)) := by
    simp_rw [source_original_FULL_RETURN_seen_mem434 BP bm hi]
  simp only [groupWeight]
  rw [source_original_FINITE_product_gate434]
  by_cases hg : ∀ g,∀ p ∈ (d g).2,p ∉ sourceOriginalPrimeProductSeen434 (bm g) (x.2.2 g)
  · rw [if_pos (hgate.mpr hg),if_pos hg]
    have hout := fun g => group_output (bm g) (x.2.2 g) (d g) (hg g)
    have ho :
        sourceOriginalPhysicalGhostAtomOutput434 SP sm BP bm M
          (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1
          (sourceOriginalPhysicalGhostPrimeBirthLift434 SP sm BP bm M
            (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1 d) =
        (sourceOriginalFullReturnDecode434 SP sm BP bm M
          (x.1,x.2.1,fun g => groupNext (bm g) (x.2.2 g) (d g))).1 := by
      apply Prod.ext
      · rfl
      · funext g
        apply Prod.ext
        · rfl
        · change
            (∑ z ∈ (sourceOriginalPrimeProductPending434 (bm g) 0 (x.2.2 g)).toFinset \ (d g).1.1,
              ({z} : Multiset (Atom (BP g) (bm g)))) +
            (∑ z ∈ (d g).2.map (sourceOriginalZeroAtomEmbedding434 (bm g)),
              ({z} : Multiset (Atom (BP g) (bm g)))) = _
          rw [Finset.sum_map]
          exact (hout g).1
    have hs :
        sourceOriginalFullReturnSeen434 BP bm x.2.2 ∪
          sourceOriginalPhysicalGhostPrimeBirthSet434 SP sm BP bm M
            (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1 d =
        sourceOriginalFullReturnSeen434 BP bm
          (fun g => groupNext (bm g) (x.2.2 g) (d g)) := by
      have he (g) :
          (sourceOriginalPrimeProductSeen434 (bm g) (x.2.2 g)).image (bm g) ∪
              (d g).2.image (bm g) =
          (sourceOriginalPrimeProductSeen434 (bm g)
            (groupNext (bm g) (x.2.2 g) (d g))).image (bm g) := by
        rw [←Finset.image_union]
        exact congrArg (fun t : Finset (BP g) => t.image (bm g)) (hout g).2
      calc
        _ = Finset.univ.biUnion (fun g =>
            (sourceOriginalPrimeProductSeen434 (bm g) (x.2.2 g)).image (bm g) ∪
              (d g).2.image (bm g)) := by
          exact union_biUnion
            (fun g => (sourceOriginalPrimeProductSeen434 (bm g) (x.2.2 g)).image (bm g))
            (fun g => (d g).2.image (bm g))
        _ = _ := congrArg (fun f : BG → Finset ℕ => Finset.univ.biUnion f) (funext he)
    have hq : ((sourceVisitQ q N i:ℝ):ℂ) = 1-(eta:ℂ) := by
      simp only [eta,sourceVisitEta,Complex.ofReal_sub,Complex.ofReal_one]
      ring
    have hc :
        sourceOriginalPhysicalGhostPrimeBirthCoefficient434 SP sm BP bm M q 1 N i V mu
          (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1 d =
        ∏ g,sourceOriginalGroupPrimeBirthWeight434 (bm g) _
          (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V g:ℂ)) (fun p => (mu g p:ℂ)) (d g) := by
      simp only [sourceOriginalPhysicalGhostPrimeBirthCoefficient434,
        Complex.ofReal_one,one_pow,div_one,hq]
      rfl
    rw [hc,ho]
    change _ * F _ (sourceOriginalFullReturnSeen434 BP bm x.2.2 ∪ _) = _
    rw [hs]
    rfl
  · rw [if_neg (fun h => hg (hgate.mp h)),if_neg hg,zero_mul]

end Green64Analytic.CorrelationSquare

end

end

