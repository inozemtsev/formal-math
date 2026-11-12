module

public import Green64.Library.Correlation.PhysicalPrimeStateTransition
public import Green64.Library.Correlation.Part031
public import Green64.Library.Correlation.PhysicalPrimeNumericG
public import Green64.Library.Weights.Part057
public import Green64.Library.Weights.Part056
public import Green64.Library.Weights.Part026
public import Green64.Library.Sieve.Foundations.Part004
public import Green64.Library.Analysis.Estimates.Part010
public import Green64.Library.Weights.Part055

@[expose] public section

/-!
# Analysis / Estimates / Part013

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPrimeChoiceFubini -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- Finite weighted pushforward of a true product of choices.
The test F is an arbitrary function of ALL output coordinates. -/
theorem source_original_FINITE_product_pushforward434
    {I : Type} [Fintype I] [DecidableEq I] (A B : I → Type)
    [∀ i,Fintype (A i)] [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]
    (phi : (i : I) → A i → B i) (w : (i : I) → A i → ℂ)
    (F : ((i : I) → B i) → ℂ) :
    (∑ a : (i : I) → A i,(∏ i,w i (a i))*F (fun i => phi i (a i))) =
    ∑ b : (i : I) → B i,
      (∏ i,∑ x : A i,if phi i x=b i then w i x else 0)*F b := by
  simp_rw [Fintype.prod_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have he : ∀ b : (i : I) → B i,
      (∏ i,if phi i (a i)=b i then w i (a i) else 0)*F b =
      if (fun i => phi i (a i))=b then (∏ i,w i (a i))*F b else 0 := by
    intro b
    rw [source_original_FINITE_product_gate434]
    by_cases h : (fun i => phi i (a i))=b
    · rw [if_pos (fun i => congrFun h i),if_pos h]
    · rw [if_neg (fun hh => h (funext hh)),if_neg h,zero_mul]
  simp_rw [he]
  simp

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (p : P)

def sourceOriginalOnePrimeChoiceWeight434 (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift s) {p}) : ℂ :=
  if d.2.1=∅ ∨ sourceOriginalOnePrimeSeen434 s=false then
    sourceOriginalGroupPrimeBirthWeight434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift s)
      (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun t => (mu t:ℂ))
      (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d)
  else 0

theorem source_original_ONE_PRIME_choice_row_sum434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s : SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (F : SourceOriginalGhostReturnState434 (ZMod (modulus p)) → ℂ) :
    sourceOriginalOnePrimeChoiceRow434 modulus p shift eta V mu s F =
    ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift s) {p},
      sourceOriginalOnePrimeChoiceWeight434 modulus p shift eta V mu s d *
        F (sourceOriginalOnePrimeNext434 modulus p shift s d.1.1 d.2.1) := by
  unfold sourceOriginalOnePrimeChoiceRow434 sourceOriginalOnePrimeChoiceWeight434
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp only [zero_mul]

def sourceOriginalPrimeReturnKernel434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s t : SourceOriginalGhostReturnState434 (ZMod (modulus p))) : ℂ :=
  sourceOriginalGhostReturnLiteralRow434 (-(shift : ZMod (modulus p))) eta (V*mu p) s
    (fun u => if u=t then 1 else 0)

/-- Every matrix entry is the pushforward of the actual singleton
choice weight, including the original no-rebirth gate. -/
theorem source_original_ONE_PRIME_choice_kernel434
    (shift : ℤ) (eta V : ℝ) (mu : P → ℝ)
    (s t : SourceOriginalGhostReturnState434 (ZMod (modulus p))) :
    (∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift s) {p},
      if sourceOriginalOnePrimeNext434 modulus p shift s d.1.1 d.2.1=t then
        sourceOriginalOnePrimeChoiceWeight434 modulus p shift eta V mu s d else 0) =
      sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu s t := by
  have h := source_original_ONE_PRIME_choice_return_row434 modulus p shift eta V mu s
    (fun u => if u=t then 1 else 0)
  rw [source_original_ONE_PRIME_choice_row_sum434] at h
  simpa only [sourceOriginalPrimeReturnKernel434,mul_ite,mul_one,mul_zero] using h
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPrimeProductReturnMatrix -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

instance sourceOriginalGhostReturnFintype434 {R : Type} [Fintype R] [DecidableEq R] :
    Fintype (SourceOriginalGhostReturnState434 R) where
  elems := insert .unborn (insert .retired (Finset.univ.image .pending))
  complete s := by cases s <;> simp

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]
variable (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)

def sourceOriginalPrimeProductNext434
    (a : SourceOriginalProductPrimeLocalChoice434 modulus shift s) :
    SourceOriginalPrimeReturnProductState434 modulus :=
  fun p => sourceOriginalOnePrimeNext434 modulus p shift (s p) (a p).1.1 (a p).2.1

/-- The simultaneous physical output stays in the exact product state
sector whenever all original singleton birth gates hold. -/
theorem source_original_PRIME_PRODUCT_choice_state_output434
    (a : SourceOriginalProductPrimeLocalChoice434 modulus shift s)
    (hg : ∀ p,(a p).2.1=∅ ∨ sourceOriginalOnePrimeSeen434 (s p)=false) :
    (∑ p,sourceOriginalGhostPiecePending434 modulus
      (sourceOriginalOnePrimePending434 modulus p shift (s p)).toFinset (a p).1.1 (a p).2.1) =
      sourceOriginalPrimeProductPending434 modulus shift
        (sourceOriginalPrimeProductNext434 modulus shift s a) ∧
    (Finset.univ.filter (fun p =>
      (sourceOriginalOnePrimeSeen434 (s p) || decide ((a p).2.1≠∅))=true)) =
      sourceOriginalPrimeProductSeen434 modulus
        (sourceOriginalPrimeProductNext434 modulus shift s a) := by
  constructor
  · unfold sourceOriginalPrimeProductPending434 sourceOriginalPrimeProductNext434
    apply Finset.sum_congr rfl
    intro p hp
    exact (source_original_ONE_PRIME_choice_state_output434 modulus p shift (s p) (a p) (hg p)).1
  · ext p
    simp only [sourceOriginalPrimeProductSeen434,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [(source_original_ONE_PRIME_choice_state_output434 modulus p shift (s p) (a p) (hg p)).2]
    rfl

def sourceOriginalPrimeProductReturnRow434
    (eta V : ℝ) (mu : P → ℝ)
    (F : SourceOriginalPrimeReturnProductState434 modulus → ℂ) : ℂ :=
  ∑ t : SourceOriginalPrimeReturnProductState434 modulus,
    (∏ p,sourceOriginalPrimeReturnKernel434 modulus p shift eta V mu (s p) (t p))*F t

theorem source_original_PRIME_PRODUCT_local_choice_weight_row434
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalProductLocalG434 modulus shift s eta V mu F =
    ∑ a : SourceOriginalProductPrimeLocalChoice434 modulus shift s,
      (∏ p,sourceOriginalOnePrimeChoiceWeight434 modulus p shift eta V mu (s p) (a p)) *
      F (sourceOriginalPrimeProductPending434 modulus shift
          (sourceOriginalPrimeProductNext434 modulus shift s a))
        (sourceOriginalPrimeProductSeen434 modulus
          (sourceOriginalPrimeProductNext434 modulus shift s a)) := by
  unfold sourceOriginalPhysicalProductLocalG434
  apply Finset.sum_congr rfl
  intro a ha
  simp_rw [sourceOriginalOnePrimeChoiceWeight434]
  rw [source_original_FINITE_product_gate434]
  by_cases hg : ∀ p,(a p).2.1=∅ ∨ sourceOriginalOnePrimeSeen434 (s p)=false
  · rw [if_pos hg,if_pos hg]
    have ho := source_original_PRIME_PRODUCT_choice_state_output434 modulus shift s a hg
    rw [ho.1,ho.2]
  · rw [if_neg hg,if_neg hg,zero_mul]

/-- Exact literal subset G to product RETURN MATRIX. The full test is
joint in every prime state, pending multiset and seen set. -/
theorem source_original_PRIME_PRODUCT_G_return_matrix434
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalProductGroupG434 modulus shift s eta V mu F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu
      (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
        (sourceOriginalPrimeProductSeen434 modulus t)) := by
  rw [source_original_PRIME_PRODUCT_physical_G_tensor434,
    source_original_PRIME_PRODUCT_local_choice_weight_row434]
  unfold sourceOriginalPrimeProductNext434
  have h := source_original_FINITE_product_pushforward434
    (fun p => SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (sourceOriginalOnePrimeZero434 modulus p shift (s p)) {p})
    (fun p => SourceOriginalGhostReturnState434 (ZMod (modulus p)))
    (fun p d => sourceOriginalOnePrimeNext434 modulus p shift (s p) d.1.1 d.2.1)
    (fun p d => sourceOriginalOnePrimeChoiceWeight434 modulus p shift eta V mu (s p) d)
    (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
      (sourceOriginalPrimeProductSeen434 modulus t))
  refine h.trans ?_
  unfold sourceOriginalPrimeProductReturnRow434
  apply Finset.sum_congr rfl
  intro t ht
  apply congrArg (fun z : ℂ => z * F (sourceOriginalPrimeProductPending434 modulus shift t)
    (sourceOriginalPrimeProductSeen434 modulus t))
  apply Finset.prod_congr rfl
  intro p hp
  exact source_original_ONE_PRIME_choice_kernel434 modulus p shift eta V mu (s p) (t p)

theorem source_original_PRIME_PRODUCT_numeric_G_return_matrix434
    (hi : Function.Injective modulus) (externalSeen : Finset ℕ)
    (hext : ∀ p,modulus p ∉ externalSeen)
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset ℕ → ℂ) :
    sourceOriginalPhysicalProductNumericG434 modulus shift s eta V mu externalSeen F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu
      (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
        (externalSeen ∪ (sourceOriginalPrimeProductSeen434 modulus t).image modulus)) := by
  rw [source_original_PRIME_PRODUCT_numeric_G_pullback434 modulus shift s hi externalSeen hext,
    source_original_PRIME_PRODUCT_G_return_matrix434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalPrimePoolChain -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {P : Type} [Fintype P] [DecidableEq P]
variable (modulus : P → ℕ) [∀ p,NeZero (modulus p)]

/-- Literal all-prime subset G on an arbitrary physical pending/seen
input. It uses the original subset weights, output and unseen gate. -/
def sourceOriginalPhysicalPrimePoolG434
    (eta V : ℝ) (mu : P → ℝ) (pending : Multiset (Atom P modulus))
    (seen : Finset P) (F : Multiset (Atom P modulus) → Finset P → ℂ) : ℂ :=
  ∑ d : SourceOriginalRestrictedPrimeBirthChoice434 modulus
      (pending.toFinset.filter (fun z => z.2=0)) Finset.univ,
    if ∀ p ∈ d.2.1,p ∉ seen then
      sourceOriginalGroupPrimeBirthWeight434 modulus
        (pending.toFinset.filter (fun z => z.2=0))
        (-(eta:ℂ)) (1-(eta:ℂ)) (-(eta:ℂ)*(V:ℂ)) (fun p => (mu p:ℂ))
        (sourceOriginalRestrictedPrimeBirthLift434 modulus _ _ d) *
      F (sourceOriginalGhostPiecePending434 modulus pending.toFinset d.1.1 d.2.1)
        (seen ∪ d.2.1)
    else 0

theorem source_original_PRIME_POOL_G_return_matrix434
    (shift : ℤ) (s : SourceOriginalPrimeReturnProductState434 modulus)
    (eta V : ℝ) (mu : P → ℝ)
    (F : Multiset (Atom P modulus) → Finset P → ℂ) :
    sourceOriginalPhysicalPrimePoolG434 modulus eta V mu
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (sourceOriginalPrimeProductSeen434 modulus s) F =
    sourceOriginalPrimeProductReturnRow434 modulus shift s eta V mu
      (fun t => F (sourceOriginalPrimeProductPending434 modulus shift t)
        (sourceOriginalPrimeProductSeen434 modulus t)) :=
  source_original_PRIME_PRODUCT_G_return_matrix434 modulus shift s eta V mu F

/-- True simultaneous physical G visits with the actual integer
translations. Each mask can depend jointly on ALL input/output
pending atoms and on the complete seen sets. -/
def sourceOriginalPhysicalPrimePoolMaskedChain434
    (V : ℝ) (mu : P → ℝ)
    (mask : ℕ → Multiset (Atom P modulus) → Finset P →
      Multiset (Atom P modulus) → Finset P → ℂ) :
    List (ℝ × ℤ) → ℕ → (Multiset (Atom P modulus) → Finset P → ℂ) →
      Multiset (Atom P modulus) → Finset P → ℂ
  | [],_,F => F
  | v::vs,start,F => fun pending seen =>
      sourceOriginalPhysicalPrimePoolG434 modulus v.1 V mu pending seen
        (fun out st =>
          mask start pending seen (out.map (translateAtom v.2)) st *
          sourceOriginalPhysicalPrimePoolMaskedChain434 V mu mask vs (start+1) F
            (out.map (translateAtom v.2)) st)

/-- Product return matrices with the SAME jointly evaluated physical
masks. The transported residue at each visit is minus the accumulated
actual integer shift. -/
def sourceOriginalPrimeProductMaskedReturnChain434
    (V : ℝ) (mu : P → ℝ)
    (mask : ℕ → Multiset (Atom P modulus) → Finset P →
      Multiset (Atom P modulus) → Finset P → ℂ) :
    List (ℝ × ℤ) → ℤ → ℕ →
      (SourceOriginalPrimeReturnProductState434 modulus → ℂ) →
      SourceOriginalPrimeReturnProductState434 modulus → ℂ
  | [],_,_,F => F
  | v::vs,shift,start,F => fun s =>
      sourceOriginalPrimeProductReturnRow434 modulus shift s v.1 V mu
        (fun t =>
          mask start (sourceOriginalPrimeProductPending434 modulus shift s)
            (sourceOriginalPrimeProductSeen434 modulus s)
            (sourceOriginalPrimeProductPending434 modulus (shift+v.2) t)
            (sourceOriginalPrimeProductSeen434 modulus t) *
          sourceOriginalPrimeProductMaskedReturnChain434 V mu mask vs
            (shift+v.2) (start+1) F t)

/-- Exact temporal transfer, with no positivity, norm or separability
premise. This is the literal many-prime physical G/translation chain,
including arbitrary joint masks at every visit and a joint terminal F. -/
theorem source_original_PHYSICAL_PRIME_POOL_masked_temporal_return434
    (V : ℝ) (mu : P → ℝ)
    (mask : ℕ → Multiset (Atom P modulus) → Finset P →
      Multiset (Atom P modulus) → Finset P → ℂ)
    (vs : List (ℝ × ℤ)) (shift : ℤ) (start : ℕ)
    (F : Multiset (Atom P modulus) → Finset P → ℂ)
    (s : SourceOriginalPrimeReturnProductState434 modulus) :
    sourceOriginalPhysicalPrimePoolMaskedChain434 modulus V mu mask vs start F
      (sourceOriginalPrimeProductPending434 modulus shift s)
      (sourceOriginalPrimeProductSeen434 modulus s) =
    sourceOriginalPrimeProductMaskedReturnChain434 modulus V mu mask vs shift start
      (fun t => F
        (sourceOriginalPrimeProductPending434 modulus (sourceOriginalSinglePrimeEndShift434 shift vs) t)
        (sourceOriginalPrimeProductSeen434 modulus t)) s := by
  induction vs generalizing shift start s with
  | nil => rfl
  | cons v vs ih =>
      dsimp only [sourceOriginalPhysicalPrimePoolMaskedChain434,
        sourceOriginalPrimeProductMaskedReturnChain434,
        sourceOriginalSinglePrimeEndShift434]
      rw [source_original_PRIME_POOL_G_return_matrix434]
      unfold sourceOriginalPrimeProductReturnRow434
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only
      simp only [source_original_PRIME_PRODUCT_translate434]
      rw [ih (shift+v.2) (start+1) t]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredIdealPhysicalRoots -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 500000

/-- The actual physical tilt is bounded using the genuine total visit
weight, including both boundary sqrt(q) visits. No atom law is renormalized. -/
theorem source_original_unfiltered_ideal_PHYSICAL_ROOT_RANGE434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (bm : (g : G) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N : ℕ)
    (pmin : ℝ) (hpmin : 0 < pmin) (hPrime : ∀ g p,pmin ≤ (bm g p:ℝ))
    (hVisits : (∑ i ∈ Finset.range (N+1),sourceVisitEta q N i) < pmin) :
    let a := 1-(∑ i ∈ Finset.range (N+1),sourceVisitEta q N i)/pmin
    let R := Real.sqrt a⁻¹
    0<a ∧ 1≤R ∧ ∀ g p,
      0 < physicalSourceBaseline BP bm q N g p ∧
      1 ≤ sourceOriginalB26PhysicalTiltRoot434 BP bm q N g p ∧
      sourceOriginalB26PhysicalTiltRoot434 BP bm q N g p ≤ R := by
  let H := ∑ i ∈ Finset.range (N+1),sourceVisitEta q N i
  let a := 1-H/pmin
  have hH : 0 ≤ H := (source_original_B26_visit_sum_unit434 q hq hq1 N).1
  have ha : 0 < a := sub_pos.mpr ((div_lt_one hpmin).mpr hVisits)
  have ha1 : a ≤ 1 := sub_le_self _ (div_nonneg hH hpmin.le)
  have hR1 : 1 ≤ Real.sqrt a⁻¹ := by
    have hi : 1 ≤ a⁻¹ := by
      simpa only [one_div,inv_one] using one_div_le_one_div_of_le ha ha1
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hi
  refine ⟨ha,hR1,?_⟩
  intro g p
  have hp : 0 < (bm g p:ℝ) := hpmin.trans_le (hPrime g p)
  have hratio : H/(bm g p:ℝ) ≤ H/pmin :=
    div_le_div_of_nonneg_left hH hpmin (hPrime g p)
  have hab : a ≤ physicalSourceBaseline BP bm q N g p := by
    change 1-H/pmin ≤ 1-H/(bm g p:ℝ)
    exact sub_le_sub_left hratio 1
  have hb : 0 < physicalSourceBaseline BP bm q N g p := ha.trans_le hab
  have hb1 : physicalSourceBaseline BP bm q N g p ≤ 1 :=
    sub_le_self _ (div_nonneg hH hp.le)
  refine ⟨hb,?_,?_⟩
  · unfold sourceOriginalB26PhysicalTiltRoot434
    have hi : 1 ≤ (physicalSourceBaseline BP bm q N g p)⁻¹ := by
      simpa only [one_div,inv_one] using one_div_le_one_div_of_le hb hb1
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hi
  · unfold sourceOriginalB26PhysicalTiltRoot434
    exact Real.sqrt_le_sqrt (by
      simpa only [one_div] using one_div_le_one_div_of_le ha hab)

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26SharedUniformBilinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Bounded joint multiplier on the actual shared-copy probability
coupling. This bound uses both actual marginals; the multiplier may
depend jointly on all source and target prime labels. -/
theorem source_original_B26_shared_uniform_bilinear434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hMass : ∀ g,∑ p : BP g,mu g p=1)
    (delta : ℝ) (hd : 0 ≤ delta)
    (F Gtest : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (K : ((g : G) → Fin (J+ell) → BP g) →
      ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (hK : ∀ s t,‖K s t‖ ≤ delta) :
    ‖∑ s : ((g : G) → Fin (J+ell) → BP g),
      ∑ t : ((g : G) → Fin (J+ell) → BP g),
        ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        (star (F s)*Gtest t*K s t)‖^2 ≤
      delta^2*sourceOriginalB26ActiveEnergy434 BP J ell mu F*
        sourceOriginalB26ActiveEnergy434 BP J ell mu Gtest := by
  classical
  let H := (g : G) → sourceBigShared J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ nu) g → BP g
  let X := (g : G) → Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → BP g
  let A := (g : G) → Fin (J+ell) → BP g
  let e := sourceOriginalB26ActiveSplitEquiv434 BP J ell m hmJ nu
  let wH := sourceOriginalB26SharedPrimeMass434 BP J ell m hmJ nu mu
  let wX := fun u : X => ∏ g : G,∏ j : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g),mu g (u g j)
  have hX : ∑ u : X,wX u=1 := by
    dsimp only [wX,X]
    have hprod := (Fintype.prod_sum (fun (g : G)
      (u : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → BP g) =>
        ∏ j,mu g (u j))).symm
    rw [hprod]
    have hg (g : G) : (∑ u : Fin (sourceOriginalProbeFreeMarkCount434 J ell m hmJ nu g) → BP g,
        ∏ j,mu g (u j))=1 := by
      rw [← Fintype.prod_sum]
      simp only [hMass,Finset.prod_const_one]
    simp only [hg,Finset.prod_const_one]
  have hwH (s : H) : 0 ≤ wH s :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (s g i)))
  have hwX (u : X) : 0 ≤ wX u :=
    Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ => hmu g (u g i)))
  let W := H × X × X
  let w := fun z : W => wH z.1*wX z.2.1*wX z.2.2
  let source := fun z : W => e.symm (z.1,z.2.1)
  let target := fun z : W => e.symm (z.1,z.2.2)
  have hMargS (f : A → ℂ) :
      (∑ z : W,w z*‖f (source z)‖^2) =
      sourceOriginalB26ActiveEnergy434 BP J ell mu f := by
    calc
      _ = ∑ s : H,∑ u : X,(wH s*wX u*‖f (e.symm (s,u))‖^2)*(∑ v : X,wX v) := by
        simp only [W,w,source,Fintype.sum_prod_type,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ s : H,∑ u : X,wH s*wX u*‖f (e.symm (s,u))‖^2 := by rw [hX];simp
      _ = _ := (source_original_B26_active_split_weighted_sum434
        BP J ell m hmJ nu mu (fun s => ‖f s‖^2)).symm
  have hMargT (f : A → ℂ) :
      (∑ z : W,w z*‖f (target z)‖^2) =
      sourceOriginalB26ActiveEnergy434 BP J ell mu f := by
    calc
      _ = ∑ z : W,w z*‖f (source z)‖^2 := by
        simp only [W,w,source,target,Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := hMargS f
  have hPoint (z : W) :
      ‖star (F (source z))*Gtest (target z)*K (source z) (target z)‖^2 ≤
        delta^2*‖F (source z)‖^2*‖Gtest (target z)‖^2 := by
    rw [norm_mul,norm_mul,norm_star,mul_pow,mul_pow]
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hK (source z) (target z)) 2)
      (mul_nonneg (sq_nonneg ‖F (source z)‖) (sq_nonneg ‖Gtest (target z)‖))
    nlinarith only [hh]
  have hBound := source_original_B26_homogeneous_shared_integration434
    w (fun z => ‖F (source z)‖^2) (fun z => ‖Gtest (target z)‖^2)
    (fun z => star (F (source z))*Gtest (target z)*K (source z) (target z))
    (delta^2) (fun z => mul_nonneg (mul_nonneg (hwH _) (hwX _)) (hwX _))
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) (sq_nonneg delta) hPoint
  rw [hMargS F,hMargT Gtest] at hBound
  rw [source_original_B26_shared_free_pairing434]
  simpa only [W,w,source,target,e,wH,wX,Fintype.sum_prod_type] using hBound
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PermutedUniformBilinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- Both actual endpoint permutations are retained in the uniform
joint-kernel estimate, with exactly the original full active energies. -/
theorem source_original_B26_permuted_uniform_bilinear434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (J ell m : ℕ) (hmJ : m ≤ J) (nu : SourceOriginalProbePattern434 G m)
    (mu : (g : G) → BP g → ℝ) (hmu : ∀ g p,0 ≤ mu g p)
    (hMass : ∀ g,∑ p : BP g,mu g p=1)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (delta : ℝ) (hd : 0 ≤ delta)
    (F Gtest : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (K : ((g : G) → Fin (J+ell) → BP g) →
      ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (hK : ∀ s t,‖K s t‖ ≤ delta) :
    ‖∑ s : ((g : G) → Fin (J+ell) → BP g),
      ∑ t : ((g : G) → Fin (J+ell) → BP g),
        ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
        (star (F s)*Gtest t*K s t)‖^2 ≤
      delta^2*sourceOriginalB26ActiveEnergy434 BP J ell mu F*
        sourceOriginalB26ActiveEnergy434 BP J ell mu Gtest := by
  classical
  let A := (g : G) → Fin (J+ell) → BP g
  let eS := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) sigma
  let eT := sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) tau
  have hReindex :
      (∑ s : A,∑ t : A,
        ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t sigma tau *
        (star (F s)*Gtest t*K s t)) =
      ∑ s : A,∑ t : A,
        ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ nu) s t
          (fun _ => Equiv.refl _) (fun _ => Equiv.refl _) *
        (star (F (eS.symm s))*Gtest (eT.symm t)*K (eS.symm s) (eT.symm t)) := by
    apply Fintype.sum_equiv eS
    intro s
    have hm := source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s sigma
    change (∏ g : G,∏ i : Fin (J+ell),mu g (eS s g i)) =
      ∏ g : G,∏ i : Fin (J+ell),mu g (s g i) at hm
    rw [Equiv.symm_apply_apply,hm]
    apply Fintype.sum_equiv eT
    intro t
    rw [Equiv.symm_apply_apply]
    rw [source_original_B26_fresh_law_permuted434 BP J ell m
      (sourceOriginalProbeMemoryPattern434 J m hmJ nu) mu s t sigma tau]
    rfl
  have hEnergy (pi : BigGroupPerm (BG := G) (J+ell)) (f : A → ℂ) :
      sourceOriginalB26ActiveEnergy434 BP J ell mu
        (fun s => f ((sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) pi).symm s)) =
      sourceOriginalB26ActiveEnergy434 BP J ell mu f := by
    unfold sourceOriginalB26ActiveEnergy434
    apply Fintype.sum_equiv (sourceOriginalB26EndpointPermutationEquiv434 BP (J+ell) pi).symm
    intro s
    congr 1
    exact (source_original_B26_endpoint_permutation_mass434 BP (J+ell) mu s
      (fun g => (pi g).symm)).symm
  have hh := source_original_B26_shared_uniform_bilinear434 BP J ell m hmJ nu
    mu hmu hMass delta hd (fun s => F (eS.symm s)) (fun t => Gtest (eT.symm t))
    (fun s t => K (eS.symm s) (eT.symm t)) (fun s t => hK _ _)
  rw [hReindex]
  dsimp only [eS,eT] at hh
  rw [hEnergy sigma F,hEnergy tau Gtest] at hh
  exact hh
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalTiltUniformBilinear -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Finite scalar-envelope transfer for the actual tilted shared law.
The downstream theorem supplies its arithmetic auxiliary-ban envelope.
An arbitrary joint K is retained without a factorization assumption. -/
theorem source_original_B26_physical_tilt_uniform_bilinear434
    {G : Type} [Fintype G] [DecidableEq G]
    (BP : G → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
    (modulus : (g : G) → BP g → ℕ) [∀ g p,NeZero (modulus g p)]
    (q : ℝ) (N : ℕ) (V : G → ℝ) (hV : ∀ g,0 < V g)
    (hVEq : ∀ g,V g=∑ p : BP g,1/(modulus g p:ℝ))
    (hb : ∀ g p,(1:ℝ)/2 ≤ physicalSourceBaseline BP modulus q N g p)
    (J ell m tmax : ℕ) (hmJ : m ≤ J) (hm : m ≤ tmax)
    (ν : SourceOriginalProbePattern434 G m)
    (sigma tau : BigGroupPerm (BG := G) (J+ell))
    (C0 L : ℝ) (hL : 1 ≤ L)
    (hGroups : (Fintype.card G:ℝ) ≤ C0*Real.log L)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (U F : ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (K : ((g : G) → Fin (J+ell) → BP g) →
      ((g : G) → Fin (J+ell) → BP g) → ℂ)
    (hK : ∀ s t,‖K s t‖ ≤ delta) :
    let mu := physicalSourceMuTilde BP modulus q N V
    ‖∑ s : ((g : G) → Fin (J+ell) → BP g),
      ∑ t : ((g : G) → Fin (J+ell) → BP g),
        ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
        sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
          (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t sigma tau *
        (star (U s)*F t*K s t)‖^2 ≤
    (delta^2*(L^(sourceOriginalB26TiltDensityExponent434 ell tmax C0))^2) *
      sourceOriginalB26ActiveEnergy434 BP J ell mu U *
      sourceOriginalB26ActiveEnergy434 BP J ell mu F := by
  classical
  let muH := sourceOriginalJointHarmonicMu434 BP modulus V
  let muT := physicalSourceMuTilde BP modulus q N V
  let W := fun pi s => sourceOriginalB26TiltEndpoint434 BP J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
    (sourceOriginalB26PhysicalTiltRoot434 BP modulus q N) pi s
  let u := fun s => (W sigma s:ℂ)*U s
  let v := fun s => (W tau s:ℂ)*F s
  let EU := sourceOriginalB26ActiveEnergy434 BP J ell muT U
  let EF := sourceOriginalB26ActiveEnergy434 BP J ell muT F
  let Ct := sourceOriginalB26TiltDensityExponent434 ell tmax C0
  have hb0 (g : G) (p : BP g) : 0 < physicalSourceBaseline BP modulus q N g p := by
    have hh := hb g p
    linarith only [hh]
  have hmuH (g : G) (p : BP g) : 0 < muH g p :=
    div_pos (one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos _))) (hV g)
  have hmuT (g : G) (p : BP g) : 0 < muT g p :=
    one_div_pos.mpr (mul_pos (mul_pos (hV g)
      (Nat.cast_pos.mpr (NeZero.pos _))) (hb0 g p))
  obtain ⟨hmuNN,hMass⟩ := source_original_joint_harmonic_normalized434 BP modulus V hV hVEq
  have hEU : 0 ≤ EU := source_original_B26_active_energy_nonneg434 BP J ell muT hmuT U
  have heq := source_original_B26_PHYSICAL_TILT_BILINEAR434 BP modulus q N V hb0
    J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) sigma tau U F K
  have heq' :
      (∑ s : ((g : G) → Fin (J+ell) → BP g),
        ∑ t : ((g : G) → Fin (J+ell) → BP g),
          ((∏ g : G,∏ i : Fin (J+ell),muT g (s g i):ℝ):ℂ) *
          sourceOriginalB26FrozenFreshLaw434 BP J ell m muT
            (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t sigma tau *
          (star (U s)*F t*K s t)) =
      ∑ s : ((g : G) → Fin (J+ell) → BP g),
        ∑ t : ((g : G) → Fin (J+ell) → BP g),
          ((∏ g : G,∏ i : Fin (J+ell),muH g (s g i):ℝ):ℂ) *
          sourceOriginalB26FrozenFreshLaw434 BP J ell m muH
            (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t sigma tau *
          (star (u s)*v t*K s t) := by
    simpa only [muT,muH,u,v,W,mul_assoc,Complex.star_def] using heq
  have hHarm := source_original_B26_permuted_uniform_bilinear434 BP J ell m hmJ ν
    muH hmuNN hMass sigma tau delta hdelta u v K hK
  have hUcap : sourceOriginalB26ActiveEnergy434 BP J ell muH u ≤ L^Ct*EU :=
    source_original_B26_PHYSICAL_TILT_ENDPOINT_CAP434 BP modulus q N V hV hb
      J ell m tmax hmJ hm ν sigma U C0 L hL hGroups
  have hFcap : sourceOriginalB26ActiveEnergy434 BP J ell muH v ≤ L^Ct*EF :=
    source_original_B26_PHYSICAL_TILT_ENDPOINT_CAP434 BP modulus q N V hV hb
      J ell m tmax hmJ hm ν tau F C0 L hL hGroups
  have hFV : 0 ≤ sourceOriginalB26ActiveEnergy434 BP J ell muH v :=
    source_original_B26_active_energy_nonneg434 BP J ell muH hmuH v
  have hProd := mul_le_mul hUcap hFcap hFV
    (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hL) _) hEU)
  change ‖_‖^2 ≤ (delta^2*(L^Ct)^2)*EU*EF
  rw [heq']
  calc
    _ ≤ delta^2*sourceOriginalB26ActiveEnergy434 BP J ell muH u*
        sourceOriginalB26ActiveEnergy434 BP J ell muH v := hHarm
    _ = delta^2*(sourceOriginalB26ActiveEnergy434 BP J ell muH u*
        sourceOriginalB26ActiveEnergy434 BP J ell muH v) := by ring
    _ ≤ delta^2*((L^Ct*EU)*(L^Ct*EF)) := mul_le_mul_of_nonneg_left hProd (sq_nonneg _)
    _ = (delta^2*(L^Ct)^2)*EU*EF := by ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26SmallNormBudget -/

section

open Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 18000000

def sourceOriginalB26SmallNormBase434 (ell : ℕ) (q vmin : ℝ) : ℝ :=
  max 1 ((ell.factorial:ℝ)/((1-q)^(ell+1)*vmin^ell))

def sourceOriginalB26SmallNormExponent434 (ell : ℕ) (q vmin C0 : ℝ) : ℝ :=
  C0*Real.log (sourceOriginalB26SmallNormBase434 ell q vmin)

theorem source_original_B26_small_norm_exponent_nonneg434
    (ell : ℕ) (q vmin C0 : ℝ) (hC0 : 0 ≤ C0) :
    0 ≤ sourceOriginalB26SmallNormExponent434 ell q vmin C0 := by
  apply mul_nonneg hC0
  exact Real.log_nonneg (le_max_left _ _)

/-- Uniform SMALL conditioning budget for the original logarithmically
many groups. q, ell and the mass floor are fixed before all moving data;
there is no dependence on J, on the moduli or on the OLD sector. -/
theorem source_original_B26_small_conditioning_polynomial434
    {SG : Type} [Fintype SG] (ell : ℕ)
    (q vmin C0 L : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (hv : 0 < vmin) (hC0 : 0 ≤ C0) (hL : 1 ≤ L)
    (Vs : SG → ℝ) (hVs : ∀ g,vmin ≤ Vs g)
    (hGroups : (Fintype.card SG:ℝ) ≤ C0*Real.log L) :
    memorySmallGroupConditioningConstant (SG := SG) ell q Vs ≤
      L^(sourceOriginalB26SmallNormExponent434 ell q vmin C0) := by
  classical
  let K := sourceOriginalB26SmallNormBase434 ell q vmin
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hq' : 0 < 1-q := sub_pos.mpr hq1
  have hEach (g : SG) :
      (ell.factorial:ℝ)/((1-q)^(ell+1)*(Vs g)^ell) ≤ K := by
    have hden : (1-q)^(ell+1)*vmin^ell ≤ (1-q)^(ell+1)*(Vs g)^ell :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv.le (hVs g) ell)
        (pow_nonneg hq'.le _)
    have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) ell.factorial)
      (mul_pos (pow_pos hq' _) (pow_pos hv _)) hden
    exact hh.trans (le_max_right _ _)
  have hProd : memorySmallGroupConditioningConstant (SG := SG) ell q Vs ≤
      K^(Fintype.card SG) := by
    unfold memorySmallGroupConditioningConstant
    calc
      _ ≤ ∏ _g : SG,K := Finset.prod_le_prod₀
        (fun g _ => div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (pow_nonneg hq'.le _) (pow_nonneg (hv.le.trans (hVs g)) _)))
        (fun g _ => hEach g)
      _ = _ := by simp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ K^(Fintype.card SG) := hProd
    _ = Real.exp (Real.log K*(Fintype.card SG:ℝ)) := by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos hK]
    _ ≤ Real.exp (Real.log K*(C0*Real.log L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hGroups hlogK)
    _ = L^(sourceOriginalB26SmallNormExponent434 ell q vmin C0) := by
      rw [Real.rpow_def_of_pos hLp]
      congr 1
      dsimp [sourceOriginalB26SmallNormExponent434,K]
      ring

theorem eventually_source_original_B26_fixed_slots_budget434 (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop, ((J+ell:ℕ):ℝ) ≤ L^(1:ℕ) := by
  simpa only [pow_one] using eventually_ge_atTop (((J+ell:ℕ):ℝ))

/-- The concrete adjustment Bideal=Bgoal+2*Csmall absorbs both SMALL
endpoint norms and is chosen before J, Q, mesh widths or conductors. -/
theorem source_original_B26_small_squared_budget434
    (L Bgoal Csmall CsmallActual : ℝ) (hL : 0 < L)
    (hC : 0 ≤ CsmallActual) (hCap : CsmallActual ≤ L^Csmall) :
    L^(-(Bgoal+2*Csmall))*CsmallActual^2 ≤ L^(-Bgoal) := by
  calc
    _ ≤ L^(-(Bgoal+2*Csmall))*(L^Csmall)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC hCap 2)
        (Real.rpow_nonneg hL.le _)
    _ = L^(-Bgoal) := by
      rw [← Real.rpow_two,← Real.rpow_mul hL.le,← Real.rpow_add hL]
      congr 1
      ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallBoundaryBudget -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 12000000

/-- A finite set of positive integers below X has cardinality at most X.
Applied to actual source prime sets, no prime-counting hypothesis is needed. -/
theorem source_original_positive_alphabet_card_le434
    (P : Finset ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hp : ∀ p ∈ P, 1 ≤ p) (hmax : ∀ p ∈ P, (p:ℝ) ≤ X) :
    (P.card:ℝ) ≤ X := by
  have hs : P ⊆ Finset.Icc 1 (Nat.floor X) := by
    intro p h
    exact Finset.mem_Icc.mpr ⟨hp p h,(Nat.le_floor_iff hX).mpr (hmax p h)⟩
  have hc : P.card ≤ Nat.floor X := by
    simpa using Finset.card_le_card hs
  exact (show (P.card:ℝ) ≤ (Nat.floor X:ℝ) by exact_mod_cast hc).trans
    (Nat.floor_le hX)

/-- The real SMALL boundary is paid explicitly. Empty alphabets are allowed;
there is no logarithm of a possibly zero initial mass. -/
theorem source_original_ACTUAL_SMALL_boundary_exp_budget434
    {SG : Type} [Fintype SG] (P : SG → Finset ℕ) (Vs : SG → ℝ)
    (M : ℕ) (L CG v : ℝ) (hL : 1 ≤ L) (hCG : 0 ≤ CG) (hv : 0 < v)
    (hM : (M:ℝ) ≤ L) (hG : (Fintype.card SG:ℝ) ≤ CG*Real.log L)
    (hV : ∀ g,v ≤ Vs g)
    (hcard : ∀ g,(P g).card ≤ Real.exp (Real.sqrt L)) :
    (∏ g : SG,((P g).card / Vs g : ℝ)^M) ≤
      Real.exp (CG*L*Real.log L*(Real.sqrt L+Real.log (max 1 v⁻¹))) := by
  let A : ℝ := max 1 v⁻¹
  let t : ℝ := Real.sqrt L+Real.log A
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have ht : 0 ≤ t := add_nonneg (Real.sqrt_nonneg L) (Real.log_nonneg hA1)
  have hbase (g : SG) : ((P g).card:ℝ)/Vs g ≤ Real.exp t := by
    have hi' : (Vs g)⁻¹ ≤ v⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hv (hV g)
    have hi : (Vs g)⁻¹ ≤ A := hi'.trans (le_max_right 1 v⁻¹)
    calc
      _ = ((P g).card:ℝ)*(Vs g)⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp (Real.sqrt L)*A :=
        mul_le_mul (hcard g) hi (inv_nonneg.mpr (hv.le.trans (hV g)))
          (Real.exp_pos _).le
      _ = Real.exp t := by dsimp only [t];rw [Real.exp_add,Real.exp_log hA]
  have hprod : (∏ g : SG,((P g).card / Vs g : ℝ)^M) ≤
      (Real.exp t)^(M*Fintype.card SG) := by
    calc
      _ ≤ ∏ _g : SG,(Real.exp t)^M := Finset.prod_le_prod₀
        (fun g _ => pow_nonneg (div_nonneg (Nat.cast_nonneg _) (hv.le.trans (hV g))) _)
        (fun g _ => pow_le_pow_left₀
          (div_nonneg (Nat.cast_nonneg _) (hv.le.trans (hV g))) (hbase g) M)
      _ = _ := by simp [pow_mul]
  have hcount : (M:ℝ)*(Fintype.card SG:ℝ) ≤ L*(CG*Real.log L) :=
    mul_le_mul hM hG (Nat.cast_nonneg _) (zero_le_one.trans hL)
  calc
    _ ≤ (Real.exp t)^(M*Fintype.card SG) := hprod
    _ = Real.exp (t*((M*Fintype.card SG:ℕ):ℝ)) := by
      rw [←Real.rpow_natCast,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    _ ≤ Real.exp (t*(L*(CG*Real.log L))) := by
      apply Real.exp_le_exp.mpr
      simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hcount ht
    _ = _ := by dsimp only [t,A];congr 1;ring

def sourceOriginalActualSmallPrimeSets434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) (g : Option ι) : Finset ℕ :=
  sourceOriginalFullGroupPrimeSets434 u (Sum.inl g)

def sourceOriginalActualSmallMass434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) (g : Option ι) : ℝ :=
  sourceOriginalFullGroupMass434 u (Sum.inl g)

/-- Original S and all Ts are subfamilies of the actual original G. -/
theorem source_original_ACTUAL_SMALL_source_bounds434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) :
    (∀ g p,p ∈ sourceOriginalActualSmallPrimeSets434 u g → p.Prime) ∧
    (∀ g p,p ∈ sourceOriginalActualSmallPrimeSets434 u g →
      (p:ℝ) ≤ Real.exp (Real.sqrt L)) ∧
    (∀ g,cfg.vmin ≤ sourceOriginalActualSmallMass434 u g) := by
  refine ⟨?_,?_,?_⟩
  · intro g p hp
    exact source_original_full_groups_prime434 u (Sum.inl g) p hp
  · intro g p hp
    apply u.hGroup p
    rw [source_original_full_groups_union434 u]
    exact Finset.mem_biUnion.mpr ⟨Sum.inl g,Finset.mem_univ _,hp⟩
  · intro g
    exact source_original_full_groups_norm_positive434 u (Sum.inl g)

/-- The distinguished S group is included, with its real cardinality cost. -/
theorem source_original_ACTUAL_SMALL_group_count434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) (hlog : 1 ≤ Real.log L) :
    (Fintype.card (Option ι):ℝ) ≤ (cfg.C0+1)*Real.log L := by
  rw [Fintype.card_option]
  push_cast
  nlinarith only [u.hSmallGroups,hlog]

/-- For a fixed source J, the threshold precedes all moving source data.
In particular M <= L is discharged, rather than added to the source contract. -/
theorem eventually_source_original_ACTUAL_SMALL_source_boundary434
    (cfg : SourceComparisonFixed434) (J ell : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
      {x Y Hp : ℝ} (u : SourceComparisonData434 ι β cfg x L Y Hp),
      (∏ g : Option ι,
        (((sourceOriginalActualSmallPrimeSets434 u g).card:ℝ)/
          sourceOriginalActualSmallMass434 u g)^(J+ell)) ≤
        Real.exp ((cfg.C0+1)*L*Real.log L*
          (Real.sqrt L+Real.log (max 1 cfg.vmin⁻¹))) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (Real.exp 1),
    eventually_source_original_B26_fixed_slots_budget434 J ell] with L hL he hM
  intro ι β _ _ _ _ x Y Hp u
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simpa using hh
  have hs := source_original_ACTUAL_SMALL_source_bounds434 u
  apply source_original_ACTUAL_SMALL_boundary_exp_budget434
    (sourceOriginalActualSmallPrimeSets434 u) (sourceOriginalActualSmallMass434 u)
    (J+ell) L (cfg.C0+1) cfg.vmin hL (by linarith [cfg.hC0]) cfg.hv
    (by simpa using hM) (source_original_ACTUAL_SMALL_group_count434 u hlog) hs.2.2
  intro g
  exact source_original_positive_alphabet_card_le434
    (sourceOriginalActualSmallPrimeSets434 u g) (Real.exp (Real.sqrt L))
    (Real.exp_pos _).le (fun p hp => (hs.1 g p hp).one_le) (hs.2.1 g)
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalActualSmallCarrierPromotion -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
set_option autoImplicit false
set_option maxHeartbeats 18000000

/-- The original source group-count cap with space for the distinguished S. -/
def sourceOriginalPromotedSmallFixed434 (cfg : SourceComparisonFixed434) :
    SourceComparisonFixed434 :=
  { cfg with C0 := cfg.C0 + 1, hC0 := by linarith [cfg.hC0] }

def sourceOriginalPromotedSmallSets434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) : Option ι → Finset ℕ
  | none => u.S
  | some i => u.Ts i

def sourceOriginalPromotedSmallMass434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) : Option ι → ℝ
  | none => u.Vs
  | some i => u.Vsmall i

def sourceOriginalPromotedSmallSlots434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) : Option ι → ℕ
  | none => 0
  | some i => u.ts i

/-- The dummy singled-out group is empty; the original physical S is
moved into the EXTRA SMALL index, rather than discarded or duplicated. -/
theorem source_original_promoted_small_union434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp) :
    (Finset.univ : Finset (Option ι)).biUnion (sourceOriginalPromotedSmallSets434 u) =
      u.S ∪ (Finset.univ : Finset ι).biUnion u.Ts := by
  ext p
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · rintro ⟨g,hg⟩
    cases g with
    | none => exact Or.inl hg
    | some i => exact Or.inr ⟨i,hg⟩
  · rintro (hs | ⟨i,hi⟩)
    · exact ⟨none,hs⟩
    · exact ⟨some i,hi⟩

/-- A real source-data reindexing, not an assumption that S had vanished.
Only the auxiliary singled-out source slot becomes empty. The actual
SMALL physical arrays are all S+Ts with their exact original masses. -/
noncomputable def sourceOriginalPromotedSmallData434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hlog : 1 ≤ Real.log L) :
    SourceComparisonData434 (Option ι) β (sourceOriginalPromotedSmallFixed434 cfg) x L Y Hp :=
  {
    Z := u.Z,
    hY := u.hY,
    hYmax := u.hYmax,
    hH := u.hH,
    hYstrong := u.hYstrong,
    hZ := u.hZ,
    hYIdent := u.hYIdent,
    hSmallGroups := by
      change ((Fintype.card (Option ι):ℝ)) ≤ (cfg.C0+1)*Real.log L
      rw [Fintype.card_option]
      push_cast
      nlinarith only [u.hSmallGroups,hlog],
    hBigGroups := by
      change ((Fintype.card β:ℝ)) ≤ (cfg.C0+1)*Real.log L
      nlinarith only [u.hBigGroups,hlog],
    lo := u.lo,
    hi := u.hi,
    Ncap := u.Ncap,
    alpha := u.alpha,
    hNcap := u.hNcap,
    hCap := u.hCap,
    hAlpha := u.hAlpha,
    G := u.G,
    Ptw := u.Ptw,
    S := ∅,
    primeSlot := u.primeSlot,
    Ts := sourceOriginalActualSmallPrimeSets434 u,
    Tb := u.Tb,
    Vs := u.Vs,
    Vsmall := sourceOriginalActualSmallMass434 u,
    Vbig := u.Vbig,
    ts := sourceOriginalPromotedSmallSlots434 u,
    tb := u.tb,
    coef := u.coef,
    k := u.k,
    qBase := u.qBase,
    c := u.c,
    chi0 := u.chi0,
    hBase := u.hBase,
    hBaseCap := u.hBaseCap,
    hk := u.hk,
    hVs := u.hVs,
    hts := by
      intro g
      cases g with
      | none => exact Nat.zero_le _
      | some i => exact u.hts i,
    htb := u.htb,
    hVsmall := by
      intro g
      cases g with
      | none => exact u.hVs
      | some i => exact u.hVsmall i,
    hVbig := u.hVbig,
    hcoef := u.hcoef,
    C := u.C,
    hC := u.hC,
    hCBudget := u.hCBudget,
    hcBound := u.hcBound,
    sigma0 := u.sigma0,
    sigma1 := u.sigma1,
    hSigma0 := u.hSigma0,
    hSigma1 := u.hSigma1,
    hModScale := u.hModScale,
    hSG := by simp,
    hSPrime := by simp,
    hSN := by simp,
    hPN := u.hPN,
    hRough := u.hRough,
    hGroup := u.hGroup,
    hLong := u.hLong,
    I := u.I,
    hI := u.hI,
    hSmall := by simp,
    hSlot := u.hSlot,
    hIBand := u.hIBand,
    F1 := u.F1,
    F2 := u.F2,
    p1 := u.p1,
    p2 := u.p2,
    U1 := u.U1,
    U2 := u.U2,
    hF1 := u.hF1,
    hF2 := u.hF2,
    hp1 := u.hp1,
    hp2 := u.hp2,
    hmin1 := u.hmin1,
    hmin2 := u.hmin2,
    hU1 := u.hU1,
    hU2 := u.hU2,
    hcell1 := u.hcell1,
    hcell2 := u.hcell2,
    hHIdent := u.hHIdent,
    psi1 := u.psi1,
    hSmooth := u.hSmooth,
    hSupport := u.hSupport,
    v1 := u.v1,
    hv1 := u.hv1,
    hBudget := u.hBudget,
    hG := by
      have hSets : sourceOriginalPromotedSmallSets434 u =
          sourceOriginalActualSmallPrimeSets434 u := by
        funext g
        cases g <;> rfl
      change u.G = (∅ : Finset ℕ) ∪
        (Finset.univ : Finset (Option ι)).biUnion (sourceOriginalActualSmallPrimeSets434 u) ∪
        (Finset.univ : Finset β).biUnion u.Tb
      rw [Finset.empty_union,←hSets,source_original_promoted_small_union434]
      exact u.hG,
    hParity := u.hParity,
    hTsPrime := by
      intro g p hp
      cases g with
      | none => exact u.hSPrime p hp
      | some i => exact u.hTsPrime i p hp,
    hTbPrime := u.hTbPrime,
    hOrigW := u.hOrigW,
    hOrigSmall := u.hOrigSmall,
    hOrigLong := u.hOrigLong,
    hSlotMin := u.hSlotMin,
    hHband := u.hHband,
    hArcCap := u.hArcCap,
    hDisjS := by simp,
    hDisjB := by simp,
  }

/-- The ORIGINAL source03 separation survives promotion of S to
Option.none, including S vs Ts, S vs Tb and all original group pairs. -/
theorem source_original_promoted_small_sep434
    {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
    {cfg : SourceComparisonFixed434} {x L Y Hp : ℝ}
    (u : SourceComparisonData434 ι β cfg x L Y Hp)
    (hlog : 1 ≤ Real.log L)
    (sep : SourceOriginalSource03GroupSeparation434 u) :
    SourceOriginalSource03GroupSeparation434 (sourceOriginalPromotedSmallData434 u hlog) := by
  constructor
  · intro i j p hi hj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some j => exact False.elim ((u.hDisjS j p hi) hj)
    | some i =>
        cases j with
        | none => exact False.elim ((u.hDisjS i p hj) hi)
        | some j => exact congrArg some (sep.hTT i j p hi hj)
  · intro i j p hi hj
    exact sep.hBB i j p hi hj
  · intro i j p hi
    cases i with
    | none => exact u.hDisjB j p hi
    | some i => exact sep.hTB i j p hi
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26SmallOldTransfer -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bigMod : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bigMod g p)]
variable (J ell : ℕ) (cap sizes : BG → ℕ)
variable (hsizes : ∀ g,sizes g ≤ cap g)
variable (prime : (g : BG) → Fin (sizes g) → BP g)
local notation "Small" => Green64SmallHaar.GroupState SP smallMod (J+ell)
local notation "SmallPerm" => Green64SmallHaar.GroupPermFamily (G := SG) (J+ell)
local notation "Shared" => SourceOriginalB26SharedTuple434 SP J ell
local notation "Active" => SourceOriginalB26Active434 BP J ell
local notation "Old" => SourceOriginalB26OldResidues434 BP bigMod sizes prime
local notation "Torus" => memoryFrozenResidueGroup SP smallMod BP bigMod sizes prime


theorem source_original_B26_small_conditioning_constant_nonneg434
    (q : ℝ) (hq1 : q < 1) (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g) :
    0 ≤ memorySmallGroupConditioningConstant (SG := SG) ell q Vs := by
  apply Finset.prod_nonneg
  intro g _
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (pow_nonneg (sub_pos.mpr hq1).le _) (pow_nonneg (hVs g).le _))

/-- Exact location of the between-P_d bilinear block in the original
SMALL/OLD Fourier pairing. Both SMALL endpoint permutation masses,
the complete Torus cardinal, and the actual Fock sector constant remain. -/
def sourceOriginalB26SmallOldLiftedPair434
    (q : ℝ) (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (B : Shared → AddChar Torus ℂ → (Active → ℂ) → (Active → ℂ) → ℂ)
    (U F : Small → Active → Old → ℂ) : ℂ :=
  (Green64SmallHaar.groupPermutationPairMass (G := SG) (J+ell):ℂ) *
    ∑ ss : SmallPerm,∑ tt : SmallPerm,
      ((sourceOriginalB26SectorConstant434 SP smallMod BP
        J ell sizes prime Vs mu * (Fintype.card Torus:ℝ) : ℝ):ℂ) *
      ∑ d : Shared,∑ psi : AddChar Torus ℂ,
        B d psi
          (fun a => (AddChar.complexBasis Torus).repr
            (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
              J ell sizes prime q Vs ss d U a) psi)
          (fun a => (AddChar.complexBasis Torus).repr
            (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
              J ell sizes prime q Vs tt d F a) psi)

/-- Quantitative actual SMALL/OLD transfer. This is a finite transfer
lemma; the arithmetic hypothesis is discharged by the canonical
comparison in the downstream theorem. No conditional unit-energy
hypothesis or per-frequency bound on the endpoint tests is imposed. -/
theorem source_original_B26_SMALL_OLD_TRANSFER434
    (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (Vs : SG → ℝ) (hVs : ∀ g,0 < Vs g)
    (mu : (g : BG) → BP g → ℝ) (hmu : ∀ g p,0 < mu g p)
    (eps : ℝ) (heps : 0 ≤ eps)
    (B : Shared → AddChar Torus ℂ → (Active → ℂ) → (Active → ℂ) → ℂ)
    (hB : ∀ d psi u v, ‖B d psi u v‖^2 ≤
      eps * sourceOriginalB26ActiveEnergy434 BP J ell mu u *
        sourceOriginalB26ActiveEnergy434 BP J ell mu v)
    (U F : Small → Active → Old → ℂ) :
    ‖sourceOriginalB26SmallOldLiftedPair434 SP smallMod BP bigMod
      J ell sizes prime q Vs mu B U F‖^2 ≤
    eps * (memorySmallGroupConditioningConstant (SG := SG) ell q Vs)^2 *
      sourceOriginalB26SectorEnergy434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu U *
      sourceOriginalB26SectorEnergy434 SP smallMod BP bigMod
        J ell cap sizes hsizes prime Vs mu F := by
  classical
  let C := memorySmallGroupConditioningConstant (SG := SG) ell q Vs
  let EU := sourceOriginalB26SectorEnergy434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs mu U
  let EF := sourceOriginalB26SectorEnergy434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs mu F
  let w := sourceOriginalB26SectorConstant434 SP smallMod BP
    J ell sizes prime Vs mu * (Fintype.card Torus:ℝ)
  let PU := fun (ss : SmallPerm) (d : Shared) (psi : AddChar Torus ℂ) (a : Active) =>
    (AddChar.complexBasis Torus).repr
      (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs ss d U a) psi
  let PF := fun (tt : SmallPerm) (d : Shared) (psi : AddChar Torus ℂ) (a : Active) =>
    (AddChar.complexBasis Torus).repr
      (sourceOriginalB26SmallLift434 SP smallMod BP bigMod
        J ell sizes prime q Vs tt d F a) psi
  let z := fun (ss tt : SmallPerm) =>
    (w:ℂ) * ∑ d : Shared,∑ psi : AddChar Torus ℂ,B d psi (PU ss d psi) (PF tt d psi)
  have hw : 0 ≤ w := mul_nonneg
    (source_original_B26_sector_constant_nonneg434 SP smallMod BP
      J ell sizes prime Vs hVs mu hmu) (Nat.cast_nonneg _)
  have hC : 0 ≤ C :=
    source_original_B26_small_conditioning_constant_nonneg434 ell q hq1 Vs hVs
  have hEU : 0 ≤ EU := source_original_B26_sector_energy_nonneg434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs hVs mu hmu U
  have hEF : 0 ≤ EF := source_original_B26_sector_energy_nonneg434 SP smallMod BP bigMod
    J ell cap sizes hsizes prime Vs hVs mu hmu F
  have hz (ss tt : SmallPerm) : ‖z ss tt‖^2 ≤ (eps*C^2)*EU*EF := by
    let H := Shared × AddChar Torus ℂ
    let eU := fun h : H => sourceOriginalB26ActiveEnergy434 BP J ell mu (PU ss h.1 h.2)
    let eF := fun h : H => sourceOriginalB26ActiveEnergy434 BP J ell mu (PF tt h.1 h.2)
    have heU (h : H) : 0 ≤ eU h :=
      source_original_B26_active_energy_nonneg434 BP J ell mu hmu _
    have heF (h : H) : 0 ≤ eF h :=
      source_original_B26_active_energy_nonneg434 BP J ell mu hmu _
    have hh := Green64Analytic.CorrelationSquare.source_original_B26_homogeneous_shared_integration434
      (fun _ : H => w) eU eF
      (fun h => B h.1 h.2 (PU ss h.1 h.2) (PF tt h.1 h.2))
      eps (fun _ => hw) heU heF heps (fun h => hB h.1 h.2 _ _)
    have hU : (∑ h : H,w*eU h) ≤ C*EU := by
      have h := source_original_B26_SMALL_OLD_FOURIER_ACTIVE_ENERGY434
        SP smallMod BP bigMod J ell cap sizes hsizes prime
        q hq hq1 Vs hVs mu hmu ss U
      simpa only [H,eU,PU,C,EU,w,Fintype.sum_prod_type,Finset.mul_sum] using h
    have hF : (∑ h : H,w*eF h) ≤ C*EF := by
      have h := source_original_B26_SMALL_OLD_FOURIER_ACTIVE_ENERGY434
        SP smallMod BP bigMod J ell cap sizes hsizes prime
        q hq hq1 Vs hVs mu hmu tt F
      simpa only [H,eF,PF,C,EF,w,Fintype.sum_prod_type,Finset.mul_sum] using h
    have hProduct := mul_le_mul hU hF
      (Finset.sum_nonneg (fun h _ => mul_nonneg hw (heF h))) (mul_nonneg hC hEU)
    have hzEq : ‖z ss tt‖^2 =
        ‖∑ h : H,(w:ℂ)*B h.1 h.2 (PU ss h.1 h.2) (PF tt h.1 h.2)‖^2 := by
      simp only [z,H,Fintype.sum_prod_type,Finset.mul_sum]
    rw [hzEq]
    calc
      _ ≤ eps*(∑ h : H,w*eU h)*(∑ h : H,w*eF h) := hh
      _ = eps*((∑ h : H,w*eU h)*(∑ h : H,w*eF h)) := by ring
      _ ≤ eps*((C*EU)*(C*EF)) := mul_le_mul_of_nonneg_left hProduct heps
      _ = (eps*C^2)*EU*EF := by ring
  have hAvg := Green64Analytic.CorrelationSquare.source_original_B26_big_permutation_mean_square434
    (G := SG) (J+ell) z (eps*C^2) EU EF
    (mul_nonneg heps (sq_nonneg C)) hEU hEF hz
  simpa only [sourceOriginalB26SmallOldLiftedPair434,z,w,PU,PF,C,EU,EF,
    bigEndpointPairMass,Green64SmallHaar.groupPermutationPairMass] using hAvg
end Green64FullPhysicalE

end

end

/-! ## SourceOriginalB26CanonicalSmallOldComparison -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

/-- The genuine signed comparison block, including both normalized
BIG endpoint permutations and both full active endpoint tests. -/
def sourceOriginalB26CanonicalComparisonForm434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) : ℂ :=
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
    ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell),
    ∑ ν ∈ family,sign ν * sourceOriginalB26PermutedFullPairing434
      data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
      (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
      (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν

theorem source_original_B26_small_tuple_positive434
    {SG : Type} [Fintype SG] [DecidableEq SG]
    (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : SG) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    (J ell : ℕ) (d : SourceOriginalB26SharedTuple434 SP J ell) :
    0 < sourceOriginalB26SmallTupleD434 SP smallMod J ell d := by
  exact Finset.prod_pos (fun g _ => Finset.prod_pos (fun i _ => NeZero.pos _))

/-- The canonical comparison term at the literal SMALL/OLD Fourier
call site. Original P_d maps, both endpoint permutations, the complete
OLD torus, the genuine family and four shared endpoint signs remain. -/
def sourceOriginalB26CanonicalSmallOldComparisonPair434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let bigMod := fun (_ : G) (p : BP _) => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP bigMod data.Vbig
  sourceOriginalB26SmallOldLiftedPair434 SP smallMod BP bigMod
    J ell sizes prime q data.Vsmall mu
    (fun d psi => sourceOriginalB26CanonicalComparisonForm434
      data blockA blockB J ell m hmJ Q h xi ζ
      (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
      o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)) U F
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26AuxBanPairing -/

section

open Filter
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

noncomputable def sourceOriginalB26PermutedAuxBanPairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ d.Tb g}),NeZero p.val]
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi ζ : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) d.Vbig
  let Active := ((g : G) → Fin (J+ell) → BP g)
  ∑ s : Active,∑ v : Active,
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v (sigma ν) (tau ν) *
      (star (sourceTest ν s)*targetTest ν v*
        sourceOriginalB26CanonicalAuxBanError434 d.Tb d.Vbig J ell m hmJ ν
          Q (hA ν) (hB ν) xi (c ν) s v (sigma ν) (tau ν) ζ (theta ν) (orientation ν) k)


def sourceOriginalB26CanonicalAuxBanForm434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) : ℂ :=
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
    ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell),
    ∑ ν ∈ family,sign ν * sourceOriginalB26PermutedAuxBanPairing434
      data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
      (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
      (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26PhysicalTiltPairings -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 24000000

noncomputable def sourceOriginalB26TiltedFullActiveEnergy434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J)
    (F : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℝ :=
  let mu := physicalSourceMuTilde
    (fun g : G => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) q N d.Vbig
  ∑ s : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}),
    (∏ g : G,∏ i : Fin (J+ell),mu g (s g i))*‖F ν s‖^2

/-- The physical endpoint test required by the exact shared-law change
of measure. It depends on the entire endpoint, pattern and permutation. -/
def sourceOriginalB26PhysicalTiltTest434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (q : ℝ) (N J ell m : ℕ) (hmJ : m ≤ J)
    (sigma : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (U : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (s : (g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) : ℂ :=
  (sourceOriginalB26TiltEndpoint434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell m
    (sourceOriginalProbeMemoryPattern434 J m hmJ ν)
    (sourceOriginalB26PhysicalTiltRoot434 (fun g => {p : ℕ // p ∈ data.Tb g})
      (fun _ p => p.val) q N) (sigma ν) s:ℂ) * U ν s
noncomputable def sourceOriginalB26TiltedPermutedFullPairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi ζ : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N d.Vbig
  let Active := ((g : G) → Fin (J+ell) → BP g)
  ∑ s : Active,∑ v : Active,
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v (sigma ν) (tau ν) *
      (star (sourceTest ν s)*targetTest ν v*
        sourceOriginalB26CanonicalComparisonValue434 d.Tb d.Vbig J ell m hmJ ν
          Q (hA ν) (hB ν) xi (c ν) s v (sigma ν) (tau ν) ζ (theta ν) (orientation ν) k)


theorem sourceOriginalB26TiltedPermutedFullPairing434_eq_harmonic434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ d.Tb g}),NeZero p.val]
    (q : ℝ) (N : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi ζ : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (hb : ∀ g (p : {p : ℕ // p ∈ d.Tb g}),0 < physicalSourceBaseline
      (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) q N g p) :
    sourceOriginalB26TiltedPermutedFullPairing434 d q N J ell m hmJ Q hA hB xi ζ c theta orientation k sigma tau
      sourceTest targetTest ν =
    sourceOriginalB26PermutedFullPairing434 d J ell m hmJ Q hA hB xi ζ c theta orientation k sigma tau
      (sourceOriginalB26PhysicalTiltTest434 d q N J ell m hmJ sigma sourceTest)
      (sourceOriginalB26PhysicalTiltTest434 d q N J ell m hmJ tau targetTest) ν := by
  classical
  unfold sourceOriginalB26TiltedPermutedFullPairing434 sourceOriginalB26PermutedFullPairing434
  dsimp only
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [source_original_B26_PHYSICAL_TILT_JOINT_DENSITY434
    (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) q N d.Vbig hb
    J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t (sigma ν) (tau ν)]
  dsimp only [sourceOriginalB26PhysicalTiltTest434]
  have hstar (a : ℝ) : star (a:ℂ) = (a:ℂ) := Complex.conj_ofReal a
  simp only [star_mul,hstar]
  ring

noncomputable def sourceOriginalB26TiltedPermutedAuxBanPairing434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ d.Tb g}),NeZero p.val]
    (q : ℝ) (N : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi ζ : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m) : ℂ :=
  let BP : G → Type := fun g => {p : ℕ // p ∈ d.Tb g}
  let mu := physicalSourceMuTilde BP (fun _ p => p.val) q N d.Vbig
  let Active := ((g : G) → Fin (J+ell) → BP g)
  ∑ s : Active,∑ v : Active,
    ((∏ g : G,∏ i : Fin (J+ell),mu g (s g i):ℝ):ℂ) *
      sourceOriginalB26FrozenFreshLaw434 BP J ell m mu
        (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s v (sigma ν) (tau ν) *
      (star (sourceTest ν s)*targetTest ν v*
        sourceOriginalB26CanonicalAuxBanError434 d.Tb d.Vbig J ell m hmJ ν
          Q (hA ν) (hB ν) xi (c ν) s v (sigma ν) (tau ν) ζ (theta ν) (orientation ν) k)


theorem sourceOriginalB26TiltedPermutedAuxBanPairing434_eq_harmonic434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (d : SourceComparisonData434 ι G cfg x L Y Hprime)
    [∀ g (p : {p : ℕ // p ∈ d.Tb g}),NeZero p.val]
    (q : ℝ) (N : ℕ)
    (J ell m : ℕ) (hmJ : m ≤ J) (Q : ℕ)
    (hA hB : SourceOriginalProbePattern434 G m → ℝ) (xi ζ : ℝ)
    (c : SourceOriginalProbePattern434 G m → ℕ)
    (theta : SourceOriginalProbePattern434 G m → ℝ)
    (orientation : SourceOriginalProbePattern434 G m → ℤ) (k : ℤ)
    (sigma tau : SourceOriginalProbePattern434 G m → BigGroupPerm (BG := G) (J+ell))
    (sourceTest targetTest : (ν : SourceOriginalProbePattern434 G m) →
      ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ d.Tb g}) → ℂ)
    (ν : SourceOriginalProbePattern434 G m)
    (hb : ∀ g (p : {p : ℕ // p ∈ d.Tb g}),0 < physicalSourceBaseline
      (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) q N g p) :
    sourceOriginalB26TiltedPermutedAuxBanPairing434 d q N J ell m hmJ Q hA hB xi ζ c theta orientation k sigma tau
      sourceTest targetTest ν =
    sourceOriginalB26PermutedAuxBanPairing434 d J ell m hmJ Q hA hB xi ζ c theta orientation k sigma tau
      (sourceOriginalB26PhysicalTiltTest434 d q N J ell m hmJ sigma sourceTest)
      (sourceOriginalB26PhysicalTiltTest434 d q N J ell m hmJ tau targetTest) ν := by
  classical
  unfold sourceOriginalB26TiltedPermutedAuxBanPairing434 sourceOriginalB26PermutedAuxBanPairing434
  dsimp only
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [source_original_B26_PHYSICAL_TILT_JOINT_DENSITY434
    (fun g => {p : ℕ // p ∈ d.Tb g}) (fun _ p => p.val) q N d.Vbig hb
    J ell m (sourceOriginalProbeMemoryPattern434 J m hmJ ν) s t (sigma ν) (tau ν)]
  dsimp only [sourceOriginalB26PhysicalTiltTest434]
  have hstar (a : ℝ) : star (a:ℂ) = (a:ℂ) := Complex.conj_ofReal a
  simp only [star_mul,hstar]
  ring

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26AveragedAuxBanSaving -/

section

open Filter Real
open scoped BigOperators Classical
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- Actual auxiliary/ACTIVE ban correction in the full harmonic bilinear
pairing, coherently summed over the genuine family and both normalized
BIG permutation averages. The logarithmic saving is proved from the
exponential prime floor and the actual canonical K bound. -/
theorem eventually_source_original_B26_AVERAGED_ALL_NU_AUX_BAN434
    (cfg : SourceComparisonFixed434) (Cslots Bgoal : ℝ) (Cq Cxi : ℕ) :
    ∀ᶠ L : ℝ in atTop,
    ∀ {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
      (x Y Hprime : ℝ) (data : SourceComparisonData434 ι G cfg x L Y Hprime)
      [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
      (hVbig : ∀ g,data.Vbig g = ∑ p ∈ data.Tb g,1/(p:ℝ))
      (hTbLower : ∀ g,∀ p ∈ data.Tb g,Real.exp (L^cfg.cexp) ≤ (p:ℝ))
      (blockA blockB : Finset G) (hBlocks : Disjoint blockA blockB)
      (J ell m : ℕ) (hmJ : m ≤ J) (hm : m ≤ cfg.tmax)
      (hSlots : ((J+ell:ℕ):ℝ) ≤ L^Cslots)
      (Q : ℕ) (h xi : ℝ) (hh : 0 < h) (hxi : 0 < xi)
      (hQ : (Q:ℝ) ≤ L^Cq) (hXi : xi⁻¹ ≤ L^Cxi)
      (ζ theta : ℝ) (o k : ℤ) (ho : o=1 ∨ o= -1)
      (epsSrc epsTgt : Bool) (dsmall : ℕ)
      (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ),
    let BP := fun g => {p : ℕ // p ∈ data.Tb g}
    let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
    ‖sourceOriginalB26CanonicalAuxBanForm434 data blockA blockB
      J ell m hmJ Q h xi ζ theta o k epsSrc epsTgt dsmall u v‖^2 ≤
      L^(-Bgoal)*sourceOriginalB26ActiveEnergy434 BP J ell mu u*
        sourceOriginalB26ActiveEnergy434 BP J ell mu v := by
  let E : ℝ := (cfg.tmax:ℝ)*cfg.C0*Real.log 2
  let Dper : ℝ := Bgoal/2+E
  have hc : 0 < cfg.cexp := cfg.haexp.trans (cfg.hab.trans cfg.hbc)
  filter_upwards [eventually_source_original_B26_canonical_aux_ban_saving434
    cfg.cexp cfg.vmin ((cfg.tmax:ℝ)*cfg.C0) Cslots Dper Cq Cxi
    hc cfg.hv (mul_nonneg (Nat.cast_nonneg _) cfg.hC0),
    eventually_ge_atTop (1:ℝ)] with L hSave hL
  intro ι G instI instDI instG instDG x Y Hprime data instNZ
    hVbig hTbLower blockA blockB hBlocks J ell m hmJ hm hSlots
    Q h xi hh hxi hQ hXi ζ theta o k ho epsSrc epsTgt dsmall u v
  classical
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let mu := sourceOriginalJointHarmonicMu434 BP (fun _ p => p.val) data.Vbig
  let Active := (g : G) → Fin (J+ell) → BP g
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  let EU := sourceOriginalB26ActiveEnergy434 BP J ell mu u
  let EV := sourceOriginalB26ActiveEnergy434 BP J ell mu v
  let delta := L^(-Dper)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hdelta : 0 ≤ delta := Real.rpow_nonneg hLp.le _
  have hVpos (g : G) : 0 < data.Vbig g := cfg.hv.trans_le (data.hVbig g)
  have hVEq (g : G) : data.Vbig g = ∑ p : BP g,1/(p.val:ℝ) := by
    rw [hVbig]
    simpa [BP] using (Finset.sum_coe_sort (data.Tb g) (fun p : ℕ => 1/(p:ℝ))).symm
  obtain ⟨hmuNN,hmuMass⟩ := source_original_joint_harmonic_normalized434
    BP (fun _ p => p.val) data.Vbig hVpos hVEq
  have hmu (g : G) (p : BP g) : 0 < mu g p := by
    have hp : (0:ℝ) < (p.val:ℝ) := by exact_mod_cast (data.hTbPrime g p.val p.property).pos
    exact div_pos (one_div_pos.mpr hp) (hVpos g)
  have hEU : 0 ≤ EU := source_original_B26_active_energy_nonneg434 BP J ell mu hmu u
  have hEV : 0 ≤ EV := source_original_B26_active_energy_nonneg434 BP J ell mu hmu v
  have hGroups : ((blockA.card+blockB.card:ℕ):ℝ) ≤ cfg.C0*Real.log L := by
    have hb : blockA.card+blockB.card ≤ Fintype.card G := by
      rw [← Finset.card_union_of_disjoint hBlocks]
      exact Finset.card_le_univ _
    exact (by exact_mod_cast hb : ((blockA.card+blockB.card:ℕ):ℝ) ≤ (Fintype.card G:ℝ)).trans
      data.hBigGroups
  have hPattern (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ((ν.1.card+ν.2.card:ℕ):ℝ) ≤ ((cfg.tmax:ℝ)*cfg.C0)*Real.log L := by
    have hmem := (source_original_two_block_probe_pattern_mem434 blockA blockB m _ _).mp hν
    have hNA : ν.1.card ≤ blockA.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.1
    have hNB : ν.2.card ≤ blockB.card*m := by
      simpa [sourceOriginalProbeBlock434] using Finset.card_le_card hmem.2.2.2
    have hNat : ν.1.card+ν.2.card ≤ m*(blockA.card+blockB.card) := by nlinarith only [hNA,hNB]
    calc
      _ ≤ (m:ℝ)*((blockA.card+blockB.card:ℕ):ℝ) := by exact_mod_cast hNat
      _ ≤ (m:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_left hGroups (Nat.cast_nonneg _)
      _ ≤ (cfg.tmax:ℝ)*(cfg.C0*Real.log L) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hm)
          (mul_nonneg cfg.hC0 (Real.log_nonneg hL))
      _ = _ := by ring
  have hPer (sigma tau : BigGroupPerm (BG := G) (J+ell))
      (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
      ‖sourceOriginalB26PermutedAuxBanPairing434 data J ell m hmJ Q
        (fun _ => h) (fun _ => h) xi ζ (fun _ => dsmall)
        (fun _ => theta) (fun _ => o) k (fun _ => sigma) (fun _ => tau)
        (fun _ => u) (fun _ => v) ν‖^2 ≤ delta^2*EU*EV := by
    apply source_original_B26_permuted_uniform_bilinear434 BP J ell m hmJ ν
      mu hmuNN hmuMass sigma tau delta hdelta u v
    intro s t
    exact hSave data.Tb data.Vbig J ell m hmJ ν
      (source_original_probe_memory_actual_pattern_disjoint434 blockA blockB hBlocks m ν hν)
      Q h h xi hh hh hxi hVbig data.hVbig hTbLower (hPattern ν hν)
      hSlots hQ hXi dsmall s t sigma tau ζ theta o k ho
  have hmE : (m:ℝ)*cfg.C0*Real.log 2 ≤ E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) cfg.hC0)
      (Real.log_nonneg (by norm_num))
  have hCard : (family.card:ℝ) ≤ L^E :=
    (source_original_probe_family_log_power_card434 blockA blockB m L cfg.C0 hL hGroups).trans
      (Real.rpow_le_rpow_of_exponent_le hL hmE)
  have hBudget : (family.card:ℝ)^2*delta^2 ≤ L^(-Bgoal) := by
    calc
      _ ≤ (L^E)^2*(L^(-Dper))^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hCard 2) (sq_nonneg _)
      _ = L^(-Bgoal) := by
        rw [← Real.rpow_two,← Real.rpow_two,← Real.rpow_mul hLp.le,
          ← Real.rpow_mul hLp.le,← Real.rpow_add hLp]
        congr 1
        dsimp [Dper]
        ring
  let z := fun (sigma tau : BigGroupPerm (BG := G) (J+ell)) =>
    ∑ ν ∈ family,sign ν * sourceOriginalB26PermutedAuxBanPairing434
      data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
      (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
      (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν
  have hz (sigma tau : BigGroupPerm (BG := G) (J+ell)) :
      ‖z sigma tau‖^2 ≤ L^(-Bgoal)*EU*EV := by
    have hEach (ν : SourceOriginalProbePattern434 G m) (hν : ν ∈ family) :
        ‖sign ν * sourceOriginalB26PermutedAuxBanPairing434
          data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
          (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
          (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν‖^2 ≤
        (1:ℝ)^2*(delta^2*EU*EV) := by
      have hs : ‖sign ν‖=1 := by
        dsimp only [sign]
        rw [norm_mul]
        split_ifs <;> simp
      rw [norm_mul,hs,one_mul,one_pow,one_mul]
      exact hPer sigma tau ν hν
    have hs := source_original_true_finite_weighted_minor_square434
      family
      (fun ν => sign ν * sourceOriginalB26PermutedAuxBanPairing434
        data J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
        (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
        (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν)
      (fun _ => (1:ℝ)) (delta^2*EU*EV)
      (mul_nonneg (mul_nonneg (sq_nonneg delta) hEU) hEV)
      (by intro ν hν;norm_num) hEach
    have hs' : ‖z sigma tau‖^2 ≤ (family.card:ℝ)^2*(delta^2*EU*EV) := by
      simpa only [z,Finset.sum_const,nsmul_eq_mul,mul_one] using hs
    calc
      _ ≤ (family.card:ℝ)^2*(delta^2*EU*EV) := hs'
      _ = ((family.card:ℝ)^2*delta^2)*(EU*EV) := by ring
      _ ≤ L^(-Bgoal)*(EU*EV) := mul_le_mul_of_nonneg_right hBudget (mul_nonneg hEU hEV)
      _ = _ := by ring
  exact source_original_B26_big_permutation_mean_square434 (J+ell) z
    (L^(-Bgoal)) EU EV (Real.rpow_nonneg hLp.le _) hEU hEV hz
end Green64Analytic.CorrelationSquare

end

/-! ## SourceOriginalB26CanonicalSmallOldAuxBan -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false
set_option maxHeartbeats 32000000

/-- The canonical comparison term at the literal SMALL/OLD Fourier
call site. Original P_d maps, both endpoint permutations, the complete
OLD torus, the genuine family and four shared endpoint signs remain. -/
def sourceOriginalB26CanonicalSmallOldAuxBanPair434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let bigMod := fun (_ : G) (p : BP _) => p.val
  let mu := sourceOriginalJointHarmonicMu434 BP bigMod data.Vbig
  sourceOriginalB26SmallOldLiftedPair434 SP smallMod BP bigMod
    J ell sizes prime q data.Vsmall mu
    (fun d psi => sourceOriginalB26CanonicalAuxBanForm434
      data blockA blockB J ell m hmJ Q h xi ζ
      (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
      o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)) U F

end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalB26TiltedCanonicalForms -/

section

open Filter Real
open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE
set_option autoImplicit false

def sourceOriginalB26TiltedCanonicalComparisonForm434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) : ℂ :=
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
    ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell),
    ∑ ν ∈ family,sign ν * sourceOriginalB26TiltedPermutedFullPairing434
      data q N J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
      (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
      (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν

def sourceOriginalB26TiltedCanonicalAuxBanForm434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (q : ℝ) (N : ℕ)
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (Q : ℕ) (h xi ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (dsmall : ℕ)
    (u v : ((g : G) → Fin (J+ell) → {p : ℕ // p ∈ data.Tb g}) → ℂ) : ℂ :=
  let family := sourceOriginalTwoBlockProbePatterns434 blockA blockB m
  let shared := fun ν : SourceOriginalProbePattern434 G m =>
    ((Fintype.card ι)*J)+∑ g : G,(sourceOriginalProbeSharedSlots434 J ell m hmJ ν g).card
  let sign := fun ν : SourceOriginalProbePattern434 G m =>
    (if epsSrc then (-1:ℂ)^(shared ν) else 1)*
    (if epsTgt then (-1:ℂ)^(shared ν) else 1)
  (bigEndpointPairMass (BG := G) (J+ell):ℂ) *
    ∑ sigma : BigGroupPerm (BG := G) (J+ell),
    ∑ tau : BigGroupPerm (BG := G) (J+ell),
    ∑ ν ∈ family,sign ν * sourceOriginalB26TiltedPermutedAuxBanPairing434
      data q N J ell m hmJ Q (fun _ => h) (fun _ => h) xi ζ
      (fun _ => dsmall) (fun _ => theta) (fun _ => o) k
      (fun _ => sigma) (fun _ => tau) (fun _ => u) (fun _ => v) ν

def sourceOriginalB26TiltedCanonicalSmallOldComparisonPair434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let bigMod := fun (_ : G) (p : BP _) => p.val
  let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
  sourceOriginalB26SmallOldLiftedPair434 SP smallMod BP bigMod
    J ell sizes prime q data.Vsmall mu
    (fun d psi => sourceOriginalB26TiltedCanonicalComparisonForm434
      data q N blockA blockB J ell m hmJ Q h xi ζ
      (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
      o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)) U F

def sourceOriginalB26TiltedCanonicalSmallOldAuxBanPair434
    {ι G : Type} [Fintype ι] [DecidableEq ι] [Fintype G] [DecidableEq G]
    {cfg : SourceComparisonFixed434} {x L Y Hprime : ℝ}
    (data : SourceComparisonData434 ι G cfg x L Y Hprime)
    (N : ℕ)
    (SP : ι → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
    (smallMod : (g : ι) → SP g → ℕ) [∀ g p,NeZero (smallMod g p)]
    [∀ g (p : {p : ℕ // p ∈ data.Tb g}),NeZero p.val]
    (blockA blockB : Finset G) (J ell m : ℕ) (hmJ : m ≤ J)
    (sizes : G → ℕ) (prime : (g : G) → Fin (sizes g) → {p : ℕ // p ∈ data.Tb g})
    (Q : ℕ) (h xi q ζ theta : ℝ) (o k : ℤ) (epsSrc epsTgt : Bool)
    (U F : Green64SmallHaar.GroupState SP smallMod (J+ell) →
      SourceOriginalB26Active434 (fun g => {p : ℕ // p ∈ data.Tb g}) J ell →
      SourceOriginalB26OldResidues434 (fun g => {p : ℕ // p ∈ data.Tb g})
        (fun _ p => p.val) sizes prime → ℂ) : ℂ :=
  let BP := fun g => {p : ℕ // p ∈ data.Tb g}
  let bigMod := fun (_ : G) (p : BP _) => p.val
  let mu := physicalSourceMuTilde BP bigMod q N data.Vbig
  sourceOriginalB26SmallOldLiftedPair434 SP smallMod BP bigMod
    J ell sizes prime q data.Vsmall mu
    (fun d psi => sourceOriginalB26TiltedCanonicalAuxBanForm434
      data q N blockA blockB J ell m hmJ Q h xi ζ
      (theta+sourceOriginalB26ModeAngle434 SP smallMod BP bigMod sizes prime psi/(2*Real.pi))
      o k epsSrc epsTgt (sourceOriginalB26SmallTupleD434 SP smallMod J ell d)) U F

end Green64Analytic.CorrelationSquare

end

end

