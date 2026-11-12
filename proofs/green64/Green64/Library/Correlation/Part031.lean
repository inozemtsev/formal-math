module

public import Green64.Library.Analysis.Estimates.GhostPrimeFiber
public import Green64.Library.Correlation.PhysicalGhostOutputSeparation
public import Green64.Library.Correlation.Part030
public import Green64.Library.Correlation.Part005
public import Green64.Library.Weights.Part002
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Green64.Library.Correlation.PhysicalGhostWitnessCollapse

@[expose] public section

/-!
# Correlation / Part031

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalBackgroundPrimeTensor -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem source_original_FINITE_product_gate434
    {I : Type} [Fintype I] (P : I → Prop) [DecidablePred P] (w : I → ℂ) :
    (∏ i,if P i then w i else 0) = if ∀ i,P i then ∏ i,w i else 0 := by
  classical
  by_cases h : ∀ i,P i
  · simp [h]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)
local notation "B" => sourceOriginalNumericBackground434 BP bm background

abbrev SourceOriginalGhostBackgroundPrimeChoice434 :=
  (g : BG) → SourceOriginalPrimeFiberChoice434 (bm g)
    (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
    (Finset.univ.filter (fun p => p ∈ background g))

def sourceOriginalBackgroundPrimeEquiv434 :
    SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y ≃
      SourceOriginalGhostBackgroundPrimeChoice434 SP sm BP bm M background y := by
  -- Matching these families only requires unfolding their abbreviations.
  with_reducible
    exact Equiv.piCongrRight (fun g => sourceOriginalPrimeFiberEquiv434 (bm g)
      (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∈ background g))
      (Finset.univ.filter (fun p => p ∈ background g)))

def sourceOriginalBackgroundPrimeWeight434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : SourceOriginalGhostBackgroundPrimeChoice434 SP sm BP bm M background y)
    (g : BG) (p : BP g) : ℂ :=
  sourceOriginalGroupPrimeBirthWeight434 (bm g)
    ((((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter
      (fun z => z.1 ∈ background g)).filter (fun z => z.1=p))
    (-((sourceVisitEta q N i:ℝ):ℂ)/(rho:ℂ))
    (((sourceVisitQ q N i:ℝ):ℂ)/(rho:ℂ)^2)
    (-((sourceVisitEta q N i:ℝ):ℂ)*(V g:ℂ)/(rho:ℂ))
    (fun t => (mu g t:ℂ)) (sourceOriginalRestrictedPrimeBirthLift434 (bm g) _ _ (a g p))

/-- All original background G coefficients split over labelled primes,
including their source retention and birth normalization. -/
theorem source_original_PHYSICAL_G_BACKGROUND_prime_fiber_coefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y) :
    sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu a =
    ∏ g,∏ p,sourceOriginalBackgroundPrimeWeight434 SP sm BP bm M background y q rho N i V mu
      (sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y a) g p := by
  unfold sourceOriginalGhostBackgroundCoefficient434 sourceOriginalBackgroundPrimeWeight434
  apply Finset.prod_congr rfl
  intro g hg
  exact source_original_GROUP_G_prime_fiber_weight434 (bm g) _ _ _ _ _ _ (a g)

/-- The genuine numerical unseen gate also separates into prime
coordinates. The same seen set is used; no independence is assumed. -/
theorem source_original_PHYSICAL_G_BACKGROUND_prime_fiber_gate434
    (seen : Finset ℕ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y) :
    (∀ g,∀ t ∈ (a g).2.1,bm g t ∉ seen ∩ B) ↔
      (∀ g p,∀ t ∈
        (sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y a g p).2.1,
          bm g t ∉ seen ∩ B) := by
  change (∀ g,∀ t ∈ (a g).2.1,bm g t ∉ seen ∩ B) ↔
    (∀ g p,∀ t ∈ (a g).2.1.filter (fun t => t=p),bm g t ∉ seen ∩ B)
  constructor
  · intro h g p t ht
    exact h g t (Finset.mem_filter.mp ht).1
  · intro h g t ht
    exact h g t t (Finset.mem_filter.mpr ⟨ht,rfl⟩)

theorem source_original_PHYSICAL_G_BACKGROUND_prime_fiber_masked_coefficient434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ)
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y) :
    (if ∀ g,∀ t ∈ (a g).2.1,bm g t ∉ seen ∩ B then
      sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu a
      else 0) =
    ∏ g,∏ p,
      if ∀ t ∈ (sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y a g p).2.1,
        bm g t ∉ seen ∩ B then
        sourceOriginalBackgroundPrimeWeight434 SP sm BP bm M background y q rho N i V mu
          (sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y a) g p
      else 0 := by
  simp_rw [source_original_FINITE_product_gate434]
  have hg := source_original_PHYSICAL_G_BACKGROUND_prime_fiber_gate434
    SP sm BP bm M background y seen a
  by_cases h : ∀ g,∀ t ∈ (a g).2.1,bm g t ∉ seen ∩ B
  · rw [if_pos h,if_pos (hg.mp h)]
    exact source_original_PHYSICAL_G_BACKGROUND_prime_fiber_coefficient434
      SP sm BP bm M background y q rho N i V mu a
  · rw [if_neg h,if_neg (fun hh => h (hg.mpr hh))]

/-- A tensor product of the ACTUAL prime-local G weights and unseen
gates. Its terminal observation still depends jointly on both G choices,
the full physical output and reconstructed numerical seen set. -/
def sourceOriginalBackgroundPrimeTensorRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ ab : SourceOriginalGhostBackgroundPrimeChoice434 SP sm BP bm M background y ×
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    let a := (sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1
    ((∏ g,∏ p,
      if ∀ t ∈ (ab.1 g p).2.1,bm g t ∉ seen ∩ B then
        sourceOriginalBackgroundPrimeWeight434 SP sm BP bm M background y q rho N i V mu ab.1 g p
      else 0) *
      (if ∀ g,∀ t ∈ (ab.2 g).2.1,bm g t ∉ seen \ B then
        sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu ab.2
      else 0)) *
    F (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y a ab.2)
      (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1)) ∪
        ((seen \ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)))

/-- Exact prime-coordinate tensorization of the literal separated-seen
G row. This preserves an arbitrary joint F and pays no cardinality. -/
theorem source_original_PHYSICAL_G_BACKGROUND_prime_tensor_row434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm M background y q rho N i V mu seen F =
    sourceOriginalBackgroundPrimeTensorRow434 SP sm BP bm M background y q rho N i V mu seen F := by
  unfold sourceOriginalGhostBackgroundSeenRow434 sourceOriginalBackgroundPrimeTensorRow434
  symm
  apply Fintype.sum_equiv (Equiv.prodCongr
    (sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm (Equiv.refl _))
  intro ab
  change _ =
    if ((∀ g,∀ p ∈
      ((sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1 g).2.1,
        bm g p ∉ seen ∩ B) ∧ (∀ g,∀ p ∈ (ab.2 g).2.1,bm g p ∉ seen \ B)) then
      (sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu
        ((sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1) *
       sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu ab.2) *
      F (sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y
        ((sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1) ab.2)
        (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g =>
          ((sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1 g).2.1)) ∪
          ((seen \ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (ab.2 g).2.1)))
    else 0
  have hc := source_original_PHYSICAL_G_BACKGROUND_prime_fiber_masked_coefficient434
    SP sm BP bm M background y q rho N i V mu seen
    ((sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1)
  simp only [Equiv.apply_symm_apply] at hc
  rw [←hc]
  by_cases hb : ∀ g,∀ t ∈
    ((sourceOriginalBackgroundPrimeEquiv434 SP sm BP bm M background y).symm ab.1 g).2.1,
      bm g t ∉ seen ∩ B
  · by_cases ha : ∀ g,∀ t ∈ (ab.2 g).2.1,bm g t ∉ seen \ B
    · rw [if_pos hb,if_pos ha,if_pos ⟨hb,ha⟩]
    · rw [if_pos hb,if_neg ha,if_neg (fun hh => ha hh.2)]
      simp only [mul_zero,zero_mul]
  · rw [if_neg hb]
    simp only [zero_mul]
    rw [if_neg (fun hh => hb hh.1)]

/-- Direct link back to the original physical marked G, with exactly
the already established reachability and source-capacity conditions. -/
theorem source_original_PHYSICAL_MARKED_G_background_prime_tensor434
    (cap : BG → ℕ) (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F =
    sourceOriginalBackgroundPrimeTensorRow434 SP sm BP bm M background
      (physicalFockProjection SP sm BP bm M cap x) q rho N i V mu seen F := by
  rw [source_original_PHYSICAL_MARKED_G_background_split434
    SP sm BP bm M background cap hi q rho N i V mu x seen hx hcap F,
    source_original_PHYSICAL_G_background_seen_row434 SP sm BP bm M background _ hi,
    source_original_PHYSICAL_G_BACKGROUND_prime_tensor_row434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostActiveRemoval -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)
local notation "removed" => sourceOriginalRemovePendingBackground434 SP sm BP bm M background y

theorem source_original_G_ACTIVE_pending_removal434 (g : BG) :
    ((removed.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) =
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∉ background g)) := by
  ext z
  simp only [sourceOriginalRemovePendingBackground434,Finset.mem_filter,
    Multiset.mem_toFinset,Multiset.mem_filter]
  tauto

theorem source_original_G_ACTIVE_zero_removal434 (g : BG) :
    (((removed.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∉ background g)) =
      (((y.2 g).2.toFinset.filter (fun z => z.2=0)).filter (fun z => z.1 ∉ background g)) := by
  ext z
  simp only [sourceOriginalRemovePendingBackground434,Finset.mem_filter,
    Multiset.mem_toFinset,Multiset.mem_filter]
  tauto

/-- The dependent active G choice carrier is unchanged by removal of
background pending atoms. Deleted and born sets are retained literally. -/
def sourceOriginalActiveGhostRemovalEquiv434 :
    SourceOriginalGhostActiveChoice434 SP sm BP bm M background y ≃
      SourceOriginalGhostActiveChoice434 SP sm BP bm M background removed where
  toFun b g := (⟨(b g).1.1,by
    rw [source_original_G_ACTIVE_zero_removal434 SP sm BP bm M background y]
    exact (b g).1.2⟩,(b g).2)
  invFun b g := (⟨(b g).1.1,by
    rw [←source_original_G_ACTIVE_zero_removal434 SP sm BP bm M background y]
    exact (b g).1.2⟩,(b g).2)
  left_inv b := by
    funext g
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv b := by
    funext g
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

theorem source_original_G_ACTIVE_coefficient_removal434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background removed q rho N i V mu
      (sourceOriginalActiveGhostRemovalEquiv434 SP sm BP bm M background y b) =
    sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu b := by
  unfold sourceOriginalGhostActiveCoefficient434
  apply Finset.prod_congr rfl
  intro g hg
  unfold sourceOriginalGroupPrimeBirthWeight434 sourceOriginalRestrictedPrimeBirthLift434
  change _^(b g).1.1.card *
      _^((((removed.2 g).2.toFinset.filter (fun z => z.2=0)).filter
          (fun z => z.1 ∉ background g)).card-(b g).1.1.card) *
      _^(b g).2.1.card * (∏ p ∈ (b g).2.1,_) = _
  rw [source_original_G_ACTIVE_zero_removal434]

theorem source_original_G_ACTIVE_output_removal434
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalPhysicalGhostActiveOutput434 SP sm BP bm M background removed
      (sourceOriginalActiveGhostRemovalEquiv434 SP sm BP bm M background y b) =
    sourceOriginalPhysicalGhostActiveOutput434 SP sm BP bm M background y b := by
  apply Prod.ext
  · rfl
  · funext g
    apply Prod.ext
    · rfl
    · change sourceOriginalGhostPiecePending434 (bm g)
        ((removed.2 g).2.toFinset.filter (fun z => z.1 ∉ background g))
        (b g).1.1 (b g).2.1 = _
      rw [source_original_G_ACTIVE_pending_removal434]
      rfl

def sourceOriginalActiveGhostSeenRow434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y,
    if ∀ g,∀ p ∈ (b g).2.1,bm g p ∉ seen then
      sourceOriginalGhostActiveCoefficient434 SP sm BP bm M background y q rho N i V mu b *
      F (sourceOriginalPhysicalGhostActiveOutput434 SP sm BP bm M background y b)
        (seen ∪ sourceOriginalNumericBackground434 BP bm (fun g => (b g).2.1))
    else 0

/-- Exact active-row transport, including dependent sum carriers,
actual coefficients, output, birth gate and arbitrary joint observation. -/
theorem source_original_G_ACTIVE_seen_row_removal434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalActiveGhostSeenRow434 SP sm BP bm M background y q rho N i V mu seen F =
      sourceOriginalActiveGhostSeenRow434 SP sm BP bm M background removed q rho N i V mu seen F := by
  unfold sourceOriginalActiveGhostSeenRow434
  apply Fintype.sum_equiv (sourceOriginalActiveGhostRemovalEquiv434 SP sm BP bm M background y)
  intro b
  rw [source_original_G_ACTIVE_coefficient_removal434,source_original_G_ACTIVE_output_removal434]
  rfl
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalPhysicalGhostSeparateOperator -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ) (background : (g : BG) → Finset (BP g))
variable (y : FullPhysicalOutput SP sm BP bm M)
local notation "B" => sourceOriginalNumericBackground434 BP bm background

/-- Attach the literal background G output to an arbitrary physical
non-background output. This is an output reconstruction, not a
factorization of the joint observation. -/
def sourceOriginalGhostBackgroundAttachChoice434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (out : FullPhysicalOutput SP sm BP bm M) : FullPhysicalOutput SP sm BP bm M :=
  (out.1,fun g => ((out.2 g).1,
    sourceOriginalGhostPiecePending434 (bm g)
      ((y.2 g).2.toFinset.filter (fun z => z.1 ∈ background g))
      (a g).1.1 (a g).2.1 + (out.2 g).2))

theorem source_original_G_ATTACH_active_output434
    (a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y)
    (b : SourceOriginalGhostActiveChoice434 SP sm BP bm M background y) :
    sourceOriginalGhostBackgroundAttachChoice434 SP sm BP bm M background y a
      (sourceOriginalPhysicalGhostActiveOutput434 SP sm BP bm M background y b) =
    sourceOriginalPhysicalGhostPartitionOutput434 SP sm BP bm M background y a b := by
  rfl

/-- The non-background G operator acts on the removed physical input.
The full background output and numeric seen component are reattached
inside the same arbitrary joint F. -/
def sourceOriginalBackgroundSeparatedGhostOperator434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) : ℂ :=
  ∑ a : SourceOriginalGhostBackgroundChoice434 SP sm BP bm M background y,
    if ∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen ∩ B then
      sourceOriginalGhostBackgroundCoefficient434 SP sm BP bm M background y q rho N i V mu a *
      sourceOriginalActiveGhostSeenRow434 SP sm BP bm M background
        (sourceOriginalRemovePendingBackground434 SP sm BP bm M background y)
        q rho N i V mu (seen \ B)
        (fun out activeSeen =>
          F (sourceOriginalGhostBackgroundAttachChoice434 SP sm BP bm M background y a out)
            (((seen ∩ B) ∪ sourceOriginalNumericBackground434 BP bm (fun g => (a g).2.1)) ∪
              activeSeen))
    else 0

/-- Exact two-component identity with dependent active carriers
transported to the removed input. All numeric gates are retained. -/
theorem source_original_PHYSICAL_G_separate_operators434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (seen : Finset ℕ) (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    sourceOriginalGhostBackgroundSeenRow434 SP sm BP bm M background y q rho N i V mu seen F =
    sourceOriginalBackgroundSeparatedGhostOperator434 SP sm BP bm M background y q rho N i V mu seen F := by
  unfold sourceOriginalGhostBackgroundSeenRow434 sourceOriginalBackgroundSeparatedGhostOperator434
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←source_original_G_ACTIVE_seen_row_removal434 SP sm BP bm M background y]
  unfold sourceOriginalActiveGhostSeenRow434
  by_cases hb : ∀ g,∀ p ∈ (a g).2.1,bm g p ∉ seen ∩ B
  · rw [if_pos hb,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hbb
    by_cases hc : ∀ g,∀ p ∈ (b g).2.1,bm g p ∉ seen \ B
    · rw [if_pos ⟨hb,hc⟩,if_pos hc]
      dsimp only
      rw [source_original_G_ATTACH_active_output434,mul_assoc]
    · rw [if_neg (fun hh => hc hh.2),if_neg hc,mul_zero]
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro b hbb
    exact if_neg (fun hh => hb hh.1)

theorem source_original_PHYSICAL_MARKED_G_separate_operators434
    (cap : BG → ℕ) (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x : FullPhysicalState SP sm BP bm M cap) (seen : Finset ℕ)
    (hx : sourceOriginalPhysicalReachable434 SP sm BP bm M
      (physicalFockProjection SP sm BP bm M cap x) seen)
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (F : FullPhysicalOutput SP sm BP bm M → Finset ℕ → ℂ) :
    physicalGBirthMarkedRow SP sm BP bm M cap q rho N i V mu x seen F =
    sourceOriginalBackgroundSeparatedGhostOperator434 SP sm BP bm M background
      (physicalFockProjection SP sm BP bm M cap x) q rho N i V mu seen F := by
  rw [source_original_PHYSICAL_MARKED_G_background_split434
    SP sm BP bm M background cap hi q rho N i V mu x seen hx hcap F,
    source_original_PHYSICAL_G_background_seen_row434 SP sm BP bm M background _ hi,
    source_original_PHYSICAL_G_separate_operators434]
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalSourceEBackgroundCounter -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock
set_option autoImplicit false
set_option maxHeartbeats 18000000
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell m : ℕ) (cap : BG → ℕ)
variable {Nu : Type} [Fintype Nu] (patterns : Nu → SourcePattern BG J m)
variable (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
variable (background : (g : BG) → Finset (BP g))
local notation "B" => sourceOriginalNumericBackground434 BP bm background
include hi

/-- Every actual E frame avoiding background preserves the numerical
background counter, including an arbitrary reattached seen component. -/
theorem source_original_SOURCE_E_frame_background_counter434
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen carry : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (f : SourceOriginalSourceEFrameInjections434 SP sm BP bm J ell m cap patterns x r) :
    ((seen ∪ (orientedEFreshBirths SP sm BP bm J ell m cap patterns
      (sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f)).toFinset) ∪
        carry) ∩ B = (seen ∪ carry) ∩ B := by
  let z := sourceOriginalSourceEFrameLift434 SP sm BP bm J ell m cap patterns x r f
  have ht : ∀ g j,bm g ((z.2.2.1.bigChoice g).1 j) ∉ B := by
    intro g j hj
    exact htarget g j ((source_original_NUMERIC_BACKGROUND_mem434 BP bm hi background g _).mp hj)
  have hd := source_original_SOURCE_E_background_births_disjoint434
    SP sm BP bm J ell m cap patterns x z B ht
  ext p
  have hp : p ∈ B → p ∉ (orientedEFreshBirths SP sm BP bm J ell m cap patterns z).toFinset :=
    fun h => Finset.disjoint_left.mp hd h
  dsimp only [z] at hp
  simp only [Finset.mem_union,Finset.mem_inter]
  tauto

/-- The complete signed E coefficient and joint output are retained.
A background birth-count mark passes through the real Fourier/Mellin E
row because its actual fresh targets avoid background. -/
theorem source_original_SOURCE_E_frame_background_counter_row434
    (q rho u : ℝ) (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (K : SourcePatternK BP J ell m patterns) (zeta theta : ℝ)
    (x : FullPhysicalState SP sm BP bm (J+ell) cap) (seen carry : Finset ℕ)
    (r : SourceOriginalSourceEFrame434 SP sm BP J ell m patterns) (o k : ℤ)
    (htarget : ∀ g j,(r.2.2.1.2.2.1 g).1 j ∉ background g)
    (F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ) :
    (u:ℂ)^((seen ∪ carry) ∩ B).card *
      sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
        q rho Vs V mu K zeta theta o k x seen r F =
    sourceOriginalSourceEFrameFibreRow434 SP sm BP bm J ell m cap patterns
      q rho Vs V mu K zeta theta o k x seen r
      (fun out st => (u:ℂ)^((st ∪ carry) ∩ B).card * F out st) := by
  unfold sourceOriginalSourceEFrameFibreRow434
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  dsimp only
  rw [source_original_SOURCE_E_frame_background_counter434
    SP sm BP bm J ell m cap patterns hi background x seen carry r htarget f.1]
  ring
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredEvolutionGhostRow -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {U : Type} [Fintype U] [DecidableEq U]

theorem source_original_evolution_ghost_length434
    (old : List U) (A : Finset (Fin old.length)) {b : ℕ} (fresh : Fin b → U) :
    (afterGhost old A fresh).length = old.length-A.card+b := by
  have h := congrArg Multiset.card (memory_source_afterGhost_bag old A fresh)
  simpa [memoryTupleBag, Multiset.card_sum, Fintype.card_subtype_compl] using h

/-- Exact positive witness sum for one literal ghost group. Indexed OLD
deletions and all repeated fresh atoms are retained, with the original 1/b!. -/
theorem source_original_evolution_GHOST_weighted_sum_exact434
    (old : List U) (zero : U → Prop) [DecidablePred zero]
    (B : ℕ) (alpha chi gamma : ℂ) (nu : U → ℂ)
    (w : ℝ) (hw : 0 < w) :
    (∑ c : GhostWitnessChoice old zero B,
      ‖sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu‖ *
        w^(afterGhost old c.1.1 c.2.2).length) =
    w^old.length * (‖alpha‖/w+‖chi‖)^(zeroOld old zero).card *
      ∑ b ∈ Finset.range (B+1),
        (‖gamma‖*w*(∑ u : U,‖nu u‖))^b/(b.factorial:ℝ) := by
  classical
  let Z := zeroOld old zero
  have ha (A : {A : Finset (Fin old.length) // A ∈ Z.powerset}) :
      A.val.card ≤ old.length :=
    (Finset.card_le_card (Finset.mem_powerset.mp A.property)).trans
      (by simpa [Z,zeroOld] using
        (Finset.card_filter_le (Finset.univ : Finset (Fin old.length)) (fun j => zero (old.get j))))
  have ht (A : {A : Finset (Fin old.length) // A ∈ Z.powerset})
      (b : ℕ) (fresh : Fin b → U) :
      ‖sourceGhostTerm old zero A.val fresh alpha chi gamma nu‖ *
          w^(afterGhost old A.val fresh).length =
      w^old.length * ((‖alpha‖/w)^A.val.card * ‖chi‖^(Z.card-A.val.card)) *
        ((‖gamma‖*w)^b/(b.factorial:ℝ)) * ∏ j : Fin b,‖nu (fresh j)‖ := by
    rw [source_original_evolution_ghost_length434]
    simp only [sourceGhostTerm,norm_mul,norm_pow,norm_div,norm_one,norm_prod,
      Complex.norm_natCast]
    have hp : w^(old.length-A.val.card)*w^A.val.card=w^old.length := by
      rw [←pow_add,Nat.sub_add_cancel (ha A)]
    rw [pow_add,div_pow,mul_pow]
    dsimp only [Z] at *
    field_simp
    linear_combination (‖alpha‖^A.val.card * ‖chi‖^((zeroOld old zero).card-A.val.card) * ‖gamma‖^b * ∏ j : Fin b,‖nu (fresh j)‖) * hp
  simp only [GhostWitnessChoice,Fintype.sum_sigma]
  simp_rw [ht]
  have hs (A : {A : Finset (Fin old.length) // A ∈ Z.powerset}) (b : Fin (B+1)) :
      (∑ fresh : Fin b.val → U,
        w^old.length * ((‖alpha‖/w)^A.val.card * ‖chi‖^(Z.card-A.val.card)) *
          ((‖gamma‖*w)^b.val/(b.val.factorial:ℝ)) * ∏ j : Fin b.val,‖nu (fresh j)‖) =
      w^old.length * ((‖alpha‖/w)^A.val.card * ‖chi‖^(Z.card-A.val.card)) *
        ((‖gamma‖*w*(∑ u : U,‖nu u‖))^b.val/(b.val.factorial:ℝ)) := by
    rw [←Finset.mul_sum,←(Fintype.prod_sum (fun _ : Fin b.val => fun u : U => ‖nu u‖))]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]
    ring
  simp_rw [hs,←Finset.mul_sum]
  rw [←Finset.sum_mul]
  have hbin :
      (∑ A : {A : Finset (Fin old.length) // A ∈ Z.powerset},
        w^old.length * ((‖alpha‖/w)^A.val.card * ‖chi‖^(Z.card-A.val.card))) =
      w^old.length*(‖alpha‖/w+‖chi‖)^Z.card := by
    rw [←Finset.mul_sum]
    congr 1
    rw [←Finset.sum_subtype Z.powerset (fun A => Iff.rfl)
      (fun A => (‖alpha‖/w)^A.card * ‖chi‖^(Z.card-A.card))]
    exact Finset.sum_pow_mul_eq_add_pow _ _ _
  rw [hbin,Fin.sum_univ_eq_sum_range
    (fun b => (‖gamma‖*w*(∑ u : U,‖nu u‖))^b/(b.factorial:ℝ)) (B+1)]

/-- Uniform weighted row bound for the actual ghost witnesses, with
arbitrary repeated OLD particles and every finite birth cutoff. -/
theorem source_original_evolution_GHOST_weighted_row434
    (old : List U) (zero : U → Prop) [DecidablePred zero]
    (B : ℕ) (alpha chi gamma : ℂ) (nu : U → ℂ)
    (w : ℝ) (hw : 0 < w) (hcontrol : ‖alpha‖/w+‖chi‖ ≤ 1) :
    (∑ c : GhostWitnessChoice old zero B,
      ‖sourceGhostTerm old zero c.1.1 c.2.2 alpha chi gamma nu‖ *
        w^(afterGhost old c.1.1 c.2.2).length) ≤
      Real.exp (‖gamma‖*w*(∑ u : U,‖nu u‖))*w^old.length := by
  rw [source_original_evolution_GHOST_weighted_sum_exact434 old zero B alpha chi gamma nu w hw]
  have hx : 0 ≤ ‖gamma‖*w*(∑ u : U,‖nu u‖) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) hw.le) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hpow : (‖alpha‖/w+‖chi‖)^(zeroOld old zero).card ≤ 1 :=
    pow_le_one₀ (add_nonneg (div_nonneg (norm_nonneg _) hw.le) (norm_nonneg _)) hcontrol
  have he := Real.sum_le_exp_of_nonneg hx (B+1)
  have hs0 : 0 ≤ ∑ b ∈ Finset.range (B+1),
      (‖gamma‖*w*(∑ u : U,‖nu u‖))^b/(b.factorial:ℝ) :=
    Finset.sum_nonneg (fun b _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
  calc
    _ ≤ w^old.length*1*(∑ b ∈ Finset.range (B+1),
        (‖gamma‖*w*(∑ u : U,‖nu u‖))^b/(b.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (pow_nonneg hw.le _)) hs0
    _ ≤ w^old.length*Real.exp (‖gamma‖*w*(∑ u : U,‖nu u‖)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (pow_nonneg hw.le _)
    _ = _ := mul_comm _ _
end Green64Analytic.CorrelationSquare

end

end

/-! ## SourceOriginalUnfilteredForestGhostPadding -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64MemoryGhostOp
set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (J ell : ℕ) (cap : BG → ℕ)
local notation "State" => FullPhysicalState SP sm BP bm (J+ell) cap
local notation "Output" => FullPhysicalOutput SP sm BP bm (J+ell)

theorem source_original_forest_G_BIRTHS_LE_OLD434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (hn : physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z ≠ 0)
    (g : BG) : (z g).2.1.val ≤ (y.2 g).2.1.val := by
  have hh := congrArg List.length
    ((physical_nonzero_ghost_witness_is_operational SP sm BP bm (J+ell) cap
      q rho N i V mu x y z hn).2 g)
  simp only [afterGhost,List.length_append,List.length_map,List.length_ofFn,
    fockToList_length] at hh
  omega

/-- Actual adjacent OLD gate kills every G branch outside the proposed
padding width. This is an equality of scalar summands, not an operator-norm
comparison with a truncated signed G. -/
theorem source_original_forest_G_PADDING_EXACT434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (T : ℕ) (F : Output → ℂ) :
    physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z *
      (if (∑ g : BG,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2.card) ≤ T
       then F (physicalFockProjection SP sm BP bm (J+ell) cap y) else 0) =
    if (∀ g,(z g).2.1.val ≤ T) then
      physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z *
        (if (∑ g : BG,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2.card) ≤ T
         then F (physicalFockProjection SP sm BP bm (J+ell) cap y) else 0)
    else 0 := by
  by_cases hb : ∀ g,(z g).2.1.val ≤ T
  · rw [if_pos hb]
  rw [if_neg hb]
  by_cases hn : physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z=0
  · simp [hn]
  by_cases hT : (∑ g : BG,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2.card) ≤ T
  · exfalso
    apply hb
    intro g
    have hg := source_original_forest_G_BIRTHS_LE_OLD434 SP sm BP bm J ell cap
      q rho N i V mu x y z hn g
    have hsum : (y.2 g).2.1.val ≤ ∑ a : BG,(y.2 a).2.1.val :=
      Finset.single_le_sum (f := fun a : BG => (y.2 a).2.1.val) (fun a _ => Nat.zero_le _) (Finset.mem_univ g)
    have ht : (∑ a : BG,(y.2 a).2.1.val) ≤ T := by
      simpa [physicalFockProjection,fockMultiset] using hT
    exact hg.trans (hsum.trans ht)
  · simp [hT]

/-- Terminal vacuum forces every actual G_N fresh length to zero, while
leaving the full G_N itself unchanged. No initial active label is removed. -/
theorem source_original_forest_TERMINAL_G_NO_BIRTH434
    (q rho : ℝ) (N i : ℕ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : State) (z : FullGhostWitness SP sm BP bm (J+ell) cap x)
    (hn : physicalGBranchTerm SP sm BP bm (J+ell) cap q rho N i V mu x y z ≠ 0)
    (hv : physicalVacuum SP sm BP bm J ell
      (physicalFockProjection SP sm BP bm (J+ell) cap y) ≠ 0) :
    ∀ g,(z g).2.1.val=0 := by
  have hzero : ∀ g,((physicalFockProjection SP sm BP bm (J+ell) cap y).2 g).2=0 := by
    by_contra hh
    exact hv (by simp [physicalVacuum,hh])
  intro g
  have hcard := congrArg Multiset.card (hzero g)
  have hlen : (y.2 g).2.1.val=0 := by
    simpa [physicalFockProjection,fockMultiset] using hcard
  have hb := source_original_forest_G_BIRTHS_LE_OLD434 SP sm BP bm J ell cap
    q rho N i V mu x y z hn g
  omega
end Green64Analytic.CorrelationSquare

end

end

