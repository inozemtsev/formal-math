module

public import Green64.Library.Correlation.PhysicalReturnGTensor
public import Green64.Library.Weights.Part069
public import Green64.Library.Weights.Part068
public import Green64.Library.Weights.Part057

@[expose] public section

/-!
# Correlation / PhysicalReturnGSchur

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalPhysicalReturnGSchur -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64PhysicalEdge Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem sum_injective_le {A X : Type} [Fintype A] [Fintype X]
    (e : A → X) (he : Function.Injective e) (f : X → ℝ) (hf : ∀ x,0 ≤ f x) :
    (∑ a,f (e a)) ≤ ∑ x,f x := by
  classical
  rw [←Finset.sum_image (fun a ha b hb h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun x hx hn => hf x)

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

def sourceOriginalFullReturnSchurBudget434 (eta : ℝ)
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  ∏ g,∏ p,(1+eta*(V g*mu g p))

private def returnMass (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (s : SourceOriginalFullReturnState434 BP bm) : ℝ :=
  ∏ g,sourceOriginalPrimeReturnDensity434 (bm g) (V g) (mu g) (s g)

private theorem group_mass_nonneg (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (h : ∀ g p,0 ≤ V g*mu g p) (g : BG)
    (s : SourceOriginalPrimeReturnProductState434 (bm g)) :
    0 ≤ sourceOriginalPrimeReturnDensity434 (bm g) (V g) (mu g) s := by
  apply Finset.prod_nonneg
  intro p hp
  cases s p <;> simp [sourceOriginalReturnPendingMass434,h g p]

private theorem return_mass_nonneg (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (h : ∀ g p,0 ≤ V g*mu g p) (s : SourceOriginalFullReturnState434 BP bm) :
    0 ≤ returnMass BP bm V mu s :=
  Finset.prod_nonneg (fun g hg => group_mass_nonneg BP bm V mu h g (s g))

private theorem budget_nonneg (eta : ℝ)
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ eta) (h : ∀ g p,0 ≤ V g*mu g p) :
    0 ≤ sourceOriginalFullReturnSchurBudget434 BP eta V mu := by
  apply Finset.prod_nonneg
  intro g hg
  apply Finset.prod_nonneg
  intro p hp
  exact add_nonneg zero_le_one (mul_nonneg he (h g p))

private theorem return_row (eta : ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (h : ∀ g p,0 ≤ V g*mu g p)
    (s : SourceOriginalFullReturnState434 BP bm) :
    (∑ t,‖sourceOriginalFullReturnGKernel434 BP bm eta V mu s t‖) ≤
      sourceOriginalFullReturnSchurBudget434 BP eta V mu := by
  simp only [sourceOriginalFullReturnGKernel434,norm_prod]
  have hs : (∑ t : SourceOriginalFullReturnState434 BP bm,
      ∏ g,∏ p,‖sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s g p) (t g p)‖) =
      ∏ g,∑ t : SourceOriginalPrimeReturnProductState434 (bm g),
        ∏ p,‖sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s g p) (t p)‖ := by
    exact (Fintype.prod_sum (fun g (t : SourceOriginalPrimeReturnProductState434 (bm g)) =>
      ∏ p,‖sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s g p) (t p)‖)).symm
  rw [hs]
  apply Finset.prod_le_prod₀
  · intro g hg
    exact Finset.sum_nonneg (fun t ht => Finset.prod_nonneg (fun p hp => norm_nonneg _))
  · intro g hg
    simpa only [norm_prod] using source_original_PRIME_RETURN_G_row434
      (bm g) 0 eta (V g) (mu g) he he1 (h g) (s g)

private theorem return_column (eta : ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (h : ∀ g p,0 ≤ V g*mu g p)
    (t : SourceOriginalFullReturnState434 BP bm) :
    (∑ s,returnMass BP bm V mu s*‖sourceOriginalFullReturnGKernel434 BP bm eta V mu s t‖) ≤
      sourceOriginalFullReturnSchurBudget434 BP eta V mu * returnMass BP bm V mu t := by
  simp only [returnMass,sourceOriginalFullReturnGKernel434,norm_prod,←Finset.prod_mul_distrib]
  have hs : (∑ s : SourceOriginalFullReturnState434 BP bm,
      ∏ g,sourceOriginalPrimeReturnDensity434 (bm g) (V g) (mu g) (s g) *
        ∏ p,‖sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s g p) (t g p)‖) =
      ∏ g,∑ s : SourceOriginalPrimeReturnProductState434 (bm g),
        sourceOriginalPrimeReturnDensity434 (bm g) (V g) (mu g) s *
        ∏ p,‖sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s p) (t g p)‖ := by
    exact (Fintype.prod_sum (fun g (s : SourceOriginalPrimeReturnProductState434 (bm g)) =>
      sourceOriginalPrimeReturnDensity434 (bm g) (V g) (mu g) s *
        ∏ p,‖sourceOriginalPrimeReturnKernel434 (bm g) p 0 eta (V g) (mu g) (s p) (t g p)‖)).symm
  rw [hs]
  rw [sourceOriginalFullReturnSchurBudget434,←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro g hg
    exact Finset.sum_nonneg (fun s hs => mul_nonneg
      (group_mass_nonneg BP bm V mu h g s)
      (Finset.prod_nonneg (fun p hp => norm_nonneg _)))
  · intro g hg
    simpa only [norm_prod] using source_original_PRIME_RETURN_G_column434
      (bm g) 0 eta (V g) (mu g) he he1 (h g) (t g)

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
variable (M : ℕ)

def sourceOriginalFullReturnGBlock434 (eta : ℝ)
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (x y : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) : ℂ :=
  if x.1=y.1 ∧ x.2.1=y.2.1 then
    sourceOriginalFullReturnGKernel434 BP bm eta V mu x.2.2 y.2.2 else 0

private def baseMass (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : (g : BG) → Fin M → BP g) : ℝ :=
  groupStateMass SP sm M Vs * ∏ g,activeMass M (mu g) (a g)

private theorem density_factor (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) :
    sourceOriginalFullReturnDensity434 SP sm BP bm M Vs V mu x =
      baseMass BP SP sm M Vs mu x.2.1 * returnMass BP bm V mu x.2.2 := by
  simp only [sourceOriginalFullReturnDensity434,baseMass,returnMass,
    Finset.prod_mul_distrib,mul_assoc]

private theorem base_mass_nonneg (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (a : (g : BG) → Fin M → BP g) :
    0 ≤ baseMass BP SP sm M Vs mu a := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun g hg =>
      (stateMass_positive (sm g) M (Vs g) (hVs g)).le)
  · apply Finset.prod_nonneg
    intro g hg
    exact Finset.prod_nonneg (fun j hj => (hmu g (a g j)).le)

private theorem coordinate_mass_nonneg (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) :
    0 ≤ sourceOriginalFullReturnDensity434 SP sm BP bm M Vs V mu x := by
  rw [density_factor]
  exact mul_nonneg (base_mass_nonneg BP SP sm M Vs mu hVs hmu x.2.1)
    (return_mass_nonneg BP bm V mu (fun g p => mul_nonneg (hV g).le (hmu g p).le) x.2.2)

private theorem block_row (eta : ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (he : 0 ≤ eta) (he1 : eta ≤ 1) (h : ∀ g p,0 ≤ V g*mu g p)
    (x : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) :
    (∑ y,‖sourceOriginalFullReturnGBlock434 BP bm SP sm M eta V mu x y‖) ≤
      sourceOriginalFullReturnSchurBudget434 BP eta V mu := by
  simpa [sourceOriginalFullReturnGBlock434,Fintype.sum_prod_type,ite_and,apply_ite,
    Finset.sum_ite_irrel] using return_row BP bm eta V mu he he1 h x.2.2

private theorem block_column (eta : ℝ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (y : SourceOriginalFullReturnCoordinate434 SP sm BP bm M) :
    (∑ x,sourceOriginalFullReturnDensity434 SP sm BP bm M Vs V mu x *
      ‖sourceOriginalFullReturnGBlock434 BP bm SP sm M eta V mu x y‖) ≤
      sourceOriginalFullReturnSchurBudget434 BP eta V mu *
        sourceOriginalFullReturnDensity434 SP sm BP bm M Vs V mu y := by
  have h := mul_le_mul_of_nonneg_left
    (return_column BP bm eta V mu he he1
      (fun g p => mul_nonneg (hV g).le (hmu g p).le) y.2.2)
    (base_mass_nonneg BP SP sm M Vs mu hVs hmu y.2.1)
  simpa [sourceOriginalFullReturnGBlock434,density_factor,Fintype.sum_prod_type,
    ite_and,apply_ite,mul_ite,Finset.sum_ite_irrel,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h

variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap
local notation "X" => SourceOriginalFullReturnCoordinate434 SP sm BP bm (J+ell)

/-- Every entry of the actual finite physical G matrix is exactly an entry
of the explicit return matrix, with the original SMALL/active block fixed. -/
theorem source_original_ACTUAL_G_return_matrix434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (a b : H) (x y : X)
    (hx : sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x=a.val)
    (hy : sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) y=b.val) :
    sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu a b =
      sourceOriginalFullReturnGBlock434 BP bm SP sm (J+ell)
        (sourceVisitEta q N i) V mu x y := by
  let F : FullPhysicalOutput SP sm BP bm (J+ell) → Finset ℕ → ℂ :=
    fun out seen => if (out,seen)=b.val then 1 else 0
  have ha := source_original_ACTUAL_original_G_matrix_exact434
    SP sm BP bm J ell cap hi hcap q 1 N i Vs V mu hVs hmu F a
  have hf (c : H) : F c.val.1 c.val.2 = if c=b then 1 else 0 := by
    dsimp only [F]
    by_cases hc : c=b
    · subst c
      simp
    · have hv : (c.val.1,c.val.2) ≠ b.val := fun h => hc (Subtype.ext h)
      rw [if_neg hv,if_neg hc]
  simp_rw [hf,mul_ite,mul_one,mul_zero] at ha
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at ha
  have ht := source_original_PHYSICAL_G_full_return434 SP sm BP bm (J+ell)
    hi q N i V mu x F
  rw [hx] at ht
  rw [ha] at ht
  refine ht.trans ?_
  unfold sourceOriginalFullReturnG434 sourceOriginalFullReturnGBlock434
  have hdec (t : SourceOriginalFullReturnState434 BP bm) :
      sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) (x.1,x.2.1,t)=b.val ↔
        (x.1=y.1 ∧ x.2.1=y.2.1) ∧ t=y.2.2 := by
    rw [←hy,(source_original_FULL_RETURN_decode_injective434 SP sm BP bm (J+ell) hi).eq_iff]
    simp only [Prod.ext_iff]
    tauto
  change (∑ t,sourceOriginalFullReturnGKernel434 BP bm (sourceVisitEta q N i) V mu x.2.2 t *
    (if sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) (x.1,x.2.1,t)=b.val then 1 else 0))=_
  simp_rw [hdec]
  by_cases hb : x.1=y.1 ∧ x.2.1=y.2.1
  · simp [hb]
  · simp [hb]

/-- True weighted rows and columns of physical G on the entire original
reachable Fock×seen carrier. There is no history count, future mask bound,
or new density assumption. -/
theorem source_original_ACTUAL_G_true_row_column434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N i : ℕ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p) :
    (∀ a : H,(∑ b : H,‖sourceOriginalActualSignedGhostMatrix434
      SP sm BP bm J ell cap q 1 N i V mu a b‖) ≤
        sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta q N i) V mu) ∧
    (∀ b : H,(∑ a : H,
      sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu a *
      ‖sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu a b‖) ≤
        sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta q N i) V mu *
        sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu b) := by
  let e : H → X := fun a =>
    Classical.choose (source_original_ACTUAL_full_return_exists434 SP sm BP bm J ell cap a)
  have hs (a : H) : sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) (e a)=a.val :=
    Classical.choose_spec (source_original_ACTUAL_full_return_exists434 SP sm BP bm J ell cap a)
  have hei : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact (hs a).symm.trans ((congrArg
      (sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell)) hab).trans (hs b))
  have hd (a : H) := source_original_ACTUAL_full_return_density434
    SP sm BP bm J ell cap Vs V mu a (e a) (hs a)
  have hm (a b : H) := source_original_ACTUAL_G_return_matrix434 BP bm SP sm J ell cap
    hi hcap q N i Vs V mu hVs hmu a b (e a) (e b) (hs a) (hs b)
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  constructor
  · intro a
    simp_rw [hm]
    exact (sum_injective_le e hei
      (fun y => ‖sourceOriginalFullReturnGBlock434 BP bm SP sm (J+ell)
        (sourceVisitEta q N i) V mu (e a) y‖) (fun y => norm_nonneg _)).trans
      (block_row BP bm SP sm (J+ell) _ V mu he.1 he.2
        (fun g p => mul_nonneg (hV g).le (hmu g p).le) (e a))
  · intro b
    simp_rw [hm,←hd]
    exact (sum_injective_le e hei
      (fun x => sourceOriginalFullReturnDensity434 SP sm BP bm (J+ell) Vs V mu x *
        ‖sourceOriginalFullReturnGBlock434 BP bm SP sm (J+ell)
          (sourceVisitEta q N i) V mu x (e b)‖)
      (fun x => mul_nonneg
        (coordinate_mass_nonneg BP bm SP sm (J+ell) Vs V mu hVs hV hmu x)
        (norm_nonneg _))).trans
      (block_column BP bm SP sm (J+ell) _ Vs V mu he.1 he.2 hVs hV hmu (e b))

/-- Quantitative bound for the actual Schur gain already used by the
physical Hilbert-E budget. The bound uses the SAME true physical pi. -/
theorem source_original_ACTUAL_G_true_Schur_gain434
    (hi : Function.Injective (fun x : Sigma BP => bm x.1 x.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N i : ℕ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p) :
    sourceOriginalSignedOneStepSchurGain434
      (sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu)
      (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu) ≤
      (sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta q N i) V mu)^2 := by
  let π := sourceOriginalActualSignedTrueFockDensity434 SP sm BP bm J ell cap Vs V mu
  let G := sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu
  let C := sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta q N i) V mu
  have hπ := source_original_ACTUAL_signed_true_fock_density_pos434
    SP sm BP bm J ell cap Vs V mu hVs hV hmu
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hC : 0 ≤ C := budget_nonneg BP _ V mu he.1
    (fun g p => mul_nonneg (hV g).le (hmu g p).le)
  have hh := source_original_ACTUAL_G_true_row_column434 BP bm SP sm J ell cap
    hi hcap q hq hq1 N i Vs V mu hVs hV hmu
  have hr : sourceOriginalSignedRowSchurMax434 G ≤ C := by
    apply Finset.sup'_le
    intro a ha
    cases a with
    | none => exact hC
    | some a => exact hh.1 a
  have hc : sourceOriginalSignedColumnSchurMax434 π G ≤ C := by
    apply Finset.sup'_le
    intro b hb
    cases b with
    | none => exact hC
    | some b => exact (div_le_iff₀ (hπ b)).mpr (hh.2 b)
  exact (mul_le_mul hc hr (source_original_SIGNED_row_Schur_max_nonneg434 G) hC).trans_eq
    (pow_two C).symm

end Green64Analytic.CorrelationSquare

end

end

