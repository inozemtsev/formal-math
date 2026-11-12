module

public import Green64.Library.Correlation.RetiredPhysicalCoordinates

@[expose] public section

/-!
# Correlation / RetiredPhysicalGHilbert

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredPhysicalGHilbert -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

private theorem sum_injective_le {A X : Type} [Fintype A] [Fintype X]
    (e : A → X) (he : Function.Injective e) (f : X → ℝ) (hf : ∀ x,0 ≤ f x) :
    (∑ a,f (e a)) ≤ ∑ x,f x := by
  rw [←Finset.sum_image (fun a ha b hb h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun x hx hn => hf x)

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
local notation "X" => SourceOriginalFullReturnCoordinate434 SP sm BP bm M

def sourceOriginalRetiredBaseMass434 (Vs : SG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (a : (g : BG) → Fin M → BP g) : ℝ :=
  groupStateMass SP sm M Vs * ∏ g, activeMass M (mu g) (a g)

def sourceOriginalRetiredCoordinateDensity434 (tau : ℝ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) (x : X) : ℝ :=
  sourceOriginalRetiredBaseMass434 BP M SP sm Vs mu x.2.1 *
    sourceOriginalPrimeRetiredDensity434 (sourceOriginalRetiredFlatMod434 BP bm) 1 tau
      (sourceOriginalRetiredAvailableMass434 BP M V mu x.2.1)
      (sourceOriginalRetiredFlatten434 BP bm x.2.2)

private theorem base_pos (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (a : (g : BG) → Fin M → BP g) :
    0 < sourceOriginalRetiredBaseMass434 BP M SP sm Vs mu a := by
  unfold sourceOriginalRetiredBaseMass434 groupStateMass
  apply mul_pos
  · exact Finset.prod_pos (fun g hg => stateMass_positive (sm g) M (Vs g) (hVs g))
  · apply Finset.prod_pos
    intro g hg
    exact Finset.prod_pos (fun j hj => hmu g (a g j))

private theorem available_nonneg (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (a : (g : BG) → Fin M → BP g) (p : Sigma BP) :
    0 ≤ sourceOriginalRetiredAvailableMass434 BP M V mu a p := by
  unfold sourceOriginalRetiredAvailableMass434
  split_ifs
  · exact le_rfl
  · exact (mul_pos (hV p.1) (hmu p.1 p.2)).le

theorem source_original_RETIRED_coordinate_density_nonneg434
    (tau : ℝ) (ht : 0 < tau) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p) (x : X) :
    0 ≤ sourceOriginalRetiredCoordinateDensity434 BP bm M SP sm tau Vs V mu x :=
  mul_nonneg (base_pos BP M SP sm Vs mu hVs hmu x.2.1).le
    (source_original_RETIRED_prime_density_nonneg434
      (sourceOriginalRetiredFlatMod434 BP bm) 1 tau
      (sourceOriginalRetiredAvailableMass434 BP M V mu x.2.1)
      (by norm_num) ht.le (available_nonneg BP M V mu hV hmu x.2.1)
      (sourceOriginalRetiredFlatten434 BP bm x.2.2))

/-- Weighted column on the original SMALL/active block. The active
labels are excluded from the return pool, not charged as histories. -/
theorem source_original_RETIRED_physical_block_column434
    (eta tau : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1) (ht : 0 < tau)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (y : X) :
    (∑ x : X, sourceOriginalRetiredCoordinateDensity434 BP bm M SP sm tau Vs V mu x *
      ‖sourceOriginalRetiredGBlock434 BP bm M SP sm eta V mu x y‖) ≤
    Real.exp (eta/tau) *
      sourceOriginalRetiredCoordinateDensity434 BP bm M SP sm tau Vs V mu y := by
  let lam := sourceOriginalRetiredAvailableMass434 BP M V mu y.2.1
  let t := sourceOriginalRetiredFlatten434 BP bm y.2.2
  let D := sourceOriginalPrimeRetiredDensity434 (sourceOriginalRetiredFlatMod434 BP bm) 1 tau lam
  let K := fun (s t : SourceOriginalPrimeReturnProductState434
    (sourceOriginalRetiredFlatMod434 BP bm)) =>
    ∏ p : Sigma BP, sourceOriginalPrimeReturnKernel434
      (sourceOriginalRetiredFlatMod434 BP bm) p 0 eta 1 lam (s p) (t p)
  have hc :
      (∑ s : SourceOriginalFullReturnState434 BP bm,
        D (sourceOriginalRetiredFlatten434 BP bm s) *
          ‖K (sourceOriginalRetiredFlatten434 BP bm s) t‖) ≤
        Real.exp (eta/tau)*D t := by
    rw [(sourceOriginalRetiredFlatten434 BP bm).sum_comp (fun s => D s*‖K s t‖)]
    simpa only [mul_one] using
      source_original_RETIRED_prime_G_column434 (sourceOriginalRetiredFlatMod434 BP bm)
        0 eta 1 tau lam he he1 (by norm_num) ht
        (available_nonneg BP M V mu hV hmu y.2.1) t
  have hh := mul_le_mul_of_nonneg_left hc (base_pos BP M SP sm Vs mu hVs hmu y.2.1).le
  simpa [sourceOriginalRetiredGBlock434,sourceOriginalRetiredCoordinateDensity434,
    Fintype.sum_prod_type,ite_and,apply_ite,mul_ite,Finset.sum_ite_irrel,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm,lam,t,D,K] using hh

variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap
local notation "Y" => SourceOriginalFullReturnCoordinate434 SP sm BP bm (J+ell)

/-- One explicitly defined density on the EXISTING physical
Fock x numerical-seen carrier. It is fixed for every visit. -/
def sourceOriginalActualRetiredFockDensity434 (tau : ℝ)
    (Vs : SG → ℝ) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ) (a : H) : ℝ :=
  sourceOriginalRetiredCoordinateDensity434 BP bm (J+ell) SP sm tau Vs V mu
    (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a)

theorem source_original_ACTUAL_retired_density_pos434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (tau : ℝ) (ht : 0 < tau) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p) (a : H) :
    0 < sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu a := by
  let x := sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a
  unfold sourceOriginalActualRetiredFockDensity434 sourceOriginalRetiredCoordinateDensity434
  apply mul_pos (base_pos BP (J+ell) SP sm Vs mu hVs hmu x.2.1)
  rw [source_original_RETIRED_prime_density_exact434]
  apply mul_pos
  · apply Finset.prod_pos
    intro p hp
    change 0 < sourceOriginalRetiredAtomBase434 1 tau
      (sourceOriginalRetiredAvailableMass434 BP (J+ell) V mu x.2.1 p) (x.2.2 p.1 p.2)
    by_cases ha : p.2 ∈ sourceOriginalRetiredActive434 BP (J+ell) x.2.1 p.1
    · have hu := source_original_ACTUAL_retired_active_unborn434
        BP bm SP sm J ell cap hi a p.1 p.2 ha
      change x.2.2 p.1 p.2 = .unborn at hu
      rw [hu]
      norm_num [sourceOriginalRetiredAtomBase434]
    · have hl := mul_pos (hV p.1) (hmu p.1 p.2)
      rw [sourceOriginalRetiredAvailableMass434,if_neg ha]
      cases x.2.2 p.1 p.2 <;>
        simp only [sourceOriginalRetiredAtomBase434,one_mul]
      · norm_num
      · exact hl
      · exact mul_pos ht hl
  · exact_mod_cast Nat.factorial_pos _

/-- Original physical G columns in the new density. This is derived
from the exact numeric matrix and injective history coordinates. -/
theorem source_original_ACTUAL_retired_G_column434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N i : ℕ)
    (tau : ℝ) (ht : 0 < tau) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p) (b : H) :
    (∑ a : H, sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu a *
      ‖sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu a b‖) ≤
    Real.exp (sourceVisitEta q N i/tau) *
      sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu b := by
  let e := sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap
  let d := sourceOriginalRetiredCoordinateDensity434 BP bm (J+ell) SP sm tau Vs V mu
  let K := sourceOriginalRetiredGBlock434 BP bm (J+ell) SP sm (sourceVisitEta q N i) V mu
  have he := source_original_B26_visit_eta_unit434 q hq hq1 N i
  have hm (a : H) := source_original_ACTUAL_retired_G_matrix_exact434
    BP bm SP sm J ell cap hi hcap q N i Vs V mu hVs hmu a b
  simp_rw [hm]
  change (∑ a : H,d (e a)*‖K (e a) (e b)‖) ≤ _*d (e b)
  exact (sum_injective_le e
    (source_original_ACTUAL_retired_encode_injective434 BP bm SP sm J ell cap)
    (fun x : Y => d x*‖K x (e b)‖)
    (fun x => mul_nonneg
      (source_original_RETIRED_coordinate_density_nonneg434
        BP bm (J+ell) SP sm tau ht Vs V mu hVs hV hmu x)
      (norm_nonneg _))).trans
    (source_original_RETIRED_physical_block_column434
      BP bm (J+ell) SP sm _ tau he.1 he.2 ht Vs V mu hVs hV hmu (e b))

/-- Unconditional Hilbert bound for the ORIGINAL finite physical G
and every complex joint future, in the fixed retired-history density. -/
theorem source_original_ACTUAL_retired_G_Hilbert434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (N i : ℕ)
    (tau : ℝ) (ht : 0 < tau) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (f : H → ℂ) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu)
      (sourceOriginalSignedMatrixAction434
        (sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu) f) ≤
    (sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta q N i) V mu *
      Real.exp (sourceVisitEta q N i/tau)) *
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu) f := by
  let pi := sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu
  let G := sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu
  let R := sourceOriginalFullReturnSchurBudget434 BP (sourceVisitEta q N i) V mu
  let C := Real.exp (sourceVisitEta q N i/tau)
  let A := fun a b => pi a*‖G a b‖
  have hp := source_original_ACTUAL_retired_density_pos434
    BP bm SP sm J ell cap hi tau ht Vs V mu hVs hV hmu
  have hn (a : H) : 0 ≤ pi a := (hp a).le
  have ha (a b : H) : 0 ≤ A a b := mul_nonneg (hn a) (norm_nonneg _)
  have hr := (source_original_ACTUAL_G_true_row_column434 BP bm SP sm J ell cap
    hi hcap q hq hq1 N i Vs V mu hVs hV hmu).1
  have hrow (a : H) : (∑ b,A a b) ≤ R*pi a := by
    dsimp only [A]
    rw [←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hr a) (hn a)).trans_eq (mul_comm _ _)
  have hcol (b : H) : (∑ a,A a b) ≤ C*pi b :=
    source_original_ACTUAL_retired_G_column434 BP bm SP sm J ell cap
      hi hcap q hq hq1 N i tau ht Vs V mu hVs hV hmu b
  have he := (source_original_B26_visit_eta_unit434 q hq hq1 N i).1
  have hR : 0 ≤ R := Finset.prod_nonneg (fun g hg =>
    Finset.prod_nonneg (fun p hp =>
      add_nonneg zero_le_one (mul_nonneg he (mul_nonneg (hV g).le (hmu g p).le))))
  have hrowf (a : H) :
      pi a*‖sourceOriginalSignedMatrixAction434 G f a‖ ≤ ∑ b,A a b*‖f b‖ := by
    change pi a*‖∑ b,G a b*f b‖ ≤ _
    calc
      _ ≤ pi a*(∑ b,‖G a b*f b‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hn a)
      _ = _ := by simp only [A,norm_mul,Finset.mul_sum,mul_assoc]
  rw [source_original_SIGNED_forward_energy_as_sum434 pi hn,
    source_original_SIGNED_forward_energy_as_sum434 pi hn]
  exact source_original_finite_density_kernel_energy434 Finset.univ pi hn A ha R C hR
    (fun a ha => hrow a) (fun b hb => hcol b) f
    (sourceOriginalSignedMatrixAction434 G f) (fun a ha => hrowf a)

end Green64Analytic.CorrelationSquare

end

end

