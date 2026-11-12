module

public import Green64.Library.Correlation.RetiredPhysicalGHilbert

@[expose] public section

/-!
# Correlation / RetiredPhysicalVacuum

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredPhysicalVacuum -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

private theorem pending_zero_iff
    {P : Type} [Fintype P] [DecidableEq P]
    (modulus : P → ℕ) [∀ p,NeZero (modulus p)] (shift : ℤ)
    (s : SourceOriginalPrimeReturnProductState434 modulus) :
    sourceOriginalPrimeProductPending434 modulus shift s=0 ↔
      ∀ p, sourceOriginalGhostReturnVacuum434 (s p)=1 := by
  constructor
  · intro h p
    have hh : sourceOriginalOnePrimePending434 modulus p shift (s p)=0 := by
      rw [←source_original_PRIME_PRODUCT_pending_filter434, h]
      simp
    cases hs : s p with
    | unborn => rfl
    | retired => rfl
    | pending r =>
        have hc := congrArg Multiset.card hh
        simp [hs,sourceOriginalOnePrimePending434] at hc
  · intro h
    unfold sourceOriginalPrimeProductPending434
    apply Finset.sum_eq_zero
    intro p hp
    have hh := h p
    cases hs : s p <;>
      simp_all [sourceOriginalOnePrimePending434,sourceOriginalGhostReturnVacuum434]

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]
variable (M : ℕ)
variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
local notation "X" => SourceOriginalFullReturnCoordinate434 SP sm BP bm M

/-- The active-coordinate swap leaves the entire physical output
unchanged. Only its auxiliary return seen encoding changes. -/
theorem source_original_RETIRED_swap_output434 (x : X) :
    (sourceOriginalFullReturnDecode434 SP sm BP bm M
      (sourceOriginalRetiredCoordinateSwap434 BP bm M SP sm x)).1 =
    (sourceOriginalFullReturnDecode434 SP sm BP bm M x).1 := by
  apply Prod.ext
  · rfl
  funext g
  apply Prod.ext
  · rfl
  change sourceOriginalPrimeProductPending434 (bm g) 0
    (fun p => if p ∈ sourceOriginalRetiredActive434 BP M x.2.1 g
      then sourceOriginalRetiredSwap434 (x.2.2 g p) else x.2.2 g p) =
    sourceOriginalPrimeProductPending434 (bm g) 0 (x.2.2 g)
  unfold sourceOriginalPrimeProductPending434
  apply Finset.sum_congr rfl
  intro p hp
  change sourceOriginalOnePrimePending434 (bm g) p 0
      (if p ∈ sourceOriginalRetiredActive434 BP M x.2.1 g
        then sourceOriginalRetiredSwap434 (x.2.2 g p) else x.2.2 g p) =
    sourceOriginalOnePrimePending434 (bm g) p 0 (x.2.2 g p)
  by_cases ha : p ∈ sourceOriginalRetiredActive434 BP M x.2.1 g
  · rw [if_pos ha]
    cases x.2.2 g p <;> rfl
  · rw [if_neg ha]

def sourceOriginalRetiredReturnVacuum434
    (s : SourceOriginalFullReturnState434 BP bm) : ℂ :=
  if sourceOriginalPrimeProductPending434 (sourceOriginalRetiredFlatMod434 BP bm) 0
    (sourceOriginalRetiredFlatten434 BP bm s)=0 then 1 else 0

def sourceOriginalRetiredBoundaryBase434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) : ℝ :=
  ∑ s : GroupState SP sm M, ∑ a : (g : BG) → Fin M → BP g,
    sourceOriginalRetiredBaseMass434 BP M SP sm Vs mu a

/-- Exact SMALL/active boundary mass. There is no pending or seen
multiplicity and no factorial loss in the active array. -/
theorem source_original_RETIRED_boundary_base_exact434
    (Vs : SG → ℝ) (mu : (g : BG) → BP g → ℝ) :
    sourceOriginalRetiredBoundaryBase434 BP M SP sm Vs mu =
      (∑ s : GroupState SP sm M, groupStateMass SP sm M Vs) *
        ∏ g, (∑ p : BP g, mu g p)^M := by
  have ha : (∑ a : (g : BG) → Fin M → BP g,
      ∏ g, activeMass M (mu g) (a g)) =
      ∏ g, (∑ p : BP g, mu g p)^M := by
    rw [←Fintype.prod_sum (fun g (a : Fin M → BP g) => activeMass M (mu g) a)]
    apply Finset.prod_congr rfl
    intro g hg
    unfold activeMass
    rw [←Fintype.prod_sum (fun _j : Fin M => fun p : BP g => mu g p)]
    simp
  unfold sourceOriginalRetiredBoundaryBase434 sourceOriginalRetiredBaseMass434
  simp only [←Finset.mul_sum,ha]
  rw [Finset.sum_mul, Finset.mul_sum]

private theorem available_mass_bound
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (a : (g : BG) → Fin M → BP g) :
    (∑ p : Sigma BP, sourceOriginalRetiredAvailableMass434 BP M V mu a p) ≤
      ∑ g, ∑ p : BP g, V g*mu g p := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro g hg
  apply Finset.sum_le_sum
  intro p hp
  unfold sourceOriginalRetiredAvailableMass434
  split_ifs
  · exact (mul_pos (hV g) (hmu g p)).le
  · exact le_rfl

/-- The common global history weight controls the whole return
vacuum over each fixed active block, even with excluded active labels. -/
theorem source_original_RETIRED_fixed_active_vacuum_bound434
    (tau : ℝ) (ht : 0 < tau) (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (hM : tau*(∑ g, ∑ p : BP g, V g*mu g p)<1)
    (a : (g : BG) → Fin M → BP g) :
    (∑ s : SourceOriginalFullReturnState434 BP bm,
      sourceOriginalPrimeRetiredDensity434 (sourceOriginalRetiredFlatMod434 BP bm) 1 tau
        (sourceOriginalRetiredAvailableMass434 BP M V mu a)
        (sourceOriginalRetiredFlatten434 BP bm s) *
      ‖sourceOriginalRetiredReturnVacuum434 BP bm s‖^2) ≤
    1/(1-tau*(∑ g, ∑ p : BP g, V g*mu g p)) := by
  let lam := sourceOriginalRetiredAvailableMass434 BP M V mu a
  have hl (p : Sigma BP) : 0 ≤ lam p := by
    dsimp only [lam,sourceOriginalRetiredAvailableMass434]
    split_ifs
    · exact le_rfl
    · exact (mul_pos (hV p.1) (hmu p.1 p.2)).le
  have hmass := mul_le_mul_of_nonneg_left
    (available_mass_bound BP M V mu hV hmu a) ht.le
  have hm : tau*(∑ p : Sigma BP,lam p)<1 := hmass.trans_lt hM
  have hh := source_original_NUMERIC_RETIRED_terminal_energy434
    (sourceOriginalRetiredFlatMod434 BP bm) 1 tau lam (by norm_num) ht hl hm
    0 ∅ (fun _ => (1:ℂ)) (fun _ => by simp)
  have hs : (∑ s : SourceOriginalFullReturnState434 BP bm,
      sourceOriginalPrimeRetiredDensity434 (sourceOriginalRetiredFlatMod434 BP bm) 1 tau lam
        (sourceOriginalRetiredFlatten434 BP bm s) *
      ‖sourceOriginalRetiredReturnVacuum434 BP bm s‖^2) ≤ 1/(1-tau*(∑ p,lam p)) := by
    unfold sourceOriginalRetiredReturnVacuum434
    rw [(sourceOriginalRetiredFlatten434 BP bm).sum_comp
      (fun s => sourceOriginalPrimeRetiredDensity434
        (sourceOriginalRetiredFlatMod434 BP bm) 1 tau lam s *
        ‖if sourceOriginalPrimeProductPending434
          (sourceOriginalRetiredFlatMod434 BP bm) 0 s=0 then (1:ℂ) else 0‖^2)]
    exact hh
  exact hs.trans (one_div_le_one_div_of_le (sub_pos.mpr hM) (by linarith))

variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap
local notation "Y" => SourceOriginalFullReturnCoordinate434 SP sm BP bm (J+ell)

/-- Literal terminal vacuum under the actual injective history
encoding. No scalar-root invariance is used to change a norm. -/
theorem source_original_ACTUAL_retired_vacuum_exact434 (a : H) :
    physicalVacuum SP sm BP bm J ell a.val.1 =
      sourceOriginalRetiredReturnVacuum434 BP bm
        (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a).2.2 := by
  let x := sourceOriginalActualReturnChoice434 BP bm SP sm J ell cap a
  let y := sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a
  have ho : (sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) y).1 = a.val.1 :=
    (source_original_RETIRED_swap_output434 BP bm (J+ell) SP sm x).trans
      (congrArg Prod.fst (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap a))
  have hiff : (∀ g, sourceOriginalPrimeProductPending434 (bm g) 0 (y.2.2 g)=0) ↔
      sourceOriginalPrimeProductPending434 (sourceOriginalRetiredFlatMod434 BP bm) 0
        (sourceOriginalRetiredFlatten434 BP bm y.2.2)=0 := by
    simp_rw [pending_zero_iff]
    change (∀ g, ∀ p, sourceOriginalGhostReturnVacuum434 (y.2.2 g p)=1) ↔
      ∀ p : Sigma BP, sourceOriginalGhostReturnVacuum434 (y.2.2 p.1 p.2)=1
    exact ⟨fun h p => h p.1 p.2, fun h g p => h ⟨g,p⟩⟩
  rw [←ho]
  change (if ∀ g,sourceOriginalPrimeProductPending434 (bm g) 0 (y.2.2 g)=0
    then (1:ℂ) else 0) = _
  change (if ∀ g,sourceOriginalPrimeProductPending434 (bm g) 0 (y.2.2 g)=0
    then (1:ℂ) else 0) =
    (if sourceOriginalPrimeProductPending434 (sourceOriginalRetiredFlatMod434 BP bm) 0
      (sourceOriginalRetiredFlatten434 BP bm y.2.2)=0 then (1:ℂ) else 0)
  simp only [hiff]

/-- New quantitative endpoint estimate for the ORIGINAL physical
vacuum in the full Fock x seen carrier. Its only history factor
is geometric in the true total harmonic mass. -/
theorem source_original_ACTUAL_retired_vacuum_energy434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (tau : ℝ) (ht : 0 < tau) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ)
    (hVs : ∀ g,0 < Vs g) (hV : ∀ g,0 < V g) (hmu : ∀ g p,0 < mu g p)
    (hM : tau*(∑ g,∑ p : BP g,V g*mu g p)<1) :
    sourceOriginalSignedJointForwardEnergy434
      (sourceOriginalActualRetiredFockDensity434 BP bm SP sm J ell cap tau Vs V mu)
      (fun a : H => physicalVacuum SP sm BP bm J ell a.val.1) ≤
    sourceOriginalRetiredBoundaryBase434 BP (J+ell) SP sm Vs mu /
      (1-tau*(∑ g,∑ p : BP g,V g*mu g p)) := by
  let e := sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap
  let d := sourceOriginalRetiredCoordinateDensity434 BP bm (J+ell) SP sm tau Vs V mu
  let c := 1/(1-tau*(∑ g,∑ p : BP g,V g*mu g p))
  have hd (x : Y) : 0 ≤ d x :=
    source_original_RETIRED_coordinate_density_nonneg434
      BP bm (J+ell) SP sm tau ht Vs V mu hVs hV hmu x
  have hpi := source_original_ACTUAL_retired_density_pos434
    BP bm SP sm J ell cap hi tau ht Vs V mu hVs hV hmu
  rw [source_original_SIGNED_forward_energy_as_sum434 _ (fun a => (hpi a).le)]
  simp_rw [source_original_ACTUAL_retired_vacuum_exact434 BP bm SP sm J ell cap]
  have hne (x : Y) : 0 ≤ d x*‖sourceOriginalRetiredReturnVacuum434 BP bm x.2.2‖^2 :=
    mul_nonneg (hd x) (sq_nonneg _)
  have hsum : (∑ a : H,d (e a)*‖sourceOriginalRetiredReturnVacuum434 BP bm (e a).2.2‖^2) ≤
      ∑ x : Y,d x*‖sourceOriginalRetiredReturnVacuum434 BP bm x.2.2‖^2 := by
    have he : Function.Injective e :=
      source_original_ACTUAL_retired_encode_injective434 BP bm SP sm J ell cap
    have himage := Finset.sum_image (g := e)
      (f := fun x : Y => d x*‖sourceOriginalRetiredReturnVacuum434 BP bm x.2.2‖^2)
      (s := Finset.univ) (fun a ha b hb h => he h)
    rw [←himage]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x hx hn => hne x)
  apply hsum.trans
  rw [div_eq_mul_one_div]
  change (∑ x : Y,d x*‖sourceOriginalRetiredReturnVacuum434 BP bm x.2.2‖^2) ≤
    sourceOriginalRetiredBoundaryBase434 BP (J+ell) SP sm Vs mu*c
  unfold sourceOriginalRetiredBoundaryBase434
  simp only [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro a ha
  have hb : 0 ≤ sourceOriginalRetiredBaseMass434 BP (J+ell) SP sm Vs mu a := by
    unfold sourceOriginalRetiredBaseMass434 groupStateMass
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun g hg => (stateMass_positive (sm g) (J+ell) (Vs g) (hVs g)).le)
    · apply Finset.prod_nonneg
      intro g hg
      exact Finset.prod_nonneg (fun j hj => (hmu g (a g j)).le)
  have hh := mul_le_mul_of_nonneg_left
    (source_original_RETIRED_fixed_active_vacuum_bound434 BP bm (J+ell)
      tau ht V mu hV hmu hM a) hb
  simpa only [d,sourceOriginalRetiredCoordinateDensity434,Finset.mul_sum,mul_assoc,c] using hh

end Green64Analytic.CorrelationSquare

end

end

