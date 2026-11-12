module

public import Green64.Library.Weights.RetiredSourceGlobalBudget

@[expose] public section

/-!
# Correlation / RetiredPhysicalCoordinates

Local supporting lemmas for the prime-factor parity theorem.
-/

/-! ## SourceOriginalRetiredPhysicalCoordinates -/

section

open scoped BigOperators Classical
noncomputable section
namespace Green64Analytic.CorrelationSquare
open Green64FullPhysicalE Green64Fock Green64SmallHaar
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

def sourceOriginalRetiredSwap434 {R : Type} :
    SourceOriginalGhostReturnState434 R ≃ SourceOriginalGhostReturnState434 R where
  toFun
    | .unborn => .retired
    | .pending r => .pending r
    | .retired => .unborn
  invFun
    | .unborn => .retired
    | .pending r => .pending r
    | .retired => .unborn
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

variable {BG : Type} [Fintype BG] [DecidableEq BG]
variable (BP : BG → Type) [∀ g,Fintype (BP g)] [∀ g,DecidableEq (BP g)]
variable (bm : (g : BG) → BP g → ℕ) [∀ g p,NeZero (bm g p)]

abbrev sourceOriginalRetiredFlatMod434 (p : Sigma BP) : ℕ := bm p.1 p.2

def sourceOriginalRetiredFlatten434 :
    SourceOriginalFullReturnState434 BP bm ≃
      SourceOriginalPrimeReturnProductState434 (sourceOriginalRetiredFlatMod434 BP bm) where
  toFun s p := s p.1 p.2
  invFun s g p := s ⟨g,p⟩
  left_inv s := rfl
  right_inv s := rfl

variable (M : ℕ)

def sourceOriginalRetiredActive434
    (a : (g : BG) → Fin M → BP g) (g : BG) : Finset (BP g) :=
  Finset.univ.image (a g)

/-- Active primes are frozen by G and must not be charged as
retired histories. Their mass in the auxiliary return alphabet is zero. -/
def sourceOriginalRetiredAvailableMass434
    (V : BG → ℝ) (mu : (g : BG) → BP g → ℝ)
    (a : (g : BG) → Fin M → BP g) (p : Sigma BP) : ℝ :=
  if p.2 ∈ sourceOriginalRetiredActive434 BP M a p.1 then 0 else V p.1*mu p.1 p.2

variable {SG : Type} [Fintype SG] [DecidableEq SG]
variable (SP : SG → Type) [∀ g,Fintype (SP g)] [∀ g,DecidableEq (SP g)]
variable (sm : (g : SG) → SP g → ℕ) [∀ g p,NeZero (sm g p)]
local notation "X" => SourceOriginalFullReturnCoordinate434 SP sm BP bm M

/-- An invertible coordinate change, not a quotient of histories.
Only the frozen active coordinates exchange unborn and retired. -/
def sourceOriginalRetiredCoordinateSwap434 : X ≃ X where
  toFun x := (x.1,x.2.1,fun g p =>
    if p ∈ sourceOriginalRetiredActive434 BP M x.2.1 g
    then sourceOriginalRetiredSwap434 (x.2.2 g p) else x.2.2 g p)
  invFun x := (x.1,x.2.1,fun g p =>
    if p ∈ sourceOriginalRetiredActive434 BP M x.2.1 g
    then sourceOriginalRetiredSwap434 (x.2.2 g p) else x.2.2 g p)
  left_inv x := by
    rcases x with ⟨s,a,t⟩
    apply congrArg (fun z : SourceOriginalFullReturnState434 BP bm => (s,a,z))
    funext g p
    by_cases hp : p ∈ sourceOriginalRetiredActive434 BP M a g
    · simp only [if_pos hp]
      cases t g p <;> rfl
    · simp only [if_neg hp]
  right_inv x := by
    rcases x with ⟨s,a,t⟩
    apply congrArg (fun z : SourceOriginalFullReturnState434 BP bm => (s,a,z))
    funext g p
    by_cases hp : p ∈ sourceOriginalRetiredActive434 BP M a g
    · simp only [if_pos hp]
      cases t g p <;> rfl
    · simp only [if_neg hp]

def sourceOriginalRetiredGBlock434 (eta : ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (x y : X) : ℂ :=
  if x.1=y.1 ∧ x.2.1=y.2.1 then
    ∏ p : Sigma BP,
      sourceOriginalPrimeReturnKernel434 (sourceOriginalRetiredFlatMod434 BP bm) p 0 eta 1
        (sourceOriginalRetiredAvailableMass434 BP M V mu x.2.1)
        (sourceOriginalRetiredFlatten434 BP bm x.2.2 p)
        (sourceOriginalRetiredFlatten434 BP bm y.2.2 p)
  else 0

variable (J ell : ℕ) (cap : BG → ℕ)
local notation "H" => sourceOriginalActualSignedHistoryState434 SP sm BP bm J ell cap
local notation "Y" => SourceOriginalFullReturnCoordinate434 SP sm BP bm (J+ell)

def sourceOriginalActualReturnChoice434 (a : H) : Y :=
  Classical.choose (source_original_ACTUAL_full_return_exists434 SP sm BP bm J ell cap a)

theorem source_original_ACTUAL_return_choice_decode434 (a : H) :
    sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell)
      (sourceOriginalActualReturnChoice434 BP bm SP sm J ell cap a) = a.val :=
  Classical.choose_spec (source_original_ACTUAL_full_return_exists434 SP sm BP bm J ell cap a)

/-- A live original active label is seen and cannot simultaneously
be a pending ghost. Thus its literal return state is retired. -/
theorem source_original_ACTUAL_active_return_retired434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (a : H) (x : Y)
    (hx : sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x = a.val)
    (g : BG) (j : Fin (J+ell)) :
    x.2.2 g (x.2.1 g j) = .retired := by
  have ha := (source_original_ACTUAL_signed_history_mem_iff434
    SP sm BP bm J ell cap a.val.1 a.val.2).mp a.property
  have hr : sourceOriginalPhysicalReachable434 SP sm BP bm (J+ell)
      (sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x).1
      (sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x).2 := by
    rw [hx]
    exact ha.2.2
  let old := sourceOriginalPrimeProductPending434 (bm g) 0 (x.2.2 g)
  let active : Multiset ℕ := ∑ i : Fin (J+ell), ({bm g (x.2.1 g i)} : Multiset ℕ)
  have hslot : ({bm g (x.2.1 g j)} : Multiset ℕ) ≤ active := by
    have hh := Finset.sum_le_sum_of_subset
      (f := fun i : Fin (J+ell) => ({bm g (x.2.1 g i)} : Multiset ℕ))
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ j))
    simpa only [Finset.sum_singleton] using hh
  have hg : active + old.map (fun z => bm g z.1) ≤
      sourceOriginalPhysicalInventory434 SP sm BP bm (J+ell)
        (sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell) x).1 := by
    have hh := Finset.sum_le_sum_of_subset
      (f := fun k => sourceOriginalBigInventory434 (bm k) (J+ell)
        (x.2.1 k) (sourceOriginalPrimeProductPending434 (bm k) 0 (x.2.2 k)))
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ g))
    simpa only [Finset.sum_singleton,sourceOriginalPhysicalInventory434,
      sourceOriginalFullReturnDecode434,sourceOriginalBigInventory434,active,old] using hh
  have hmem : bm g (x.2.1 g j) ∈ active :=
    Multiset.mem_of_le hslot (by simp)
  have hseen : bm g (x.2.1 g j) ∈ sourceOriginalFullReturnSeen434 BP bm x.2.2 :=
    hr.2 _ (Multiset.mem_of_le hg (Multiset.mem_add.mpr (Or.inl hmem)))
  have hn := Multiset.nodup_of_le hg hr.1
  have hnot : bm g (x.2.1 g j) ∉ old.map (fun z => bm g z.1) :=
    fun hh => (Multiset.disjoint_left.mp (Multiset.nodup_add.mp hn).2.2) hmem hh
  cases hs : x.2.2 g (x.2.1 g j) with
  | retired => rfl
  | unborn =>
      have hh := (source_original_FULL_RETURN_seen_mem434 BP bm hi x.2.2 g (x.2.1 g j)).mp hseen
      rw [source_original_PRIME_PRODUCT_seen_mem434,hs] at hh
      simp [sourceOriginalOnePrimeSeen434] at hh
  | pending r =>
      exfalso
      apply hnot
      have hf : old.filter (fun z => z.1=x.2.1 g j) =
          ({⟨x.2.1 g j,r⟩} : Multiset (Atom (BP g) (bm g))) := by
        dsimp only [old]
        rw [source_original_PRIME_PRODUCT_pending_filter434,hs]
        simp [sourceOriginalOnePrimePending434]
      have hm : (⟨x.2.1 g j,r⟩ : Atom (BP g) (bm g)) ∈ old := by
        have hh : (⟨x.2.1 g j,r⟩ : Atom (BP g) (bm g)) ∈
            old.filter (fun z => z.1=x.2.1 g j) := by
          rw [hf]
          simp
        exact (Multiset.mem_filter.mp hh).1
      exact Multiset.mem_map.mpr ⟨⟨x.2.1 g j,r⟩,hm,rfl⟩

def sourceOriginalActualRetiredEncode434 (a : H) : Y :=
  sourceOriginalRetiredCoordinateSwap434 BP bm (J+ell) SP sm
    (sourceOriginalActualReturnChoice434 BP bm SP sm J ell cap a)

theorem source_original_ACTUAL_retired_encode_injective434 :
    Function.Injective (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap) := by
  intro a b hab
  have hh := (sourceOriginalRetiredCoordinateSwap434 BP bm (J+ell) SP sm).injective hab
  apply Subtype.ext
  exact (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap a).symm.trans
    ((congrArg (sourceOriginalFullReturnDecode434 SP sm BP bm (J+ell)) hh).trans
      (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap b))

theorem source_original_ACTUAL_retired_active_unborn434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (a : H) (g : BG) (p : BP g)
    (hp : p ∈ sourceOriginalRetiredActive434 BP (J+ell)
      (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a).2.1 g) :
    (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a).2.2 g p = .unborn := by
  let x := sourceOriginalActualReturnChoice434 BP bm SP sm J ell cap a
  have hp' : p ∈ sourceOriginalRetiredActive434 BP (J+ell) x.2.1 g := hp
  obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hp'
  have hr := source_original_ACTUAL_active_return_retired434 BP bm SP sm J ell cap hi a x
    (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap a) g j
  rw [hjp] at hr
  change (if p ∈ sourceOriginalRetiredActive434 BP (J+ell) x.2.1 g
    then sourceOriginalRetiredSwap434 (x.2.2 g p) else x.2.2 g p) = _
  rw [if_pos hp',hr]
  rfl

/-- The new weighted carrier still carries the EXACT original
physical G matrix, including numerical seen and active exclusions. -/
theorem source_original_ACTUAL_retired_G_matrix_exact434
    (hi : Function.Injective (fun p : Sigma BP => bm p.1 p.2))
    (hcap : ∀ g,Fintype.card (BP g) ≤ cap g)
    (q : ℝ) (N i : ℕ) (Vs : SG → ℝ) (V : BG → ℝ)
    (mu : (g : BG) → BP g → ℝ) (hVs : ∀ g,0 < Vs g) (hmu : ∀ g p,0 < mu g p)
    (a b : H) :
    sourceOriginalActualSignedGhostMatrix434 SP sm BP bm J ell cap q 1 N i V mu a b =
      sourceOriginalRetiredGBlock434 BP bm (J+ell) SP sm (sourceVisitEta q N i) V mu
        (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap a)
        (sourceOriginalActualRetiredEncode434 BP bm SP sm J ell cap b) := by
  let x := sourceOriginalActualReturnChoice434 BP bm SP sm J ell cap a
  let y := sourceOriginalActualReturnChoice434 BP bm SP sm J ell cap b
  rw [source_original_ACTUAL_G_return_matrix434 BP bm SP sm J ell cap
    hi hcap q N i Vs V mu hVs hmu a b x y
    (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap a)
    (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap b)]
  change sourceOriginalFullReturnGBlock434 BP bm SP sm (J+ell)
      (sourceVisitEta q N i) V mu x y =
    sourceOriginalRetiredGBlock434 BP bm (J+ell) SP sm (sourceVisitEta q N i) V mu
      (sourceOriginalRetiredCoordinateSwap434 BP bm (J+ell) SP sm x)
      (sourceOriginalRetiredCoordinateSwap434 BP bm (J+ell) SP sm y)
  unfold sourceOriginalFullReturnGBlock434 sourceOriginalRetiredGBlock434
  change (if x.1=y.1 ∧ x.2.1=y.2.1 then _ else 0) =
    (if x.1=y.1 ∧ x.2.1=y.2.1 then _ else 0)
  by_cases hxy : x.1=y.1 ∧ x.2.1=y.2.1
  · rw [if_pos hxy,if_pos hxy]
    rw [Fintype.prod_sigma]
    unfold sourceOriginalFullReturnGKernel434
    apply Finset.prod_congr rfl
    intro g hg
    apply Finset.prod_congr rfl
    intro p hp
    change sourceOriginalGhostReturnLiteralRow434 (-((0 : ℤ) : ZMod (bm g p)))
        (sourceVisitEta q N i) (V g*mu g p) (x.2.2 g p)
        (fun u => if u=y.2.2 g p then 1 else 0) =
      sourceOriginalGhostReturnLiteralRow434 (-((0 : ℤ) : ZMod (bm g p)))
        (sourceVisitEta q N i)
        (1*(if p ∈ sourceOriginalRetiredActive434 BP (J+ell) x.2.1 g then 0 else V g*mu g p))
        (if p ∈ sourceOriginalRetiredActive434 BP (J+ell) x.2.1 g
          then sourceOriginalRetiredSwap434 (x.2.2 g p) else x.2.2 g p)
        (fun u => if u=(if p ∈ sourceOriginalRetiredActive434 BP (J+ell) y.2.1 g
          then sourceOriginalRetiredSwap434 (y.2.2 g p) else y.2.2 g p) then 1 else 0)
    by_cases hact : p ∈ sourceOriginalRetiredActive434 BP (J+ell) x.2.1 g
    · have hacty : p ∈ sourceOriginalRetiredActive434 BP (J+ell) y.2.1 g := hxy.2 ▸ hact
      obtain ⟨j,hj,hjp⟩ := Finset.mem_image.mp hact
      obtain ⟨k,hk,hkp⟩ := Finset.mem_image.mp hacty
      have hx := source_original_ACTUAL_active_return_retired434 BP bm SP sm J ell cap hi a x
        (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap a) g j
      have hy := source_original_ACTUAL_active_return_retired434 BP bm SP sm J ell cap hi b y
        (source_original_ACTUAL_return_choice_decode434 BP bm SP sm J ell cap b) g k
      rw [hjp] at hx
      rw [hkp] at hy
      simp [sourceOriginalPrimeReturnKernel434,sourceOriginalRetiredCoordinateSwap434,
        sourceOriginalRetiredFlatten434,sourceOriginalRetiredAvailableMass434,
        sourceOriginalRetiredFlatMod434,hact,hacty,hx,hy,sourceOriginalRetiredSwap434,
        source_original_GHOST_RETURN_literal_retired434,source_original_GHOST_RETURN_literal_unborn434]
    · have hacty : p ∉ sourceOriginalRetiredActive434 BP (J+ell) y.2.1 g := hxy.2 ▸ hact
      simp only [sourceOriginalPrimeReturnKernel434,sourceOriginalRetiredCoordinateSwap434,
        sourceOriginalRetiredFlatten434,sourceOriginalRetiredAvailableMass434,
        sourceOriginalRetiredFlatMod434,Equiv.coe_fn_mk,if_neg hact,if_neg hacty,one_mul]
  · rw [if_neg hxy,if_neg hxy]

end Green64Analytic.CorrelationSquare

end

end

